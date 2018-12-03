Require Import List.
Import ListNotations.
Require Import BinPosDef.

Require Import compcert.common.Memory.
Require Import compcert.common.AST.
Require Import compcert.common.Values.

Require Import compcert.lib.Integers.

Require Import GHC.CmmExpr.
Require Import GHC.CmmType.
Require Import GHC.CmmMachOp.
Require Import GHC.Unique.

Require Import Cminor.Cminor.

Require Import CmmType_sem.

(* FIXME: Implement all literals *)
Definition cmmLitDenote (l : CmmLit) : option val :=
  match l with
  | CmmInt n _ => Some (Vlong (Int64.repr n)) (* Ignore upper bits *)
  | CmmFloat rat w => match w with
                      | W32 => None
                      | W64 => None
                      | _ => None
                      end
  | CmmLabel l => None
  | CmmLabelOff l off => None
  | CmmLabelDiffOff l1 l2 off w => None
  | CmmBlock blk => None
  | CmmHighStackMark => None
  end.

Definition moDenote (mo : MachOp) (ps : list (option val)) : option val :=
  match mo,ps with
  | MO_Add _, [Some v1;Some v2] => Some (Val.addl v1 v2)
  | MO_Sub _, [Some v1;Some v2] => Some (Val.subl v1 v2)
  | MO_Eq _,  [Some v1;Some v2] => Val.cmpl Ceq v1 v2
  | MO_Ne _,  [Some v1;Some v2] => Val.cmpl Cne v1 v2
  | MO_Mul _, [Some v1;Some v2] => Some (Val.mull v1 v2)
  | _, _ => None
  end.

(* FIXME: Implement all expressions *)
Fixpoint cmmExprDenote (m : mem) (e : CmmExpr) : option val :=
  match e with
  | CE_CmmLit l => cmmLitDenote l
  | CE_CmmLoad e' t => match (cmmExprDenote m e') with
                       | None => None
                       | Some v => Mem.loadv (cmmTypeToChunk t) m v
                       end
  | CE_CmmMachOp mo ps => moDenote mo (List.map (cmmExprDenote m) ps)
  | _ => None
  end.

(* Cminor semantics *)

Definition cmmLitToCminorConst (l:CmmLit) : constant :=
  match l with
  | CmmInt i W64 => Olongconst (Int64.repr i)
  | CmmInt i W32 => Ointconst (Int.repr i)
  | _            => Ointconst (Int.repr 0)
  end.


Definition globalRegToChunk (g:GlobalReg) : memory_chunk :=
  match g with
  | VanillaReg _ _ => Many64
  | FloatReg _     => Mfloat32
  | DoubleReg _    => Mfloat64
  | LongReg _      => Mint64
  | BaseReg        => Many64
  | PicBaseReg     => Many64
  end.

Definition globalRegToExpr (g:GlobalReg) :expr :=
  Econst (Oaddrsymbol 1%positive (Ptrofs.of_int64 Int64.zero)). (* TODO: Give each register its own memory location :-) *)

Definition eight := Int64.repr 8.


Fixpoint cmmExprToCminorExpr (e:CmmExpr) {struct e} : expr :=
  let regToExpr := fun r => match r with
                            | CmmLocal (LR_LocalReg l t) => Evar (uniqueToIdent l) (* What to do with type? *) 
                            | CmmGlobal g => Eload (globalRegToChunk g) (globalRegToExpr g)
                            end
  in
  match e with
  | CE_CmmLit l => Econst (cmmLitToCminorConst l)
  | CE_CmmLoad e t => Eload (cmmTypeToChunk t) (cmmExprToCminorExpr e)
  | CE_CmmReg r => regToExpr r
  | CE_CmmMachOp mo exs => let cmexs := List.map cmmExprToCminorExpr exs
                           in
                           let binop op := match cmexs with
                                           | [x1;x2] => Ebinop op x1 x2
                                           | _ => Econst (Ointconst (Int.repr 0)) (* panic *)
                                           end
                           in match mo with
                              | MO_Add _ => binop Oadd
                              | MO_Sub _ => binop Osub
                              | MO_Eq _  => binop (Ocmpl Ceq)
                              | MO_Ne _  => binop (Ocmpl Cne)
                              | MO_Mul _ => binop Omul
                              end
  | CE_CmmStackSlot area slot => Econst (Oaddrstack (Ptrofs.of_int64 (Int64.mul slot eight))) 
  | CE_CmmRegOff r off => Ebinop Oadd (regToExpr r) (Econst (cmmLitToCminorConst (CmmInt 0%Z W64))) (* FIXME: We need fromIntegral here *)
  end.
