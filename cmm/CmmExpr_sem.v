Require Import List.
Import ListNotations.
Require Import BinPosDef.

Require Import compcert.common.Memory.
Require Import compcert.common.AST.
Require Import compcert.common.Values.

Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.

Require Import GHC.CmmExpr.
Require Import GHC.CmmType.
Require Import GHC.CmmMachOp.
Require Import GHC.Unique.

Require Import Cminor.Cminor.

Require Import CmmType_sem.
Require Import Identifiers.

(* FIXME: Implement all literals *)
Definition cmmLitDenote (l : CmmLit) : option val :=
  match l with
  | CmmInt n _ => Some (Vlong (Int64.repr n)) (* Ignore upper bits *)
  | CmmFloat rat w => match w with
                      | W32 => None
                      | W64 => None
                      | _ => None
                      end
  | CmmLabel lab => None
  | CmmLabelOff lab off => None
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

Definition globalRegToChunk (g:GlobalReg) : memory_chunk :=
  match g with
  | VanillaReg _ _ => Many64
  | FloatReg _     => Mfloat32
  | DoubleReg _    => Mfloat64
  | LongReg _      => Mint64
  | BaseReg        => Many64
  | PicBaseReg     => Many64
  end.

Local Open Scope Z_scope.

Definition globalRegToPtr (g:GlobalReg) : option val :=
  let off_zero := (Ptrofs.of_int64 Int64.zero)
  in match g with
     | VanillaReg r _ => match Int64.unsigned r with
                         | 1 => Some (Vptr _R1 off_zero)
                         | 2 => Some (Vptr _R2 off_zero)
                         | 3 => Some (Vptr _R3 off_zero)
                         | 4 => Some (Vptr _R4 off_zero)
                         | 5 => Some (Vptr _R5 off_zero)
                         | 6 => Some (Vptr _R6 off_zero)
                         | 7 => Some (Vptr _R7 off_zero)
                         | 8 => Some (Vptr _R8 off_zero)
                         | 9 => Some (Vptr _R9 off_zero)
                         | 10 => Some (Vptr _R10 off_zero)
                         | _ => None
                         end
     | FloatReg f     => match Int64.unsigned f with
                         | 1 => Some (Vptr _F1 off_zero)
                         | 2 => Some (Vptr _F2 off_zero)
                         | 3 => Some (Vptr _F3 off_zero)
                         | 4 => Some (Vptr _F4 off_zero)
                         | 5 => Some (Vptr _F5 off_zero)
                         | 6 => Some (Vptr _F6 off_zero)
                         | _ => None
                         end
     | DoubleReg d    => match Int64.unsigned d with
                         | 1 => Some (Vptr _D1 off_zero)
                         | 2 => Some (Vptr _D2 off_zero)
                         | 3 => Some (Vptr _D3 off_zero)
                         | 4 => Some (Vptr _D4 off_zero)
                         | 5 => Some (Vptr _D5 off_zero)
                         | 6 => Some (Vptr _D6 off_zero)
                         | _ => None
                         end
     | LongReg l      => None (* These seem to be unused now *)
     | BaseReg        => Some (Vptr _BaseReg off_zero)
     | PicBaseReg     => Some (Vptr _PicBaseReg off_zero)
     end.


(* FIXME: Implement all expressions *)
Fixpoint cmmExprDenote (m:mem) (en:env) (sp:val) (e:CmmExpr) : option val :=
  match e with
  | CE_CmmLit l => cmmLitDenote l
  | CE_CmmLoad e' t => match (cmmExprDenote m en sp e') with
                       | None => None
                       | Some v => Mem.loadv (cmmTypeToChunk t) m v
                       end
  | CE_CmmReg r => match r with
                   | CmmLocal (LR_LocalReg u t) => PTree.get u en
                   | CmmGlobal g => match globalRegToPtr g with
                                    | None   => None
                                    | Some p => Mem.loadv (globalRegToChunk g) m p
                                    end
                   end
  | CE_CmmMachOp mo ps => moDenote mo (List.map (cmmExprDenote m en sp) ps)
  | CE_CmmStackSlot a off => Some (Val.offset_ptr sp (Ptrofs.of_int64 off)) (* TODO parameter a: What is the semantics of an Area? *)
  | CE_CmmRegOff r off => match r with
                          | CmmLocal (LR_LocalReg u t) => match PTree.get u en with
                                                          | Some v => Some(Val.offset_ptr sp (Ptrofs.of_int64 off))
                                                          | None => None
                                                          end
                          | CmmGlobal g =>
                            match globalRegToPtr g with
                            | None   => None
                            | Some p => match Mem.loadv (globalRegToChunk g) m p with
                                        | Some v => Some(Val.offset_ptr sp (Ptrofs.of_int64 off))
                                        | None => None
                                        end
                            end
                          end
  end.


(* This is much prettier in monadic notation *)
Fixpoint cmmExprListDenote (m:mem) (en:env) (sp:val) (es:list CmmExpr) : option (list val) :=
  match es with
  | [] => Some []
  | e::es' => match cmmExprDenote m en sp e with
              | None => None
              | Some v => match (cmmExprListDenote m en sp es') with
                          | Some vs => Some (v::vs)
                          | None => None
                          end
              end
  end.

(* Cminor semantics *)

Definition cmmLitToCminorConst (l:CmmLit) : constant :=
  match l with
  | CmmInt i W64 => Olongconst (Int64.repr i)
  | CmmInt i W32 => Ointconst (Int.repr i)
  | _            => Ointconst (Int.repr 0)
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
