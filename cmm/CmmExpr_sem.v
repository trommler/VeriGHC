Require Import List.
Import ListNotations.
Require Import BinPosDef.

Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import common.HaskellValues.

Require Import GHC.CmmExpr.
Require Import GHC.CmmType.
Require Import GHC.CmmMachOp.
Require Import GHC.Unique.

Require Import Cminor.Cminor.

Require Import CmmType_sem.

(* Remove the following imports when we switch to comcert memory *)
Require Import compcert.common.Values.
Require Import heap.

(* FIXME: Implement all literals *)
Definition cmmLitDenote (l : CmmLit) : hval :=
  match l with
  | CmmInt n width => match width with
                      | W64 => HSint (Int64.repr n)
                      | _ => HSundef
                      end
  | _ => HSundef
  end.

Definition moDenote (mo : MachOp) (ps : list hval) : hval :=
  match mo,ps with
  | MO_Add W64, v1::v2::nil => HaskellVal.add v1 v2
  | MO_Sub W64, v1::v2::nil => HaskellVal.sub v1 v2
  | MO_Eq W64, v1::v2::nil => HaskellVal.cmp Ceq v1 v2
  | MO_Ne W64, v1::v2::nil => HaskellVal.cmp Cne v1 v2
  | MO_Mul W64, v1::v2::nil => HaskellVal.mul v1 v2
  | _, _ => HSundef
  end.

Definition from_block (b : block) : ptr :=
  pred (Pos.to_nat b).

Definition from_CmmType (t: CmmType) (v: cmmTypeDenote t) : hval :=
  (match t return cmmTypeDenote t -> hval with
   | CT_CmmType BitsCat W64 => fun v => HSint v
   | _ => fun _ => HSundef
   end) v.

Definition read_heap (p : hval) (h : heap) : option hval :=
  match p with
  | HSptr blk _ => match lookup (from_block blk) h with (* ignore offset for now *)
                   | None => None
                   | Some v => match v with
                               | existT t' v' => Some (from_CmmType t' v')
                               end
                   end
  | _ => None
  end.

(* FIXME: Implement all expressions *)
Fixpoint cmmExprDenote (h : heap) (e : CmmExpr) : hval :=
  match e with
  | CE_CmmLit l => cmmLitDenote l
  | CE_CmmLoad e' t => match read_heap (cmmExprDenote h e') h with
                       | None => HSundef
                       | Some v => v
                       end
  | CE_CmmMachOp mo ps => moDenote mo (List.map (cmmExprDenote h) ps)
  | _ => HSundef
  end.


Inductive answer :=
| AValue : hval -> answer
| AError : answer
.

Inductive comp := 
| Ret : answer -> comp
| Bind : comp -> (answer -> comp) -> comp
(*| Delay : exp -> (* list (var * value) ->*) comp *).

Fixpoint cmmExprDenote' (h : heap) (e : CmmExpr) : comp :=
  Ret (AValue (
        match e with
        | CE_CmmLit l => cmmLitDenote l
        | CE_CmmLoad e' t => match read_heap (cmmExprDenote h e') h with
                             | None => HSundef
                             | Some v => v
                             end
        | CE_CmmMachOp mo ps => moDenote mo (List.map (cmmExprDenote h) ps)
        | _ => HSundef
        end)).

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
(*
Fixpoint cmmExprToCminorExpr (e:CmmExpr) {struct e} : expr :=
  match e with
  | CE_CmmLit l => Econst (cmmLitToCminorConst l)
  | CE_CmmLoad e t => Eload (cmmTypeToChunk t) (cmmExprToCminorExpr e)
  | CE_CmmReg r => match r with
                   | CmmLocal (LR_LocalReg l t) => Evar (uniqueToIdent l) (* What to do with type? *) 
                   | CmmGlobal g => Eload (globalRegToChunk g) (globalRegToExpr g)
                   end
  | CE_CmmMachOp mo exs => machOpToCminorExpr mo exs
  | CE_CmmStackSlot area slot => Econst (Oaddrstack (Ptrofs.of_int64 (Int64.mul slot eight))) 
  | CE_CmmRegOff r off => machOpToCminorExpr (MO_Add W64) [(CE_CmmReg r); CE_CmmLit (CmmInt 0%Z W64)] (* FIXME: We need fromIntegral here *)
  end
with machOpToCminorExpr (mo:MachOp) (exs:list CmmExpr) : expr :=
       match mo with
       | MO_Add _ => cminorBinop Oadd exs 
       | MO_Sub _ => cminorBinop Osub exs
       | MO_Eq w =>  cminorBinop (Ocmpl Ceq) exs(* TODO: Implement width and also sign *)
       | MO_Ne w =>  cminorBinop (Ocmpl Cne) exs
       | MO_Mul w => cminorBinop Omul exs
       end
with cminorBinop (op:binary_operation) (exs:list CmmExpr) : expr :=
       match (List.map cmmExprToCminorExpr exs) with
       | [x1;x2] => Ebinop op x1 x2
       | _ => Econst (Ointconst (Int.repr 0)) (* panic *)
(*       end
with cminorUnop (op:unary_operation) (exs:list CmmExpr) : expr :=
       match (List.map cmmExprToCminorExpr exs) with
       | [x] => Eunop op x
       | _ => Econst (Ointconst (Int.repr 0)) (* panic *)*)
       end.

*)
