Require Import compcert.common.Values.
Require Import compcert.lib.Integers.

Require Import List.

Require Import GHC.CmmExpr.
Require Import GHC.CmmType.
Require Import GHC.CmmMachOp.

(* FIXME: Implement all literals *)

Definition cmmLitDenote (l : CmmLit) : val :=
  match l with
  | CmmInt n width => match width with
                      | W32 => Vint (Int.repr n)
                      | W64 => Vlong (Int64.repr n)
                      | _ => Vundef
                      end
  | _ => Vundef
  end.

Definition Vtrue: val := Vlong Int64.one.
Definition Vfalse: val := Vlong Int64.zero.

Definition from_bool (b :bool) : val :=
  if b then Vtrue else Vfalse.

Definition moDenote (mo : MachOp) (ps : list val) : val :=
(* TODO: compcert/common/Value.v defines ops on val but only for Vint.
         Provide our own definition for Vlong *)
  match mo,ps with
  | MO_Add W64, ((Vlong v1)::(Vlong v2)::nil) => Vlong (Int64.add v1 v2)
  | MO_Sub W64, ((Vlong v1)::(Vlong v2)::nil) => Vlong (Int64.sub v1 v2)
  | MO_Eq W64, ((Vlong v1)::(Vlong v2)::nil) => from_bool (Int64.eq v1 v2)
  | MO_Ne W64, ((Vlong v1)::(Vlong v2)::nil) => from_bool (negb (Int64.eq v1 v2))
  | MO_Mul W64, ((Vlong v1)::(Vlong v2)::nil) => Vlong (Int64.mul v1 v2)
  | _, _ => Vundef
  end.

(* FIXME: Implement all expressions *)
Fixpoint cmmExprDenote (e : CmmExpr) : val :=
  match e with
  | CE_CmmLit l => cmmLitDenote l
  | CE_CmmLoad e t => Vundef
  | CE_CmmMachOp mo ps => moDenote mo (List.map cmmExprDenote ps)
  | _ => Vundef
  end.
