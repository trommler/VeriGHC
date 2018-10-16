Require Import GHC.CmmType.

Inductive MachOp :=
  (* Integer operations (insensitive to signed/unsigned) *)
| MO_Add: Width -> MachOp
| MO_Sub: Width -> MachOp
| MO_Eq: Width -> MachOp
| MO_Ne: Width -> MachOp
| MO_Mul: Width -> MachOp
(* ... *)
.

Definition MachOp_eq_dec (m1 m2 : MachOp) : {m1 = m2} + {m1 <> m2}.
  decide equality; try (apply Width_eq).
Defined.

Definition comparisonResultRep := bWord. (* but Haskellers are not sure about it :-) *)
                                    
Definition machOpResultType (mo:MachOp) (tys:list CmmType) : CmmType :=
  match mo with
  | MO_Add r => cmmBits r (* should be type of first argument
                             if we are interested in GC-ptr-hood of values *)
  | MO_Sub r => cmmBits r (* same as above *)
  | MO_Mul r => cmmBits r
  | MO_Eq _ => comparisonResultRep
  | MO_Ne _ => comparisonResultRep
  end.
