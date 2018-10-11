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
