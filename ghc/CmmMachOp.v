Require Import GHC.CmmType.

Inductive MachOp :=
| MO_Add: Width -> MachOp
(* ... *)
| MO_Mul: Width -> MachOp
(* ... *)
.
