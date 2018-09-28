Require Import GHC.Reg.

Inductive Instr :=
| ADD: Reg -> Reg -> Reg -> Instr
.
