Require Import GHC.Int.
Require Import GHC.Label.

Inductive SwitchTargets : Set :=
| ST_SwitchTargets : bool -> (Integer * Integer)%type -> option Label -> (list (Integer * Label)%type) -> SwitchTargets.
