Require Import GHC.Int.

Definition Label := nat.

Definition range := prod Integer Integer.

Inductive SwitchTargets : Set :=
| ST_SwitchTargets : bool -> (Integer * Integer)%type -> option Label -> (list (Integer * Label)%type) -> SwitchTargets.
