(* ------------- CoreSyn midamble.v ------------ *)
Require Import Coq.ZArith.ZArith.
Require Import Omega.

Ltac termination_by_omega :=
  Coq.Program.Tactics.program_simpl;
  simpl;Omega.omega.

Ltac intro_split := 
  try intros [? [? [? ?]]];
  try intros [? [? ?]];
  try intros [? ?].
  
Ltac distinguish3 := 
  split; intros; unfold not;  intro_split; discriminate.

(* ---------------------------------- *)

Instance Default__Tickish {a} : GHC.Err.Default (Tickish a) :=
  GHC.Err.Build_Default _ (Breakpoint GHC.Err.default GHC.Err.default).
