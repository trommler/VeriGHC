Inductive SwitchTargets : Set :=
| ST_SwitchTargets : bool -> (Integer, Integer) -> option Label -> (Map Integer Label) -> SwitchTargets.
