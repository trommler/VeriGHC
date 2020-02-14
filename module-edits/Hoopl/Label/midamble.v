Require GHC.Err.

(* Instance Default_UniqueMap {a} : Err.Default (UniqueMap a) := _.*)

Instance Default_LabelMap {a} : Err.Default (LabelMap a) := (GHC.Err.Build_Default _ (LM GHC.Err.default)).
