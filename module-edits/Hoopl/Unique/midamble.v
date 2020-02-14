Require GHC.Err.


Instance Default_UniqueMap {a} : Err.Default (UniqueMap a) := (GHC.Err.Build_Default _ (UM GHC.Err.default)).
