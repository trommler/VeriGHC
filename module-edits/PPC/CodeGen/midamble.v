Require GHC.Err.

Program Instance Default_CondCode : Err.Default CondCode :=
  GHC.Err.Build_Default _ (MkCondCode GHC.Err.default GHC.Err.default GHC.Err.default).
