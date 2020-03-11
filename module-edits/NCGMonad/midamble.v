Require GHC.Err.

Program Instance Default_NatM {a} `(DA : Err.Default a) : Err.Default (NatM a) := (GHC.Err.Build_Default _ (MkNatM (fun (s:NatM_State) => (GHC.Err.default, s)))).
