
(*
Program Fixpoint cmmNodeDenote (node : CmmNode) : Cmd unit :=
  match node with
  | CmmStore lexpr rexpr => ptr <- exprDenote lexpr ;
                            val <- exprDenote rexpr ;
                            write ptr val

  | CmmComment
  | CmmEntry _  => ret tt
 
  | CmmCondBranch _ _ _ _
  | CmmAssign _ _
  | CmmUnsafeForeignCall _ _ _
  | CmmBranch _
  | CmmSwitch _ _
  | CmmCall _ _ _ _ _ _
  | CmmForeignCall _ _ _ _ _ _ _
    => ret tt
  end.
*)
