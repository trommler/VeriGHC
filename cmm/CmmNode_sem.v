Require Import HaskellValues.
Require Import GHC.CmmNode.
Require Import GHC.Label.
Require Import GHC.Unique.

Require Import CmmExpr.

Require Import CmmExpr_sem.
Require Import CmmType_sem.

Require Import Cminor.

Definition cmmLabelToCminorLabel (l:Label) : label := l.

Fixpoint cmmNodeToCminorStmt (n:CmmNode) : stmt :=
  match n with
  | CmmEntry l => Slabel (cmmLabelToCminorLabel l) Sskip
  | CmmComment => Sskip
  | CmmAssign r e => match r with
                     | CmmLocal (LR_LocalReg l t) => Sassign (uniqueToIdent l) (cmmExprToCminorExpr e) (* What to do with type? *) 
                     | CmmGlobal g => Sstore (globalRegToChunk g) (globalRegToExpr g) (cmmExprToCminorExpr e)
                     end 
  | CmmStore e1 e2 => Sstore (cmmTypeToChunk (cmmExprType e2)) (cmmExprToCminorExpr e1) (cmmExprToCminorExpr e2)
  | CmmUnsafeForeignCall tgt fs acs => Sskip (* FIXME: Add C calling convention *)
  | CmmCondBranch e t f _ => Sifthenelse (cmmExprToCminorExpr e)
                                         (Sgoto (cmmLabelToCminorLabel t))
                                         (Sgoto (cmmLabelToCminorLabel f))
  | CmmBranch t => Sgoto (cmmLabelToCminorLabel t)
  | CmmSwitch e tgts => Sskip (* FIXME: Implement switch table *)
  | CmmCall e optl grs off1 off2 off3 => Sskip (* FIXME: Add GHC calling convention and tailcall *)
  end.


(*Inductive answer : Type := 
| Value : hval -> answer 
| Error : answer.


Inductive comp := 
| Ret : answer -> comp
| Bind : comp -> (hval -> comp) -> comp
| Delay : exp -> list (var * value) -> comp.
 *)

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
