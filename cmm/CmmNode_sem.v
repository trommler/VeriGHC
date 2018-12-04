Require Import compcert.lib.Maps.
Require Import List.
Import ListNotations.

Require Import compcert.common.Memory.
Require Import compcert.common.Values.

Require Import GHC.CmmNode.
Require Import GHC.Label.
Require Import GHC.Unique.

Require Import CmmExpr.

Require Import CmmExpr_sem.
Require Import CmmType_sem.

Require Import Cminor.

Inductive cont: Type :=
| Kstop: cont
| Klist: (list CmmNode) -> cont -> cont
(*  | Kcall: option ident -> function -> val -> env -> cont -> cont.*)
.

Definition env := PTree.t val.

Inductive state : Type :=
| Sequence : forall (* (f:function) *)
    (n:CmmNode)
    (k:cont)
    (sp:val)
    (e:env)
    (m:mem),
    state
.

Inductive step : state -> state -> Prop :=
| step_comment : forall n ns k sp e m,
    step (Sequence CmmComment (Klist (n::ns) k) sp e m)
         (Sequence n (Klist ns k) sp e m)
| step_label : forall l n ns k sp e m,
    step (Sequence (CmmEntry l) (Klist (n::ns) k) sp e m)
         (Sequence n (Klist ns k) sp e m)
| step_assign_local : forall reg l t ex v n ns k sp e m,
    cmmExprDenote m ex = Some v ->
    cmmExprType ex = t ->
    CmmLocal (LR_LocalReg l t) = reg ->
    step (Sequence (CmmAssign reg ex) (Klist (n::ns) k) sp e m)
         (Sequence n (Klist ns k) sp (PTree.set l v e) m)
| step_store : forall lexp rexp ptr val ch n ns k sp e m m',
    cmmExprDenote m lexp = Some ptr ->
    cmmExprDenote m rexp = Some val ->
    cmmTypeToChunk (cmmExprType rexp) = ch ->
    Mem.storev ch m ptr val = Some m' ->
    step (Sequence (CmmStore lexp rexp) (Klist (n::ns) k) sp e m)
         (Sequence n (Klist ns k) sp e m') 
.

(* Monadic 

Inductive answer : Type := 
| Value : val -> answer 
| Error : answer.


Inductive comp := 
| Ret : answer -> comp
| Bind : comp -> (val -> comp) -> comp
| Delay : list CmmNode -> comp.

Notation "'ret' x" := (Ret (Value x)) (at level 75) : comp_scope.
Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2))
        (right associativity, at level 84, c1 at next level) : comp_scope.
Local Open Scope comp_scope.


Fixpoint cmmNodeDenote (n:CmmNode) (m:mem) : option mem :=
  match n with
  | CmmStore lexp rexpr => match cmmDenote m lexpr, cmmDenote m rexpr, cmmTypeDenote (cmmExprType rexpr) with
                           | Some ptr, Some val, chunk => Mem.storev chunk m ptr val
                           | _, _, _ => None
                           end
  | CmmComment => Some m
  | CmmEntry _ => Some m
  | CmmBranch l =>

*) 
(*
Program Fixpoint cmmNodeDenote (node : CmmNode) (m:mem) : comp :=
  match node with
  | CmmStore lexpr rexpr => ptr <- cmmExprDenote m lexpr ;
                            val <- cmmExprDenote m rexpr ;
                            chunk <- cmmTypeDenote(cmmExprType rexpr) ;
                            Mem.storev chunk m ptr val

  | CmmComment
  | CmmEntry _  => ret HSundef
 
  | CmmCondBranch _ _ _ _
  | CmmAssign _ _
  | CmmUnsafeForeignCall _ _ _
  | CmmBranch _
  | CmmSwitch _ _
  | CmmCall _ _ _ _ _ _
    => ret HSundef
  end.
*)

(* Cminor semantics *)

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
