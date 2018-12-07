Require Import List.
Import ListNotations.
Require Import Coq.ZArith.BinInt.

Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.

Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.

Require Import GHC.CmmNode.
Require Import GHC.Label.
Require Import GHC.Unique.
Require Import GHC.Int.
Require Import GHC.CmmSwitch.
Require Import GHC.CmmMachOp.
Require Import CmmExpr.

Require Import CmmExpr_sem.
Require Import CmmType_sem.

Require Import Cminor.

Record cmm_function : Type := mkfunction {
  fn_sig: signature;
  (* fn_params: list ident; *)
  (* fn_vars: list ident; *)
  (* fn_stackspace: Z; *)
  fn_body: list CmmNode
}.

Definition cmm_fundef := AST.fundef cmm_function.

Inductive cont: Type :=
| Kstop: cont
| Klist: (list CmmNode) -> cont -> cont
| Kcall: option ident -> cmm_function -> val -> env -> cont -> cont
.

Definition genv := Genv.t cmm_fundef unit.
Definition env := PTree.t val.

Fixpoint find_entry (l:Label) (ns:list CmmNode) : list CmmNode :=
  match ns with
  | n::ns' => match n with
              | CmmEntry l' => if Label_eq l l' then ns' else find_entry l ns'
              | _ => find_entry l ns'
              end
  | [] => []
  end.

Definition jumpish (n:CmmNode) : bool :=
  match n with
  | CmmBranch _ => true
  | CmmCondBranch _ _ _ _ => true
  | CmmSwitch _ _ => true
  | CmmCall _ _ _ _ _ _ => true
  | CmmUnsafeForeignCall _ _ _ => true
  | _ => false
  end.

Fixpoint first_block (ns:list CmmNode) : list CmmNode :=
  match ns with
  | n::ns' => if jumpish n then [n] else n::first_block ns'
  | [] => [] (* This must not happen, because the last Node must be jumpish *)
  end.

Definition find_block (l:Label) (ns:list CmmNode) : list CmmNode :=
  first_block (find_entry l ns).

Fixpoint tgt_list_find (vi:Integer) (olbl:option Label) (tgts:list (Integer*Label)) : option Label :=
  match tgts with
  | (i, l)::tgts' => if Z.eq_dec i vi then Some l else tgt_list_find vi olbl tgts'
  | [] => olbl
  end.
    
Definition switch_label (v:val) (st:SwitchTargets) : option Label :=
  match v with
  | Vlong i => match st with
               | ST_SwitchTargets sign (lo,hi) olbl tgts =>
                 let vi := if sign then Int64.signed i else Int64.unsigned i
                 in if Z.ltb vi lo then None
                    else if Z.gtb vi hi then None
                         else tgt_list_find vi olbl tgts
               end
  | _ => None
  end.

Inductive state : Type :=
| Sequence :
    forall (f:cmm_function)
           (n:CmmNode)
           (k:cont)
           (sp:val)
           (e:env)
           (m:mem),
      state
| CallState:
    forall (f:cmm_fundef)
           (args:list val)
           (k:cont)
           (m:mem),
      state
.
Definition cmmCallishMachOpDenote (m:mem) (cmo:CallishMachOp) (vs:list val) : option ((list val) * mem) :=
  None. (* FIXME *) 

Fixpoint assign_values (ress:list CmmFormal) (rs:list val) (e:env) : env :=
  match ress, rs with
  | (LR_LocalReg l t)::ress', r::rs' => assign_values ress' rs' (PTree.set l r e)
  | [], [] => e
  | _, _ => e (* This should not happen! *)
  end.

Inductive step : state -> state -> Prop :=
| step_comment : forall f n ns k sp e m,
    step (Sequence f CmmComment (Klist (n::ns) k) sp e m)
         (Sequence f n (Klist ns k) sp e m)
| step_label : forall f l n ns k sp e m,
    step (Sequence f(CmmEntry l) (Klist (n::ns) k) sp e m)
         (Sequence f n (Klist ns k) sp e m)
| step_assign_local : forall f reg l t ex v n ns k sp e m,
    cmmExprDenote m ex = Some v ->
    cmmExprType ex = t ->
    CmmLocal (LR_LocalReg l t) = reg ->
    step (Sequence f (CmmAssign reg ex) (Klist (n::ns) k) sp e m)
         (Sequence f n (Klist ns k) sp (PTree.set l v e) m)
| step_store : forall f lexp rexp ptr val ch n ns k sp e m m',
    cmmExprDenote m lexp = Some ptr ->
    cmmExprDenote m rexp = Some val ->
    cmmTypeToChunk (cmmExprType rexp) = ch ->
    Mem.storev ch m ptr val = Some m' ->
    step (Sequence f (CmmStore lexp rexp) (Klist (n::ns) k) sp e m)
         (Sequence f n (Klist ns k) sp e m') 
| step_goto : forall f l k sp e m ns,
    find_block l f.(fn_body) = ns ->
    step (Sequence f (CmmBranch l) (Klist [] k) sp e m)
         (Sequence f (CmmEntry l) (Klist ns k) sp e m)
| step_conditional : forall f ex v l1 l2 p k sp e m b,
    cmmExprDenote m ex = Some v ->
    Val.bool_of_val v b ->
    step (Sequence f (CmmCondBranch ex l1 l2 p) k sp e m)
         (Sequence f (CmmBranch (if b then l1 else l2)) k sp e m)
| step_switch : forall f ex v st k sp e m l,
    cmmExprDenote m ex = Some v ->
    switch_label v st = Some l ->
    step (Sequence f (CmmSwitch ex st) k sp e m)
         (Sequence f (CmmBranch l) k sp e m)
| step_callish_machop : forall args vs m cmo rs m' ress e e' n ns k f sp,
    cmmExprListDenote m args = Some vs ->
    cmmCallishMachOpDenote m cmo vs = Some (rs, m') ->
    assign_values ress rs e = e' ->
    step (Sequence f (CmmUnsafeForeignCall (FT_PrimTarget cmo) ress args) (Klist (n::ns) k) sp e m)
         (Sequence f n (Klist ns k) sp e' m') 
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
                                           | CmmForeignCall t form act succ ret_args ret_off interupt => Sskip
  end.
