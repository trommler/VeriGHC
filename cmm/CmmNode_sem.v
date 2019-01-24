Require Import List.
Import ListNotations.
Require Import Coq.ZArith.BinInt.

Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.

Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.

Require Import GHC.BlockId.
Require Import GHC.CmmNode.
Require Import GHC.Label.
Require Import GHC.Unique.
Require Import GHC.Int.
Require Import GHC.CmmSwitch.
Require Import GHC.CmmMachOp.
Require Import CmmExpr.
Require Import Cmm.

Require Import CmmExpr_sem.
Require Import CmmType_sem.

Record cmm_function : Type := mkfunction
                                {
                                  topInfo: CmmTopInfo;
                                  globals: list GlobalReg;
                                  entry: BlockId;
                                  fn_body: Graph CmmNode
                                }.

Definition cmm_fundef := AST.fundef cmm_function.

Inductive cont: Type :=
| Kstop: cont
| Klist: (list CmmNode) -> cont -> cont
| Kcall: option ident -> cmm_function -> val -> env -> cont -> cont
.

Definition genv := Genv.t cmm_fundef unit.
Definition env := PTree.t val.

Section CmmSmallStep.
  Variable ge:genv.
  
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
  match cmo with
  | MO_F64_Pwr => match vs with
                  | [v1;v2] => None
                  | _ => None
                  end
    | MO_F64_Sin
    | MO_F64_Cos
    | MO_F64_Tan
    | MO_F64_Sinh
    | MO_F64_Cosh
    | MO_F64_Tanh
    | MO_F64_Asin
    | MO_F64_Acos
    | MO_F64_Atan
    | MO_F64_Asinh
    | MO_F64_Acosh
    | MO_F64_Atanh
    | MO_F64_Log
    | MO_F64_Exp
    | MO_F64_Fabs
    | MO_F64_Sqrt
    | MO_F32_Pwr
    | MO_F32_Sin
    | MO_F32_Cos
    | MO_F32_Tan
    | MO_F32_Sinh
    | MO_F32_Cosh
    | MO_F32_Tanh
    | MO_F32_Asin
    | MO_F32_Acos
    | MO_F32_Atan
    | MO_F32_Asinh
    | MO_F32_Acosh
    | MO_F32_Atanh
    | MO_F32_Log
    | MO_F32_Exp
    | MO_F32_Fabs
    | MO_F32_Sqrt => None
    
    | MO_UF_Conv w
             
    | MO_S_QuotRem w
    | MO_U_QuotRem w
    | MO_U_QuotRem2 w
    | MO_Add2 w
    | MO_AddWordC w
    | MO_SubWordC w
    | MO_AddIntC w
    | MO_SubIntC w
    | MO_U_Mul2 w => None
                                
    | MO_WriteBarrier
    | MO_Touch => None
    | MO_Prefetch_Data _ => None
    | MO_Memcpy i
    | MO_Memset i
    | MO_Memmove i
    | MO_Memcmp i => None
            
    | MO_PopCnt w
    | MO_Pdep w
    | MO_Pext w
    | MO_Clz w
    | MO_Ctz w => None

    | MO_BSwap w => None

    | MO_AtomicRMW w op => None
    | MO_AtomicRead w => match vs with
                         | [v1] => match Mem.loadv (widthToChunk w) m v1 with
                                   | Some v => Some ([v], m)
                                   | None => None
                                   end
                         | _ => None
                         end
    | MO_AtomicWrite w => match vs with
                          | [v1;v2] => match Mem.storev (widthToChunk w) m v1 v2 with
                                       | Some m' => Some ([],m')
                                       | None => None
                                       end
                          | _ => None
                          end
    | MO_Cmpxchg w => None
  end.

Definition foreignTargetDenote (m:mem) (ft:ForeignTarget) (vs:list val) : option ((list val) * mem) :=
  match ft with
  | FT_ForeignTarget e => None (* FIXME *)
  | FT_PrimTarget cmo => cmmCallishMachOpDenote m cmo vs
  end.

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
    cmmExprDenote m e sp ex = Some v ->
    cmmExprType ex = t ->
    CmmLocal (LR_LocalReg l t) = reg ->
    step (Sequence f (CmmAssign reg ex) (Klist (n::ns) k) sp e m)
         (Sequence f n (Klist ns k) sp (PTree.set l v e) m)
| step_store : forall f lexp rexp ptr val ch n ns k sp e m m',
    cmmExprDenote m e sp lexp = Some ptr ->
    cmmExprDenote m e sp rexp = Some val ->
    cmmTypeToChunk (cmmExprType rexp) = ch ->
    Mem.storev ch m ptr val = Some m' ->
    step (Sequence f (CmmStore lexp rexp) (Klist (n::ns) k) sp e m)
         (Sequence f n (Klist ns k) sp e m') 
| step_goto : forall f l k sp e m ns,
    find_block l f.(fn_body) = ns ->
    step (Sequence f (CmmBranch l) (Klist [] k) sp e m)
         (Sequence f (CmmEntry l) (Klist ns k) sp e m)
| step_conditional : forall f ex v l1 l2 p k sp e m b,
    cmmExprDenote m e sp ex = Some v ->
    Val.bool_of_val v b ->
    step (Sequence f (CmmCondBranch ex l1 l2 p) k sp e m)
         (Sequence f (CmmBranch (if b then l1 else l2)) k sp e m)
| step_switch : forall f ex v st k sp e m l,
    cmmExprDenote m e sp ex = Some v ->
    switch_label v st = Some l ->
    step (Sequence f (CmmSwitch ex st) k sp e m)
         (Sequence f (CmmBranch l) k sp e m)
| step_foreign_target : forall args vs m ft rs m' ress e e' n ns k f sp,
    cmmExprListDenote m e sp args = Some vs ->
    foreignTargetDenote m ft vs = Some (rs, m') ->
    assign_values ress rs e = e' ->
    step (Sequence f (CmmUnsafeForeignCall ft ress args) (Klist (n::ns) k) sp e m)
         (Sequence f n (Klist ns k) sp e' m') 
| step_call : forall f expr v lbl grs a_off r_a_off r_off k sp e m fd vs,
    cmmExprDenote m e sp expr = Some v ->
    Genv.find_funct ge v = Some fd ->
    (* PowerPC and SPARC ignore grs (live global regs) but Intel doesn't *)
    step (Sequence f (CmmCall expr lbl grs a_off r_a_off r_off) (Klist [] k) sp e m)
         (CallState fd vs (Kcall lbl f sp e k) m)
| step_call_enter : forall fd vs lbl f sp e k m f' l sp' e',
(* what do stack and environment look like upon proc entry? *)
    step (CallState fd vs (Kcall lbl f sp e k) m)
         (Sequence f' (CmmBranch l) k sp' e' m)
.
End CmmSmallStep.
