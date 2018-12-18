Require Import Coq.Numbers.BinNums.

Require Import compcert.common.AST.
Require Import compcert.common.Values.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.

Require Import GHC.Cmm.
Require Import Cmm.CmmNode_sem.

Definition cmm_program := AST.program cmm_fundef unit.


(* TODO: Work out the details *)
Definition cmmStaticToinit_data (s:CmmStatic) : list init_data :=
  match s with
  | CmmStaticLit l => nil
  | CmmUninitialised n => nil
  | CmmString cs => nil
  end.

Definition cmmStaticsToinit_datas (ss:list CmmStatic) : list init_data :=
  List.concat (List.map cmmStaticToinit_data ss).

Definition cmmDeclToAST (d:CmmDecl) : (ident * globdef cmm_fundef unit) :=
  match d with
  | CmmProc h l grs (CG_CmmGraph e g) => (l, Gfun (Internal (mkfunction h grs e g)))
  | CmmData sect (Statics l s) => (l, Gvar (mkglobvar tt (cmmStaticsToinit_datas s) (isSecConstant sect) false))
  end.

Definition cmmGroupToAST (g:CmmGroup) : list (ident * globdef cmm_fundef unit) :=
  List.map cmmDeclToAST g.

(* TODO: Finish implementation *)
  
Definition cmmProgramToAST (cmm_prog:CmmProgram) : cmm_program :=
  {| prog_defs := List.concat (List.map cmmGroupToAST cmm_prog);
     prog_public := nil;
     prog_main := 1%positive
  |}.

Inductive initial_state (p:cmm_program) : state -> Prop :=
| initial_state_intro: forall m0 b f,
    let ge := Genv.globalenv p in
    Genv.init_mem p = Some m0 ->
    Genv.find_symbol ge p.(prog_main) = Some b ->
    Genv.find_funct_ptr ge b = Some f ->
    initial_state p (CallState f nil Kstop m0).
