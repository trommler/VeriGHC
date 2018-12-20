Require Import Coq.Numbers.BinNums.
Require Import List.
Import ListNotations.

Require Import compcert.common.AST.
Require Import compcert.common.Values.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.

Require Import compcert.lib.Integers.
Require Import compcert.lib.Floats.

Require Import GHC.CmmType.
Require Import GHC.Cmm.
Require Import GHC.Int.
Require Import Cmm.CmmNode_sem.

Require Import GHC.CmmExpr. (* FIXME: This should be GHC.Rational. See #2 *)

Definition cmm_program := AST.program cmm_fundef unit.


Definition cmmIntToinit_data (i:Integer) (w:Width) : init_data :=
  match w with
  | W8 =>  Init_int8 (Int.repr i)
  | W16 => Init_int16 (Int.repr i)
  | W32 => Init_int32 (Int.repr i)
  | W64 => Init_int64 (Int64.repr i)
  | _ =>   Init_int32 Int.zero (* panic *)
  end.

(* TODO: Work out the details *)
Definition cmmFloatToInitdata (r:Rational) (w:Width) : init_data :=
  match w with
  | W32 => Init_float32 (Float.to_single Float.zero)
  | W64 => Init_float64 Float.zero
  | _   => Init_float64 Float.zero
  end.
  
  
Definition cmmStaticToinit_data (s:CmmStatic) : list init_data :=
  match s with
  | CmmStaticLit l => match l with
                      | CmmInt i w => [ cmmIntToinit_data i w ]
                      | CmmFloat r w => [ cmmFloatToInitdata r w ]
                      | CmmLabel l => [ Init_addrof l (Ptrofs.of_int64 Int64.zero) ]
                      | CmmLabelOff l off => [ Init_addrof l (Ptrofs.of_int64 off) ]
                      | CmmLabelDiffOff l1 l2 off w => [ Init_addrof l1 (Ptrofs.of_int64 off) ] (* FIXME: Need pointer difference for this *) 
                      | CmmBlock b => [ Init_addrof b (Ptrofs.of_int64 Int64.zero) ]
                      | CmmHighStackMark => [ Init_int64 Int64.zero ]
                      end
  | CmmUninitialised n => [Init_space (IntToZ n)]
  | CmmString cs => nil
  end.

Definition cmmStaticsToinit_datas (css:list CmmStatic) : list init_data :=
  List.concat (List.map cmmStaticToinit_data css).

Definition cmmDeclToAST (d:CmmDecl) : (ident * globdef cmm_fundef unit) :=
  match d with
  | CmmProc h l grs (CG_CmmGraph e g) => (l, Gfun (Internal (mkfunction h grs e g)))
  | CmmData sect (Statics l s) => (l, Gvar (mkglobvar tt (cmmStaticsToinit_datas s) (isSecConstant sect) false))
  end.

Definition cmmGroupToAST (g:CmmGroup) : list (ident * globdef cmm_fundef unit) :=
  List.map cmmDeclToAST g.

Definition cmmProgramToAST (cmm_prog:CmmProgram) : cmm_program :=
  {| prog_defs := List.concat (List.map cmmGroupToAST cmm_prog);
     prog_public := nil;
     prog_main := 1%positive (* FIXME: Where does a Cmm program start? hs_main? *)
  |}.

Inductive initial_state (p:cmm_program) : state -> Prop :=
| initial_state_intro: forall m0 b f,
    let ge := Genv.globalenv p in
    Genv.init_mem p = Some m0 ->
    Genv.find_symbol ge p.(prog_main) = Some b ->
    Genv.find_funct_ptr ge b = Some f ->
    initial_state p (CallState f nil Kstop m0).

(* FIXME: What is the final state? *)
