(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.
Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require BlockId.
Require Cmm.
Require CmmExpr.
Require CmmMachOp.
Require CmmType.
Require DynFlags.
Require Format.
Require GHC.Base.
Require GHC.Err.
Require GHC.Num.
Require GHC.Real.
Require NCGMonad.
Require OrdList.
Require PIC.
Require PPC.Cond.
Require PPC.Instr.
Require PPC.Regs.
Require Panic.
Require Platform.
Require PprCmmExpr.
Require Reg.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive InstrForm : Type := | D : InstrForm |  DS : InstrForm.

Definition InstrBlock :=
  (OrdList.OrdList PPC.Instr.Instr)%type.

Inductive Register : Type
  := | Fixed : Format.Format -> Reg.Reg -> InstrBlock -> Register
  |  Any : Format.Format -> (Reg.Reg -> InstrBlock) -> Register.

Inductive GenCCallPlatform : Type
  := | GCPLinux : GenCCallPlatform
  |  GCPDarwin : GenCCallPlatform
  |  GCPLinux64ELF : GHC.Num.Int -> GenCCallPlatform
  |  GCPAIX : GenCCallPlatform.

Inductive CondCode : Type
  := | MkCondCode : bool -> PPC.Cond.Cond -> InstrBlock -> CondCode.

Inductive ChildCode64 : Type
  := | MkChildCode64 : InstrBlock -> Reg.Reg -> ChildCode64.

Inductive Amode : Type := | MkAmode : PPC.Regs.AddrMode -> InstrBlock -> Amode.

Instance Default__InstrForm : GHC.Err.Default InstrForm :=
  GHC.Err.Build_Default _ D.

Instance Default__GenCCallPlatform : GHC.Err.Default GenCCallPlatform :=
  GHC.Err.Build_Default _ GCPLinux.

(* Midamble *)

Require GHC.Err.

Program Instance Default_CondCode : Err.Default CondCode :=
  GHC.Err.Build_Default _ (MkCondCode GHC.Err.default GHC.Err.default GHC.Err.default).

(* Converted value declarations: *)

Axiom trivialUCode : Format.Format ->
                     (Reg.Reg -> Reg.Reg -> PPC.Instr.Instr) ->
                     CmmExpr.CmmExpr -> NCGMonad.NatM Register.

Axiom trivialCodeNoImmSign : Format.Format ->
                             bool ->
                             (Format.Format -> bool -> Reg.Reg -> Reg.Reg -> Reg.Reg -> PPC.Instr.Instr) ->
                             CmmExpr.CmmExpr -> CmmExpr.CmmExpr -> NCGMonad.NatM Register.

Axiom trivialCodeNoImm' : Format.Format ->
                          (Reg.Reg -> Reg.Reg -> Reg.Reg -> PPC.Instr.Instr) ->
                          CmmExpr.CmmExpr -> CmmExpr.CmmExpr -> NCGMonad.NatM Register.

Axiom trivialCodeNoImm : Format.Format ->
                         (Format.Format -> Reg.Reg -> Reg.Reg -> Reg.Reg -> PPC.Instr.Instr) ->
                         CmmExpr.CmmExpr -> CmmExpr.CmmExpr -> NCGMonad.NatM Register.

Definition swizzleRegisterRep : Register -> Format.Format -> Register :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Fixed _ reg code, format => Fixed format reg code
    | Any _ codefn, format => Any format codefn
    end.

Axiom shiftMulCode : CmmType.Width ->
                     bool ->
                     (Format.Format -> Reg.Reg -> Reg.Reg -> PPC.Instr.RI -> PPC.Instr.Instr) ->
                     CmmExpr.CmmExpr -> CmmExpr.CmmExpr -> NCGMonad.NatM Register.

Axiom remainderCode : CmmType.Width ->
                      bool -> CmmExpr.CmmExpr -> CmmExpr.CmmExpr -> NCGMonad.NatM Register.

Definition platformToGCP : Platform.Platform -> GenCCallPlatform :=
  fun platform =>
    match Platform.platformOS platform with
    | Platform.OSLinux =>
        match Platform.platformArch platform with
        | Platform.ArchPPC => GCPLinux
        | Platform.ArchPPC_64 Platform.ELF_V1 => GCPLinux64ELF #1
        | Platform.ArchPPC_64 Platform.ELF_V2 => GCPLinux64ELF #2
        | _ =>
            Panic.panic (GHC.Base.hs_string__ "PPC.CodeGen.platformToGCP: Unknown Linux")
        end
    | Platform.OSAIX => GCPAIX
    | Platform.OSDarwin => GCPDarwin
    | _ =>
        Panic.panic (GHC.Base.hs_string__
                     "PPC.CodeGen.platformToGCP: not defined for this OS")
    end.

Definition mangleIndexTree
   : DynFlags.DynFlags -> CmmExpr.CmmExpr -> CmmExpr.CmmExpr :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | dflags, CmmExpr.CmmRegOff reg off =>
        let width := CmmType.typeWidth (CmmExpr.cmmRegType dflags reg) in
        CmmExpr.CmmMachOp (CmmMachOp.MO_Add width) (cons (CmmExpr.Mk_CmmReg reg) (cons
                                                          (CmmExpr.Mk_CmmLit (CmmExpr.CmmInt (GHC.Real.fromIntegral off)
                                                                              width)) nil))
    | _, _ =>
        Panic.panic (GHC.Base.hs_string__ "PPC.CodeGen.mangleIndexTree: no match")
    end.

Axiom iselExpr64 : CmmExpr.CmmExpr -> NCGMonad.NatM ChildCode64.

Axiom getRegisterReg : Platform.Platform -> CmmExpr.CmmReg -> Reg.Reg.

Axiom getAmode : InstrForm -> CmmExpr.CmmExpr -> NCGMonad.NatM Amode.

Definition extendUExpr
   : DynFlags.DynFlags -> CmmType.Width -> CmmExpr.CmmExpr -> CmmExpr.CmmExpr :=
  fun arg_0__ arg_1__ arg_2__ =>
    let j_5__ :=
      match arg_0__, arg_1__, arg_2__ with
      | dflags, rep, x =>
          let size :=
            if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool
            then CmmType.W32
            else CmmType.W64 in
          CmmExpr.CmmMachOp (CmmMachOp.MO_UU_Conv rep size) (cons x nil)
      end in
    match arg_0__, arg_1__, arg_2__ with
    | dflags, CmmType.W32, x =>
        if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool then x else
        j_5__
    | dflags, CmmType.W64, x =>
        if negb (Platform.target32Bit (DynFlags.targetPlatform dflags)) : bool
        then x else
        j_5__
    | _, _, _ => j_5__
    end.

Definition extendSExpr
   : DynFlags.DynFlags -> CmmType.Width -> CmmExpr.CmmExpr -> CmmExpr.CmmExpr :=
  fun arg_0__ arg_1__ arg_2__ =>
    let j_5__ :=
      match arg_0__, arg_1__, arg_2__ with
      | dflags, rep, x =>
          let size :=
            if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool
            then CmmType.W32
            else CmmType.W64 in
          CmmExpr.CmmMachOp (CmmMachOp.MO_SS_Conv rep size) (cons x nil)
      end in
    match arg_0__, arg_1__, arg_2__ with
    | dflags, CmmType.W32, x =>
        if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool then x else
        j_5__
    | dflags, CmmType.W64, x =>
        if negb (Platform.target32Bit (DynFlags.targetPlatform dflags)) : bool
        then x else
        j_5__
    | _, _, _ => j_5__
    end.

Definition condReg : NCGMonad.NatM CondCode -> NCGMonad.NatM Register :=
  fun getCond =>
    let cont_0__ arg_1__ :=
      let 'MkCondCode _ cond cond_code := arg_1__ in
      DynFlags.getDynFlags GHC.Base.>>=
      (fun dflags =>
         let format :=
           PPC.Instr.archWordFormat (Platform.target32Bit (DynFlags.targetPlatform
                                                           dflags)) in
         let 'pair bit do_negate := (match cond with
                                       | PPC.Cond.LTT => pair #0 false
                                       | PPC.Cond.LE => pair #1 true
                                       | PPC.Cond.EQQ => pair #2 false
                                       | PPC.Cond.GE => pair #0 true
                                       | PPC.Cond.GTT => pair #1 false
                                       | PPC.Cond.NE => pair #2 true
                                       | PPC.Cond.LU => pair #0 false
                                       | PPC.Cond.LEU => pair #1 true
                                       | PPC.Cond.GEU => pair #0 true
                                       | PPC.Cond.GU => pair #1 false
                                       | _ => Panic.panic (GHC.Base.hs_string__ "PPC.CodeGen.codeReg: no match")
                                       end) in
         let negate_code :=
           if do_negate : bool then OrdList.unitOL (PPC.Instr.CRNOR bit bit bit) else
           OrdList.nilOL in
         let code :=
           fun dst =>
             OrdList.appOL (OrdList.appOL cond_code negate_code) (OrdList.toOL (cons
                                                                                (PPC.Instr.MFCR dst) (cons
                                                                                 (PPC.Instr.RLWINM dst dst (bit
                                                                                                            GHC.Num.+
                                                                                                            #1) #31 #31)
                                                                                 nil))) in
         GHC.Base.return_ (Any format code)) in
    getCond GHC.Base.>>= cont_0__.

Axiom condIntReg : PPC.Cond.Cond ->
                   CmmExpr.CmmExpr -> CmmExpr.CmmExpr -> NCGMonad.NatM Register.

Axiom condIntCode : PPC.Cond.Cond ->
                    CmmExpr.CmmExpr -> CmmExpr.CmmExpr -> NCGMonad.NatM CondCode.

Axiom condFltReg : PPC.Cond.Cond ->
                   CmmExpr.CmmExpr -> CmmExpr.CmmExpr -> NCGMonad.NatM Register.

Equations getRegister (e : CmmExpr.CmmExpr) : NCGMonad.NatM Register by struct e:=
  getRegister e:= DynFlags.getDynFlags GHC.Base.>>= (fun dflags => getRegister' dflags e)

  with getSomeReg (expr : CmmExpr.CmmExpr) : NCGMonad.NatM (Reg.Reg *
                                                                         InstrBlock)%type :=
                    getSomeReg expr  := getRegister expr GHC.Base.>>=
                         (fun r =>
                            match r with
                            | Any rep code =>
                                NCGMonad.getNewRegNat rep GHC.Base.>>=
                                (fun tmp => GHC.Base.return_ (pair tmp (code tmp)))
                            | Fixed _ reg code => GHC.Base.return_ (pair reg code)
                            end)
  with trivialCode (arg_0__ : CmmType.Width) (arg_1__ : bool) (arg_2__
                     : (Reg.Reg -> Reg.Reg -> PPC.Instr.RI -> PPC.Instr.Instr)) (arg_3__ arg_4__
                     : CmmExpr.CmmExpr) : NCGMonad.NatM Register :=
         trivialCode rep signed instr x (CmmExpr.Mk_CmmLit (CmmExpr.CmmInt y _)) :=
                match PPC.Regs.makeImmediate rep signed y with
                | Some imm =>
                    let cont_12__ arg_13__ :=
                      let 'pair src1 code1 := arg_13__ in
                      let code :=
                        fun dst => OrdList.snocOL code1 (instr dst src1 (PPC.Instr.RIImm imm)) in
                      GHC.Base.return_ (Any (Format.intFormat rep) code) in
                    getSomeReg x GHC.Base.>>= cont_12__
                | _ => match rep, signed, instr, x, CmmExpr.Mk_CmmLit (CmmExpr.CmmInt y _) with
                       | rep, _, instr, x, y =>
                            let cont_5__ arg_6__ :=
                              let 'pair src1 code1 := arg_6__ in
                              let cont_7__ arg_8__ :=
                                let 'pair src2 code2 := arg_8__ in
                                let code :=
                                  fun dst =>
                                    OrdList.snocOL (OrdList.appOL code1 code2) (instr dst src1 (PPC.Instr.RIReg
                                                                                                src2)) in
                                GHC.Base.return_ (Any (Format.intFormat rep) code) in
                              getSomeReg y GHC.Base.>>= cont_7__ in
                            getSomeReg x GHC.Base.>>= cont_5__
                        end
                end;
          trivialCode rep _ instr x y :=
                let cont_5__ arg_6__ :=
                  let 'pair src1 code1 := arg_6__ in
                  let cont_7__ arg_8__ :=
                    let 'pair src2 code2 := arg_8__ in
                    let code :=
                      fun dst =>
                        OrdList.snocOL (OrdList.appOL code1 code2) (instr dst src1 (PPC.Instr.RIReg
                                                                                    src2)) in
                    GHC.Base.return_ (Any (Format.intFormat rep) code) in
                  getSomeReg y GHC.Base.>>= cont_7__ in
                getSomeReg x GHC.Base.>>= cont_5__


  with getRegister' (arg_0__ : DynFlags.DynFlags) (arg_1__ : CmmExpr.CmmExpr) : NCGMonad.NatM Register :=
        getRegister' arg_0__ arg_1__ :=
           match arg_0__, arg_1__ with
           | dflags, CmmExpr.Mk_CmmReg reg =>
               GHC.Base.return_ (Fixed (Format.cmmTypeFormat (CmmExpr.cmmRegType dflags reg))
                                 (getRegisterReg (DynFlags.targetPlatform dflags) reg) OrdList.nilOL)
           | dflags, (CmmExpr.CmmRegOff _ _ as tree) =>
               getRegister' dflags (mangleIndexTree dflags tree)
           | dflags
           , CmmExpr.CmmMachOp (CmmMachOp.MO_UU_Conv CmmType.W64 CmmType.W32) (cons
            (CmmExpr.CmmMachOp (CmmMachOp.MO_U_Shr CmmType.W64) (cons x (cons
               (CmmExpr.Mk_CmmLit (CmmExpr.CmmInt num_2__ _)) nil))) nil) =>
               if num_2__ GHC.Base.== #32 : bool
               then if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool
                    then let cont_136__ arg_137__ :=
                           let 'MkChildCode64 code rlo := arg_137__ in
                           GHC.Base.return_ (Fixed Format.II32 (Reg.getHiVRegFromLo rlo) code) in
                         iselExpr64 x GHC.Base.>>= cont_136__ else
                    (match arg_0__, arg_1__ with
                     | dflags
                     , CmmExpr.CmmMachOp (CmmMachOp.MO_UU_Conv CmmType.W64 CmmType.W32) (cons x
                      nil) =>
                         if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool
                         then let cont_22__ arg_23__ :=
                                let 'MkChildCode64 code rlo := arg_23__ in
                                GHC.Base.return_ (Fixed Format.II32 rlo code) in
                              iselExpr64 x GHC.Base.>>= cont_22__ else
                         (match arg_0__, arg_1__ with
                          | _, CmmExpr.Mk_CmmLit (CmmExpr.CmmFloat f frep) =>
                               NCGMonad.getNewLabelNat GHC.Base.>>=
                               (fun lbl =>
                                  DynFlags.getDynFlags GHC.Base.>>=
                                  (fun dflags =>
                                     PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                                     (fun dynRef =>
                                        let cont_6__ arg_7__ :=
                                          let 'MkAmode addr addr_code := arg_7__ in
                                          let format := Format.floatFormat frep in
                                          let code :=
                                            fun dst =>
                                              OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                              (Cmm.Statics lbl (cons (Cmm.CmmStaticLit (CmmExpr.CmmFloat f frep))
                                                                                     nil))) (OrdList.snocOL addr_code (PPC.Instr.LD
                                                                                                             format dst addr)) in
                                          GHC.Base.return_ (Any format code) in
                                        getAmode D dynRef GHC.Base.>>= cont_6__)))
                          | dflags, CmmExpr.Mk_CmmLit lit =>
                               if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool
                               then let imm := PPC.Regs.litToImm lit in
                                    let code :=
                                      fun dst =>
                                        OrdList.toOL (cons (PPC.Instr.LIS dst (PPC.Regs.HA imm)) (cons (PPC.Instr.ADD
                                                                                                        dst dst (PPC.Instr.RIImm
                                                                                                                 (PPC.Regs.LO imm)))
                                                                                                       nil)) in
                                    let rep := CmmExpr.cmmLitType dflags lit in
                                    GHC.Base.return_ (Any (Format.cmmTypeFormat rep) code) else
                               NCGMonad.getNewLabelNat GHC.Base.>>=
                               (fun lbl =>
                                  DynFlags.getDynFlags GHC.Base.>>=
                                  (fun dflags =>
                                     PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                                     (fun dynRef =>
                                        let cont_14__ arg_15__ :=
                                          let 'MkAmode addr addr_code := arg_15__ in
                                          let rep := CmmExpr.cmmLitType dflags lit in
                                          let format := Format.cmmTypeFormat rep in
                                          let code :=
                                            fun dst =>
                                              OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                              (Cmm.Statics lbl (cons (Cmm.CmmStaticLit lit) nil))) (OrdList.snocOL
                                                              addr_code (PPC.Instr.LD format dst addr)) in
                                          GHC.Base.return_ (Any format code) in
                                        getAmode D dynRef GHC.Base.>>= cont_14__)))
                          | _, other =>
                                       Panic.panicStr (GHC.Base.hs_string__ "getRegister(ppc)") (PprCmmExpr.pprExpr
                                                                                                 other)
                           end )
                     | dflags
                     , CmmExpr.CmmMachOp (CmmMachOp.MO_SS_Conv CmmType.W64 CmmType.W32) (cons x
                      nil) =>
                         if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool
                         then let cont_25__ arg_26__ :=
                                let 'MkChildCode64 code rlo := arg_26__ in
                                GHC.Base.return_ (Fixed Format.II32 rlo code) in
                              iselExpr64 x GHC.Base.>>= cont_25__ else
                         (match arg_0__, arg_1__ with
                          | _, CmmExpr.Mk_CmmLit (CmmExpr.CmmFloat f frep) =>
                               NCGMonad.getNewLabelNat GHC.Base.>>=
                               (fun lbl =>
                                  DynFlags.getDynFlags GHC.Base.>>=
                                  (fun dflags =>
                                     PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                                     (fun dynRef =>
                                        let cont_6__ arg_7__ :=
                                          let 'MkAmode addr addr_code := arg_7__ in
                                          let format := Format.floatFormat frep in
                                          let code :=
                                            fun dst =>
                                              OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                              (Cmm.Statics lbl (cons (Cmm.CmmStaticLit (CmmExpr.CmmFloat f frep))
                                                                                     nil))) (OrdList.snocOL addr_code (PPC.Instr.LD
                                                                                                             format dst addr)) in
                                          GHC.Base.return_ (Any format code) in
                                        getAmode D dynRef GHC.Base.>>= cont_6__)))
                          | dflags, CmmExpr.Mk_CmmLit lit =>
                               if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool
                               then let imm := PPC.Regs.litToImm lit in
                                    let code :=
                                      fun dst =>
                                        OrdList.toOL (cons (PPC.Instr.LIS dst (PPC.Regs.HA imm)) (cons (PPC.Instr.ADD
                                                                                                        dst dst (PPC.Instr.RIImm
                                                                                                                 (PPC.Regs.LO imm)))
                                                                                                       nil)) in
                                    let rep := CmmExpr.cmmLitType dflags lit in
                                    GHC.Base.return_ (Any (Format.cmmTypeFormat rep) code) else
                               NCGMonad.getNewLabelNat GHC.Base.>>=
                               (fun lbl =>
                                  DynFlags.getDynFlags GHC.Base.>>=
                                  (fun dflags =>
                                     PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                                     (fun dynRef =>
                                        let cont_14__ arg_15__ :=
                                          let 'MkAmode addr addr_code := arg_15__ in
                                          let rep := CmmExpr.cmmLitType dflags lit in
                                          let format := Format.cmmTypeFormat rep in
                                          let code :=
                                            fun dst =>
                                              OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                              (Cmm.Statics lbl (cons (Cmm.CmmStaticLit lit) nil))) (OrdList.snocOL
                                                              addr_code (PPC.Instr.LD format dst addr)) in
                                          GHC.Base.return_ (Any format code) in
                                        getAmode D dynRef GHC.Base.>>= cont_14__)))
                          | _, other =>
                                       Panic.panicStr (GHC.Base.hs_string__ "getRegister(ppc)") (PprCmmExpr.pprExpr
                                                                                                 other)
                           end)
                     | _
                     , CmmExpr.CmmMachOp (CmmMachOp.MO_UU_Conv CmmType.W8 CmmType.W32) (cons
                      (CmmExpr.CmmLoad mem _) nil) =>
                         let cont_28__ arg_29__ :=
                           let 'MkAmode addr addr_code := arg_29__ in
                           GHC.Base.return_ (Any Format.II32 (fun dst =>
                                                                OrdList.snocOL addr_code (PPC.Instr.LD Format.II8 dst addr))) in
                         getAmode D mem GHC.Base.>>= cont_28__
                     | _
                     , CmmExpr.CmmMachOp (CmmMachOp.MO_UU_Conv CmmType.W8 CmmType.W64) (cons
                      (CmmExpr.CmmLoad mem _) nil) =>
                         let cont_32__ arg_33__ :=
                           let 'MkAmode addr addr_code := arg_33__ in
                           GHC.Base.return_ (Any Format.II64 (fun dst =>
                                                                OrdList.snocOL addr_code (PPC.Instr.LD Format.II8 dst addr))) in
                         getAmode D mem GHC.Base.>>= cont_32__
                     | _
                     , CmmExpr.CmmMachOp (CmmMachOp.MO_UU_Conv CmmType.W16 CmmType.W32) (cons
                      (CmmExpr.CmmLoad mem _) nil) =>
                         let cont_36__ arg_37__ :=
                           let 'MkAmode addr addr_code := arg_37__ in
                           GHC.Base.return_ (Any Format.II32 (fun dst =>
                                                                OrdList.snocOL addr_code (PPC.Instr.LD Format.II16 dst
                                                                                addr))) in
                         getAmode D mem GHC.Base.>>= cont_36__
                     | _
                     , CmmExpr.CmmMachOp (CmmMachOp.MO_SS_Conv CmmType.W16 CmmType.W32) (cons
                      (CmmExpr.CmmLoad mem _) nil) =>
                         let cont_40__ arg_41__ :=
                           let 'MkAmode addr addr_code := arg_41__ in
                           GHC.Base.return_ (Any Format.II32 (fun dst =>
                                                                OrdList.snocOL addr_code (PPC.Instr.LA Format.II16 dst
                                                                                addr))) in
                         getAmode D mem GHC.Base.>>= cont_40__
                     | _
                     , CmmExpr.CmmMachOp (CmmMachOp.MO_UU_Conv CmmType.W16 CmmType.W64) (cons
                      (CmmExpr.CmmLoad mem _) nil) =>
                         let cont_44__ arg_45__ :=
                           let 'MkAmode addr addr_code := arg_45__ in
                           GHC.Base.return_ (Any Format.II64 (fun dst =>
                                                                OrdList.snocOL addr_code (PPC.Instr.LD Format.II16 dst
                                                                                addr))) in
                         getAmode D mem GHC.Base.>>= cont_44__
                     | _
                     , CmmExpr.CmmMachOp (CmmMachOp.MO_SS_Conv CmmType.W16 CmmType.W64) (cons
                      (CmmExpr.CmmLoad mem _) nil) =>
                         let cont_48__ arg_49__ :=
                           let 'MkAmode addr addr_code := arg_49__ in
                           GHC.Base.return_ (Any Format.II64 (fun dst =>
                                                                OrdList.snocOL addr_code (PPC.Instr.LA Format.II16 dst
                                                                                addr))) in
                         getAmode D mem GHC.Base.>>= cont_48__
                     | _
                     , CmmExpr.CmmMachOp (CmmMachOp.MO_UU_Conv CmmType.W32 CmmType.W64) (cons
                      (CmmExpr.CmmLoad mem _) nil) =>
                         let cont_52__ arg_53__ :=
                           let 'MkAmode addr addr_code := arg_53__ in
                           GHC.Base.return_ (Any Format.II64 (fun dst =>
                                                                OrdList.snocOL addr_code (PPC.Instr.LD Format.II32 dst
                                                                                addr))) in
                         getAmode D mem GHC.Base.>>= cont_52__
                     | _
                     , CmmExpr.CmmMachOp (CmmMachOp.MO_SS_Conv CmmType.W32 CmmType.W64) (cons
                      (CmmExpr.CmmLoad mem _) nil) =>
                         let cont_56__ arg_57__ :=
                           let 'MkAmode addr addr_code := arg_57__ in
                           GHC.Base.return_ (Any Format.II64 (fun dst =>
                                                                OrdList.snocOL addr_code (PPC.Instr.LA Format.II32 dst
                                                                                addr))) in
                         getAmode DS mem GHC.Base.>>= cont_56__
                     | dflags, CmmExpr.CmmMachOp mop (cons x (cons y nil)) =>
                         let triv_float
                          : CmmType.Width ->
                            (Format.Format -> Reg.Reg -> Reg.Reg -> Reg.Reg -> PPC.Instr.Instr) ->
                            NCGMonad.NatM Register :=
                           fun width instr => trivialCodeNoImm (Format.floatFormat width) instr x y in
                         match mop with
                         | CmmMachOp.MO_F_Eq _ => condFltReg PPC.Cond.EQQ x y
                         | CmmMachOp.MO_F_Ne _ => condFltReg PPC.Cond.NE x y
                         | CmmMachOp.MO_F_Gt _ => condFltReg PPC.Cond.GTT x y
                         | CmmMachOp.MO_F_Ge _ => condFltReg PPC.Cond.GE x y
                         | CmmMachOp.MO_F_Lt _ => condFltReg PPC.Cond.LTT x y
                         | CmmMachOp.MO_F_Le _ => condFltReg PPC.Cond.LE x y
                         | CmmMachOp.MO_Eq rep =>
                             condIntReg PPC.Cond.EQQ (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                         | CmmMachOp.MO_Ne rep =>
                             condIntReg PPC.Cond.NE (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                         | CmmMachOp.MO_S_Gt rep =>
                             condIntReg PPC.Cond.GTT (extendSExpr dflags rep x) (extendSExpr dflags rep y)
                         | CmmMachOp.MO_S_Ge rep =>
                             condIntReg PPC.Cond.GE (extendSExpr dflags rep x) (extendSExpr dflags rep y)
                         | CmmMachOp.MO_S_Lt rep =>
                             condIntReg PPC.Cond.LTT (extendSExpr dflags rep x) (extendSExpr dflags rep y)
                         | CmmMachOp.MO_S_Le rep =>
                             condIntReg PPC.Cond.LE (extendSExpr dflags rep x) (extendSExpr dflags rep y)
                         | CmmMachOp.MO_U_Gt rep =>
                             condIntReg PPC.Cond.GU (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                         | CmmMachOp.MO_U_Ge rep =>
                             condIntReg PPC.Cond.GEU (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                         | CmmMachOp.MO_U_Lt rep =>
                             condIntReg PPC.Cond.LU (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                         | CmmMachOp.MO_U_Le rep =>
                             condIntReg PPC.Cond.LEU (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                         | CmmMachOp.MO_F_Add w => triv_float w PPC.Instr.FADD
                         | CmmMachOp.MO_F_Sub w => triv_float w PPC.Instr.FSUB
                         | CmmMachOp.MO_F_Mul w => triv_float w PPC.Instr.FMUL
                         | CmmMachOp.MO_F_Quot w => triv_float w PPC.Instr.FDIV
                         | CmmMachOp.MO_Add CmmType.W32 =>
                             let j_87__ :=
                               match y with
                               | CmmExpr.Mk_CmmLit lit =>
                                   let cont_81__ arg_82__ :=
                                     let 'pair src srcCode := arg_82__ in
                                     let imm := PPC.Regs.litToImm lit in
                                     let code :=
                                       fun dst =>
                                         OrdList.appOL srcCode (OrdList.toOL (cons (PPC.Instr.ADDIS dst src (PPC.Regs.HA
                                                                                                             imm)) (cons
                                                                                    (PPC.Instr.ADD dst dst (PPC.Instr.RIImm
                                                                                                            (PPC.Regs.LO imm)))
                                                                                    nil))) in
                                     GHC.Base.return_ (Any Format.II32 code) in
                                   getSomeReg x GHC.Base.>>= cont_81__
                               | _ => trivialCode CmmType.W32 true PPC.Instr.ADD x y
                               end in
                             match y with
                             | CmmExpr.Mk_CmmLit (CmmExpr.CmmInt imm immrep) =>
                                 match PPC.Regs.makeImmediate CmmType.W32 true imm with
                                 | Some _ =>
                                     trivialCode CmmType.W32 true PPC.Instr.ADD x (CmmExpr.Mk_CmmLit (CmmExpr.CmmInt
                                                                                                      imm immrep))
                                 | _ => j_87__
                                 end
                             | _ => j_87__
                             end
                         | CmmMachOp.MO_Add rep => trivialCode rep true PPC.Instr.ADD x y
                         | CmmMachOp.MO_Sub rep =>
                             let j_97__ :=
                               let j_93__ := trivialCodeNoImm' (Format.intFormat rep) PPC.Instr.SUBF y x in
                               match x with
                               | CmmExpr.Mk_CmmLit (CmmExpr.CmmInt imm _) =>
                                   match PPC.Regs.makeImmediate rep true imm with
                                   | Some _ => trivialCode rep true PPC.Instr.SUBFC y x
                                   | _ => j_93__
                                   end
                               | _ => j_93__
                               end in
                             match y with
                             | CmmExpr.Mk_CmmLit (CmmExpr.CmmInt imm immrep) =>
                                 match PPC.Regs.makeImmediate rep true (GHC.Num.negate imm) with
                                 | Some _ =>
                                     trivialCode rep true PPC.Instr.ADD x (CmmExpr.Mk_CmmLit (CmmExpr.CmmInt
                                                                                              (GHC.Num.negate imm) immrep))
                                 | _ => j_97__
                                 end
                             | _ => j_97__
                             end
                         | CmmMachOp.MO_Mul rep => shiftMulCode rep true PPC.Instr.MULL x y
                         | CmmMachOp.MO_S_MulMayOflo rep =>
                             let cont_102__ arg_103__ :=
                               let 'pair src1 code1 := arg_103__ in
                               let cont_104__ arg_105__ :=
                                 let 'pair src2 code2 := arg_105__ in
                                 let format := Format.intFormat rep in
                                 let code :=
                                   fun dst =>
                                     OrdList.appOL (OrdList.appOL code1 code2) (OrdList.toOL (cons (PPC.Instr.MULLO
                                                                                                    format dst src1 src2) (cons
                                                                                                    (PPC.Instr.MFOV format dst)
                                                                                                    nil))) in
                                 GHC.Base.return_ (Any format code) in
                               getSomeReg y GHC.Base.>>= cont_104__ in
                             getSomeReg x GHC.Base.>>= cont_102__
                         | CmmMachOp.MO_S_Quot rep =>
                             trivialCodeNoImmSign (Format.intFormat rep) true PPC.Instr.DIV (extendSExpr
                                                                                             dflags rep x) (extendSExpr dflags
                                                                                                            rep y)
                         | CmmMachOp.MO_U_Quot rep =>
                             trivialCodeNoImmSign (Format.intFormat rep) false PPC.Instr.DIV (extendUExpr
                                                                                              dflags rep x) (extendUExpr dflags
                                                                                                             rep y)
                         | CmmMachOp.MO_S_Rem rep =>
                             remainderCode rep true (extendSExpr dflags rep x) (extendSExpr dflags rep y)
                         | CmmMachOp.MO_U_Rem rep =>
                             remainderCode rep false (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                         | CmmMachOp.MO_And rep =>
                             let j_114__ := trivialCode rep false PPC.Instr.AND x y in
                             match y with
                             | CmmExpr.Mk_CmmLit (CmmExpr.CmmInt imm _) =>
                                 if orb (imm GHC.Base.== GHC.Num.negate #8) (imm GHC.Base.==
                                         GHC.Num.negate #4) : bool
                                 then let cont_115__ arg_116__ :=
                                        let 'pair src srcCode := arg_116__ in
                                        let fmt := Format.intFormat rep in
                                        let clear_mask := if imm GHC.Base.== GHC.Num.negate #4 : bool then #2 else #3 in
                                        let code :=
                                          fun dst =>
                                            OrdList.appOL srcCode (OrdList.unitOL (PPC.Instr.CLRRI fmt dst src
                                                                                   clear_mask)) in
                                        GHC.Base.return_ (Any fmt code) in
                                      getSomeReg x GHC.Base.>>= cont_115__ else
                                 j_114__
                             | _ => j_114__
                             end
                         | CmmMachOp.MO_Or rep => trivialCode rep false PPC.Instr.OR x y
                         | CmmMachOp.MO_Xor rep => trivialCode rep false PPC.Instr.XOR x y
                         | CmmMachOp.MO_Shl rep => shiftMulCode rep false PPC.Instr.SL x y
                         | CmmMachOp.MO_S_Shr rep =>
                             shiftMulCode rep false PPC.Instr.SRA (extendSExpr dflags rep x) y
                         | CmmMachOp.MO_U_Shr rep =>
                             shiftMulCode rep false PPC.Instr.SR (extendUExpr dflags rep x) y
                         | _ => Panic.panic (GHC.Base.hs_string__ "PPC.CodeGen.getRegister: no match")
                         end
                     | _, CmmExpr.Mk_CmmLit (CmmExpr.CmmInt i rep) =>
                         match PPC.Regs.makeImmediate rep true i with
                         | Some imm =>
                             let code := fun dst => OrdList.unitOL (PPC.Instr.LI dst imm) in
                             GHC.Base.return_ (Any (Format.intFormat rep) code)
                         | _ => (match arg_0__, arg_1__ with
                                 | _, CmmExpr.Mk_CmmLit (CmmExpr.CmmFloat f frep) =>
                                     NCGMonad.getNewLabelNat GHC.Base.>>=
                                     (fun lbl =>
                                        DynFlags.getDynFlags GHC.Base.>>=
                                        (fun dflags =>
                                           PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                                           (fun dynRef =>
                                              let cont_6__ arg_7__ :=
                                                let 'MkAmode addr addr_code := arg_7__ in
                                                let format := Format.floatFormat frep in
                                                let code :=
                                                  fun dst =>
                                                    OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                                    (Cmm.Statics lbl (cons (Cmm.CmmStaticLit (CmmExpr.CmmFloat f frep))
                                                                                           nil))) (OrdList.snocOL addr_code (PPC.Instr.LD
                                                                                                                   format dst addr)) in
                                                GHC.Base.return_ (Any format code) in
                                              getAmode D dynRef GHC.Base.>>= cont_6__)))
                                 | dflags, CmmExpr.Mk_CmmLit lit =>
                                     if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool
                                     then let imm := PPC.Regs.litToImm lit in
                                          let code :=
                                            fun dst =>
                                              OrdList.toOL (cons (PPC.Instr.LIS dst (PPC.Regs.HA imm)) (cons (PPC.Instr.ADD
                                                                                                              dst dst (PPC.Instr.RIImm
                                                                                                                       (PPC.Regs.LO imm)))
                                                                                                             nil)) in
                                          let rep := CmmExpr.cmmLitType dflags lit in
                                          GHC.Base.return_ (Any (Format.cmmTypeFormat rep) code) else
                                     NCGMonad.getNewLabelNat GHC.Base.>>=
                                     (fun lbl =>
                                        DynFlags.getDynFlags GHC.Base.>>=
                                        (fun dflags =>
                                           PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                                           (fun dynRef =>
                                              let cont_14__ arg_15__ :=
                                                let 'MkAmode addr addr_code := arg_15__ in
                                                let rep := CmmExpr.cmmLitType dflags lit in
                                                let format := Format.cmmTypeFormat rep in
                                                let code :=
                                                  fun dst =>
                                                    OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                                    (Cmm.Statics lbl (cons (Cmm.CmmStaticLit lit) nil))) (OrdList.snocOL
                                                                    addr_code (PPC.Instr.LD format dst addr)) in
                                                GHC.Base.return_ (Any format code) in
                                              getAmode D dynRef GHC.Base.>>= cont_14__)))
                                 | _, other =>
                                             Panic.panicStr (GHC.Base.hs_string__ "getRegister(ppc)") (PprCmmExpr.pprExpr
                                                                                                       other)
                                 end)
                         end
                     | _, CmmExpr.Mk_CmmLit (CmmExpr.CmmFloat f frep) =>
                         NCGMonad.getNewLabelNat GHC.Base.>>=
                         (fun lbl =>
                            DynFlags.getDynFlags GHC.Base.>>=
                            (fun dflags =>
                               PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                               (fun dynRef =>
                                  let cont_6__ arg_7__ :=
                                    let 'MkAmode addr addr_code := arg_7__ in
                                    let format := Format.floatFormat frep in
                                    let code :=
                                      fun dst =>
                                        OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                        (Cmm.Statics lbl (cons (Cmm.CmmStaticLit (CmmExpr.CmmFloat f frep))
                                                                               nil))) (OrdList.snocOL addr_code (PPC.Instr.LD
                                                                                                       format dst addr)) in
                                    GHC.Base.return_ (Any format code) in
                                  getAmode D dynRef GHC.Base.>>= cont_6__)))
                     | dflags, CmmExpr.Mk_CmmLit lit =>
                         if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool
                         then let imm := PPC.Regs.litToImm lit in
                              let code :=
                                fun dst =>
                                  OrdList.toOL (cons (PPC.Instr.LIS dst (PPC.Regs.HA imm)) (cons (PPC.Instr.ADD
                                                                                                  dst dst (PPC.Instr.RIImm
                                                                                                           (PPC.Regs.LO imm)))
                                                                                                 nil)) in
                              let rep := CmmExpr.cmmLitType dflags lit in
                              GHC.Base.return_ (Any (Format.cmmTypeFormat rep) code) else
                         NCGMonad.getNewLabelNat GHC.Base.>>=
                         (fun lbl =>
                            DynFlags.getDynFlags GHC.Base.>>=
                            (fun dflags =>
                               PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                               (fun dynRef =>
                                  let cont_14__ arg_15__ :=
                                    let 'MkAmode addr addr_code := arg_15__ in
                                    let rep := CmmExpr.cmmLitType dflags lit in
                                    let format := Format.cmmTypeFormat rep in
                                    let code :=
                                      fun dst =>
                                        OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                        (Cmm.Statics lbl (cons (Cmm.CmmStaticLit lit) nil))) (OrdList.snocOL
                                                        addr_code (PPC.Instr.LD format dst addr)) in
                                    GHC.Base.return_ (Any format code) in
                                  getAmode D dynRef GHC.Base.>>= cont_14__)))
                     | _, other =>
                                 Panic.panicStr (GHC.Base.hs_string__ "getRegister(ppc)") (PprCmmExpr.pprExpr
                                                                                           other)

                     end) else
               (match arg_0__, arg_1__ with
                | dflags
                 , CmmExpr.CmmMachOp (CmmMachOp.MO_UU_Conv CmmType.W64 CmmType.W32) (cons x
                  nil) =>
                     if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool
                     then let cont_22__ arg_23__ :=
                            let 'MkChildCode64 code rlo := arg_23__ in
                            GHC.Base.return_ (Fixed Format.II32 rlo code) in
                          iselExpr64 x GHC.Base.>>= cont_22__ else
                     (match arg_0__, arg_1__ with
                      | _, CmmExpr.Mk_CmmLit (CmmExpr.CmmFloat f frep) =>
                           NCGMonad.getNewLabelNat GHC.Base.>>=
                           (fun lbl =>
                              DynFlags.getDynFlags GHC.Base.>>=
                              (fun dflags =>
                                 PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                                 (fun dynRef =>
                                    let cont_6__ arg_7__ :=
                                      let 'MkAmode addr addr_code := arg_7__ in
                                      let format := Format.floatFormat frep in
                                      let code :=
                                        fun dst =>
                                          OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                          (Cmm.Statics lbl (cons (Cmm.CmmStaticLit (CmmExpr.CmmFloat f frep))
                                                                                 nil))) (OrdList.snocOL addr_code (PPC.Instr.LD
                                                                                                         format dst addr)) in
                                      GHC.Base.return_ (Any format code) in
                                    getAmode D dynRef GHC.Base.>>= cont_6__)))
                      | dflags, CmmExpr.Mk_CmmLit lit =>
                           if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool
                           then let imm := PPC.Regs.litToImm lit in
                                let code :=
                                  fun dst =>
                                    OrdList.toOL (cons (PPC.Instr.LIS dst (PPC.Regs.HA imm)) (cons (PPC.Instr.ADD
                                                                                                    dst dst (PPC.Instr.RIImm
                                                                                                             (PPC.Regs.LO imm)))
                                                                                                   nil)) in
                                let rep := CmmExpr.cmmLitType dflags lit in
                                GHC.Base.return_ (Any (Format.cmmTypeFormat rep) code) else
                           NCGMonad.getNewLabelNat GHC.Base.>>=
                           (fun lbl =>
                              DynFlags.getDynFlags GHC.Base.>>=
                              (fun dflags =>
                                 PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                                 (fun dynRef =>
                                    let cont_14__ arg_15__ :=
                                      let 'MkAmode addr addr_code := arg_15__ in
                                      let rep := CmmExpr.cmmLitType dflags lit in
                                      let format := Format.cmmTypeFormat rep in
                                      let code :=
                                        fun dst =>
                                          OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                          (Cmm.Statics lbl (cons (Cmm.CmmStaticLit lit) nil))) (OrdList.snocOL
                                                          addr_code (PPC.Instr.LD format dst addr)) in
                                      GHC.Base.return_ (Any format code) in
                                    getAmode D dynRef GHC.Base.>>= cont_14__)))
                      | _, other =>
                                   Panic.panicStr (GHC.Base.hs_string__ "getRegister(ppc)") (PprCmmExpr.pprExpr
                                                                                             other)
                       end )
                | dflags
                 , CmmExpr.CmmMachOp (CmmMachOp.MO_SS_Conv CmmType.W64 CmmType.W32) (cons x
                  nil) =>
                     if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool
                     then let cont_25__ arg_26__ :=
                            let 'MkChildCode64 code rlo := arg_26__ in
                            GHC.Base.return_ (Fixed Format.II32 rlo code) in
                          iselExpr64 x GHC.Base.>>= cont_25__ else
                     (match arg_0__, arg_1__ with
                      | _, CmmExpr.Mk_CmmLit (CmmExpr.CmmFloat f frep) =>
                           NCGMonad.getNewLabelNat GHC.Base.>>=
                           (fun lbl =>
                              DynFlags.getDynFlags GHC.Base.>>=
                              (fun dflags =>
                                 PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                                 (fun dynRef =>
                                    let cont_6__ arg_7__ :=
                                      let 'MkAmode addr addr_code := arg_7__ in
                                      let format := Format.floatFormat frep in
                                      let code :=
                                        fun dst =>
                                          OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                          (Cmm.Statics lbl (cons (Cmm.CmmStaticLit (CmmExpr.CmmFloat f frep))
                                                                                 nil))) (OrdList.snocOL addr_code (PPC.Instr.LD
                                                                                                         format dst addr)) in
                                      GHC.Base.return_ (Any format code) in
                                    getAmode D dynRef GHC.Base.>>= cont_6__)))
                      | dflags, CmmExpr.Mk_CmmLit lit =>
                           if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool
                           then let imm := PPC.Regs.litToImm lit in
                                let code :=
                                  fun dst =>
                                    OrdList.toOL (cons (PPC.Instr.LIS dst (PPC.Regs.HA imm)) (cons (PPC.Instr.ADD
                                                                                                    dst dst (PPC.Instr.RIImm
                                                                                                             (PPC.Regs.LO imm)))
                                                                                                   nil)) in
                                let rep := CmmExpr.cmmLitType dflags lit in
                                GHC.Base.return_ (Any (Format.cmmTypeFormat rep) code) else
                           NCGMonad.getNewLabelNat GHC.Base.>>=
                           (fun lbl =>
                              DynFlags.getDynFlags GHC.Base.>>=
                              (fun dflags =>
                                 PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                                 (fun dynRef =>
                                    let cont_14__ arg_15__ :=
                                      let 'MkAmode addr addr_code := arg_15__ in
                                      let rep := CmmExpr.cmmLitType dflags lit in
                                      let format := Format.cmmTypeFormat rep in
                                      let code :=
                                        fun dst =>
                                          OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                          (Cmm.Statics lbl (cons (Cmm.CmmStaticLit lit) nil))) (OrdList.snocOL
                                                          addr_code (PPC.Instr.LD format dst addr)) in
                                      GHC.Base.return_ (Any format code) in
                                    getAmode D dynRef GHC.Base.>>= cont_14__)))
                      | _, other =>
                                   Panic.panicStr (GHC.Base.hs_string__ "getRegister(ppc)") (PprCmmExpr.pprExpr
                                                                                             other)
                       end)
                | _
                 , CmmExpr.CmmMachOp (CmmMachOp.MO_UU_Conv CmmType.W8 CmmType.W32) (cons
                  (CmmExpr.CmmLoad mem _) nil) =>
                     let cont_28__ arg_29__ :=
                       let 'MkAmode addr addr_code := arg_29__ in
                       GHC.Base.return_ (Any Format.II32 (fun dst =>
                                                            OrdList.snocOL addr_code (PPC.Instr.LD Format.II8 dst addr))) in
                     getAmode D mem GHC.Base.>>= cont_28__
                | _
                 , CmmExpr.CmmMachOp (CmmMachOp.MO_UU_Conv CmmType.W8 CmmType.W64) (cons
                  (CmmExpr.CmmLoad mem _) nil) =>
                     let cont_32__ arg_33__ :=
                       let 'MkAmode addr addr_code := arg_33__ in
                       GHC.Base.return_ (Any Format.II64 (fun dst =>
                                                            OrdList.snocOL addr_code (PPC.Instr.LD Format.II8 dst addr))) in
                     getAmode D mem GHC.Base.>>= cont_32__
                | _
                 , CmmExpr.CmmMachOp (CmmMachOp.MO_UU_Conv CmmType.W16 CmmType.W32) (cons
                  (CmmExpr.CmmLoad mem _) nil) =>
                     let cont_36__ arg_37__ :=
                       let 'MkAmode addr addr_code := arg_37__ in
                       GHC.Base.return_ (Any Format.II32 (fun dst =>
                                                            OrdList.snocOL addr_code (PPC.Instr.LD Format.II16 dst
                                                                            addr))) in
                     getAmode D mem GHC.Base.>>= cont_36__
                | _
                 , CmmExpr.CmmMachOp (CmmMachOp.MO_SS_Conv CmmType.W16 CmmType.W32) (cons
                  (CmmExpr.CmmLoad mem _) nil) =>
                     let cont_40__ arg_41__ :=
                       let 'MkAmode addr addr_code := arg_41__ in
                       GHC.Base.return_ (Any Format.II32 (fun dst =>
                                                            OrdList.snocOL addr_code (PPC.Instr.LA Format.II16 dst
                                                                            addr))) in
                     getAmode D mem GHC.Base.>>= cont_40__
                | _
                 , CmmExpr.CmmMachOp (CmmMachOp.MO_UU_Conv CmmType.W16 CmmType.W64) (cons
                  (CmmExpr.CmmLoad mem _) nil) =>
                     let cont_44__ arg_45__ :=
                       let 'MkAmode addr addr_code := arg_45__ in
                       GHC.Base.return_ (Any Format.II64 (fun dst =>
                                                            OrdList.snocOL addr_code (PPC.Instr.LD Format.II16 dst
                                                                            addr))) in
                     getAmode D mem GHC.Base.>>= cont_44__
                | _
                 , CmmExpr.CmmMachOp (CmmMachOp.MO_SS_Conv CmmType.W16 CmmType.W64) (cons
                  (CmmExpr.CmmLoad mem _) nil) =>
                     let cont_48__ arg_49__ :=
                       let 'MkAmode addr addr_code := arg_49__ in
                       GHC.Base.return_ (Any Format.II64 (fun dst =>
                                                            OrdList.snocOL addr_code (PPC.Instr.LA Format.II16 dst
                                                                            addr))) in
                     getAmode D mem GHC.Base.>>= cont_48__
                | _
                 , CmmExpr.CmmMachOp (CmmMachOp.MO_UU_Conv CmmType.W32 CmmType.W64) (cons
                  (CmmExpr.CmmLoad mem _) nil) =>
                     let cont_52__ arg_53__ :=
                       let 'MkAmode addr addr_code := arg_53__ in
                       GHC.Base.return_ (Any Format.II64 (fun dst =>
                                                            OrdList.snocOL addr_code (PPC.Instr.LD Format.II32 dst
                                                                            addr))) in
                     getAmode D mem GHC.Base.>>= cont_52__
                | _
                 , CmmExpr.CmmMachOp (CmmMachOp.MO_SS_Conv CmmType.W32 CmmType.W64) (cons
                  (CmmExpr.CmmLoad mem _) nil) =>
                     let cont_56__ arg_57__ :=
                       let 'MkAmode addr addr_code := arg_57__ in
                       GHC.Base.return_ (Any Format.II64 (fun dst =>
                                                            OrdList.snocOL addr_code (PPC.Instr.LA Format.II32 dst
                                                                            addr))) in
                     getAmode DS mem GHC.Base.>>= cont_56__
                | dflags, CmmExpr.CmmMachOp mop (cons x (cons y nil)) =>
                     let triv_float
                      : CmmType.Width ->
                        (Format.Format -> Reg.Reg -> Reg.Reg -> Reg.Reg -> PPC.Instr.Instr) ->
                        NCGMonad.NatM Register :=
                       fun width instr => trivialCodeNoImm (Format.floatFormat width) instr x y in
                     match mop with
                     | CmmMachOp.MO_F_Eq _ => condFltReg PPC.Cond.EQQ x y
                     | CmmMachOp.MO_F_Ne _ => condFltReg PPC.Cond.NE x y
                     | CmmMachOp.MO_F_Gt _ => condFltReg PPC.Cond.GTT x y
                     | CmmMachOp.MO_F_Ge _ => condFltReg PPC.Cond.GE x y
                     | CmmMachOp.MO_F_Lt _ => condFltReg PPC.Cond.LTT x y
                     | CmmMachOp.MO_F_Le _ => condFltReg PPC.Cond.LE x y
                     | CmmMachOp.MO_Eq rep =>
                         condIntReg PPC.Cond.EQQ (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                     | CmmMachOp.MO_Ne rep =>
                         condIntReg PPC.Cond.NE (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                     | CmmMachOp.MO_S_Gt rep =>
                         condIntReg PPC.Cond.GTT (extendSExpr dflags rep x) (extendSExpr dflags rep y)
                     | CmmMachOp.MO_S_Ge rep =>
                         condIntReg PPC.Cond.GE (extendSExpr dflags rep x) (extendSExpr dflags rep y)
                     | CmmMachOp.MO_S_Lt rep =>
                         condIntReg PPC.Cond.LTT (extendSExpr dflags rep x) (extendSExpr dflags rep y)
                     | CmmMachOp.MO_S_Le rep =>
                         condIntReg PPC.Cond.LE (extendSExpr dflags rep x) (extendSExpr dflags rep y)
                     | CmmMachOp.MO_U_Gt rep =>
                         condIntReg PPC.Cond.GU (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                     | CmmMachOp.MO_U_Ge rep =>
                         condIntReg PPC.Cond.GEU (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                     | CmmMachOp.MO_U_Lt rep =>
                         condIntReg PPC.Cond.LU (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                     | CmmMachOp.MO_U_Le rep =>
                         condIntReg PPC.Cond.LEU (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                     | CmmMachOp.MO_F_Add w => triv_float w PPC.Instr.FADD
                     | CmmMachOp.MO_F_Sub w => triv_float w PPC.Instr.FSUB
                     | CmmMachOp.MO_F_Mul w => triv_float w PPC.Instr.FMUL
                     | CmmMachOp.MO_F_Quot w => triv_float w PPC.Instr.FDIV
                     | CmmMachOp.MO_Add CmmType.W32 =>
                         let j_87__ :=
                           match y with
                           | CmmExpr.Mk_CmmLit lit =>
                               let cont_81__ arg_82__ :=
                                 let 'pair src srcCode := arg_82__ in
                                 let imm := PPC.Regs.litToImm lit in
                                 let code :=
                                   fun dst =>
                                     OrdList.appOL srcCode (OrdList.toOL (cons (PPC.Instr.ADDIS dst src (PPC.Regs.HA
                                                                                                         imm)) (cons
                                                                                (PPC.Instr.ADD dst dst (PPC.Instr.RIImm
                                                                                                        (PPC.Regs.LO imm)))
                                                                                nil))) in
                                 GHC.Base.return_ (Any Format.II32 code) in
                               getSomeReg x GHC.Base.>>= cont_81__
                           | _ => trivialCode CmmType.W32 true PPC.Instr.ADD x y
                           end in
                         match y with
                         | CmmExpr.Mk_CmmLit (CmmExpr.CmmInt imm immrep) =>
                             match PPC.Regs.makeImmediate CmmType.W32 true imm with
                             | Some _ =>
                                 trivialCode CmmType.W32 true PPC.Instr.ADD x (CmmExpr.Mk_CmmLit (CmmExpr.CmmInt
                                                                                                  imm immrep))
                             | _ => j_87__
                             end
                         | _ => j_87__
                         end
                     | CmmMachOp.MO_Add rep => trivialCode rep true PPC.Instr.ADD x y
                     | CmmMachOp.MO_Sub rep =>
                         let j_97__ :=
                           let j_93__ := trivialCodeNoImm' (Format.intFormat rep) PPC.Instr.SUBF y x in
                           match x with
                           | CmmExpr.Mk_CmmLit (CmmExpr.CmmInt imm _) =>
                               match PPC.Regs.makeImmediate rep true imm with
                               | Some _ => trivialCode rep true PPC.Instr.SUBFC y x
                               | _ => j_93__
                               end
                           | _ => j_93__
                           end in
                         match y with
                         | CmmExpr.Mk_CmmLit (CmmExpr.CmmInt imm immrep) =>
                             match PPC.Regs.makeImmediate rep true (GHC.Num.negate imm) with
                             | Some _ =>
                                 trivialCode rep true PPC.Instr.ADD x (CmmExpr.Mk_CmmLit (CmmExpr.CmmInt
                                                                                          (GHC.Num.negate imm) immrep))
                             | _ => j_97__
                             end
                         | _ => j_97__
                         end
                     | CmmMachOp.MO_Mul rep => shiftMulCode rep true PPC.Instr.MULL x y
                     | CmmMachOp.MO_S_MulMayOflo rep =>
                         let cont_102__ arg_103__ :=
                           let 'pair src1 code1 := arg_103__ in
                           let cont_104__ arg_105__ :=
                             let 'pair src2 code2 := arg_105__ in
                             let format := Format.intFormat rep in
                             let code :=
                               fun dst =>
                                 OrdList.appOL (OrdList.appOL code1 code2) (OrdList.toOL (cons (PPC.Instr.MULLO
                                                                                                format dst src1 src2) (cons
                                                                                                (PPC.Instr.MFOV format dst)
                                                                                                nil))) in
                             GHC.Base.return_ (Any format code) in
                           getSomeReg y GHC.Base.>>= cont_104__ in
                         getSomeReg x GHC.Base.>>= cont_102__
                     | CmmMachOp.MO_S_Quot rep =>
                         trivialCodeNoImmSign (Format.intFormat rep) true PPC.Instr.DIV (extendSExpr
                                                                                         dflags rep x) (extendSExpr dflags
                                                                                                        rep y)
                     | CmmMachOp.MO_U_Quot rep =>
                         trivialCodeNoImmSign (Format.intFormat rep) false PPC.Instr.DIV (extendUExpr
                                                                                          dflags rep x) (extendUExpr dflags
                                                                                                         rep y)
                     | CmmMachOp.MO_S_Rem rep =>
                         remainderCode rep true (extendSExpr dflags rep x) (extendSExpr dflags rep y)
                     | CmmMachOp.MO_U_Rem rep =>
                         remainderCode rep false (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                     | CmmMachOp.MO_And rep =>
                         let j_114__ := trivialCode rep false PPC.Instr.AND x y in
                         match y with
                         | CmmExpr.Mk_CmmLit (CmmExpr.CmmInt imm _) =>
                             if orb (imm GHC.Base.== GHC.Num.negate #8) (imm GHC.Base.==
                                     GHC.Num.negate #4) : bool
                             then let cont_115__ arg_116__ :=
                                    let 'pair src srcCode := arg_116__ in
                                    let fmt := Format.intFormat rep in
                                    let clear_mask := if imm GHC.Base.== GHC.Num.negate #4 : bool then #2 else #3 in
                                    let code :=
                                      fun dst =>
                                        OrdList.appOL srcCode (OrdList.unitOL (PPC.Instr.CLRRI fmt dst src
                                                                               clear_mask)) in
                                    GHC.Base.return_ (Any fmt code) in
                                  getSomeReg x GHC.Base.>>= cont_115__ else
                             j_114__
                         | _ => j_114__
                         end
                     | CmmMachOp.MO_Or rep => trivialCode rep false PPC.Instr.OR x y
                     | CmmMachOp.MO_Xor rep => trivialCode rep false PPC.Instr.XOR x y
                     | CmmMachOp.MO_Shl rep => shiftMulCode rep false PPC.Instr.SL x y
                     | CmmMachOp.MO_S_Shr rep =>
                         shiftMulCode rep false PPC.Instr.SRA (extendSExpr dflags rep x) y
                     | CmmMachOp.MO_U_Shr rep =>
                         shiftMulCode rep false PPC.Instr.SR (extendUExpr dflags rep x) y
                     | _ => Panic.panic (GHC.Base.hs_string__ "PPC.CodeGen.getRegister: no match")
                     end
                | _, CmmExpr.Mk_CmmLit (CmmExpr.CmmInt i rep) =>
                     match PPC.Regs.makeImmediate rep true i with
                     | Some imm =>
                         let code := fun dst => OrdList.unitOL (PPC.Instr.LI dst imm) in
                         GHC.Base.return_ (Any (Format.intFormat rep) code)
                     | _ => (match arg_0__, arg_1__ with
                             | _, CmmExpr.Mk_CmmLit (CmmExpr.CmmFloat f frep) =>
                                 NCGMonad.getNewLabelNat GHC.Base.>>=
                                 (fun lbl =>
                                    DynFlags.getDynFlags GHC.Base.>>=
                                    (fun dflags =>
                                       PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                                       (fun dynRef =>
                                          let cont_6__ arg_7__ :=
                                            let 'MkAmode addr addr_code := arg_7__ in
                                            let format := Format.floatFormat frep in
                                            let code :=
                                              fun dst =>
                                                OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                                (Cmm.Statics lbl (cons (Cmm.CmmStaticLit (CmmExpr.CmmFloat f frep))
                                                                                       nil))) (OrdList.snocOL addr_code (PPC.Instr.LD
                                                                                                               format dst addr)) in
                                            GHC.Base.return_ (Any format code) in
                                          getAmode D dynRef GHC.Base.>>= cont_6__)))
                             | dflags, CmmExpr.Mk_CmmLit lit =>
                                 if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool
                                 then let imm := PPC.Regs.litToImm lit in
                                      let code :=
                                        fun dst =>
                                          OrdList.toOL (cons (PPC.Instr.LIS dst (PPC.Regs.HA imm)) (cons (PPC.Instr.ADD
                                                                                                          dst dst (PPC.Instr.RIImm
                                                                                                                   (PPC.Regs.LO imm)))
                                                                                                         nil)) in
                                      let rep := CmmExpr.cmmLitType dflags lit in
                                      GHC.Base.return_ (Any (Format.cmmTypeFormat rep) code) else
                                 NCGMonad.getNewLabelNat GHC.Base.>>=
                                 (fun lbl =>
                                    DynFlags.getDynFlags GHC.Base.>>=
                                    (fun dflags =>
                                       PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                                       (fun dynRef =>
                                          let cont_14__ arg_15__ :=
                                            let 'MkAmode addr addr_code := arg_15__ in
                                            let rep := CmmExpr.cmmLitType dflags lit in
                                            let format := Format.cmmTypeFormat rep in
                                            let code :=
                                              fun dst =>
                                                OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                                (Cmm.Statics lbl (cons (Cmm.CmmStaticLit lit) nil))) (OrdList.snocOL
                                                                addr_code (PPC.Instr.LD format dst addr)) in
                                            GHC.Base.return_ (Any format code) in
                                          getAmode D dynRef GHC.Base.>>= cont_14__)))
                             | _, other =>
                                         Panic.panicStr (GHC.Base.hs_string__ "getRegister(ppc)") (PprCmmExpr.pprExpr
                                                                                                   other)
                             end)
                     end
                | _, CmmExpr.Mk_CmmLit (CmmExpr.CmmFloat f frep) =>
                     NCGMonad.getNewLabelNat GHC.Base.>>=
                     (fun lbl =>
                        DynFlags.getDynFlags GHC.Base.>>=
                        (fun dflags =>
                           PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                           (fun dynRef =>
                              let cont_6__ arg_7__ :=
                                let 'MkAmode addr addr_code := arg_7__ in
                                let format := Format.floatFormat frep in
                                let code :=
                                  fun dst =>
                                    OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                    (Cmm.Statics lbl (cons (Cmm.CmmStaticLit (CmmExpr.CmmFloat f frep))
                                                                           nil))) (OrdList.snocOL addr_code (PPC.Instr.LD
                                                                                                   format dst addr)) in
                                GHC.Base.return_ (Any format code) in
                              getAmode D dynRef GHC.Base.>>= cont_6__)))
                | dflags, CmmExpr.Mk_CmmLit lit =>
                     if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool
                     then let imm := PPC.Regs.litToImm lit in
                          let code :=
                            fun dst =>
                              OrdList.toOL (cons (PPC.Instr.LIS dst (PPC.Regs.HA imm)) (cons (PPC.Instr.ADD
                                                                                              dst dst (PPC.Instr.RIImm
                                                                                                       (PPC.Regs.LO imm)))
                                                                                             nil)) in
                          let rep := CmmExpr.cmmLitType dflags lit in
                          GHC.Base.return_ (Any (Format.cmmTypeFormat rep) code) else
                     NCGMonad.getNewLabelNat GHC.Base.>>=
                     (fun lbl =>
                        DynFlags.getDynFlags GHC.Base.>>=
                        (fun dflags =>
                           PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                           (fun dynRef =>
                              let cont_14__ arg_15__ :=
                                let 'MkAmode addr addr_code := arg_15__ in
                                let rep := CmmExpr.cmmLitType dflags lit in
                                let format := Format.cmmTypeFormat rep in
                                let code :=
                                  fun dst =>
                                    OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                    (Cmm.Statics lbl (cons (Cmm.CmmStaticLit lit) nil))) (OrdList.snocOL
                                                    addr_code (PPC.Instr.LD format dst addr)) in
                                GHC.Base.return_ (Any format code) in
                              getAmode D dynRef GHC.Base.>>= cont_14__)))
                | _, other =>
                             Panic.panicStr (GHC.Base.hs_string__ "getRegister(ppc)") (PprCmmExpr.pprExpr
                                                                                       other)

                end)
           | dflags
           , CmmExpr.CmmMachOp (CmmMachOp.MO_SS_Conv CmmType.W64 CmmType.W32) (cons
            (CmmExpr.CmmMachOp (CmmMachOp.MO_U_Shr CmmType.W64) (cons x (cons
               (CmmExpr.Mk_CmmLit (CmmExpr.CmmInt num_3__ _)) nil))) nil) =>
               if num_3__ GHC.Base.== #32 : bool
               then if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool
                    then let cont_139__ arg_140__ :=
                           let 'MkChildCode64 code rlo := arg_140__ in
                           GHC.Base.return_ (Fixed Format.II32 (Reg.getHiVRegFromLo rlo) code) in
                         iselExpr64 x GHC.Base.>>= cont_139__ else
                    (match arg_0__, arg_1__ with
                     | dflags
                     , CmmExpr.CmmMachOp (CmmMachOp.MO_UU_Conv CmmType.W64 CmmType.W32) (cons x
                      nil) =>
                         if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool
                         then let cont_22__ arg_23__ :=
                                let 'MkChildCode64 code rlo := arg_23__ in
                                GHC.Base.return_ (Fixed Format.II32 rlo code) in
                              iselExpr64 x GHC.Base.>>= cont_22__ else
                         (match arg_0__, arg_1__ with
                          | _, CmmExpr.Mk_CmmLit (CmmExpr.CmmFloat f frep) =>
                               NCGMonad.getNewLabelNat GHC.Base.>>=
                               (fun lbl =>
                                  DynFlags.getDynFlags GHC.Base.>>=
                                  (fun dflags =>
                                     PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                                     (fun dynRef =>
                                        let cont_6__ arg_7__ :=
                                          let 'MkAmode addr addr_code := arg_7__ in
                                          let format := Format.floatFormat frep in
                                          let code :=
                                            fun dst =>
                                              OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                              (Cmm.Statics lbl (cons (Cmm.CmmStaticLit (CmmExpr.CmmFloat f frep))
                                                                                     nil))) (OrdList.snocOL addr_code (PPC.Instr.LD
                                                                                                             format dst addr)) in
                                          GHC.Base.return_ (Any format code) in
                                        getAmode D dynRef GHC.Base.>>= cont_6__)))
                          | dflags, CmmExpr.Mk_CmmLit lit =>
                               if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool
                               then let imm := PPC.Regs.litToImm lit in
                                    let code :=
                                      fun dst =>
                                        OrdList.toOL (cons (PPC.Instr.LIS dst (PPC.Regs.HA imm)) (cons (PPC.Instr.ADD
                                                                                                        dst dst (PPC.Instr.RIImm
                                                                                                                 (PPC.Regs.LO imm)))
                                                                                                       nil)) in
                                    let rep := CmmExpr.cmmLitType dflags lit in
                                    GHC.Base.return_ (Any (Format.cmmTypeFormat rep) code) else
                               NCGMonad.getNewLabelNat GHC.Base.>>=
                               (fun lbl =>
                                  DynFlags.getDynFlags GHC.Base.>>=
                                  (fun dflags =>
                                     PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                                     (fun dynRef =>
                                        let cont_14__ arg_15__ :=
                                          let 'MkAmode addr addr_code := arg_15__ in
                                          let rep := CmmExpr.cmmLitType dflags lit in
                                          let format := Format.cmmTypeFormat rep in
                                          let code :=
                                            fun dst =>
                                              OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                              (Cmm.Statics lbl (cons (Cmm.CmmStaticLit lit) nil))) (OrdList.snocOL
                                                              addr_code (PPC.Instr.LD format dst addr)) in
                                          GHC.Base.return_ (Any format code) in
                                        getAmode D dynRef GHC.Base.>>= cont_14__)))
                          | _, other =>
                                       Panic.panicStr (GHC.Base.hs_string__ "getRegister(ppc)") (PprCmmExpr.pprExpr
                                                                                                 other)
                           end )
                     | dflags
                     , CmmExpr.CmmMachOp (CmmMachOp.MO_SS_Conv CmmType.W64 CmmType.W32) (cons x
                      nil) =>
                         if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool
                         then let cont_25__ arg_26__ :=
                                let 'MkChildCode64 code rlo := arg_26__ in
                                GHC.Base.return_ (Fixed Format.II32 rlo code) in
                              iselExpr64 x GHC.Base.>>= cont_25__ else
                         (match arg_0__, arg_1__ with
                          | _, CmmExpr.Mk_CmmLit (CmmExpr.CmmFloat f frep) =>
                               NCGMonad.getNewLabelNat GHC.Base.>>=
                               (fun lbl =>
                                  DynFlags.getDynFlags GHC.Base.>>=
                                  (fun dflags =>
                                     PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                                     (fun dynRef =>
                                        let cont_6__ arg_7__ :=
                                          let 'MkAmode addr addr_code := arg_7__ in
                                          let format := Format.floatFormat frep in
                                          let code :=
                                            fun dst =>
                                              OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                              (Cmm.Statics lbl (cons (Cmm.CmmStaticLit (CmmExpr.CmmFloat f frep))
                                                                                     nil))) (OrdList.snocOL addr_code (PPC.Instr.LD
                                                                                                             format dst addr)) in
                                          GHC.Base.return_ (Any format code) in
                                        getAmode D dynRef GHC.Base.>>= cont_6__)))
                          | dflags, CmmExpr.Mk_CmmLit lit =>
                               if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool
                               then let imm := PPC.Regs.litToImm lit in
                                    let code :=
                                      fun dst =>
                                        OrdList.toOL (cons (PPC.Instr.LIS dst (PPC.Regs.HA imm)) (cons (PPC.Instr.ADD
                                                                                                        dst dst (PPC.Instr.RIImm
                                                                                                                 (PPC.Regs.LO imm)))
                                                                                                       nil)) in
                                    let rep := CmmExpr.cmmLitType dflags lit in
                                    GHC.Base.return_ (Any (Format.cmmTypeFormat rep) code) else
                               NCGMonad.getNewLabelNat GHC.Base.>>=
                               (fun lbl =>
                                  DynFlags.getDynFlags GHC.Base.>>=
                                  (fun dflags =>
                                     PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                                     (fun dynRef =>
                                        let cont_14__ arg_15__ :=
                                          let 'MkAmode addr addr_code := arg_15__ in
                                          let rep := CmmExpr.cmmLitType dflags lit in
                                          let format := Format.cmmTypeFormat rep in
                                          let code :=
                                            fun dst =>
                                              OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                              (Cmm.Statics lbl (cons (Cmm.CmmStaticLit lit) nil))) (OrdList.snocOL
                                                              addr_code (PPC.Instr.LD format dst addr)) in
                                          GHC.Base.return_ (Any format code) in
                                        getAmode D dynRef GHC.Base.>>= cont_14__)))
                          | _, other =>
                                       Panic.panicStr (GHC.Base.hs_string__ "getRegister(ppc)") (PprCmmExpr.pprExpr
                                                                                                 other)
                           end)
                     | _
                     , CmmExpr.CmmMachOp (CmmMachOp.MO_UU_Conv CmmType.W8 CmmType.W32) (cons
                      (CmmExpr.CmmLoad mem _) nil) =>
                         let cont_28__ arg_29__ :=
                           let 'MkAmode addr addr_code := arg_29__ in
                           GHC.Base.return_ (Any Format.II32 (fun dst =>
                                                                OrdList.snocOL addr_code (PPC.Instr.LD Format.II8 dst addr))) in
                         getAmode D mem GHC.Base.>>= cont_28__
                     | _
                     , CmmExpr.CmmMachOp (CmmMachOp.MO_UU_Conv CmmType.W8 CmmType.W64) (cons
                      (CmmExpr.CmmLoad mem _) nil) =>
                         let cont_32__ arg_33__ :=
                           let 'MkAmode addr addr_code := arg_33__ in
                           GHC.Base.return_ (Any Format.II64 (fun dst =>
                                                                OrdList.snocOL addr_code (PPC.Instr.LD Format.II8 dst addr))) in
                         getAmode D mem GHC.Base.>>= cont_32__
                     | _
                     , CmmExpr.CmmMachOp (CmmMachOp.MO_UU_Conv CmmType.W16 CmmType.W32) (cons
                      (CmmExpr.CmmLoad mem _) nil) =>
                         let cont_36__ arg_37__ :=
                           let 'MkAmode addr addr_code := arg_37__ in
                           GHC.Base.return_ (Any Format.II32 (fun dst =>
                                                                OrdList.snocOL addr_code (PPC.Instr.LD Format.II16 dst
                                                                                addr))) in
                         getAmode D mem GHC.Base.>>= cont_36__
                     | _
                     , CmmExpr.CmmMachOp (CmmMachOp.MO_SS_Conv CmmType.W16 CmmType.W32) (cons
                      (CmmExpr.CmmLoad mem _) nil) =>
                         let cont_40__ arg_41__ :=
                           let 'MkAmode addr addr_code := arg_41__ in
                           GHC.Base.return_ (Any Format.II32 (fun dst =>
                                                                OrdList.snocOL addr_code (PPC.Instr.LA Format.II16 dst
                                                                                addr))) in
                         getAmode D mem GHC.Base.>>= cont_40__
                     | _
                     , CmmExpr.CmmMachOp (CmmMachOp.MO_UU_Conv CmmType.W16 CmmType.W64) (cons
                      (CmmExpr.CmmLoad mem _) nil) =>
                         let cont_44__ arg_45__ :=
                           let 'MkAmode addr addr_code := arg_45__ in
                           GHC.Base.return_ (Any Format.II64 (fun dst =>
                                                                OrdList.snocOL addr_code (PPC.Instr.LD Format.II16 dst
                                                                                addr))) in
                         getAmode D mem GHC.Base.>>= cont_44__
                     | _
                     , CmmExpr.CmmMachOp (CmmMachOp.MO_SS_Conv CmmType.W16 CmmType.W64) (cons
                      (CmmExpr.CmmLoad mem _) nil) =>
                         let cont_48__ arg_49__ :=
                           let 'MkAmode addr addr_code := arg_49__ in
                           GHC.Base.return_ (Any Format.II64 (fun dst =>
                                                                OrdList.snocOL addr_code (PPC.Instr.LA Format.II16 dst
                                                                                addr))) in
                         getAmode D mem GHC.Base.>>= cont_48__
                     | _
                     , CmmExpr.CmmMachOp (CmmMachOp.MO_UU_Conv CmmType.W32 CmmType.W64) (cons
                      (CmmExpr.CmmLoad mem _) nil) =>
                         let cont_52__ arg_53__ :=
                           let 'MkAmode addr addr_code := arg_53__ in
                           GHC.Base.return_ (Any Format.II64 (fun dst =>
                                                                OrdList.snocOL addr_code (PPC.Instr.LD Format.II32 dst
                                                                                addr))) in
                         getAmode D mem GHC.Base.>>= cont_52__
                     | _
                     , CmmExpr.CmmMachOp (CmmMachOp.MO_SS_Conv CmmType.W32 CmmType.W64) (cons
                      (CmmExpr.CmmLoad mem _) nil) =>
                         let cont_56__ arg_57__ :=
                           let 'MkAmode addr addr_code := arg_57__ in
                           GHC.Base.return_ (Any Format.II64 (fun dst =>
                                                                OrdList.snocOL addr_code (PPC.Instr.LA Format.II32 dst
                                                                                addr))) in
                         getAmode DS mem GHC.Base.>>= cont_56__
                     | dflags, CmmExpr.CmmMachOp mop (cons x (cons y nil)) =>
                         let triv_float
                          : CmmType.Width ->
                            (Format.Format -> Reg.Reg -> Reg.Reg -> Reg.Reg -> PPC.Instr.Instr) ->
                            NCGMonad.NatM Register :=
                           fun width instr => trivialCodeNoImm (Format.floatFormat width) instr x y in
                         match mop with
                         | CmmMachOp.MO_F_Eq _ => condFltReg PPC.Cond.EQQ x y
                         | CmmMachOp.MO_F_Ne _ => condFltReg PPC.Cond.NE x y
                         | CmmMachOp.MO_F_Gt _ => condFltReg PPC.Cond.GTT x y
                         | CmmMachOp.MO_F_Ge _ => condFltReg PPC.Cond.GE x y
                         | CmmMachOp.MO_F_Lt _ => condFltReg PPC.Cond.LTT x y
                         | CmmMachOp.MO_F_Le _ => condFltReg PPC.Cond.LE x y
                         | CmmMachOp.MO_Eq rep =>
                             condIntReg PPC.Cond.EQQ (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                         | CmmMachOp.MO_Ne rep =>
                             condIntReg PPC.Cond.NE (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                         | CmmMachOp.MO_S_Gt rep =>
                             condIntReg PPC.Cond.GTT (extendSExpr dflags rep x) (extendSExpr dflags rep y)
                         | CmmMachOp.MO_S_Ge rep =>
                             condIntReg PPC.Cond.GE (extendSExpr dflags rep x) (extendSExpr dflags rep y)
                         | CmmMachOp.MO_S_Lt rep =>
                             condIntReg PPC.Cond.LTT (extendSExpr dflags rep x) (extendSExpr dflags rep y)
                         | CmmMachOp.MO_S_Le rep =>
                             condIntReg PPC.Cond.LE (extendSExpr dflags rep x) (extendSExpr dflags rep y)
                         | CmmMachOp.MO_U_Gt rep =>
                             condIntReg PPC.Cond.GU (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                         | CmmMachOp.MO_U_Ge rep =>
                             condIntReg PPC.Cond.GEU (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                         | CmmMachOp.MO_U_Lt rep =>
                             condIntReg PPC.Cond.LU (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                         | CmmMachOp.MO_U_Le rep =>
                             condIntReg PPC.Cond.LEU (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                         | CmmMachOp.MO_F_Add w => triv_float w PPC.Instr.FADD
                         | CmmMachOp.MO_F_Sub w => triv_float w PPC.Instr.FSUB
                         | CmmMachOp.MO_F_Mul w => triv_float w PPC.Instr.FMUL
                         | CmmMachOp.MO_F_Quot w => triv_float w PPC.Instr.FDIV
                         | CmmMachOp.MO_Add CmmType.W32 =>
                             let j_87__ :=
                               match y with
                               | CmmExpr.Mk_CmmLit lit =>
                                   let cont_81__ arg_82__ :=
                                     let 'pair src srcCode := arg_82__ in
                                     let imm := PPC.Regs.litToImm lit in
                                     let code :=
                                       fun dst =>
                                         OrdList.appOL srcCode (OrdList.toOL (cons (PPC.Instr.ADDIS dst src (PPC.Regs.HA
                                                                                                             imm)) (cons
                                                                                    (PPC.Instr.ADD dst dst (PPC.Instr.RIImm
                                                                                                            (PPC.Regs.LO imm)))
                                                                                    nil))) in
                                     GHC.Base.return_ (Any Format.II32 code) in
                                   getSomeReg x GHC.Base.>>= cont_81__
                               | _ => trivialCode CmmType.W32 true PPC.Instr.ADD x y
                               end in
                             match y with
                             | CmmExpr.Mk_CmmLit (CmmExpr.CmmInt imm immrep) =>
                                 match PPC.Regs.makeImmediate CmmType.W32 true imm with
                                 | Some _ =>
                                     trivialCode CmmType.W32 true PPC.Instr.ADD x (CmmExpr.Mk_CmmLit (CmmExpr.CmmInt
                                                                                                      imm immrep))
                                 | _ => j_87__
                                 end
                             | _ => j_87__
                             end
                         | CmmMachOp.MO_Add rep => trivialCode rep true PPC.Instr.ADD x y
                         | CmmMachOp.MO_Sub rep =>
                             let j_97__ :=
                               let j_93__ := trivialCodeNoImm' (Format.intFormat rep) PPC.Instr.SUBF y x in
                               match x with
                               | CmmExpr.Mk_CmmLit (CmmExpr.CmmInt imm _) =>
                                   match PPC.Regs.makeImmediate rep true imm with
                                   | Some _ => trivialCode rep true PPC.Instr.SUBFC y x
                                   | _ => j_93__
                                   end
                               | _ => j_93__
                               end in
                             match y with
                             | CmmExpr.Mk_CmmLit (CmmExpr.CmmInt imm immrep) =>
                                 match PPC.Regs.makeImmediate rep true (GHC.Num.negate imm) with
                                 | Some _ =>
                                     trivialCode rep true PPC.Instr.ADD x (CmmExpr.Mk_CmmLit (CmmExpr.CmmInt
                                                                                              (GHC.Num.negate imm) immrep))
                                 | _ => j_97__
                                 end
                             | _ => j_97__
                             end
                         | CmmMachOp.MO_Mul rep => shiftMulCode rep true PPC.Instr.MULL x y
                         | CmmMachOp.MO_S_MulMayOflo rep =>
                             let cont_102__ arg_103__ :=
                               let 'pair src1 code1 := arg_103__ in
                               let cont_104__ arg_105__ :=
                                 let 'pair src2 code2 := arg_105__ in
                                 let format := Format.intFormat rep in
                                 let code :=
                                   fun dst =>
                                     OrdList.appOL (OrdList.appOL code1 code2) (OrdList.toOL (cons (PPC.Instr.MULLO
                                                                                                    format dst src1 src2) (cons
                                                                                                    (PPC.Instr.MFOV format dst)
                                                                                                    nil))) in
                                 GHC.Base.return_ (Any format code) in
                               getSomeReg y GHC.Base.>>= cont_104__ in
                             getSomeReg x GHC.Base.>>= cont_102__
                         | CmmMachOp.MO_S_Quot rep =>
                             trivialCodeNoImmSign (Format.intFormat rep) true PPC.Instr.DIV (extendSExpr
                                                                                             dflags rep x) (extendSExpr dflags
                                                                                                            rep y)
                         | CmmMachOp.MO_U_Quot rep =>
                             trivialCodeNoImmSign (Format.intFormat rep) false PPC.Instr.DIV (extendUExpr
                                                                                              dflags rep x) (extendUExpr dflags
                                                                                                             rep y)
                         | CmmMachOp.MO_S_Rem rep =>
                             remainderCode rep true (extendSExpr dflags rep x) (extendSExpr dflags rep y)
                         | CmmMachOp.MO_U_Rem rep =>
                             remainderCode rep false (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                         | CmmMachOp.MO_And rep =>
                             let j_114__ := trivialCode rep false PPC.Instr.AND x y in
                             match y with
                             | CmmExpr.Mk_CmmLit (CmmExpr.CmmInt imm _) =>
                                 if orb (imm GHC.Base.== GHC.Num.negate #8) (imm GHC.Base.==
                                         GHC.Num.negate #4) : bool
                                 then let cont_115__ arg_116__ :=
                                        let 'pair src srcCode := arg_116__ in
                                        let fmt := Format.intFormat rep in
                                        let clear_mask := if imm GHC.Base.== GHC.Num.negate #4 : bool then #2 else #3 in
                                        let code :=
                                          fun dst =>
                                            OrdList.appOL srcCode (OrdList.unitOL (PPC.Instr.CLRRI fmt dst src
                                                                                   clear_mask)) in
                                        GHC.Base.return_ (Any fmt code) in
                                      getSomeReg x GHC.Base.>>= cont_115__ else
                                 j_114__
                             | _ => j_114__
                             end
                         | CmmMachOp.MO_Or rep => trivialCode rep false PPC.Instr.OR x y
                         | CmmMachOp.MO_Xor rep => trivialCode rep false PPC.Instr.XOR x y
                         | CmmMachOp.MO_Shl rep => shiftMulCode rep false PPC.Instr.SL x y
                         | CmmMachOp.MO_S_Shr rep =>
                             shiftMulCode rep false PPC.Instr.SRA (extendSExpr dflags rep x) y
                         | CmmMachOp.MO_U_Shr rep =>
                             shiftMulCode rep false PPC.Instr.SR (extendUExpr dflags rep x) y
                         | _ => Panic.panic (GHC.Base.hs_string__ "PPC.CodeGen.getRegister: no match")
                         end
                     | _, CmmExpr.Mk_CmmLit (CmmExpr.CmmInt i rep) =>
                         match PPC.Regs.makeImmediate rep true i with
                         | Some imm =>
                             let code := fun dst => OrdList.unitOL (PPC.Instr.LI dst imm) in
                             GHC.Base.return_ (Any (Format.intFormat rep) code)
                         | _ => (match arg_0__, arg_1__ with
                                 | _, CmmExpr.Mk_CmmLit (CmmExpr.CmmFloat f frep) =>
                                     NCGMonad.getNewLabelNat GHC.Base.>>=
                                     (fun lbl =>
                                        DynFlags.getDynFlags GHC.Base.>>=
                                        (fun dflags =>
                                           PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                                           (fun dynRef =>
                                              let cont_6__ arg_7__ :=
                                                let 'MkAmode addr addr_code := arg_7__ in
                                                let format := Format.floatFormat frep in
                                                let code :=
                                                  fun dst =>
                                                    OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                                    (Cmm.Statics lbl (cons (Cmm.CmmStaticLit (CmmExpr.CmmFloat f frep))
                                                                                           nil))) (OrdList.snocOL addr_code (PPC.Instr.LD
                                                                                                                   format dst addr)) in
                                                GHC.Base.return_ (Any format code) in
                                              getAmode D dynRef GHC.Base.>>= cont_6__)))
                                 | dflags, CmmExpr.Mk_CmmLit lit =>
                                     if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool
                                     then let imm := PPC.Regs.litToImm lit in
                                          let code :=
                                            fun dst =>
                                              OrdList.toOL (cons (PPC.Instr.LIS dst (PPC.Regs.HA imm)) (cons (PPC.Instr.ADD
                                                                                                              dst dst (PPC.Instr.RIImm
                                                                                                                       (PPC.Regs.LO imm)))
                                                                                                             nil)) in
                                          let rep := CmmExpr.cmmLitType dflags lit in
                                          GHC.Base.return_ (Any (Format.cmmTypeFormat rep) code) else
                                     NCGMonad.getNewLabelNat GHC.Base.>>=
                                     (fun lbl =>
                                        DynFlags.getDynFlags GHC.Base.>>=
                                        (fun dflags =>
                                           PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                                           (fun dynRef =>
                                              let cont_14__ arg_15__ :=
                                                let 'MkAmode addr addr_code := arg_15__ in
                                                let rep := CmmExpr.cmmLitType dflags lit in
                                                let format := Format.cmmTypeFormat rep in
                                                let code :=
                                                  fun dst =>
                                                    OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                                    (Cmm.Statics lbl (cons (Cmm.CmmStaticLit lit) nil))) (OrdList.snocOL
                                                                    addr_code (PPC.Instr.LD format dst addr)) in
                                                GHC.Base.return_ (Any format code) in
                                              getAmode D dynRef GHC.Base.>>= cont_14__)))
                                 | _, other =>
                                             Panic.panicStr (GHC.Base.hs_string__ "getRegister(ppc)") (PprCmmExpr.pprExpr
                                                                                                       other)
                                 end)
                         end
                     | _, CmmExpr.Mk_CmmLit (CmmExpr.CmmFloat f frep) =>
                         NCGMonad.getNewLabelNat GHC.Base.>>=
                         (fun lbl =>
                            DynFlags.getDynFlags GHC.Base.>>=
                            (fun dflags =>
                               PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                               (fun dynRef =>
                                  let cont_6__ arg_7__ :=
                                    let 'MkAmode addr addr_code := arg_7__ in
                                    let format := Format.floatFormat frep in
                                    let code :=
                                      fun dst =>
                                        OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                        (Cmm.Statics lbl (cons (Cmm.CmmStaticLit (CmmExpr.CmmFloat f frep))
                                                                               nil))) (OrdList.snocOL addr_code (PPC.Instr.LD
                                                                                                       format dst addr)) in
                                    GHC.Base.return_ (Any format code) in
                                  getAmode D dynRef GHC.Base.>>= cont_6__)))
                     | dflags, CmmExpr.Mk_CmmLit lit =>
                         if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool
                         then let imm := PPC.Regs.litToImm lit in
                              let code :=
                                fun dst =>
                                  OrdList.toOL (cons (PPC.Instr.LIS dst (PPC.Regs.HA imm)) (cons (PPC.Instr.ADD
                                                                                                  dst dst (PPC.Instr.RIImm
                                                                                                           (PPC.Regs.LO imm)))
                                                                                                 nil)) in
                              let rep := CmmExpr.cmmLitType dflags lit in
                              GHC.Base.return_ (Any (Format.cmmTypeFormat rep) code) else
                         NCGMonad.getNewLabelNat GHC.Base.>>=
                         (fun lbl =>
                            DynFlags.getDynFlags GHC.Base.>>=
                            (fun dflags =>
                               PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                               (fun dynRef =>
                                  let cont_14__ arg_15__ :=
                                    let 'MkAmode addr addr_code := arg_15__ in
                                    let rep := CmmExpr.cmmLitType dflags lit in
                                    let format := Format.cmmTypeFormat rep in
                                    let code :=
                                      fun dst =>
                                        OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                        (Cmm.Statics lbl (cons (Cmm.CmmStaticLit lit) nil))) (OrdList.snocOL
                                                        addr_code (PPC.Instr.LD format dst addr)) in
                                    GHC.Base.return_ (Any format code) in
                                  getAmode D dynRef GHC.Base.>>= cont_14__)))
                     | _, other =>
                                 Panic.panicStr (GHC.Base.hs_string__ "getRegister(ppc)") (PprCmmExpr.pprExpr
                                                                                           other)

                     end ) else
               (match arg_0__, arg_1__ with
                 | dflags
                 , CmmExpr.CmmMachOp (CmmMachOp.MO_UU_Conv CmmType.W64 CmmType.W32) (cons x
                  nil) =>
                     if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool
                     then let cont_22__ arg_23__ :=
                            let 'MkChildCode64 code rlo := arg_23__ in
                            GHC.Base.return_ (Fixed Format.II32 rlo code) in
                          iselExpr64 x GHC.Base.>>= cont_22__ else
                     (match arg_0__, arg_1__ with
                      | _, CmmExpr.Mk_CmmLit (CmmExpr.CmmFloat f frep) =>
                           NCGMonad.getNewLabelNat GHC.Base.>>=
                           (fun lbl =>
                              DynFlags.getDynFlags GHC.Base.>>=
                              (fun dflags =>
                                 PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                                 (fun dynRef =>
                                    let cont_6__ arg_7__ :=
                                      let 'MkAmode addr addr_code := arg_7__ in
                                      let format := Format.floatFormat frep in
                                      let code :=
                                        fun dst =>
                                          OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                          (Cmm.Statics lbl (cons (Cmm.CmmStaticLit (CmmExpr.CmmFloat f frep))
                                                                                 nil))) (OrdList.snocOL addr_code (PPC.Instr.LD
                                                                                                         format dst addr)) in
                                      GHC.Base.return_ (Any format code) in
                                    getAmode D dynRef GHC.Base.>>= cont_6__)))
                      | dflags, CmmExpr.Mk_CmmLit lit =>
                           if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool
                           then let imm := PPC.Regs.litToImm lit in
                                let code :=
                                  fun dst =>
                                    OrdList.toOL (cons (PPC.Instr.LIS dst (PPC.Regs.HA imm)) (cons (PPC.Instr.ADD
                                                                                                    dst dst (PPC.Instr.RIImm
                                                                                                             (PPC.Regs.LO imm)))
                                                                                                   nil)) in
                                let rep := CmmExpr.cmmLitType dflags lit in
                                GHC.Base.return_ (Any (Format.cmmTypeFormat rep) code) else
                           NCGMonad.getNewLabelNat GHC.Base.>>=
                           (fun lbl =>
                              DynFlags.getDynFlags GHC.Base.>>=
                              (fun dflags =>
                                 PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                                 (fun dynRef =>
                                    let cont_14__ arg_15__ :=
                                      let 'MkAmode addr addr_code := arg_15__ in
                                      let rep := CmmExpr.cmmLitType dflags lit in
                                      let format := Format.cmmTypeFormat rep in
                                      let code :=
                                        fun dst =>
                                          OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                          (Cmm.Statics lbl (cons (Cmm.CmmStaticLit lit) nil))) (OrdList.snocOL
                                                          addr_code (PPC.Instr.LD format dst addr)) in
                                      GHC.Base.return_ (Any format code) in
                                    getAmode D dynRef GHC.Base.>>= cont_14__)))
                      | _, other =>
                                   Panic.panicStr (GHC.Base.hs_string__ "getRegister(ppc)") (PprCmmExpr.pprExpr
                                                                                             other)
                       end )
                 | dflags
                 , CmmExpr.CmmMachOp (CmmMachOp.MO_SS_Conv CmmType.W64 CmmType.W32) (cons x
                  nil) =>
                     if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool
                     then let cont_25__ arg_26__ :=
                            let 'MkChildCode64 code rlo := arg_26__ in
                            GHC.Base.return_ (Fixed Format.II32 rlo code) in
                          iselExpr64 x GHC.Base.>>= cont_25__ else
                     (match arg_0__, arg_1__ with
                      | _, CmmExpr.Mk_CmmLit (CmmExpr.CmmFloat f frep) =>
                           NCGMonad.getNewLabelNat GHC.Base.>>=
                           (fun lbl =>
                              DynFlags.getDynFlags GHC.Base.>>=
                              (fun dflags =>
                                 PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                                 (fun dynRef =>
                                    let cont_6__ arg_7__ :=
                                      let 'MkAmode addr addr_code := arg_7__ in
                                      let format := Format.floatFormat frep in
                                      let code :=
                                        fun dst =>
                                          OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                          (Cmm.Statics lbl (cons (Cmm.CmmStaticLit (CmmExpr.CmmFloat f frep))
                                                                                 nil))) (OrdList.snocOL addr_code (PPC.Instr.LD
                                                                                                         format dst addr)) in
                                      GHC.Base.return_ (Any format code) in
                                    getAmode D dynRef GHC.Base.>>= cont_6__)))
                      | dflags, CmmExpr.Mk_CmmLit lit =>
                           if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool
                           then let imm := PPC.Regs.litToImm lit in
                                let code :=
                                  fun dst =>
                                    OrdList.toOL (cons (PPC.Instr.LIS dst (PPC.Regs.HA imm)) (cons (PPC.Instr.ADD
                                                                                                    dst dst (PPC.Instr.RIImm
                                                                                                             (PPC.Regs.LO imm)))
                                                                                                   nil)) in
                                let rep := CmmExpr.cmmLitType dflags lit in
                                GHC.Base.return_ (Any (Format.cmmTypeFormat rep) code) else
                           NCGMonad.getNewLabelNat GHC.Base.>>=
                           (fun lbl =>
                              DynFlags.getDynFlags GHC.Base.>>=
                              (fun dflags =>
                                 PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                                 (fun dynRef =>
                                    let cont_14__ arg_15__ :=
                                      let 'MkAmode addr addr_code := arg_15__ in
                                      let rep := CmmExpr.cmmLitType dflags lit in
                                      let format := Format.cmmTypeFormat rep in
                                      let code :=
                                        fun dst =>
                                          OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                          (Cmm.Statics lbl (cons (Cmm.CmmStaticLit lit) nil))) (OrdList.snocOL
                                                          addr_code (PPC.Instr.LD format dst addr)) in
                                      GHC.Base.return_ (Any format code) in
                                    getAmode D dynRef GHC.Base.>>= cont_14__)))
                      | _, other =>
                                   Panic.panicStr (GHC.Base.hs_string__ "getRegister(ppc)") (PprCmmExpr.pprExpr
                                                                                             other)
                       end)
                 | _
                 , CmmExpr.CmmMachOp (CmmMachOp.MO_UU_Conv CmmType.W8 CmmType.W32) (cons
                  (CmmExpr.CmmLoad mem _) nil) =>
                     let cont_28__ arg_29__ :=
                       let 'MkAmode addr addr_code := arg_29__ in
                       GHC.Base.return_ (Any Format.II32 (fun dst =>
                                                            OrdList.snocOL addr_code (PPC.Instr.LD Format.II8 dst addr))) in
                     getAmode D mem GHC.Base.>>= cont_28__
                 | _
                 , CmmExpr.CmmMachOp (CmmMachOp.MO_UU_Conv CmmType.W8 CmmType.W64) (cons
                  (CmmExpr.CmmLoad mem _) nil) =>
                     let cont_32__ arg_33__ :=
                       let 'MkAmode addr addr_code := arg_33__ in
                       GHC.Base.return_ (Any Format.II64 (fun dst =>
                                                            OrdList.snocOL addr_code (PPC.Instr.LD Format.II8 dst addr))) in
                     getAmode D mem GHC.Base.>>= cont_32__
                 | _
                 , CmmExpr.CmmMachOp (CmmMachOp.MO_UU_Conv CmmType.W16 CmmType.W32) (cons
                  (CmmExpr.CmmLoad mem _) nil) =>
                     let cont_36__ arg_37__ :=
                       let 'MkAmode addr addr_code := arg_37__ in
                       GHC.Base.return_ (Any Format.II32 (fun dst =>
                                                            OrdList.snocOL addr_code (PPC.Instr.LD Format.II16 dst
                                                                            addr))) in
                     getAmode D mem GHC.Base.>>= cont_36__
                 | _
                 , CmmExpr.CmmMachOp (CmmMachOp.MO_SS_Conv CmmType.W16 CmmType.W32) (cons
                  (CmmExpr.CmmLoad mem _) nil) =>
                     let cont_40__ arg_41__ :=
                       let 'MkAmode addr addr_code := arg_41__ in
                       GHC.Base.return_ (Any Format.II32 (fun dst =>
                                                            OrdList.snocOL addr_code (PPC.Instr.LA Format.II16 dst
                                                                            addr))) in
                     getAmode D mem GHC.Base.>>= cont_40__
                 | _
                 , CmmExpr.CmmMachOp (CmmMachOp.MO_UU_Conv CmmType.W16 CmmType.W64) (cons
                  (CmmExpr.CmmLoad mem _) nil) =>
                     let cont_44__ arg_45__ :=
                       let 'MkAmode addr addr_code := arg_45__ in
                       GHC.Base.return_ (Any Format.II64 (fun dst =>
                                                            OrdList.snocOL addr_code (PPC.Instr.LD Format.II16 dst
                                                                            addr))) in
                     getAmode D mem GHC.Base.>>= cont_44__
                 | _
                 , CmmExpr.CmmMachOp (CmmMachOp.MO_SS_Conv CmmType.W16 CmmType.W64) (cons
                  (CmmExpr.CmmLoad mem _) nil) =>
                     let cont_48__ arg_49__ :=
                       let 'MkAmode addr addr_code := arg_49__ in
                       GHC.Base.return_ (Any Format.II64 (fun dst =>
                                                            OrdList.snocOL addr_code (PPC.Instr.LA Format.II16 dst
                                                                            addr))) in
                     getAmode D mem GHC.Base.>>= cont_48__
                 | _
                 , CmmExpr.CmmMachOp (CmmMachOp.MO_UU_Conv CmmType.W32 CmmType.W64) (cons
                  (CmmExpr.CmmLoad mem _) nil) =>
                     let cont_52__ arg_53__ :=
                       let 'MkAmode addr addr_code := arg_53__ in
                       GHC.Base.return_ (Any Format.II64 (fun dst =>
                                                            OrdList.snocOL addr_code (PPC.Instr.LD Format.II32 dst
                                                                            addr))) in
                     getAmode D mem GHC.Base.>>= cont_52__
                 | _
                 , CmmExpr.CmmMachOp (CmmMachOp.MO_SS_Conv CmmType.W32 CmmType.W64) (cons
                  (CmmExpr.CmmLoad mem _) nil) =>
                     let cont_56__ arg_57__ :=
                       let 'MkAmode addr addr_code := arg_57__ in
                       GHC.Base.return_ (Any Format.II64 (fun dst =>
                                                            OrdList.snocOL addr_code (PPC.Instr.LA Format.II32 dst
                                                                            addr))) in
                     getAmode DS mem GHC.Base.>>= cont_56__
                 | dflags, CmmExpr.CmmMachOp mop (cons x (cons y nil)) =>
                     let triv_float
                      : CmmType.Width ->
                        (Format.Format -> Reg.Reg -> Reg.Reg -> Reg.Reg -> PPC.Instr.Instr) ->
                        NCGMonad.NatM Register :=
                       fun width instr => trivialCodeNoImm (Format.floatFormat width) instr x y in
                     match mop with
                     | CmmMachOp.MO_F_Eq _ => condFltReg PPC.Cond.EQQ x y
                     | CmmMachOp.MO_F_Ne _ => condFltReg PPC.Cond.NE x y
                     | CmmMachOp.MO_F_Gt _ => condFltReg PPC.Cond.GTT x y
                     | CmmMachOp.MO_F_Ge _ => condFltReg PPC.Cond.GE x y
                     | CmmMachOp.MO_F_Lt _ => condFltReg PPC.Cond.LTT x y
                     | CmmMachOp.MO_F_Le _ => condFltReg PPC.Cond.LE x y
                     | CmmMachOp.MO_Eq rep =>
                         condIntReg PPC.Cond.EQQ (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                     | CmmMachOp.MO_Ne rep =>
                         condIntReg PPC.Cond.NE (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                     | CmmMachOp.MO_S_Gt rep =>
                         condIntReg PPC.Cond.GTT (extendSExpr dflags rep x) (extendSExpr dflags rep y)
                     | CmmMachOp.MO_S_Ge rep =>
                         condIntReg PPC.Cond.GE (extendSExpr dflags rep x) (extendSExpr dflags rep y)
                     | CmmMachOp.MO_S_Lt rep =>
                         condIntReg PPC.Cond.LTT (extendSExpr dflags rep x) (extendSExpr dflags rep y)
                     | CmmMachOp.MO_S_Le rep =>
                         condIntReg PPC.Cond.LE (extendSExpr dflags rep x) (extendSExpr dflags rep y)
                     | CmmMachOp.MO_U_Gt rep =>
                         condIntReg PPC.Cond.GU (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                     | CmmMachOp.MO_U_Ge rep =>
                         condIntReg PPC.Cond.GEU (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                     | CmmMachOp.MO_U_Lt rep =>
                         condIntReg PPC.Cond.LU (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                     | CmmMachOp.MO_U_Le rep =>
                         condIntReg PPC.Cond.LEU (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                     | CmmMachOp.MO_F_Add w => triv_float w PPC.Instr.FADD
                     | CmmMachOp.MO_F_Sub w => triv_float w PPC.Instr.FSUB
                     | CmmMachOp.MO_F_Mul w => triv_float w PPC.Instr.FMUL
                     | CmmMachOp.MO_F_Quot w => triv_float w PPC.Instr.FDIV
                     | CmmMachOp.MO_Add CmmType.W32 =>
                         let j_87__ :=
                           match y with
                           | CmmExpr.Mk_CmmLit lit =>
                               let cont_81__ arg_82__ :=
                                 let 'pair src srcCode := arg_82__ in
                                 let imm := PPC.Regs.litToImm lit in
                                 let code :=
                                   fun dst =>
                                     OrdList.appOL srcCode (OrdList.toOL (cons (PPC.Instr.ADDIS dst src (PPC.Regs.HA
                                                                                                         imm)) (cons
                                                                                (PPC.Instr.ADD dst dst (PPC.Instr.RIImm
                                                                                                        (PPC.Regs.LO imm)))
                                                                                nil))) in
                                 GHC.Base.return_ (Any Format.II32 code) in
                               getSomeReg x GHC.Base.>>= cont_81__
                           | _ => trivialCode CmmType.W32 true PPC.Instr.ADD x y
                           end in
                         match y with
                         | CmmExpr.Mk_CmmLit (CmmExpr.CmmInt imm immrep) =>
                             match PPC.Regs.makeImmediate CmmType.W32 true imm with
                             | Some _ =>
                                 trivialCode CmmType.W32 true PPC.Instr.ADD x (CmmExpr.Mk_CmmLit (CmmExpr.CmmInt
                                                                                                  imm immrep))
                             | _ => j_87__
                             end
                         | _ => j_87__
                         end
                     | CmmMachOp.MO_Add rep => trivialCode rep true PPC.Instr.ADD x y
                     | CmmMachOp.MO_Sub rep =>
                         let j_97__ :=
                           let j_93__ := trivialCodeNoImm' (Format.intFormat rep) PPC.Instr.SUBF y x in
                           match x with
                           | CmmExpr.Mk_CmmLit (CmmExpr.CmmInt imm _) =>
                               match PPC.Regs.makeImmediate rep true imm with
                               | Some _ => trivialCode rep true PPC.Instr.SUBFC y x
                               | _ => j_93__
                               end
                           | _ => j_93__
                           end in
                         match y with
                         | CmmExpr.Mk_CmmLit (CmmExpr.CmmInt imm immrep) =>
                             match PPC.Regs.makeImmediate rep true (GHC.Num.negate imm) with
                             | Some _ =>
                                 trivialCode rep true PPC.Instr.ADD x (CmmExpr.Mk_CmmLit (CmmExpr.CmmInt
                                                                                          (GHC.Num.negate imm) immrep))
                             | _ => j_97__
                             end
                         | _ => j_97__
                         end
                     | CmmMachOp.MO_Mul rep => shiftMulCode rep true PPC.Instr.MULL x y
                     | CmmMachOp.MO_S_MulMayOflo rep =>
                         let cont_102__ arg_103__ :=
                           let 'pair src1 code1 := arg_103__ in
                           let cont_104__ arg_105__ :=
                             let 'pair src2 code2 := arg_105__ in
                             let format := Format.intFormat rep in
                             let code :=
                               fun dst =>
                                 OrdList.appOL (OrdList.appOL code1 code2) (OrdList.toOL (cons (PPC.Instr.MULLO
                                                                                                format dst src1 src2) (cons
                                                                                                (PPC.Instr.MFOV format dst)
                                                                                                nil))) in
                             GHC.Base.return_ (Any format code) in
                           getSomeReg y GHC.Base.>>= cont_104__ in
                         getSomeReg x GHC.Base.>>= cont_102__
                     | CmmMachOp.MO_S_Quot rep =>
                         trivialCodeNoImmSign (Format.intFormat rep) true PPC.Instr.DIV (extendSExpr
                                                                                         dflags rep x) (extendSExpr dflags
                                                                                                        rep y)
                     | CmmMachOp.MO_U_Quot rep =>
                         trivialCodeNoImmSign (Format.intFormat rep) false PPC.Instr.DIV (extendUExpr
                                                                                          dflags rep x) (extendUExpr dflags
                                                                                                         rep y)
                     | CmmMachOp.MO_S_Rem rep =>
                         remainderCode rep true (extendSExpr dflags rep x) (extendSExpr dflags rep y)
                     | CmmMachOp.MO_U_Rem rep =>
                         remainderCode rep false (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                     | CmmMachOp.MO_And rep =>
                         let j_114__ := trivialCode rep false PPC.Instr.AND x y in
                         match y with
                         | CmmExpr.Mk_CmmLit (CmmExpr.CmmInt imm _) =>
                             if orb (imm GHC.Base.== GHC.Num.negate #8) (imm GHC.Base.==
                                     GHC.Num.negate #4) : bool
                             then let cont_115__ arg_116__ :=
                                    let 'pair src srcCode := arg_116__ in
                                    let fmt := Format.intFormat rep in
                                    let clear_mask := if imm GHC.Base.== GHC.Num.negate #4 : bool then #2 else #3 in
                                    let code :=
                                      fun dst =>
                                        OrdList.appOL srcCode (OrdList.unitOL (PPC.Instr.CLRRI fmt dst src
                                                                               clear_mask)) in
                                    GHC.Base.return_ (Any fmt code) in
                                  getSomeReg x GHC.Base.>>= cont_115__ else
                             j_114__
                         | _ => j_114__
                         end
                     | CmmMachOp.MO_Or rep => trivialCode rep false PPC.Instr.OR x y
                     | CmmMachOp.MO_Xor rep => trivialCode rep false PPC.Instr.XOR x y
                     | CmmMachOp.MO_Shl rep => shiftMulCode rep false PPC.Instr.SL x y
                     | CmmMachOp.MO_S_Shr rep =>
                         shiftMulCode rep false PPC.Instr.SRA (extendSExpr dflags rep x) y
                     | CmmMachOp.MO_U_Shr rep =>
                         shiftMulCode rep false PPC.Instr.SR (extendUExpr dflags rep x) y
                     | _ => Panic.panic (GHC.Base.hs_string__ "PPC.CodeGen.getRegister: no match")
                     end
                 | _, CmmExpr.Mk_CmmLit (CmmExpr.CmmInt i rep) =>
                     match PPC.Regs.makeImmediate rep true i with
                     | Some imm =>
                         let code := fun dst => OrdList.unitOL (PPC.Instr.LI dst imm) in
                         GHC.Base.return_ (Any (Format.intFormat rep) code)
                     | _ => (match arg_0__, arg_1__ with
                             | _, CmmExpr.Mk_CmmLit (CmmExpr.CmmFloat f frep) =>
                                 NCGMonad.getNewLabelNat GHC.Base.>>=
                                 (fun lbl =>
                                    DynFlags.getDynFlags GHC.Base.>>=
                                    (fun dflags =>
                                       PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                                       (fun dynRef =>
                                          let cont_6__ arg_7__ :=
                                            let 'MkAmode addr addr_code := arg_7__ in
                                            let format := Format.floatFormat frep in
                                            let code :=
                                              fun dst =>
                                                OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                                (Cmm.Statics lbl (cons (Cmm.CmmStaticLit (CmmExpr.CmmFloat f frep))
                                                                                       nil))) (OrdList.snocOL addr_code (PPC.Instr.LD
                                                                                                               format dst addr)) in
                                            GHC.Base.return_ (Any format code) in
                                          getAmode D dynRef GHC.Base.>>= cont_6__)))
                             | dflags, CmmExpr.Mk_CmmLit lit =>
                                 if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool
                                 then let imm := PPC.Regs.litToImm lit in
                                      let code :=
                                        fun dst =>
                                          OrdList.toOL (cons (PPC.Instr.LIS dst (PPC.Regs.HA imm)) (cons (PPC.Instr.ADD
                                                                                                          dst dst (PPC.Instr.RIImm
                                                                                                                   (PPC.Regs.LO imm)))
                                                                                                         nil)) in
                                      let rep := CmmExpr.cmmLitType dflags lit in
                                      GHC.Base.return_ (Any (Format.cmmTypeFormat rep) code) else
                                 NCGMonad.getNewLabelNat GHC.Base.>>=
                                 (fun lbl =>
                                    DynFlags.getDynFlags GHC.Base.>>=
                                    (fun dflags =>
                                       PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                                       (fun dynRef =>
                                          let cont_14__ arg_15__ :=
                                            let 'MkAmode addr addr_code := arg_15__ in
                                            let rep := CmmExpr.cmmLitType dflags lit in
                                            let format := Format.cmmTypeFormat rep in
                                            let code :=
                                              fun dst =>
                                                OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                                (Cmm.Statics lbl (cons (Cmm.CmmStaticLit lit) nil))) (OrdList.snocOL
                                                                addr_code (PPC.Instr.LD format dst addr)) in
                                            GHC.Base.return_ (Any format code) in
                                          getAmode D dynRef GHC.Base.>>= cont_14__)))
                             | _, other =>
                                         Panic.panicStr (GHC.Base.hs_string__ "getRegister(ppc)") (PprCmmExpr.pprExpr
                                                                                                   other)
                             end)
                     end
                 | _, CmmExpr.Mk_CmmLit (CmmExpr.CmmFloat f frep) =>
                     NCGMonad.getNewLabelNat GHC.Base.>>=
                     (fun lbl =>
                        DynFlags.getDynFlags GHC.Base.>>=
                        (fun dflags =>
                           PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                           (fun dynRef =>
                              let cont_6__ arg_7__ :=
                                let 'MkAmode addr addr_code := arg_7__ in
                                let format := Format.floatFormat frep in
                                let code :=
                                  fun dst =>
                                    OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                    (Cmm.Statics lbl (cons (Cmm.CmmStaticLit (CmmExpr.CmmFloat f frep))
                                                                           nil))) (OrdList.snocOL addr_code (PPC.Instr.LD
                                                                                                   format dst addr)) in
                                GHC.Base.return_ (Any format code) in
                              getAmode D dynRef GHC.Base.>>= cont_6__)))
                 | dflags, CmmExpr.Mk_CmmLit lit =>
                     if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool
                     then let imm := PPC.Regs.litToImm lit in
                          let code :=
                            fun dst =>
                              OrdList.toOL (cons (PPC.Instr.LIS dst (PPC.Regs.HA imm)) (cons (PPC.Instr.ADD
                                                                                              dst dst (PPC.Instr.RIImm
                                                                                                       (PPC.Regs.LO imm)))
                                                                                             nil)) in
                          let rep := CmmExpr.cmmLitType dflags lit in
                          GHC.Base.return_ (Any (Format.cmmTypeFormat rep) code) else
                     NCGMonad.getNewLabelNat GHC.Base.>>=
                     (fun lbl =>
                        DynFlags.getDynFlags GHC.Base.>>=
                        (fun dflags =>
                           PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                           (fun dynRef =>
                              let cont_14__ arg_15__ :=
                                let 'MkAmode addr addr_code := arg_15__ in
                                let rep := CmmExpr.cmmLitType dflags lit in
                                let format := Format.cmmTypeFormat rep in
                                let code :=
                                  fun dst =>
                                    OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                    (Cmm.Statics lbl (cons (Cmm.CmmStaticLit lit) nil))) (OrdList.snocOL
                                                    addr_code (PPC.Instr.LD format dst addr)) in
                                GHC.Base.return_ (Any format code) in
                              getAmode D dynRef GHC.Base.>>= cont_14__)))
                 | _, other =>
                             Panic.panicStr (GHC.Base.hs_string__ "getRegister(ppc)") (PprCmmExpr.pprExpr
                                                                                       other)
                 end )
          | dflags
             , CmmExpr.CmmMachOp (CmmMachOp.MO_UU_Conv CmmType.W64 CmmType.W32) (cons x
              nil) =>
                 if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool
                 then let cont_22__ arg_23__ :=
                        let 'MkChildCode64 code rlo := arg_23__ in
                        GHC.Base.return_ (Fixed Format.II32 rlo code) in
                      iselExpr64 x GHC.Base.>>= cont_22__ else
                 (match arg_0__, arg_1__ with
                  | _, CmmExpr.Mk_CmmLit (CmmExpr.CmmFloat f frep) =>
                       NCGMonad.getNewLabelNat GHC.Base.>>=
                       (fun lbl =>
                          DynFlags.getDynFlags GHC.Base.>>=
                          (fun dflags =>
                             PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                             (fun dynRef =>
                                let cont_6__ arg_7__ :=
                                  let 'MkAmode addr addr_code := arg_7__ in
                                  let format := Format.floatFormat frep in
                                  let code :=
                                    fun dst =>
                                      OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                      (Cmm.Statics lbl (cons (Cmm.CmmStaticLit (CmmExpr.CmmFloat f frep))
                                                                             nil))) (OrdList.snocOL addr_code (PPC.Instr.LD
                                                                                                     format dst addr)) in
                                  GHC.Base.return_ (Any format code) in
                                getAmode D dynRef GHC.Base.>>= cont_6__)))
                  | dflags, CmmExpr.Mk_CmmLit lit =>
                       if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool
                       then let imm := PPC.Regs.litToImm lit in
                            let code :=
                              fun dst =>
                                OrdList.toOL (cons (PPC.Instr.LIS dst (PPC.Regs.HA imm)) (cons (PPC.Instr.ADD
                                                                                                dst dst (PPC.Instr.RIImm
                                                                                                         (PPC.Regs.LO imm)))
                                                                                               nil)) in
                            let rep := CmmExpr.cmmLitType dflags lit in
                            GHC.Base.return_ (Any (Format.cmmTypeFormat rep) code) else
                       NCGMonad.getNewLabelNat GHC.Base.>>=
                       (fun lbl =>
                          DynFlags.getDynFlags GHC.Base.>>=
                          (fun dflags =>
                             PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                             (fun dynRef =>
                                let cont_14__ arg_15__ :=
                                  let 'MkAmode addr addr_code := arg_15__ in
                                  let rep := CmmExpr.cmmLitType dflags lit in
                                  let format := Format.cmmTypeFormat rep in
                                  let code :=
                                    fun dst =>
                                      OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                      (Cmm.Statics lbl (cons (Cmm.CmmStaticLit lit) nil))) (OrdList.snocOL
                                                      addr_code (PPC.Instr.LD format dst addr)) in
                                  GHC.Base.return_ (Any format code) in
                                getAmode D dynRef GHC.Base.>>= cont_14__)))
                  | _, other =>
                               Panic.panicStr (GHC.Base.hs_string__ "getRegister(ppc)") (PprCmmExpr.pprExpr
                                                                                         other)
                   end )
          | dflags
             , CmmExpr.CmmMachOp (CmmMachOp.MO_SS_Conv CmmType.W64 CmmType.W32) (cons x
              nil) =>
                 if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool
                 then let cont_25__ arg_26__ :=
                        let 'MkChildCode64 code rlo := arg_26__ in
                        GHC.Base.return_ (Fixed Format.II32 rlo code) in
                      iselExpr64 x GHC.Base.>>= cont_25__ else
                 (match arg_0__, arg_1__ with
                  | _, CmmExpr.Mk_CmmLit (CmmExpr.CmmFloat f frep) =>
                       NCGMonad.getNewLabelNat GHC.Base.>>=
                       (fun lbl =>
                          DynFlags.getDynFlags GHC.Base.>>=
                          (fun dflags =>
                             PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                             (fun dynRef =>
                                let cont_6__ arg_7__ :=
                                  let 'MkAmode addr addr_code := arg_7__ in
                                  let format := Format.floatFormat frep in
                                  let code :=
                                    fun dst =>
                                      OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                      (Cmm.Statics lbl (cons (Cmm.CmmStaticLit (CmmExpr.CmmFloat f frep))
                                                                             nil))) (OrdList.snocOL addr_code (PPC.Instr.LD
                                                                                                     format dst addr)) in
                                  GHC.Base.return_ (Any format code) in
                                getAmode D dynRef GHC.Base.>>= cont_6__)))
                  | dflags, CmmExpr.Mk_CmmLit lit =>
                       if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool
                       then let imm := PPC.Regs.litToImm lit in
                            let code :=
                              fun dst =>
                                OrdList.toOL (cons (PPC.Instr.LIS dst (PPC.Regs.HA imm)) (cons (PPC.Instr.ADD
                                                                                                dst dst (PPC.Instr.RIImm
                                                                                                         (PPC.Regs.LO imm)))
                                                                                               nil)) in
                            let rep := CmmExpr.cmmLitType dflags lit in
                            GHC.Base.return_ (Any (Format.cmmTypeFormat rep) code) else
                       NCGMonad.getNewLabelNat GHC.Base.>>=
                       (fun lbl =>
                          DynFlags.getDynFlags GHC.Base.>>=
                          (fun dflags =>
                             PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                             (fun dynRef =>
                                let cont_14__ arg_15__ :=
                                  let 'MkAmode addr addr_code := arg_15__ in
                                  let rep := CmmExpr.cmmLitType dflags lit in
                                  let format := Format.cmmTypeFormat rep in
                                  let code :=
                                    fun dst =>
                                      OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                      (Cmm.Statics lbl (cons (Cmm.CmmStaticLit lit) nil))) (OrdList.snocOL
                                                      addr_code (PPC.Instr.LD format dst addr)) in
                                  GHC.Base.return_ (Any format code) in
                                getAmode D dynRef GHC.Base.>>= cont_14__)))
                  | _, other =>
                               Panic.panicStr (GHC.Base.hs_string__ "getRegister(ppc)") (PprCmmExpr.pprExpr
                                                                                         other)
                   end)
          | _
             , CmmExpr.CmmMachOp (CmmMachOp.MO_UU_Conv CmmType.W8 CmmType.W32) (cons
              (CmmExpr.CmmLoad mem _) nil) =>
                 let cont_28__ arg_29__ :=
                   let 'MkAmode addr addr_code := arg_29__ in
                   GHC.Base.return_ (Any Format.II32 (fun dst =>
                                                        OrdList.snocOL addr_code (PPC.Instr.LD Format.II8 dst addr))) in
                 getAmode D mem GHC.Base.>>= cont_28__
          | _
             , CmmExpr.CmmMachOp (CmmMachOp.MO_UU_Conv CmmType.W8 CmmType.W64) (cons
              (CmmExpr.CmmLoad mem _) nil) =>
                 let cont_32__ arg_33__ :=
                   let 'MkAmode addr addr_code := arg_33__ in
                   GHC.Base.return_ (Any Format.II64 (fun dst =>
                                                        OrdList.snocOL addr_code (PPC.Instr.LD Format.II8 dst addr))) in
                 getAmode D mem GHC.Base.>>= cont_32__
          | _
             , CmmExpr.CmmMachOp (CmmMachOp.MO_UU_Conv CmmType.W16 CmmType.W32) (cons
              (CmmExpr.CmmLoad mem _) nil) =>
                 let cont_36__ arg_37__ :=
                   let 'MkAmode addr addr_code := arg_37__ in
                   GHC.Base.return_ (Any Format.II32 (fun dst =>
                                                        OrdList.snocOL addr_code (PPC.Instr.LD Format.II16 dst
                                                                        addr))) in
                 getAmode D mem GHC.Base.>>= cont_36__
          | _
             , CmmExpr.CmmMachOp (CmmMachOp.MO_SS_Conv CmmType.W16 CmmType.W32) (cons
              (CmmExpr.CmmLoad mem _) nil) =>
                 let cont_40__ arg_41__ :=
                   let 'MkAmode addr addr_code := arg_41__ in
                   GHC.Base.return_ (Any Format.II32 (fun dst =>
                                                        OrdList.snocOL addr_code (PPC.Instr.LA Format.II16 dst
                                                                        addr))) in
                 getAmode D mem GHC.Base.>>= cont_40__
          | _
             , CmmExpr.CmmMachOp (CmmMachOp.MO_UU_Conv CmmType.W16 CmmType.W64) (cons
              (CmmExpr.CmmLoad mem _) nil) =>
                 let cont_44__ arg_45__ :=
                   let 'MkAmode addr addr_code := arg_45__ in
                   GHC.Base.return_ (Any Format.II64 (fun dst =>
                                                        OrdList.snocOL addr_code (PPC.Instr.LD Format.II16 dst
                                                                        addr))) in
                 getAmode D mem GHC.Base.>>= cont_44__
          | _
             , CmmExpr.CmmMachOp (CmmMachOp.MO_SS_Conv CmmType.W16 CmmType.W64) (cons
              (CmmExpr.CmmLoad mem _) nil) =>
                 let cont_48__ arg_49__ :=
                   let 'MkAmode addr addr_code := arg_49__ in
                   GHC.Base.return_ (Any Format.II64 (fun dst =>
                                                        OrdList.snocOL addr_code (PPC.Instr.LA Format.II16 dst
                                                                        addr))) in
                 getAmode D mem GHC.Base.>>= cont_48__
          | _
             , CmmExpr.CmmMachOp (CmmMachOp.MO_UU_Conv CmmType.W32 CmmType.W64) (cons
              (CmmExpr.CmmLoad mem _) nil) =>
                 let cont_52__ arg_53__ :=
                   let 'MkAmode addr addr_code := arg_53__ in
                   GHC.Base.return_ (Any Format.II64 (fun dst =>
                                                        OrdList.snocOL addr_code (PPC.Instr.LD Format.II32 dst
                                                                        addr))) in
                 getAmode D mem GHC.Base.>>= cont_52__
          | _
             , CmmExpr.CmmMachOp (CmmMachOp.MO_SS_Conv CmmType.W32 CmmType.W64) (cons
              (CmmExpr.CmmLoad mem _) nil) =>
                 let cont_56__ arg_57__ :=
                   let 'MkAmode addr addr_code := arg_57__ in
                   GHC.Base.return_ (Any Format.II64 (fun dst =>
                                                        OrdList.snocOL addr_code (PPC.Instr.LA Format.II32 dst
                                                                        addr))) in
                 getAmode DS mem GHC.Base.>>= cont_56__
          | dflags, CmmExpr.CmmMachOp mop (cons x (cons y nil)) =>
                 let triv_float
                  : CmmType.Width ->
                    (Format.Format -> Reg.Reg -> Reg.Reg -> Reg.Reg -> PPC.Instr.Instr) ->
                    NCGMonad.NatM Register :=
                   fun width instr => trivialCodeNoImm (Format.floatFormat width) instr x y in
                 match mop with
                 | CmmMachOp.MO_F_Eq _ => condFltReg PPC.Cond.EQQ x y
                 | CmmMachOp.MO_F_Ne _ => condFltReg PPC.Cond.NE x y
                 | CmmMachOp.MO_F_Gt _ => condFltReg PPC.Cond.GTT x y
                 | CmmMachOp.MO_F_Ge _ => condFltReg PPC.Cond.GE x y
                 | CmmMachOp.MO_F_Lt _ => condFltReg PPC.Cond.LTT x y
                 | CmmMachOp.MO_F_Le _ => condFltReg PPC.Cond.LE x y
                 | CmmMachOp.MO_Eq rep =>
                     condIntReg PPC.Cond.EQQ (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                 | CmmMachOp.MO_Ne rep =>
                     condIntReg PPC.Cond.NE (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                 | CmmMachOp.MO_S_Gt rep =>
                     condIntReg PPC.Cond.GTT (extendSExpr dflags rep x) (extendSExpr dflags rep y)
                 | CmmMachOp.MO_S_Ge rep =>
                     condIntReg PPC.Cond.GE (extendSExpr dflags rep x) (extendSExpr dflags rep y)
                 | CmmMachOp.MO_S_Lt rep =>
                     condIntReg PPC.Cond.LTT (extendSExpr dflags rep x) (extendSExpr dflags rep y)
                 | CmmMachOp.MO_S_Le rep =>
                     condIntReg PPC.Cond.LE (extendSExpr dflags rep x) (extendSExpr dflags rep y)
                 | CmmMachOp.MO_U_Gt rep =>
                     condIntReg PPC.Cond.GU (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                 | CmmMachOp.MO_U_Ge rep =>
                     condIntReg PPC.Cond.GEU (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                 | CmmMachOp.MO_U_Lt rep =>
                     condIntReg PPC.Cond.LU (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                 | CmmMachOp.MO_U_Le rep =>
                     condIntReg PPC.Cond.LEU (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                 | CmmMachOp.MO_F_Add w => triv_float w PPC.Instr.FADD
                 | CmmMachOp.MO_F_Sub w => triv_float w PPC.Instr.FSUB
                 | CmmMachOp.MO_F_Mul w => triv_float w PPC.Instr.FMUL
                 | CmmMachOp.MO_F_Quot w => triv_float w PPC.Instr.FDIV
                 | CmmMachOp.MO_Add CmmType.W32 =>
                     let j_87__ :=
                       match y with
                       | CmmExpr.Mk_CmmLit lit =>
                           let cont_81__ arg_82__ :=
                             let 'pair src srcCode := arg_82__ in
                             let imm := PPC.Regs.litToImm lit in
                             let code :=
                               fun dst =>
                                 OrdList.appOL srcCode (OrdList.toOL (cons (PPC.Instr.ADDIS dst src (PPC.Regs.HA
                                                                                                     imm)) (cons
                                                                            (PPC.Instr.ADD dst dst (PPC.Instr.RIImm
                                                                                                    (PPC.Regs.LO imm)))
                                                                            nil))) in
                             GHC.Base.return_ (Any Format.II32 code) in
                           getSomeReg x GHC.Base.>>= cont_81__
                       | _ => trivialCode CmmType.W32 true PPC.Instr.ADD x y
                       end in
                     match y with
                     | CmmExpr.Mk_CmmLit (CmmExpr.CmmInt imm immrep) =>
                         match PPC.Regs.makeImmediate CmmType.W32 true imm with
                         | Some _ =>
                             trivialCode CmmType.W32 true PPC.Instr.ADD x (CmmExpr.Mk_CmmLit (CmmExpr.CmmInt
                                                                                              imm immrep))
                         | _ => j_87__
                         end
                     | _ => j_87__
                     end
                 | CmmMachOp.MO_Add rep => trivialCode rep true PPC.Instr.ADD x y
                 | CmmMachOp.MO_Sub rep =>
                     let j_97__ :=
                       let j_93__ := trivialCodeNoImm' (Format.intFormat rep) PPC.Instr.SUBF y x in
                       match x with
                       | CmmExpr.Mk_CmmLit (CmmExpr.CmmInt imm _) =>
                           match PPC.Regs.makeImmediate rep true imm with
                           | Some _ => trivialCode rep true PPC.Instr.SUBFC y x
                           | _ => j_93__
                           end
                       | _ => j_93__
                       end in
                     match y with
                     | CmmExpr.Mk_CmmLit (CmmExpr.CmmInt imm immrep) =>
                         match PPC.Regs.makeImmediate rep true (GHC.Num.negate imm) with
                         | Some _ =>
                             trivialCode rep true PPC.Instr.ADD x (CmmExpr.Mk_CmmLit (CmmExpr.CmmInt
                                                                                      (GHC.Num.negate imm) immrep))
                         | _ => j_97__
                         end
                     | _ => j_97__
                     end
                 | CmmMachOp.MO_Mul rep => shiftMulCode rep true PPC.Instr.MULL x y
                 | CmmMachOp.MO_S_MulMayOflo rep =>
                     let cont_102__ arg_103__ :=
                       let 'pair src1 code1 := arg_103__ in
                       let cont_104__ arg_105__ :=
                         let 'pair src2 code2 := arg_105__ in
                         let format := Format.intFormat rep in
                         let code :=
                           fun dst =>
                             OrdList.appOL (OrdList.appOL code1 code2) (OrdList.toOL (cons (PPC.Instr.MULLO
                                                                                            format dst src1 src2) (cons
                                                                                            (PPC.Instr.MFOV format dst)
                                                                                            nil))) in
                         GHC.Base.return_ (Any format code) in
                       getSomeReg y GHC.Base.>>= cont_104__ in
                     getSomeReg x GHC.Base.>>= cont_102__
                 | CmmMachOp.MO_S_Quot rep =>
                     trivialCodeNoImmSign (Format.intFormat rep) true PPC.Instr.DIV (extendSExpr
                                                                                     dflags rep x) (extendSExpr dflags
                                                                                                    rep y)
                 | CmmMachOp.MO_U_Quot rep =>
                     trivialCodeNoImmSign (Format.intFormat rep) false PPC.Instr.DIV (extendUExpr
                                                                                      dflags rep x) (extendUExpr dflags
                                                                                                     rep y)
                 | CmmMachOp.MO_S_Rem rep =>
                     remainderCode rep true (extendSExpr dflags rep x) (extendSExpr dflags rep y)
                 | CmmMachOp.MO_U_Rem rep =>
                     remainderCode rep false (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                 | CmmMachOp.MO_And rep =>
                     let j_114__ := trivialCode rep false PPC.Instr.AND x y in
                     match y with
                     | CmmExpr.Mk_CmmLit (CmmExpr.CmmInt imm _) =>
                         if orb (imm GHC.Base.== GHC.Num.negate #8) (imm GHC.Base.==
                                 GHC.Num.negate #4) : bool
                         then let cont_115__ arg_116__ :=
                                let 'pair src srcCode := arg_116__ in
                                let fmt := Format.intFormat rep in
                                let clear_mask := if imm GHC.Base.== GHC.Num.negate #4 : bool then #2 else #3 in
                                let code :=
                                  fun dst =>
                                    OrdList.appOL srcCode (OrdList.unitOL (PPC.Instr.CLRRI fmt dst src
                                                                           clear_mask)) in
                                GHC.Base.return_ (Any fmt code) in
                              getSomeReg x GHC.Base.>>= cont_115__ else
                         j_114__
                     | _ => j_114__
                     end
                 | CmmMachOp.MO_Or rep => trivialCode rep false PPC.Instr.OR x y
                 | CmmMachOp.MO_Xor rep => trivialCode rep false PPC.Instr.XOR x y
                 | CmmMachOp.MO_Shl rep => shiftMulCode rep false PPC.Instr.SL x y
                 | CmmMachOp.MO_S_Shr rep =>
                     shiftMulCode rep false PPC.Instr.SRA (extendSExpr dflags rep x) y
                 | CmmMachOp.MO_U_Shr rep =>
                     shiftMulCode rep false PPC.Instr.SR (extendUExpr dflags rep x) y
                 | _ => Panic.panic (GHC.Base.hs_string__ "PPC.CodeGen.getRegister: no match")
                 end
          | _, CmmExpr.Mk_CmmLit (CmmExpr.CmmInt i rep) =>
                 match PPC.Regs.makeImmediate rep true i with
                 | Some imm =>
                     let code := fun dst => OrdList.unitOL (PPC.Instr.LI dst imm) in
                     GHC.Base.return_ (Any (Format.intFormat rep) code)
                 | _ => (match arg_0__, arg_1__ with
                         | _, CmmExpr.Mk_CmmLit (CmmExpr.CmmFloat f frep) =>
                             NCGMonad.getNewLabelNat GHC.Base.>>=
                             (fun lbl =>
                                DynFlags.getDynFlags GHC.Base.>>=
                                (fun dflags =>
                                   PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                                   (fun dynRef =>
                                      let cont_6__ arg_7__ :=
                                        let 'MkAmode addr addr_code := arg_7__ in
                                        let format := Format.floatFormat frep in
                                        let code :=
                                          fun dst =>
                                            OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                            (Cmm.Statics lbl (cons (Cmm.CmmStaticLit (CmmExpr.CmmFloat f frep))
                                                                                   nil))) (OrdList.snocOL addr_code (PPC.Instr.LD
                                                                                                           format dst addr)) in
                                        GHC.Base.return_ (Any format code) in
                                      getAmode D dynRef GHC.Base.>>= cont_6__)))
                         | dflags, CmmExpr.Mk_CmmLit lit =>
                             if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool
                             then let imm := PPC.Regs.litToImm lit in
                                  let code :=
                                    fun dst =>
                                      OrdList.toOL (cons (PPC.Instr.LIS dst (PPC.Regs.HA imm)) (cons (PPC.Instr.ADD
                                                                                                      dst dst (PPC.Instr.RIImm
                                                                                                               (PPC.Regs.LO imm)))
                                                                                                     nil)) in
                                  let rep := CmmExpr.cmmLitType dflags lit in
                                  GHC.Base.return_ (Any (Format.cmmTypeFormat rep) code) else
                             NCGMonad.getNewLabelNat GHC.Base.>>=
                             (fun lbl =>
                                DynFlags.getDynFlags GHC.Base.>>=
                                (fun dflags =>
                                   PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                                   (fun dynRef =>
                                      let cont_14__ arg_15__ :=
                                        let 'MkAmode addr addr_code := arg_15__ in
                                        let rep := CmmExpr.cmmLitType dflags lit in
                                        let format := Format.cmmTypeFormat rep in
                                        let code :=
                                          fun dst =>
                                            OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                            (Cmm.Statics lbl (cons (Cmm.CmmStaticLit lit) nil))) (OrdList.snocOL
                                                            addr_code (PPC.Instr.LD format dst addr)) in
                                        GHC.Base.return_ (Any format code) in
                                      getAmode D dynRef GHC.Base.>>= cont_14__)))
                         | _, other =>
                                     Panic.panicStr (GHC.Base.hs_string__ "getRegister(ppc)") (PprCmmExpr.pprExpr
                                                                                               other)
                         end)
                 end
          | _, CmmExpr.Mk_CmmLit (CmmExpr.CmmFloat f frep) =>
                 NCGMonad.getNewLabelNat GHC.Base.>>=
                 (fun lbl =>
                    DynFlags.getDynFlags GHC.Base.>>=
                    (fun dflags =>
                       PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                       (fun dynRef =>
                          let cont_6__ arg_7__ :=
                            let 'MkAmode addr addr_code := arg_7__ in
                            let format := Format.floatFormat frep in
                            let code :=
                              fun dst =>
                                OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                (Cmm.Statics lbl (cons (Cmm.CmmStaticLit (CmmExpr.CmmFloat f frep))
                                                                       nil))) (OrdList.snocOL addr_code (PPC.Instr.LD
                                                                                               format dst addr)) in
                            GHC.Base.return_ (Any format code) in
                          getAmode D dynRef GHC.Base.>>= cont_6__)))
          | dflags, CmmExpr.Mk_CmmLit lit =>
                 if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool
                 then let imm := PPC.Regs.litToImm lit in
                      let code :=
                        fun dst =>
                          OrdList.toOL (cons (PPC.Instr.LIS dst (PPC.Regs.HA imm)) (cons (PPC.Instr.ADD
                                                                                          dst dst (PPC.Instr.RIImm
                                                                                                   (PPC.Regs.LO imm)))
                                                                                         nil)) in
                      let rep := CmmExpr.cmmLitType dflags lit in
                      GHC.Base.return_ (Any (Format.cmmTypeFormat rep) code) else
                 NCGMonad.getNewLabelNat GHC.Base.>>=
                 (fun lbl =>
                    DynFlags.getDynFlags GHC.Base.>>=
                    (fun dflags =>
                       PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                       (fun dynRef =>
                          let cont_14__ arg_15__ :=
                            let 'MkAmode addr addr_code := arg_15__ in
                            let rep := CmmExpr.cmmLitType dflags lit in
                            let format := Format.cmmTypeFormat rep in
                            let code :=
                              fun dst =>
                                OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                (Cmm.Statics lbl (cons (Cmm.CmmStaticLit lit) nil))) (OrdList.snocOL
                                                addr_code (PPC.Instr.LD format dst addr)) in
                            GHC.Base.return_ (Any format code) in
                          getAmode D dynRef GHC.Base.>>= cont_14__)))
          | _, other =>
                         Panic.panicStr (GHC.Base.hs_string__ "getRegister(ppc)") (PprCmmExpr.pprExpr
                                                                                  other)
          end.

Definition genJump'
   : CmmExpr.CmmExpr -> GenCCallPlatform -> NCGMonad.NatM InstrBlock :=
  fun arg_0__ arg_1__ =>
    let j_7__ :=
      match arg_0__, arg_1__ with
      | tree, _ =>
          let cont_4__ arg_5__ :=
            let 'pair target code := arg_5__ in
            GHC.Base.return_ (OrdList.snocOL (OrdList.snocOL code (PPC.Instr.MTCTR target))
                                             (PPC.Instr.BCTR nil None)) in
          getSomeReg tree GHC.Base.>>= cont_4__
      end in
    let j_11__ :=
      match arg_0__, arg_1__ with
      | tree, GCPLinux64ELF num_3__ =>
          if num_3__ GHC.Base.== #2 : bool
          then let cont_8__ arg_9__ :=
                 let 'pair target code := arg_9__ in
                 GHC.Base.return_ (OrdList.snocOL (OrdList.snocOL (OrdList.snocOL code
                                                                                  (PPC.Instr.MR PPC.Regs.r12 target))
                                                                  (PPC.Instr.MTCTR PPC.Regs.r12)) (PPC.Instr.BCTR nil
                                                   None)) in
               getSomeReg tree GHC.Base.>>= cont_8__ else
          j_7__
      | _, _ => j_7__
      end in
    match arg_0__, arg_1__ with
    | tree, GCPLinux64ELF num_2__ =>
        if num_2__ GHC.Base.== #1 : bool
        then let cont_12__ arg_13__ :=
               let 'pair target code := arg_13__ in
               GHC.Base.return_ (OrdList.snocOL (OrdList.snocOL (OrdList.snocOL (OrdList.snocOL
                                                                                 (OrdList.snocOL code (PPC.Instr.LD
                                                                                                  Format.II64
                                                                                                  PPC.Regs.r11
                                                                                                  (PPC.Regs.AddrRegImm
                                                                                                   target
                                                                                                   (PPC.Regs.ImmInt
                                                                                                    #0)))) (PPC.Instr.LD
                                                                                  Format.II64 PPC.Regs.toc
                                                                                  (PPC.Regs.AddrRegImm target
                                                                                   (PPC.Regs.ImmInt #8))))
                                                                                (PPC.Instr.MTCTR PPC.Regs.r11))
                                                                (PPC.Instr.LD Format.II64 PPC.Regs.r11
                                                                 (PPC.Regs.AddrRegImm target (PPC.Regs.ImmInt #16))))
                                                (PPC.Instr.BCTR nil None)) in
             getSomeReg tree GHC.Base.>>= cont_12__ else
        j_11__
    | _, _ => j_11__
    end.

Definition genJump : CmmExpr.CmmExpr -> NCGMonad.NatM InstrBlock :=
  fun arg_0__ =>
    match arg_0__ with
    | CmmExpr.Mk_CmmLit (CmmExpr.CmmLabel lbl) =>
        GHC.Base.return_ (OrdList.unitOL (PPC.Instr.JMP lbl))
    | tree =>
        DynFlags.getDynFlags GHC.Base.>>=
        (fun dflags => genJump' tree (platformToGCP (DynFlags.targetPlatform dflags)))
    end.

Definition trivialCode
   : CmmType.Width ->
     bool ->
     (Reg.Reg -> Reg.Reg -> PPC.Instr.RI -> PPC.Instr.Instr) ->
     CmmExpr.CmmExpr -> CmmExpr.CmmExpr -> NCGMonad.NatM Register :=
  fix getRegister' (arg_0__ : DynFlags.DynFlags) (arg_1__ : CmmExpr.CmmExpr)
        : NCGMonad.NatM Register
        := let j_5__ :=
             match arg_0__, arg_1__ with
             | _, other =>
                 Panic.panicStr (GHC.Base.hs_string__ "getRegister(ppc)") (PprCmmExpr.pprExpr
                                                                           other)
             end in
           let j_21__ :=
             match arg_0__, arg_1__ with
             | _, CmmExpr.Mk_CmmLit (CmmExpr.CmmFloat f frep) =>
                 NCGMonad.getNewLabelNat GHC.Base.>>=
                 (fun lbl =>
                    DynFlags.getDynFlags GHC.Base.>>=
                    (fun dflags =>
                       PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                       (fun dynRef =>
                          let cont_6__ arg_7__ :=
                            let 'MkAmode addr addr_code := arg_7__ in
                            let format := Format.floatFormat frep in
                            let code :=
                              fun dst =>
                                OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                (Cmm.Statics lbl (cons (Cmm.CmmStaticLit (CmmExpr.CmmFloat f frep))
                                                                       nil))) (OrdList.snocOL addr_code (PPC.Instr.LD
                                                                                               format dst addr)) in
                            GHC.Base.return_ (Any format code) in
                          getAmode D dynRef GHC.Base.>>= cont_6__)))
             | dflags, CmmExpr.Mk_CmmLit lit =>
                 if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool
                 then let imm := PPC.Regs.litToImm lit in
                      let code :=
                        fun dst =>
                          OrdList.toOL (cons (PPC.Instr.LIS dst (PPC.Regs.HA imm)) (cons (PPC.Instr.ADD
                                                                                          dst dst (PPC.Instr.RIImm
                                                                                                   (PPC.Regs.LO imm)))
                                                                                         nil)) in
                      let rep := CmmExpr.cmmLitType dflags lit in
                      GHC.Base.return_ (Any (Format.cmmTypeFormat rep) code) else
                 NCGMonad.getNewLabelNat GHC.Base.>>=
                 (fun lbl =>
                    DynFlags.getDynFlags GHC.Base.>>=
                    (fun dflags =>
                       PIC.cmmMakeDynamicReference dflags PIC.DataReference lbl GHC.Base.>>=
                       (fun dynRef =>
                          let cont_14__ arg_15__ :=
                            let 'MkAmode addr addr_code := arg_15__ in
                            let rep := CmmExpr.cmmLitType dflags lit in
                            let format := Format.cmmTypeFormat rep in
                            let code :=
                              fun dst =>
                                OrdList.consOL (PPC.Instr.LDATA (Cmm.Mk_Section Cmm.ReadOnlyData lbl)
                                                (Cmm.Statics lbl (cons (Cmm.CmmStaticLit lit) nil))) (OrdList.snocOL
                                                addr_code (PPC.Instr.LD format dst addr)) in
                            GHC.Base.return_ (Any format code) in
                          getAmode D dynRef GHC.Base.>>= cont_14__)))
             | _, _ => j_5__
             end in
           let j_133__ :=
             match arg_0__, arg_1__ with
             | dflags
             , CmmExpr.CmmMachOp (CmmMachOp.MO_UU_Conv CmmType.W64 CmmType.W32) (cons x
              nil) =>
                 if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool
                 then let cont_22__ arg_23__ :=
                        let 'MkChildCode64 code rlo := arg_23__ in
                        GHC.Base.return_ (Fixed Format.II32 rlo code) in
                      iselExpr64 x GHC.Base.>>= cont_22__ else
                 j_21__
             | dflags
             , CmmExpr.CmmMachOp (CmmMachOp.MO_SS_Conv CmmType.W64 CmmType.W32) (cons x
              nil) =>
                 if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool
                 then let cont_25__ arg_26__ :=
                        let 'MkChildCode64 code rlo := arg_26__ in
                        GHC.Base.return_ (Fixed Format.II32 rlo code) in
                      iselExpr64 x GHC.Base.>>= cont_25__ else
                 j_21__
             | _
             , CmmExpr.CmmMachOp (CmmMachOp.MO_UU_Conv CmmType.W8 CmmType.W32) (cons
              (CmmExpr.CmmLoad mem _) nil) =>
                 let cont_28__ arg_29__ :=
                   let 'MkAmode addr addr_code := arg_29__ in
                   GHC.Base.return_ (Any Format.II32 (fun dst =>
                                                        OrdList.snocOL addr_code (PPC.Instr.LD Format.II8 dst addr))) in
                 getAmode D mem GHC.Base.>>= cont_28__
             | _
             , CmmExpr.CmmMachOp (CmmMachOp.MO_UU_Conv CmmType.W8 CmmType.W64) (cons
              (CmmExpr.CmmLoad mem _) nil) =>
                 let cont_32__ arg_33__ :=
                   let 'MkAmode addr addr_code := arg_33__ in
                   GHC.Base.return_ (Any Format.II64 (fun dst =>
                                                        OrdList.snocOL addr_code (PPC.Instr.LD Format.II8 dst addr))) in
                 getAmode D mem GHC.Base.>>= cont_32__
             | _
             , CmmExpr.CmmMachOp (CmmMachOp.MO_UU_Conv CmmType.W16 CmmType.W32) (cons
              (CmmExpr.CmmLoad mem _) nil) =>
                 let cont_36__ arg_37__ :=
                   let 'MkAmode addr addr_code := arg_37__ in
                   GHC.Base.return_ (Any Format.II32 (fun dst =>
                                                        OrdList.snocOL addr_code (PPC.Instr.LD Format.II16 dst
                                                                        addr))) in
                 getAmode D mem GHC.Base.>>= cont_36__
             | _
             , CmmExpr.CmmMachOp (CmmMachOp.MO_SS_Conv CmmType.W16 CmmType.W32) (cons
              (CmmExpr.CmmLoad mem _) nil) =>
                 let cont_40__ arg_41__ :=
                   let 'MkAmode addr addr_code := arg_41__ in
                   GHC.Base.return_ (Any Format.II32 (fun dst =>
                                                        OrdList.snocOL addr_code (PPC.Instr.LA Format.II16 dst
                                                                        addr))) in
                 getAmode D mem GHC.Base.>>= cont_40__
             | _
             , CmmExpr.CmmMachOp (CmmMachOp.MO_UU_Conv CmmType.W16 CmmType.W64) (cons
              (CmmExpr.CmmLoad mem _) nil) =>
                 let cont_44__ arg_45__ :=
                   let 'MkAmode addr addr_code := arg_45__ in
                   GHC.Base.return_ (Any Format.II64 (fun dst =>
                                                        OrdList.snocOL addr_code (PPC.Instr.LD Format.II16 dst
                                                                        addr))) in
                 getAmode D mem GHC.Base.>>= cont_44__
             | _
             , CmmExpr.CmmMachOp (CmmMachOp.MO_SS_Conv CmmType.W16 CmmType.W64) (cons
              (CmmExpr.CmmLoad mem _) nil) =>
                 let cont_48__ arg_49__ :=
                   let 'MkAmode addr addr_code := arg_49__ in
                   GHC.Base.return_ (Any Format.II64 (fun dst =>
                                                        OrdList.snocOL addr_code (PPC.Instr.LA Format.II16 dst
                                                                        addr))) in
                 getAmode D mem GHC.Base.>>= cont_48__
             | _
             , CmmExpr.CmmMachOp (CmmMachOp.MO_UU_Conv CmmType.W32 CmmType.W64) (cons
              (CmmExpr.CmmLoad mem _) nil) =>
                 let cont_52__ arg_53__ :=
                   let 'MkAmode addr addr_code := arg_53__ in
                   GHC.Base.return_ (Any Format.II64 (fun dst =>
                                                        OrdList.snocOL addr_code (PPC.Instr.LD Format.II32 dst
                                                                        addr))) in
                 getAmode D mem GHC.Base.>>= cont_52__
             | _
             , CmmExpr.CmmMachOp (CmmMachOp.MO_SS_Conv CmmType.W32 CmmType.W64) (cons
              (CmmExpr.CmmLoad mem _) nil) =>
                 let cont_56__ arg_57__ :=
                   let 'MkAmode addr addr_code := arg_57__ in
                   GHC.Base.return_ (Any Format.II64 (fun dst =>
                                                        OrdList.snocOL addr_code (PPC.Instr.LA Format.II32 dst
                                                                        addr))) in
                 getAmode DS mem GHC.Base.>>= cont_56__
             | dflags, CmmExpr.CmmMachOp mop (cons x (cons y nil)) =>
                 let triv_float
                  : CmmType.Width ->
                    (Format.Format -> Reg.Reg -> Reg.Reg -> Reg.Reg -> PPC.Instr.Instr) ->
                    NCGMonad.NatM Register :=
                   fun width instr => trivialCodeNoImm (Format.floatFormat width) instr x y in
                 match mop with
                 | CmmMachOp.MO_F_Eq _ => condFltReg PPC.Cond.EQQ x y
                 | CmmMachOp.MO_F_Ne _ => condFltReg PPC.Cond.NE x y
                 | CmmMachOp.MO_F_Gt _ => condFltReg PPC.Cond.GTT x y
                 | CmmMachOp.MO_F_Ge _ => condFltReg PPC.Cond.GE x y
                 | CmmMachOp.MO_F_Lt _ => condFltReg PPC.Cond.LTT x y
                 | CmmMachOp.MO_F_Le _ => condFltReg PPC.Cond.LE x y
                 | CmmMachOp.MO_Eq rep =>
                     condIntReg PPC.Cond.EQQ (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                 | CmmMachOp.MO_Ne rep =>
                     condIntReg PPC.Cond.NE (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                 | CmmMachOp.MO_S_Gt rep =>
                     condIntReg PPC.Cond.GTT (extendSExpr dflags rep x) (extendSExpr dflags rep y)
                 | CmmMachOp.MO_S_Ge rep =>
                     condIntReg PPC.Cond.GE (extendSExpr dflags rep x) (extendSExpr dflags rep y)
                 | CmmMachOp.MO_S_Lt rep =>
                     condIntReg PPC.Cond.LTT (extendSExpr dflags rep x) (extendSExpr dflags rep y)
                 | CmmMachOp.MO_S_Le rep =>
                     condIntReg PPC.Cond.LE (extendSExpr dflags rep x) (extendSExpr dflags rep y)
                 | CmmMachOp.MO_U_Gt rep =>
                     condIntReg PPC.Cond.GU (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                 | CmmMachOp.MO_U_Ge rep =>
                     condIntReg PPC.Cond.GEU (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                 | CmmMachOp.MO_U_Lt rep =>
                     condIntReg PPC.Cond.LU (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                 | CmmMachOp.MO_U_Le rep =>
                     condIntReg PPC.Cond.LEU (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                 | CmmMachOp.MO_F_Add w => triv_float w PPC.Instr.FADD
                 | CmmMachOp.MO_F_Sub w => triv_float w PPC.Instr.FSUB
                 | CmmMachOp.MO_F_Mul w => triv_float w PPC.Instr.FMUL
                 | CmmMachOp.MO_F_Quot w => triv_float w PPC.Instr.FDIV
                 | CmmMachOp.MO_Add CmmType.W32 =>
                     let j_87__ :=
                       match y with
                       | CmmExpr.Mk_CmmLit lit =>
                           let cont_81__ arg_82__ :=
                             let 'pair src srcCode := arg_82__ in
                             let imm := PPC.Regs.litToImm lit in
                             let code :=
                               fun dst =>
                                 OrdList.appOL srcCode (OrdList.toOL (cons (PPC.Instr.ADDIS dst src (PPC.Regs.HA
                                                                                                     imm)) (cons
                                                                            (PPC.Instr.ADD dst dst (PPC.Instr.RIImm
                                                                                                    (PPC.Regs.LO imm)))
                                                                            nil))) in
                             GHC.Base.return_ (Any Format.II32 code) in
                           getSomeReg x GHC.Base.>>= cont_81__
                       | _ => trivialCode CmmType.W32 true PPC.Instr.ADD x y
                       end in
                     match y with
                     | CmmExpr.Mk_CmmLit (CmmExpr.CmmInt imm immrep) =>
                         match PPC.Regs.makeImmediate CmmType.W32 true imm with
                         | Some _ =>
                             trivialCode CmmType.W32 true PPC.Instr.ADD x (CmmExpr.Mk_CmmLit (CmmExpr.CmmInt
                                                                                              imm immrep))
                         | _ => j_87__
                         end
                     | _ => j_87__
                     end
                 | CmmMachOp.MO_Add rep => trivialCode rep true PPC.Instr.ADD x y
                 | CmmMachOp.MO_Sub rep =>
                     let j_97__ :=
                       let j_93__ := trivialCodeNoImm' (Format.intFormat rep) PPC.Instr.SUBF y x in
                       match x with
                       | CmmExpr.Mk_CmmLit (CmmExpr.CmmInt imm _) =>
                           match PPC.Regs.makeImmediate rep true imm with
                           | Some _ => trivialCode rep true PPC.Instr.SUBFC y x
                           | _ => j_93__
                           end
                       | _ => j_93__
                       end in
                     match y with
                     | CmmExpr.Mk_CmmLit (CmmExpr.CmmInt imm immrep) =>
                         match PPC.Regs.makeImmediate rep true (GHC.Num.negate imm) with
                         | Some _ =>
                             trivialCode rep true PPC.Instr.ADD x (CmmExpr.Mk_CmmLit (CmmExpr.CmmInt
                                                                                      (GHC.Num.negate imm) immrep))
                         | _ => j_97__
                         end
                     | _ => j_97__
                     end
                 | CmmMachOp.MO_Mul rep => shiftMulCode rep true PPC.Instr.MULL x y
                 | CmmMachOp.MO_S_MulMayOflo rep =>
                     let cont_102__ arg_103__ :=
                       let 'pair src1 code1 := arg_103__ in
                       let cont_104__ arg_105__ :=
                         let 'pair src2 code2 := arg_105__ in
                         let format := Format.intFormat rep in
                         let code :=
                           fun dst =>
                             OrdList.appOL (OrdList.appOL code1 code2) (OrdList.toOL (cons (PPC.Instr.MULLO
                                                                                            format dst src1 src2) (cons
                                                                                            (PPC.Instr.MFOV format dst)
                                                                                            nil))) in
                         GHC.Base.return_ (Any format code) in
                       getSomeReg y GHC.Base.>>= cont_104__ in
                     getSomeReg x GHC.Base.>>= cont_102__
                 | CmmMachOp.MO_S_Quot rep =>
                     trivialCodeNoImmSign (Format.intFormat rep) true PPC.Instr.DIV (extendSExpr
                                                                                     dflags rep x) (extendSExpr dflags
                                                                                                    rep y)
                 | CmmMachOp.MO_U_Quot rep =>
                     trivialCodeNoImmSign (Format.intFormat rep) false PPC.Instr.DIV (extendUExpr
                                                                                      dflags rep x) (extendUExpr dflags
                                                                                                     rep y)
                 | CmmMachOp.MO_S_Rem rep =>
                     remainderCode rep true (extendSExpr dflags rep x) (extendSExpr dflags rep y)
                 | CmmMachOp.MO_U_Rem rep =>
                     remainderCode rep false (extendUExpr dflags rep x) (extendUExpr dflags rep y)
                 | CmmMachOp.MO_And rep =>
                     let j_114__ := trivialCode rep false PPC.Instr.AND x y in
                     match y with
                     | CmmExpr.Mk_CmmLit (CmmExpr.CmmInt imm _) =>
                         if orb (imm GHC.Base.== GHC.Num.negate #8) (imm GHC.Base.==
                                 GHC.Num.negate #4) : bool
                         then let cont_115__ arg_116__ :=
                                let 'pair src srcCode := arg_116__ in
                                let fmt := Format.intFormat rep in
                                let clear_mask := if imm GHC.Base.== GHC.Num.negate #4 : bool then #2 else #3 in
                                let code :=
                                  fun dst =>
                                    OrdList.appOL srcCode (OrdList.unitOL (PPC.Instr.CLRRI fmt dst src
                                                                           clear_mask)) in
                                GHC.Base.return_ (Any fmt code) in
                              getSomeReg x GHC.Base.>>= cont_115__ else
                         j_114__
                     | _ => j_114__
                     end
                 | CmmMachOp.MO_Or rep => trivialCode rep false PPC.Instr.OR x y
                 | CmmMachOp.MO_Xor rep => trivialCode rep false PPC.Instr.XOR x y
                 | CmmMachOp.MO_Shl rep => shiftMulCode rep false PPC.Instr.SL x y
                 | CmmMachOp.MO_S_Shr rep =>
                     shiftMulCode rep false PPC.Instr.SRA (extendSExpr dflags rep x) y
                 | CmmMachOp.MO_U_Shr rep =>
                     shiftMulCode rep false PPC.Instr.SR (extendUExpr dflags rep x) y
                 | _ => Panic.panic (GHC.Base.hs_string__ "PPC.CodeGen.getRegister: no match")
                 end
             | _, CmmExpr.Mk_CmmLit (CmmExpr.CmmInt i rep) =>
                 match PPC.Regs.makeImmediate rep true i with
                 | Some imm =>
                     let code := fun dst => OrdList.unitOL (PPC.Instr.LI dst imm) in
                     GHC.Base.return_ (Any (Format.intFormat rep) code)
                 | _ => j_21__
                 end
             | _, _ => j_21__
             end in
           match arg_0__, arg_1__ with
           | dflags, CmmExpr.Mk_CmmReg reg =>
               GHC.Base.return_ (Fixed (Format.cmmTypeFormat (CmmExpr.cmmRegType dflags reg))
                                 (getRegisterReg (DynFlags.targetPlatform dflags) reg) OrdList.nilOL)
           | dflags, (CmmExpr.CmmRegOff _ _ as tree) =>
               getRegister' dflags (mangleIndexTree dflags tree)
           | dflags
           , CmmExpr.CmmMachOp (CmmMachOp.MO_UU_Conv CmmType.W64 CmmType.W32) (cons
            (CmmExpr.CmmMachOp (CmmMachOp.MO_U_Shr CmmType.W64) (cons x (cons
               (CmmExpr.Mk_CmmLit (CmmExpr.CmmInt num_2__ _)) nil))) nil) =>
               if num_2__ GHC.Base.== #32 : bool
               then if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool
                    then let cont_136__ arg_137__ :=
                           let 'MkChildCode64 code rlo := arg_137__ in
                           GHC.Base.return_ (Fixed Format.II32 (Reg.getHiVRegFromLo rlo) code) in
                         iselExpr64 x GHC.Base.>>= cont_136__ else
                    j_133__ else
               j_133__
           | dflags
           , CmmExpr.CmmMachOp (CmmMachOp.MO_SS_Conv CmmType.W64 CmmType.W32) (cons
            (CmmExpr.CmmMachOp (CmmMachOp.MO_U_Shr CmmType.W64) (cons x (cons
               (CmmExpr.Mk_CmmLit (CmmExpr.CmmInt num_3__ _)) nil))) nil) =>
               if num_3__ GHC.Base.== #32 : bool
               then if Platform.target32Bit (DynFlags.targetPlatform dflags) : bool
                    then let cont_139__ arg_140__ :=
                           let 'MkChildCode64 code rlo := arg_140__ in
                           GHC.Base.return_ (Fixed Format.II32 (Reg.getHiVRegFromLo rlo) code) in
                         iselExpr64 x GHC.Base.>>= cont_139__ else
                    j_133__ else
               j_133__
           | _, _ => j_133__
           end with getSomeReg (expr : CmmExpr.CmmExpr) : NCGMonad.NatM (Reg.Reg *
                                                                         InstrBlock)%type
                      := getRegister expr GHC.Base.>>=
                         (fun r =>
                            match r with
                            | Any rep code =>
                                NCGMonad.getNewRegNat rep GHC.Base.>>=
                                (fun tmp => GHC.Base.return_ (pair tmp (code tmp)))
                            | Fixed _ reg code => GHC.Base.return_ (pair reg code)
                            end) with getRegister (e : CmmExpr.CmmExpr) : NCGMonad.NatM Register
                                        := DynFlags.getDynFlags GHC.Base.>>= (fun dflags => getRegister' dflags e)
  with trivialCode (arg_0__ : CmmType.Width) (arg_1__ : bool) (arg_2__
                     : (Reg.Reg -> Reg.Reg -> PPC.Instr.RI -> PPC.Instr.Instr)) (arg_3__ arg_4__
                     : CmmExpr.CmmExpr) : NCGMonad.NatM Register
         := let j_11__ :=
              match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
              | rep, _, instr, x, y =>
                  let cont_5__ arg_6__ :=
                    let 'pair src1 code1 := arg_6__ in
                    let cont_7__ arg_8__ :=
                      let 'pair src2 code2 := arg_8__ in
                      let code :=
                        fun dst =>
                          OrdList.snocOL (OrdList.appOL code1 code2) (instr dst src1 (PPC.Instr.RIReg
                                                                                      src2)) in
                      GHC.Base.return_ (Any (Format.intFormat rep) code) in
                    getSomeReg y GHC.Base.>>= cont_7__ in
                  getSomeReg x GHC.Base.>>= cont_5__
              end in
            match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
            | rep, signed, instr, x, CmmExpr.Mk_CmmLit (CmmExpr.CmmInt y _) =>
                match PPC.Regs.makeImmediate rep signed y with
                | Some imm =>
                    let cont_12__ arg_13__ :=
                      let 'pair src1 code1 := arg_13__ in
                      let code :=
                        fun dst => OrdList.snocOL code1 (instr dst src1 (PPC.Instr.RIImm imm)) in
                      GHC.Base.return_ (Any (Format.intFormat rep) code) in
                    getSomeReg x GHC.Base.>>= cont_12__
                | _ => j_11__
                end
            | _, _, _, _, _ => j_11__
            end for trivialCode.

Axiom condFltCode : PPC.Cond.Cond ->
                    CmmExpr.CmmExpr -> CmmExpr.CmmExpr -> NCGMonad.NatM CondCode.

Definition getCondCode : CmmExpr.CmmExpr -> NCGMonad.NatM CondCode :=
  fun arg_0__ =>
    match arg_0__ with
    | CmmExpr.CmmMachOp mop (cons x (cons y nil)) =>
        DynFlags.getDynFlags GHC.Base.>>=
        (fun dflags =>
           match mop with
           | CmmMachOp.MO_F_Eq CmmType.W32 => condFltCode PPC.Cond.EQQ x y
           | CmmMachOp.MO_F_Ne CmmType.W32 => condFltCode PPC.Cond.NE x y
           | CmmMachOp.MO_F_Gt CmmType.W32 => condFltCode PPC.Cond.GTT x y
           | CmmMachOp.MO_F_Ge CmmType.W32 => condFltCode PPC.Cond.GE x y
           | CmmMachOp.MO_F_Lt CmmType.W32 => condFltCode PPC.Cond.LTT x y
           | CmmMachOp.MO_F_Le CmmType.W32 => condFltCode PPC.Cond.LE x y
           | CmmMachOp.MO_F_Eq CmmType.W64 => condFltCode PPC.Cond.EQQ x y
           | CmmMachOp.MO_F_Ne CmmType.W64 => condFltCode PPC.Cond.NE x y
           | CmmMachOp.MO_F_Gt CmmType.W64 => condFltCode PPC.Cond.GTT x y
           | CmmMachOp.MO_F_Ge CmmType.W64 => condFltCode PPC.Cond.GE x y
           | CmmMachOp.MO_F_Lt CmmType.W64 => condFltCode PPC.Cond.LTT x y
           | CmmMachOp.MO_F_Le CmmType.W64 => condFltCode PPC.Cond.LE x y
           | CmmMachOp.MO_Eq rep =>
               condIntCode PPC.Cond.EQQ (extendUExpr dflags rep x) (extendUExpr dflags rep y)
           | CmmMachOp.MO_Ne rep =>
               condIntCode PPC.Cond.NE (extendUExpr dflags rep x) (extendUExpr dflags rep y)
           | CmmMachOp.MO_S_Gt rep =>
               condIntCode PPC.Cond.GTT (extendSExpr dflags rep x) (extendSExpr dflags rep y)
           | CmmMachOp.MO_S_Ge rep =>
               condIntCode PPC.Cond.GE (extendSExpr dflags rep x) (extendSExpr dflags rep y)
           | CmmMachOp.MO_S_Lt rep =>
               condIntCode PPC.Cond.LTT (extendSExpr dflags rep x) (extendSExpr dflags rep y)
           | CmmMachOp.MO_S_Le rep =>
               condIntCode PPC.Cond.LE (extendSExpr dflags rep x) (extendSExpr dflags rep y)
           | CmmMachOp.MO_U_Gt rep =>
               condIntCode PPC.Cond.GU (extendSExpr dflags rep x) (extendSExpr dflags rep y)
           | CmmMachOp.MO_U_Ge rep =>
               condIntCode PPC.Cond.GEU (extendSExpr dflags rep x) (extendSExpr dflags rep y)
           | CmmMachOp.MO_U_Lt rep =>
               condIntCode PPC.Cond.LU (extendSExpr dflags rep x) (extendSExpr dflags rep y)
           | CmmMachOp.MO_U_Le rep =>
               condIntCode PPC.Cond.LEU (extendSExpr dflags rep x) (extendSExpr dflags rep y)
           | _ =>
               Panic.panicStr (GHC.Base.hs_string__ "getCondCode(powerpc)")
               (CmmMachOp.pprMachOp mop)
           end)
    | _ => Panic.panic (GHC.Base.hs_string__ "getCondCode(2)(powerpc)")
    end.

Definition genCondJump
   : BlockId.BlockId ->
     CmmExpr.CmmExpr -> option bool -> NCGMonad.NatM InstrBlock :=
  fun id bool prediction =>
    let cont_0__ arg_1__ :=
      let 'MkCondCode _ cond code := arg_1__ in
      GHC.Base.return_ (OrdList.snocOL code (PPC.Instr.BCC cond id prediction)) in
    getCondCode bool GHC.Base.>>= cont_0__.

Axiom coerceInt2FP' : Platform.Arch ->
                      CmmType.Width -> CmmType.Width -> CmmExpr.CmmExpr -> NCGMonad.NatM Register.

Axiom coerceInt2FP : CmmType.Width ->
                     CmmType.Width -> CmmExpr.CmmExpr -> NCGMonad.NatM Register.

Definition coerceFP2Int'
   : Platform.Arch ->
     CmmType.Width -> CmmType.Width -> CmmExpr.CmmExpr -> NCGMonad.NatM Register :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | Platform.ArchPPC, _, toRep, x =>
        DynFlags.getDynFlags GHC.Base.>>=
        (fun dflags =>
           let cont_4__ arg_5__ :=
             let 'pair src code := arg_5__ in
             NCGMonad.getNewRegNat Format.FF64 GHC.Base.>>=
             (fun tmp =>
                let code' :=
                  fun dst =>
                    OrdList.appOL code (OrdList.toOL (cons (PPC.Instr.FCTIWZ tmp src) (cons
                                                            (PPC.Instr.ST Format.FF64 tmp (PPC.Regs.spRel dflags #2))
                                                            (cons (PPC.Instr.LD Format.II32 dst (PPC.Regs.spRel dflags
                                                                                                 #3)) nil)))) in
                GHC.Base.return_ (Any (Format.intFormat toRep) code')) in
           getSomeReg x GHC.Base.>>= cont_4__)
    | Platform.ArchPPC_64 _, _, toRep, x =>
        DynFlags.getDynFlags GHC.Base.>>=
        (fun dflags =>
           let cont_8__ arg_9__ :=
             let 'pair src code := arg_9__ in
             NCGMonad.getNewRegNat Format.FF64 GHC.Base.>>=
             (fun tmp =>
                let code' :=
                  fun dst =>
                    OrdList.appOL code (OrdList.toOL (cons (PPC.Instr.FCTIDZ tmp src) (cons
                                                            (PPC.Instr.ST Format.FF64 tmp (PPC.Regs.spRel dflags #3))
                                                            (cons (PPC.Instr.LD Format.II64 dst (PPC.Regs.spRel dflags
                                                                                                 #3)) nil)))) in
                GHC.Base.return_ (Any (Format.intFormat toRep) code')) in
           getSomeReg x GHC.Base.>>= cont_8__)
    | _, _, _, _ =>
        Panic.panic (GHC.Base.hs_string__ "PPC.CodeGen.coerceFP2Int: unknown arch")
    end.

Axiom coerceFP2Int : CmmType.Width ->
                     CmmType.Width -> CmmExpr.CmmExpr -> NCGMonad.NatM Register.

Definition assignReg_IntCode
   : Format.Format ->
     CmmExpr.CmmReg -> CmmExpr.CmmExpr -> NCGMonad.NatM InstrBlock :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | _, reg, src =>
        DynFlags.getDynFlags GHC.Base.>>=
        (fun dflags =>
           let dst := getRegisterReg (DynFlags.targetPlatform dflags) reg in
           getRegister src GHC.Base.>>=
           (fun r =>
              GHC.Base.return_ (match r with
                                | Any _ code => code dst
                                | Fixed _ freg fcode => OrdList.snocOL fcode (PPC.Instr.MR dst freg)
                                end)))
    end.

Definition assignReg_FltCode
   : Format.Format ->
     CmmExpr.CmmReg -> CmmExpr.CmmExpr -> NCGMonad.NatM InstrBlock :=
  assignReg_IntCode.

Definition assignMem_IntCode
   : Format.Format ->
     CmmExpr.CmmExpr -> CmmExpr.CmmExpr -> NCGMonad.NatM InstrBlock :=
  fun pk addr src =>
    let cont_0__ arg_1__ :=
      let 'pair srcReg code := arg_1__ in
      let cont_5__ arg_6__ :=
        let 'MkAmode dstAddr addr_code := arg_6__ in
        GHC.Base.return_ (OrdList.snocOL (OrdList.appOL code addr_code) (PPC.Instr.ST pk
                                          srcReg dstAddr)) in
      (match pk with
       | Format.II64 => getAmode DS addr
       | _ => getAmode D addr
       end) GHC.Base.>>=
      cont_5__ in
    getSomeReg src GHC.Base.>>= cont_0__.

Definition assignMem_FltCode
   : Format.Format ->
     CmmExpr.CmmExpr -> CmmExpr.CmmExpr -> NCGMonad.NatM InstrBlock :=
  assignMem_IntCode.

(* External variables:
     None Some bool cons false negb nil op_zt__ option orb pair true BlockId.BlockId
     Cmm.CmmStaticLit Cmm.Mk_Section Cmm.ReadOnlyData Cmm.Statics CmmExpr.CmmExpr
     CmmExpr.CmmFloat CmmExpr.CmmInt CmmExpr.CmmLabel CmmExpr.CmmLoad
     CmmExpr.CmmMachOp CmmExpr.CmmReg CmmExpr.CmmRegOff CmmExpr.Mk_CmmLit
     CmmExpr.Mk_CmmReg CmmExpr.cmmLitType CmmExpr.cmmRegType CmmMachOp.MO_Add
     CmmMachOp.MO_And CmmMachOp.MO_Eq CmmMachOp.MO_F_Add CmmMachOp.MO_F_Eq
     CmmMachOp.MO_F_Ge CmmMachOp.MO_F_Gt CmmMachOp.MO_F_Le CmmMachOp.MO_F_Lt
     CmmMachOp.MO_F_Mul CmmMachOp.MO_F_Ne CmmMachOp.MO_F_Quot CmmMachOp.MO_F_Sub
     CmmMachOp.MO_Mul CmmMachOp.MO_Ne CmmMachOp.MO_Or CmmMachOp.MO_SS_Conv
     CmmMachOp.MO_S_Ge CmmMachOp.MO_S_Gt CmmMachOp.MO_S_Le CmmMachOp.MO_S_Lt
     CmmMachOp.MO_S_MulMayOflo CmmMachOp.MO_S_Quot CmmMachOp.MO_S_Rem
     CmmMachOp.MO_S_Shr CmmMachOp.MO_Shl CmmMachOp.MO_Sub CmmMachOp.MO_UU_Conv
     CmmMachOp.MO_U_Ge CmmMachOp.MO_U_Gt CmmMachOp.MO_U_Le CmmMachOp.MO_U_Lt
     CmmMachOp.MO_U_Quot CmmMachOp.MO_U_Rem CmmMachOp.MO_U_Shr CmmMachOp.MO_Xor
     CmmMachOp.pprMachOp CmmType.W16 CmmType.W32 CmmType.W64 CmmType.W8 CmmType.Width
     CmmType.typeWidth DynFlags.DynFlags DynFlags.getDynFlags DynFlags.targetPlatform
     Format.FF64 Format.Format Format.II16 Format.II32 Format.II64 Format.II8
     Format.cmmTypeFormat Format.floatFormat Format.intFormat GHC.Base.op_zeze__
     GHC.Base.op_zgzgze__ GHC.Base.return_ GHC.Err.Build_Default GHC.Err.Default
     GHC.Num.Int GHC.Num.fromInteger GHC.Num.negate GHC.Num.op_zp__
     GHC.Real.fromIntegral NCGMonad.NatM NCGMonad.getNewLabelNat
     NCGMonad.getNewRegNat OrdList.OrdList OrdList.appOL OrdList.consOL OrdList.nilOL
     OrdList.snocOL OrdList.toOL OrdList.unitOL PIC.DataReference
     PIC.cmmMakeDynamicReference PPC.Cond.Cond PPC.Cond.EQQ PPC.Cond.GE PPC.Cond.GEU
     PPC.Cond.GTT PPC.Cond.GU PPC.Cond.LE PPC.Cond.LEU PPC.Cond.LTT PPC.Cond.LU
     PPC.Cond.NE PPC.Instr.ADD PPC.Instr.ADDIS PPC.Instr.AND PPC.Instr.BCC
     PPC.Instr.BCTR PPC.Instr.CLRRI PPC.Instr.CRNOR PPC.Instr.DIV PPC.Instr.FADD
     PPC.Instr.FCTIDZ PPC.Instr.FCTIWZ PPC.Instr.FDIV PPC.Instr.FMUL PPC.Instr.FSUB
     PPC.Instr.Instr PPC.Instr.JMP PPC.Instr.LA PPC.Instr.LD PPC.Instr.LDATA
     PPC.Instr.LI PPC.Instr.LIS PPC.Instr.MFCR PPC.Instr.MFOV PPC.Instr.MR
     PPC.Instr.MTCTR PPC.Instr.MULL PPC.Instr.MULLO PPC.Instr.OR PPC.Instr.RI
     PPC.Instr.RIImm PPC.Instr.RIReg PPC.Instr.RLWINM PPC.Instr.SL PPC.Instr.SR
     PPC.Instr.SRA PPC.Instr.ST PPC.Instr.SUBF PPC.Instr.SUBFC PPC.Instr.XOR
     PPC.Instr.archWordFormat PPC.Regs.AddrMode PPC.Regs.AddrRegImm PPC.Regs.HA
     PPC.Regs.ImmInt PPC.Regs.LO PPC.Regs.litToImm PPC.Regs.makeImmediate
     PPC.Regs.r11 PPC.Regs.r12 PPC.Regs.spRel PPC.Regs.toc Panic.panic Panic.panicStr
     Platform.Arch Platform.ArchPPC Platform.ArchPPC_64 Platform.ELF_V1
     Platform.ELF_V2 Platform.OSAIX Platform.OSDarwin Platform.OSLinux
     Platform.Platform Platform.platformArch Platform.platformOS Platform.target32Bit
     PprCmmExpr.pprExpr Reg.Reg Reg.getHiVRegFromLo
*)
