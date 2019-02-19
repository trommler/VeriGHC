(* Coq implementation of compiler/cmm/CmmExpr.hs *)
Require Import List.

Require Import GHC.BlockId.
Require Import GHC.CmmType.
Require Import GHC.Int.
Require Import GHC.Unique.
Require Import GHC.CmmMachOp.

Require Import compcert.common.AST.

Inductive LocalReg : Set :=
| LR_LocalReg: Unique -> CmmType -> LocalReg.

Inductive VGcPtr : Set := VG_VGcPtr | VNonGcPtr.

Inductive GlobalReg : Set :=
| VanillaReg: Int -> VGcPtr -> GlobalReg
| FloatReg: Int -> GlobalReg
| DoubleReg: Int -> GlobalReg
| LongReg: Int -> GlobalReg
| XmmReg: Int -> GlobalReg
| YmmReg: Int -> GlobalReg
| ZmmReg: Int -> GlobalReg
| Sp: GlobalReg
| SpLim: GlobalReg
| Hp: GlobalReg
| HpLim: GlobalReg
| CCCS: GlobalReg
| CurrentTSO: GlobalReg
| CurrentNursery: GlobalReg
| HpAlloc: GlobalReg
| EagerBlackholeInfo: GlobalReg
| GCEnter1: GlobalReg
| GCFun: GlobalReg
| BaseReg: GlobalReg
| MachSp: GlobalReg
| UnwindReturnReg: GlobalReg
| PicBaseReg: GlobalReg
.

Inductive CmmReg : Set :=
| CmmLocal: LocalReg -> CmmReg
| CmmGlobal: GlobalReg -> CmmReg
.

Inductive Area : Set :=
| Old: Area
| Young: BlockId -> Area
.

(* FIXME: Put these definitions in the appropriate files and check types
   with GHC implementation *)
Inductive Rational := Ratio: Int -> Int -> Rational.

Definition CLabel := ident.

Inductive CmmLit : Set :=
| CmmInt: Integer -> Width -> CmmLit
| CmmFloat: Rational -> Width -> CmmLit
| CmmLabel: CLabel -> CmmLit
| CmmLabelOff: CLabel -> Int -> CmmLit
| CmmLabelDiffOff: CLabel -> CLabel -> Int -> Width -> CmmLit
| CmmBlock: BlockId -> CmmLit
| CmmHighStackMark: CmmLit
.

Inductive CmmExpr : Set :=
| CE_CmmLit: CmmLit -> CmmExpr
| CE_CmmLoad: CmmExpr -> CmmType -> CmmExpr
| CE_CmmReg: CmmReg -> CmmExpr
| CE_CmmMachOp: MachOp -> list CmmExpr -> CmmExpr
| CE_CmmStackSlot: Area -> Int -> CmmExpr
| CE_CmmRegOff : CmmReg -> Int -> CmmExpr
.

Definition cmmLabelType (lbl:CLabel) : CmmType := bWord.

Definition cmmLitType (l : CmmLit) : CmmType :=
  match l with
  | CmmInt _ width => cmmBits width
  | CmmFloat _ width => cmmFloat width
  | CmmLabel lbl => cmmLabelType lbl
  | CmmLabelOff lbl _ => cmmLabelType lbl
  | CmmLabelDiffOff _ _ _ width => cmmBits width
  | CmmBlock _ => bWord
  | CmmHighStackMark => bWord
  end.

Definition localRegType (l:LocalReg) : CmmType :=
  match l with
  | LR_LocalReg _ rep => rep
  end.

Definition globalRegType (g:GlobalReg) : CmmType :=
  match g with
  | VanillaReg _ _ => bWord (* we might want to look at the second parameter *)
  | FloatReg _ => cmmFloat W32
  | DoubleReg _ => cmmFloat W64
  | LongReg _ => cmmBits W64
  | _ => bWord
  end.
                                         
Definition cmmRegType (r:CmmReg) : CmmType :=
  match r with
  | CmmLocal reg => localRegType reg
  | CmmGlobal reg => globalRegType reg
  end.

Fixpoint cmmExprType (e : CmmExpr) : CmmType :=
  match e with
  | CE_CmmLit lit => cmmLitType lit
  | CE_CmmLoad _ rep => rep
  | CE_CmmReg reg => cmmRegType reg
  | CE_CmmMachOp op args => machOpResultType op (List.map cmmExprType args)
  | CE_CmmStackSlot _ _ => bWord
  | CE_CmmRegOff reg _ => cmmRegType reg
  end.
