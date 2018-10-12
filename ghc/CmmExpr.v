(* Coq implementation of compiler/cmm/CmmExpr.hs *)
Require Import BinNums.

Require Import GHC.CmmType.
Require Import GHC.Int.
Require Import GHC.Unique.
Require Import GHC.CmmMachOp.

Inductive LocalReg : Set :=
| LR_LocalReg: Unique -> CmmType -> LocalReg.

Inductive VGcPtr : Set := VG_VGcPtr | VNonGcPtr.

Inductive GlobalReg : Set :=
| VanillaReg: Int -> VGcPtr -> GlobalReg
| FloatReg: Int -> GlobalReg
| DoubleReg: Int -> GlobalReg
| LongReg: Int -> GlobalReg
                    (* ... and some more *)
| BaseReg: GlobalReg
| PicBaseReg: GlobalReg
.

Inductive CmmReg : Set :=
| CmmLocal: LocalReg -> CmmReg
| CmmGlobal: GlobalReg -> CmmReg
.

(* FIXME: BlockId should be defined in its own file and is a Label *)
Definition BlockId := nat.

Inductive Area : Set :=
| Old: Area
| Young: BlockId -> Area
.

(* FIXME: Put these definitions in the appropriate files and check types
   with GHC implementation *)
Definition Integer := Z.

Inductive Rational := Ratio: Int -> Int -> Rational.

Inductive CLabel := nat.

Inductive CmmLit : Set :=
| CmmInt: Integer -> Width -> CmmLit
| CmmFloat: Rational -> Width -> CmmLit
| CmmVec: list CmmLit -> CmmLit
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
