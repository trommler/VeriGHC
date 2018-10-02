(* Coq implementation of compiler/cmm/CmmExpr.hs *)
Require Import GHC.CmmType.
Require Import GHC.Int.
Require Import GHC.Unique.
Require Import GHC.CmmMachOp.

Inductive LocalReg :=
| LR_LocalReg: Unique -> CmmType -> LocalReg.

Inductive VGcPtr := VG_VGcPtr | VNonGcPtr.

Inductive GlobalReg :=
| VanillaReg: Int -> VGcPtr -> GlobalReg
| FloatReg: Int -> GlobalReg
| DoubleReg: Int -> GlobalReg
| LongReg: Int -> GlobalReg
                    (* ... and some more *)
| BaseReg: GlobalReg
| PicBaseReg: GlobalReg
.

Inductive CmmReg :=
| CmmLocal: LocalReg -> CmmReg
| CmmGlobal: GlobalReg -> CmmReg
.

(* FIXME: BlockId shoul be defined in its own file and is a Label *)
Definition BlockId := nat.

Inductive Area :=
| Old: Area
| Young: BlockId -> Area
.

(* FIXME: Put these definitions in the appropriate files and check types
   with GHC implementation *)
Inductive Rational := Ratio: Int -> Int -> Rational.

Inductive CLabel := nat.

Inductive CmmLit :=
| CmmInt: Int (*eger *) -> Width -> CmmLit
| CmmFloat: Rational -> Width -> CmmLit
| CmmVec: list CmmLit -> CmmLit
| CmmLabel: CLabel -> CmmLit
| CmmLabelOff: CLabel -> Int -> CmmLit
| CmmLabelDiffOff: CLabel -> CLabel -> Int -> Width -> CmmLit
| CmmBlock: BlockId -> CmmLit
| CmmHighStackMark: CmmLit
.

Inductive CmmExpr :=
| CE_CmmLit: CmmLit -> CmmExpr
| CE_CmmLoad: CmmExpr -> CmmType -> CmmExpr
| CE_CmmReg: CmmReg -> CmmExpr
| CE_CmmMachOp: MachOp -> list CmmExpr -> CmmExpr
| CE_CmmStackSlot: Area -> Int -> CmmExpr
| CE_CmmRegOff : CmmReg -> Int -> CmmExpr
.
