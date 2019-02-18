(* Coq implementation of compiler/cmm/CmmExpr.hs *)
Require Import List.

Require Import GHC.BlockId.
Require Import CmmCore.CmmCoreType.
Require Import GHC.Int.
Require Import GHC.Unique.
Require Import GHC.CmmMachOp.

Require Import compcert.common.AST.

Inductive LocalReg : Set :=
| LR_LocalReg: Unique -> CC_CmmType -> LocalReg.

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

(* FIXME: Put these definitions in the appropriate files and check types
   with GHC implementation *)
Inductive Rational := Ratio: Int -> Int -> Rational.

Definition CLabel := ident.

Inductive isFloatWidth (w:Width) : Prop :=
| ifw_single: w=W32 -> isFloatWidth w
| ifw_double: w=W64 -> isFloatWidth w
.

Inductive CC_CmmLit : Set :=
| CmmInt: Integer -> Width -> CC_CmmLit
| CmmFloat: Rational -> forall (w:Width), isFloatWidth w -> CC_CmmLit
| CmmLabel: CLabel -> CC_CmmLit
| CmmLabelOff: CLabel -> Int -> CC_CmmLit
| CmmLabelDiffOff: CLabel -> CLabel -> Int -> Width -> CC_CmmLit
.

Inductive CmmExpr : Set :=
| CE_CmmLit: CC_CmmLit -> CmmExpr
| CE_CmmLoad: CmmExpr -> CC_CmmType -> CmmExpr
| CE_CmmReg: CmmReg -> CmmExpr
| CE_CmmMachOp: MachOp -> list CmmExpr -> CmmExpr
| CE_CmmRegOff : CmmReg -> Int -> CmmExpr
.

Definition cmmLabelType (lbl:CLabel) : CC_CmmType := bWord.

(*
Definition cmmLitType (l : CC_CmmLit) : CC_CmmType :=
  match l with
  | CmmInt _ width => cmmBits width
  | CmmFloat _ width pf => match width with
                           | W32 => cmmFloat
                           | W64 => cmmDouble
                           end
  | CmmLabel lbl => cmmLabelType lbl
  | CmmLabelOff lbl _ => cmmLabelType lbl
  | CmmLabelDiffOff _ _ _ width => cmmBits width
  end.
 *)

Definition localRegType (l:LocalReg) : CC_CmmType :=
  match l with
  | LR_LocalReg _ rep => rep
  end.

Definition globalRegType (g:GlobalReg) : CC_CmmType :=
  match g with
  | VanillaReg _ _ => bWord (* we might want to look at the second parameter *)
  | FloatReg _ => cmmFloat
  | DoubleReg _ => cmmDouble
  | LongReg _ => cmmBits W64
  | _ => bWord
  end.
                                         
Definition cmmRegType (r:CmmReg) : CC_CmmType :=
  match r with
  | CmmLocal reg => localRegType reg
  | CmmGlobal reg => globalRegType reg
  end.

(*
Fixpoint cmmExprType (e : CmmExpr) : CC_CmmType :=
  match e with
  | CE_CmmLit lit => cmmLitType lit
  | CE_CmmLoad _ rep => rep
  | CE_CmmReg reg => cmmRegType reg
  | CE_CmmMachOp op args => machOpResultType op (List.map cmmExprType args)
  | CE_CmmStackSlot _ _ => bWord
  | CE_CmmRegOff reg _ => cmmRegType reg
  end.
*)
