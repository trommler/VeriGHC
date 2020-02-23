(* Coq implementation of compiler/cmm/CmmExpr.hs *)
Require Import List.

Require Import BlockId.
Require Import Int.
Require Import Unique.
Require Import CmmMachOp.
Require Import CmmType.
Require Import CmmExpr.

Require Import CmmCore.CmmCoreType.

Require Import compcert.common.AST.

Inductive CC_LocalReg : Set :=
| CC_LR: Unique -> CC_CmmType -> CC_LocalReg.

Inductive GlobalReg : Set :=
| VanillaReg: Int -> VGcPtr -> GlobalReg
| FloatReg: Int -> GlobalReg
| DoubleReg: Int -> GlobalReg
| LongReg: Int -> GlobalReg
                    (* ... and some more *)
| BaseReg: GlobalReg
| PicBaseReg: GlobalReg
.

Inductive CC_CmmReg : Set :=
| CmmLocal: CC_LocalReg -> CC_CmmReg
| CmmGlobal: GlobalReg -> CC_CmmReg
.

Inductive CC_CmmLit : Set :=
| CmmInt: Integer -> { w : Width | isIntWidth w} -> CC_CmmLit
| CmmFloat: Rational -> {w : Width | isFloatWidth w} -> CC_CmmLit
| CmmLabel: CLabel -> CC_CmmLit
| CmmLabelOff: CLabel -> Int -> CC_CmmLit
| CmmLabelDiffOff: CLabel -> CLabel -> Int -> { w : Width | isIntWidth w} -> CC_CmmLit
.

Inductive CmmExpr : Set :=
| CE_CmmLit: CC_CmmLit -> CmmExpr
| CE_CmmLoad: CmmExpr -> CC_CmmType -> CmmExpr
| CE_CmmReg: CmmReg -> CmmExpr
| CE_CmmMachOp: MachOp -> list CmmExpr -> CmmExpr
| CE_CmmRegOff : CmmReg -> Int -> CmmExpr
.

Definition cmmLabelType (lbl:CLabel) : CC_CmmType := bWord.

Definition cmmLitType (l : CC_CmmLit) : CC_CmmType :=
  match l with
  | CmmInt _ width => CC_cmmBits width
  | CmmFloat _ width => CC_cmmFloat width
  | CmmLabel lbl => cmmLabelType lbl
  | CmmLabelOff lbl _ => cmmLabelType lbl
  | CmmLabelDiffOff _ _ _ width => CC_cmmBits width
  end.

Definition localRegType (l:CC_LocalReg) : CC_CmmType :=
  match l with
  | CC_LR _ rep => rep
  end.

Definition globalRegType (g:GlobalReg) : CC_CmmType :=
  match g with
  | VanillaReg _ _ => bWord (* we might want to look at the second parameter *)
  | FloatReg _ => CC_cmmFloat (exist _ W32 I)
  | DoubleReg _ => CC_cmmFloat (exist _ W64 I)
  | LongReg _ => b64
  | _ => bWord
  end.
                                         
Definition cmmRegType (r:CC_CmmReg) : CC_CmmType :=
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
  | CE_CmmRegOff reg _ => cmmRegType reg
  end.
*)
