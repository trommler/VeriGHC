(* Coq implementation of compiler/cmm/CmmExpr.hs *)
Require Import List.

Require Import GHC.BlockId.
Require Import GHC.Int.
Require Import GHC.Unique.
Require Import GHC.CmmMachOp.
Require Import GHC.CmmType.

Require Import CmmCore.CmmCoreType.

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

(*
Lemma noW8isFloatWidth : isFloatWidth W8 -> False.
Proof.
  intro. inversion H; discriminate.
Qed.

Lemma noW16isFloatWidth : isFloatWidth W16 -> False.
Proof.
  intro. inversion H; discriminate.
Qed.

Definition floatLitType (w:Width) : isFloatWidth w -> CC_CmmType :=
  match w with
  | W8  => fun pf : isFloatWidth W8 => match noW8isFloatWidth pf with end
  | W16 => fun pf : isFloatWidth W16 => match noW16isFloatWidth pf with end
  | W32 => fun _ => cmmFloat
  | W64 => fun _ => cmmDouble
  end.
 *)

Definition cmmLitType (l : CC_CmmLit) : CC_CmmType :=
  match l with
  | CmmInt _ width => cmmBits width
  | CmmFloat _ width => cmmFloat width
  | CmmLabel lbl => cmmLabelType lbl
  | CmmLabelOff lbl _ => cmmLabelType lbl
  | CmmLabelDiffOff _ _ _ width => cmmBits width
  end.

Definition localRegType (l:LocalReg) : CC_CmmType :=
  match l with
  | LR_LocalReg _ rep => rep
  end.

Definition globalRegType (g:GlobalReg) : CC_CmmType :=
  match g with
  | VanillaReg _ _ => bWord (* we might want to look at the second parameter *)
  | FloatReg _ => cmmFloat (exist _ W32 I)
  | DoubleReg _ => cmmFloat (exist _ W64 I)
  | LongReg _ => b64
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
  | CE_CmmRegOff reg _ => cmmRegType reg
  end.
*)
