Require Import BinNums. (* for ByteOff *)

Require Import CmmMachOp.
Require Import CmmExpr.
Require Import CmmSwitch.
Require Import Label.

Definition ULabel := CLabel.

Definition CmmActual := CmmExpr.
Definition CmmFormal := LocalReg.

Inductive ForeignTarget : Set :=
| FT_ForeignTarget : CmmExpr -> (* ForeignConvention -> *) ForeignTarget
| FT_PrimTarget : CallishMachOp -> ForeignTarget
.

Definition ByteOff := Z.

Inductive CmmNode : Set :=
| CmmEntry : ULabel (* -> CmmTickScope *) -> CmmNode
| CmmComment : (* FastString -> *) CmmNode
| CmmAssign : CmmReg -> CmmExpr -> CmmNode
| CmmStore : CmmExpr -> CmmExpr -> CmmNode
| CmmUnsafeForeignCall : ForeignTarget -> list CmmFormal -> list CmmActual
                                                         -> CmmNode
| CmmCondBranch : CmmExpr -> ULabel -> ULabel -> option bool -> CmmNode
| CmmBranch : ULabel -> CmmNode
| CmmSwitch : CmmExpr -> SwitchTargets -> CmmNode
| CmmCall   : CmmExpr -> option Label -> list GlobalReg -> ByteOff -> ByteOff
                                      -> ByteOff -> CmmNode
| CmmForeignCall : ForeignTarget -> list CmmFormal -> list CmmActual -> ULabel -> ByteOff -> ByteOff -> bool -> CmmNode
.
