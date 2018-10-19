Require Import CmmExpr.

Definition ULabel := CLabel.

Definition CmmActual := CmmExpr.
Definition CmmFormal := LocalReg.

Inductive CmmNode : Set :=
| CmmEntry : ULabel (* -> CmmTickScope *) -> CmmNode
| CmmComment : (* FastString -> *) CmmNode
| CmmAssign : CmmReg -> CmmExpr -> CmmNode
| CmmStore : CmmExpr -> CmmExpr -> CmmNode
| CmmUnsafeForeignCall : ForeignTarget -> list CmmFormal -> list CmmActual
                                                         -> CmmNode
| CmmCondBranch : CmmExpr CmmWord -> Label -> Label -> option Bool -> CmmNode
| CmmBranch : ULabel -> CmmNode
| CmmSwitch : CmmExpr -> SwitchTargets -> CmmNode
| CmmCall   : CmmExpr -> option Label -> list GlobalReg -> ByteOff -> ByteOff
                                      -> ByteOff -> CmmNode
| CmmForeignCall : ForeignTarget -> list CmmFormal -> list CmmActual -> Label
                                 -> ByteOff -> ByteOff -> Bool -> CmmNode
.
