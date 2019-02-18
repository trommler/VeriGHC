(* compiler/nativeGen/Reg.hs *)
Require Import GHC.Int.
Require Import GHC.Unique.

Definition RegNo := Int.

Inductive RealReg :=
| RealRegSingle: RegNo -> RealReg
| RealRegPair:   RegNo -> RegNo -> RealReg
.

Inductive VirtualReg :=
| VirtualRegI:   Unique -> VirtualReg
| VirtualRegHi:  Unique -> VirtualReg
| VirtualRegF:   Unique -> VirtualReg
| VirtualRegD:   Unique -> VirtualReg
| VirtualRegSSE: Unique -> VirtualReg
.

Inductive Reg :=
| RegVirtual: VirtualReg -> Reg
| RegReal:    RealReg -> Reg
.
