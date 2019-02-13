Require Import GHC.Int.
Require Import GHC.CmmExpr. (* for CLabel *)
Require Import GHC.Reg.

Inductive Imm :=
| ImmInt:          Int -> Imm
| ImmInteger:      Integer -> Imm
| ImmCLbl:         CLabel -> Imm
| ImmLit:          (*SDoc -> *) Imm
| ImmIndex:        CLabel -> Int -> Imm
| ImmFloat:        Rational -> Imm
| ImmDouble:       Rational -> Imm
| ImmConstantSum:  Imm -> Imm -> Imm
| ImmConstantDiff: Imm -> Imm -> Imm
| LO:              Imm -> Imm
| HI:              Imm -> Imm
| HA:              Imm -> Imm
| HIGHERA:         Imm -> Imm
| HIGHESTA:        Imm -> Imm
.


Inductive AddrMode :=
| AddrRegReg:    Reg -> Reg -> AddrMode
| AddrRegImm:    Reg -> Imm -> AddrMode
.
