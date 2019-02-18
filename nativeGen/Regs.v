Require Import GHC.Int.
Require Import GHC.CmmType.
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


Definition litToImm (cl:CmmLit) : Imm :=
  match cl with
  | CmmInt i w                  => ImmInteger i (* TODO: narrow to width *)
  | CmmFloat f W32              => ImmFloat f
  | CmmFloat f W64              => ImmDouble f
  | CmmLabel l                  => ImmCLbl l
  | CmmLabelOff l off           => ImmIndex l off
  | CmmLabelDiffOff l1 l2 off _ => ImmConstantSum
                                     (ImmConstantDiff (ImmCLbl l1) (ImmCLbl l2))
                                     (ImmInt off)
  | _ => ImmLit (* TODO: panic, or even better a more precise type *)
  end.


Inductive AddrMode :=
| AddrRegReg:    Reg -> Reg -> AddrMode
| AddrRegImm:    Reg -> Imm -> AddrMode
.
