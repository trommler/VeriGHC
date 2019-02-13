Require Import GHC.Cmm.
Require Import GHC.CmmExpr. (* for CLabel *)
Require Import GHC.BlockId.
Require Import GHC.Int.
Require Import GHC.Reg.

Require Import nativeGen.Regs.
Require Import nativeGen.Format.
Require Import nativeGen.Cond.

Inductive RI :=
| RIReg: Reg -> RI
| RIImm: Imm -> RI
.

Inductive Instr := 
| COMMENT:  (* FastString -> *) Instr 
| LDATA:    section -> CmmStatics -> Instr
| NEWBLOCK: BlockId -> Instr
| DELTA:    Int -> Instr
| LD:       Format -> Reg -> AddrMode -> Instr
| LDFAR:    Format -> Reg -> AddrMode -> Instr
| LDR:      Format -> Reg -> AddrMode -> Instr
| LA:       Format -> Reg -> AddrMode -> Instr
| ST:       Format -> Reg -> AddrMode -> Instr
| STFAR:    Format -> Reg -> AddrMode -> Instr
| STU:      Format -> Reg -> AddrMode -> Instr
| STC:      Format -> Reg -> AddrMode -> Instr
| LIS:      Reg -> Imm -> Instr
| LI:       Reg -> Imm -> Instr
| MR:       Reg -> Reg -> Instr
| CMP:      Format -> Reg -> RI -> Instr
| CMPL:     Format -> Reg -> RI -> Instr
| BCC:      Cond -> BlockId -> option bool -> Instr
| BCCFAR:   Cond -> BlockId -> option bool -> Instr
| JMP:      CLabel -> Instr
| MTCTR:    Reg -> Instr
| BCTR:     list (option BlockId) -> option CLabel -> Instr
| BL:       CLabel -> list Reg -> Instr
| BCTRL:    list Reg -> Instr
| ADD:      Reg -> Reg -> RI -> Instr
| ADDO:     Reg -> Reg -> Reg -> Instr
| ADDC:     Reg -> Reg -> Reg -> Instr
| ADDE:     Reg -> Reg -> Reg -> Instr
| ADDZE:    Reg -> Reg -> Instr
| ADDIS:    Reg -> Reg -> Imm -> Instr
| SUBF:     Reg -> Reg -> Reg -> Instr
| SUBFO:    Reg -> Reg -> Reg -> Instr
| SUBFC:    Reg -> Reg -> RI -> Instr
| SUBFE:    Reg -> Reg -> Reg -> Instr
| MULL:     Format -> Reg -> Reg -> RI -> Instr
| MULLO:    Format -> Reg -> Reg -> Reg -> Instr
| MFOV:     Format -> Reg -> Instr
| MULHU:    Format -> Reg -> Reg -> Reg -> Instr
| DIV:      Format -> bool -> Reg -> Reg -> Reg -> Instr
| AND:      Reg -> Reg -> RI -> Instr
| ANDC:     Reg -> Reg -> Reg -> Instr
| NAND:     Reg -> Reg -> Reg -> Instr
| OR:       Reg -> Reg -> RI -> Instr
| ORIS:     Reg -> Reg -> Imm -> Instr
| XOR:      Reg -> Reg -> RI -> Instr
| XORIS:    Reg -> Reg -> Imm -> Instr
| EXTS:     Format -> Reg -> Reg -> Instr
| CNTLZ:    Format -> Reg -> Reg -> Instr
| NEG:      Reg -> Reg -> Instr
| NOT:      Reg -> Reg -> Instr
| SL:       Format -> Reg -> Reg -> RI -> Instr
| SR:       Format -> Reg -> Reg -> RI -> Instr
| SRA:      Format -> Reg -> Reg -> RI -> Instr
| RLWINM:   Reg -> Reg -> Int -> Int -> Int -> Instr
| CLRLI:    Format -> Reg -> Reg -> Int -> Instr
| CLRRI:    Format -> Reg -> Reg -> Int -> Instr
| FADD:     Format -> Reg -> Reg -> Reg -> Instr
| FSUB:     Format -> Reg -> Reg -> Reg -> Instr
| FMUL:     Format -> Reg -> Reg -> Reg -> Instr
| FDIV:     Format -> Reg -> Reg -> Reg -> Instr
| FABS:     Reg -> Reg -> Instr
| FNEG:     Reg -> Reg -> Instr
| FCMP:     Reg -> Reg -> Instr
| FCTIWZ:   Reg -> Reg -> Instr
| FCTIDZ:   Reg -> Reg -> Instr
| FCFID:    Reg -> Reg -> Instr
| FRSP:     Reg -> Reg -> Instr
| CRNOR:    Int -> Int -> Int -> Instr
| MFCR:     Reg -> Instr
| MFLR:     Reg -> Instr
| FETCHPC:  Reg -> Instr
| HWSYNC:   Instr
| ISYNC:    Instr
| LWSYNC:   Instr
| NOP:      Instr
.
