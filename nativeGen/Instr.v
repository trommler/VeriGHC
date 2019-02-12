

(*
Inductive Instr := 
| COMMENT:  FastString -> Instr 
| LDATA:    Section -> CmmStatics -> Instr
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

    | BCC     Cond BlockId (Maybe Bool) -- cond, block, hint
    | BCCFAR  Cond BlockId (Maybe Bool) -- cond, block, hint
                                    --   hint:
                                    --    Just True:  branch likely taken
                                    --    Just False: branch likely not taken
                                    --    Nothing:    no hint
    | JMP     CLabel                -- same as branch,
                                    -- but with CLabel instead of block ID
    | MTCTR   Reg
    | BCTR    [Maybe BlockId] (Maybe CLabel) -- with list of local destinations, and jump table location if necessary
    | BL      CLabel [Reg]          -- with list of argument regs
    | BCTRL   [Reg]

    | ADD     Reg Reg RI            -- dst, src1, src2
    | ADDO    Reg Reg Reg           -- add and set overflow
    | ADDC    Reg Reg Reg           -- (carrying) dst, src1, src2
    | ADDE    Reg Reg Reg           -- (extended) dst, src1, src2
    | ADDZE   Reg Reg               -- (to zero extended) dst, src
    | ADDIS   Reg Reg Imm           -- Add Immediate Shifted dst, src1, src2
    | SUBF    Reg Reg Reg           -- dst, src1, src2 ; dst = src2 - src1
    | SUBFO   Reg Reg Reg           -- subtract from and set overflow
    | SUBFC   Reg Reg RI            -- (carrying) dst, src1, src2 ;
                                    -- dst = src2 - src1
    | SUBFE   Reg Reg Reg           -- (extended) dst, src1, src2 ;
                                    -- dst = src2 - src1
    | MULL    Format Reg Reg RI
    | MULLO   Format Reg Reg Reg    -- multiply and set overflow
    | MFOV    Format Reg            -- move overflow bit (1|33) to register
                                    -- pseudo-instruction; pretty printed as
                                    -- mfxer dst
                                    -- extr[w|d]i dst, dst, 1, [1|33]
    | MULHU   Format Reg Reg Reg
    | DIV     Format Bool Reg Reg Reg
    | AND     Reg Reg RI            -- dst, src1, src2
    | ANDC    Reg Reg Reg           -- AND with complement, dst = src1 & ~ src2
    | NAND    Reg Reg Reg           -- dst, src1, src2
    | OR      Reg Reg RI            -- dst, src1, src2
    | ORIS    Reg Reg Imm           -- OR Immediate Shifted dst, src1, src2
    | XOR     Reg Reg RI            -- dst, src1, src2
    | XORIS   Reg Reg Imm           -- XOR Immediate Shifted dst, src1, src2

    | EXTS    Format Reg Reg
    | CNTLZ   Format Reg Reg

    | NEG     Reg Reg
    | NOT     Reg Reg

    | SL      Format Reg Reg RI            -- shift left
    | SR      Format Reg Reg RI            -- shift right
    | SRA     Format Reg Reg RI            -- shift right arithmetic

    | RLWINM  Reg Reg Int Int Int   -- Rotate Left Word Immediate then AND with Mask
    | CLRLI   Format Reg Reg Int    -- clear left immediate (extended mnemonic)
    | CLRRI   Format Reg Reg Int    -- clear right immediate (extended mnemonic)

    | FADD    Format Reg Reg Reg
    | FSUB    Format Reg Reg Reg
    | FMUL    Format Reg Reg Reg
    | FDIV    Format Reg Reg Reg
    | FABS    Reg Reg               -- abs is the same for single and double
    | FNEG    Reg Reg               -- negate is the same for single and double prec.

    | FCMP    Reg Reg

    | FCTIWZ  Reg Reg           -- convert to integer word
    | FCTIDZ  Reg Reg           -- convert to integer double word
    | FCFID   Reg Reg           -- convert from integer double word
    | FRSP    Reg Reg           -- reduce to single precision
                                -- (but destination is a FP register)

    | CRNOR   Int Int Int       -- condition register nor
    | MFCR    Reg               -- move from condition register

    | MFLR    Reg               -- move from link register
    | FETCHPC Reg               -- pseudo-instruction:
                                -- bcl to next insn, mflr reg
    | HWSYNC                    -- heavy weight sync
    | ISYNC                     -- instruction synchronize
    | LWSYNC                    -- memory barrier
    | NOP                       -- no operation, PowerPC 64 bit
                                -- needs this as place holder to
                                -- reload TOC pointer
*)
