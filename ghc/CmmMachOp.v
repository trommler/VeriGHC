Require Import GHC.Int.
Require Import GHC.CmmType.

Inductive MachOp :=
  (* Integer operations (insensitive to signed/unsigned) *)
| MO_Add: Width -> MachOp
| MO_Sub: Width -> MachOp
| MO_Eq: Width -> MachOp
| MO_Ne: Width -> MachOp
| MO_Mul: Width -> MachOp
(* ... *)
.

Definition MachOp_eq_dec (m1 m2 : MachOp) : {m1 = m2} + {m1 <> m2}.
  decide equality; try (apply Width_eq).
Defined.

Definition comparisonResultRep := bWord. (* but Haskellers are not sure about it :-) *)
                                    
Definition machOpResultType (mo:MachOp) (tys:list CmmType) : CmmType :=
  match mo with
  | MO_Add r => cmmBits r (* should be type of first argument
                             if we are interested in GC-ptr-hood of values *)
  | MO_Sub r => cmmBits r (* same as above *)
  | MO_Mul r => cmmBits r
  | MO_Eq _ => comparisonResultRep
  | MO_Ne _ => comparisonResultRep
  end.

Inductive AtomicMachOp :=
| AMO_Add
| AMO_Sub
| AMO_And
| AMO_Nand
| AMO_Or
| AMO_Xor
.

Inductive CallishMachOp : Set :=
| MO_F64_Pwr
| MO_F64_Sin
| MO_F64_Cos
| MO_F64_Tan
| MO_F64_Sinh
| MO_F64_Cosh
| MO_F64_Tanh
| MO_F64_Asin
| MO_F64_Acos
| MO_F64_Atan
| MO_F64_Asinh
| MO_F64_Acosh
| MO_F64_Atanh
| MO_F64_Log
| MO_F64_Exp
| MO_F64_Fabs
| MO_F64_Sqrt
| MO_F32_Pwr
| MO_F32_Sin
| MO_F32_Cos
| MO_F32_Tan
| MO_F32_Sinh
| MO_F32_Cosh
| MO_F32_Tanh
| MO_F32_Asin
| MO_F32_Acos
| MO_F32_Atan
| MO_F32_Asinh
| MO_F32_Acosh
| MO_F32_Atanh
| MO_F32_Log
| MO_F32_Exp
| MO_F32_Fabs
| MO_F32_Sqrt
    
| MO_UF_Conv : Width -> CallishMachOp
             
| MO_S_QuotRem : Width -> CallishMachOp
| MO_U_QuotRem : Width -> CallishMachOp
| MO_U_QuotRem2 : Width -> CallishMachOp
| MO_Add2      : Width -> CallishMachOp
| MO_AddWordC  : Width -> CallishMachOp
| MO_SubWordC  : Width -> CallishMachOp
| MO_AddIntC   : Width -> CallishMachOp
| MO_SubIntC   : Width -> CallishMachOp
| MO_U_Mul2    : Width -> CallishMachOp
               
| MO_WriteBarrier
| MO_Touch         (* Keep variables live (when using interior pointers) *)
                   
| MO_Prefetch_Data : Int -> CallishMachOp
                   (*-- Prefetch hint. May change program performance but not
                     -- program behavior.
                     -- the Int can be 0-3. Needs to be known at compile time
                     -- to interact with code generation correctly.
                     --  TODO: add support for prefetch WRITES,
                     --  currently only exposes prefetch reads, which
                     -- would the majority of use cases in ghc anyways
*)

(*  -- These three MachOps are parameterised by the known alignment
  -- of the destination and source (for memcpy/memmove) pointers.
  -- This information may be used for optimisation in backends. *)
| MO_Memcpy : Int -> CallishMachOp
| MO_Memset : Int -> CallishMachOp
| MO_Memmove : Int -> CallishMachOp
| MO_Memcmp : Int -> CallishMachOp
            
| MO_PopCnt : Width -> CallishMachOp
| MO_Pdep : Width -> CallishMachOp
| MO_Pext : Width -> CallishMachOp
| MO_Clz : Width -> CallishMachOp
| MO_Ctz : Width -> CallishMachOp

| MO_BSwap : Width -> CallishMachOp

(*  -- Atomic read-modify-write. *)
| MO_AtomicRMW : Width -> AtomicMachOp -> CallishMachOp
| MO_AtomicRead : Width -> CallishMachOp
| MO_AtomicWrite : Width -> CallishMachOp
| MO_Cmpxchg : Width -> CallishMachOp
.
