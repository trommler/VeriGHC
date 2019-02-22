Require Import GHC.Int.
Require Import GHC.CmmType.

Inductive MachOp :=
  (* Integer operations (insensitive to signed/unsigned) *)
| MO_Add: Width -> MachOp
| MO_Sub: Width -> MachOp
| MO_Eq: Width -> MachOp
| MO_Ne: Width -> MachOp
| MO_Mul: Width -> MachOp
(* Signed multiply/divide *)
| MO_S_MulMayOflo: Width -> MachOp
| MO_S_Quot: Width -> MachOp
| MO_S_Rem: Width -> MachOp
| MO_S_Neg: Width -> MachOp
(* Unsigned multiply/divide *)
| MO_U_MulMayOflo: Width -> MachOp
| MO_U_Quot: Width -> MachOp
| MO_U_Rem: Width -> MachOp
(* Signed comparisons *)
| MO_S_Ge: Width -> MachOp
| MO_S_Le: Width -> MachOp
| MO_S_Gt: Width -> MachOp
| MO_S_Lt: Width -> MachOp
(* Unsigned comparisons *)
| MO_U_Ge: Width -> MachOp
| MO_U_Le: Width -> MachOp
| MO_U_Gt: Width -> MachOp
| MO_U_Lt: Width -> MachOp
(* Floating point arithmetic *)
| MO_F_Add: Width -> MachOp
| MO_F_Sub: Width -> MachOp
| MO_F_Neg: Width -> MachOp
| MO_F_Mul: Width -> MachOp
| MO_F_Quot: Width -> MachOp
(* Floating point comparison *)
| MO_F_Eq: Width -> MachOp
| MO_F_Ne: Width -> MachOp
| MO_F_Ge: Width -> MachOp
| MO_F_Le: Width -> MachOp
| MO_F_Gt: Width -> MachOp
| MO_F_Lt: Width -> MachOp
(* Bitwise operations.  Not all of these may be supported
   at all sizes, and only integral Widths are valid. *)
| MO_And: Width -> MachOp
| MO_Or: Width -> MachOp
| MO_Xor: Width -> MachOp
| MO_Not: Width -> MachOp
| MO_Shl: Width -> MachOp
| MO_U_Shr: Width -> MachOp
| MO_S_Shr: Width -> MachOp
(* Conversions.  Some of these will be NOPs.
   Floating-point conversions use the signed variant. *)
| MO_SF_Conv: Width -> Width -> MachOp
| MO_FS_Conv: Width -> Width -> MachOp
| MO_SS_Conv: Width -> Width -> MachOp
| MO_UU_Conv: Width -> Width -> MachOp
| MO_XX_Conv: Width -> Width -> MachOp
| MO_FF_Conv: Width -> Width -> MachOp
(* Vector element insertion and extraction operations *)
| MO_V_Insert: Length -> Width -> MachOp
| MO_V_Extract: Length -> Width -> MachOp
(* Integer vector operations *)
| MO_V_Add: Length -> Width -> MachOp
| MO_V_Sub: Length -> Width -> MachOp
| MO_V_Mul: Length -> Width -> MachOp
(* Signed vector multiply/divide *)
| MO_VS_Quot: Length -> Width -> MachOp
| MO_VS_Rem: Length -> Width -> MachOp
| MO_VS_Neg: Length -> Width -> MachOp
(* Unsigned vector multiply/divide *)
| MO_VU_Quot: Length -> Width -> MachOp
| MO_VU_Rem: Length -> Width -> MachOp
(* Floting point vector element insertion and extraction operations *)
| MO_VF_Insert: Length -> Width -> MachOp
| MO_VF_Extract: Length -> Width -> MachOp
(* Floating point vector operations *)
| MO_VF_Add: Length -> Width -> MachOp
| MO_VF_Sub: Length -> Width -> MachOp
| MO_VF_Neg: Length -> Width -> MachOp
| MO_VF_Mul: Length -> Width -> MachOp
| MO_VF_Quot: Length -> Width -> MachOp
(* Alignment check (for -falignment-sanitisation) *)
| MO_AlignmentCheck: Int -> Width -> MachOp
.

(*
Definition MachOp_eq_dec (m1 m2 : MachOp) : {m1 = m2} + {m1 <> m2}.
  decide equality; try (apply Width_eq).
Defined.
*)
Definition comparisonResultRep := bWord. (* but Haskellers are not sure about it :-) *)
                                    
Definition machOpResultType (mo:MachOp) (tys:list CmmType) : CmmType :=
  match mo with
  | MO_Add r => match tys with
                | nil => cmmBits r (* should never happen*)
                | cons h _ => h
                end
  | MO_Sub r => match tys with
                | nil => cmmBits r (* should never happen*)
                | cons h _ => h
                end
  | MO_Mul r
  | MO_S_MulMayOflo r
  | MO_S_Quot r
  | MO_S_Rem  r
  | MO_S_Neg  r
  | MO_U_MulMayOflo r
  | MO_U_Quot r
  | MO_U_Rem  r => cmmBits r
  | MO_Eq _
  | MO_Ne _
  | MO_S_Ge _
  | MO_S_Le _
  | MO_S_Gt _
  | MO_S_Lt _
  | MO_U_Ge _
  | MO_U_Le _
  | MO_U_Gt _
  | MO_U_Lt _ => comparisonResultRep
  | MO_F_Add r
  | MO_F_Sub r
  | MO_F_Mul r
  | MO_F_Quot r
  | MO_F_Neg r => cmmFloat r
  | MO_F_Eq  _
  | MO_F_Ne  _
  | MO_F_Ge  _
  | MO_F_Le  _
  | MO_F_Gt  _
  | MO_F_Lt  _  => comparisonResultRep
  | MO_And r
  | MO_Or r
  | MO_Xor r => match tys with
                | nil => cmmBits r (* should never happen*)
                | cons h _ => h
                end
  | MO_Not   r
  | MO_Shl   r
  | MO_U_Shr r
  | MO_S_Shr r => cmmBits r
  | MO_SS_Conv _ to
  | MO_UU_Conv _ to
  | MO_XX_Conv _ to
  | MO_FS_Conv _ to
  | MO_SF_Conv _ to
  | MO_FF_Conv _ to => cmmFloat to
  | MO_V_Insert  l w => cmmVec l (cmmBits w)
  | MO_V_Extract _ w => cmmBits w
  | MO_V_Add l w
  | MO_V_Sub l w
  | MO_V_Mul l w
  | MO_VS_Quot l w
  | MO_VS_Rem  l w
  | MO_VS_Neg  l w
  | MO_VU_Quot l w
  | MO_VU_Rem  l w => cmmVec l (cmmBits w)
  | MO_VF_Insert  l w => cmmVec l (cmmFloat w)
  | MO_VF_Extract _ w => cmmFloat w
  | MO_VF_Add  l w
  | MO_VF_Sub  l w
  | MO_VF_Mul  l w
  | MO_VF_Quot l w
  | MO_VF_Neg  l w => cmmVec l (cmmFloat w)
  | MO_AlignmentCheck _ r => match tys with
                             | nil => cmmBits r (* should never happen*)
                             | cons h _ => h
                             end 
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
