(* Coq representation of compiler/cmm/CmmType.hs *)
Require Import Eqdep.

Require Import compcert.lib.Integers.
Require Import GHC.Int.


Inductive CmmCat :=
| GcPtrCat: CmmCat
| BitsCat: CmmCat
| FloatCat: CmmCat
.

Definition CmmCat_eq (c1 c2 : CmmCat) : {c1=c2} + {c1<> c2}.
  decide equality.
Defined.

Inductive Width :=
  W8 | W16 | W32 | W64.

Definition Width_eq (w1 w2 : Width) : {w1=w2} + {w1<>w2}.
  decide equality.
Defined.

Inductive catMatchWidth (c:CmmCat) (w:Width) : Prop :=
| cmw_Bits: c=BitsCat -> catMatchWidth c w
| cmw_Ptr: c=GcPtrCat -> catMatchWidth c w
| cmw_Float: c=FloatCat -> w=W32 -> catMatchWidth c w
| cmw_Double: c=FloatCat -> w=W64 -> catMatchWidth c w
.


Inductive CC_CmmType :=
  CCT_CmmType: forall (c:CmmCat) (w:Width), catMatchWidth c w -> CC_CmmType.

Definition cmmBits (w:Width) : CC_CmmType :=
  CCT_CmmType BitsCat w (cmw_Bits _ _ eq_refl).

Definition cmmFloat : CC_CmmType :=
  CCT_CmmType FloatCat W32 (cmw_Float _ _ eq_refl eq_refl).

Definition cmmDouble : CC_CmmType :=
  CCT_CmmType FloatCat W64 (cmw_Double _ _ eq_refl eq_refl).

Definition b64 : CC_CmmType := cmmBits W64.
Definition bWord : CC_CmmType := cmmBits W64. (* Need DynFlags here *) 
