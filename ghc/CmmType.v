(* Coq representation of compiler/cmm/CmmType.hs *)

Require Import GHC.Int.

Definition Length := Int.

Inductive CmmCat :=
| GcPtrCat: CmmCat
| BitsCat: CmmCat
| FloatCat: CmmCat
| VecCat: Length -> CmmCat -> CmmCat
.

Inductive Width :=
  W8 | W16 | W32 | W64 | W128 | W256 | W512.

Inductive CmmType :=
  CT_CmmType: CmmCat ->  Width -> CmmType.
