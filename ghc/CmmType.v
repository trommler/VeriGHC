(* Coq representation of compiler/cmm/CmmType.hs *)
Require Import Eqdep.

Require Import GHC.Int.

Definition Length := Int.

Inductive CmmCat :=
| GcPtrCat: CmmCat
| BitsCat: CmmCat
| FloatCat: CmmCat
| VecCat: Length -> CmmCat -> CmmCat
.

Definition CmmCat_eq (c1 c2 : CmmCat) : {c1=c2} + {c1<> c2}.
  decide equality.
  decide equality.
Defined.

Inductive Width :=
  W8 | W16 | W32 | W64 | W128 | W256 | W512.

Definition Width_eq (w1 w2 : Width) : {w1=w2} + {w1<>w2}.
  decide equality.
Defined.


Inductive CmmType :=
  CT_CmmType: CmmCat ->  Width -> CmmType.

Definition CmmType_eq (t1 t2 : CmmType) : {t1=t2} + {t1<>t2}.
  decide equality.
  apply Width_eq.
  apply CmmCat_eq.
Defined.
