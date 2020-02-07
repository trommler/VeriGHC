(* Coq representation of compiler/cmm/CmmType.hs *)
Require Import Eqdep.
Require Import Coq.ZArith.BinInt. 

Require Import compcert.lib.Integers.
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
  apply Int64.eq_dec.
Defined.

Inductive Width :=
  W8 | W16 | W32 | W64 | W80 | W128 | W256 | W512.

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

Definition cmmBits : Width -> CmmType :=
  CT_CmmType BitsCat.

Definition cmmFloat : Width -> CmmType :=
  CT_CmmType FloatCat.

Definition b64 : CmmType := cmmBits W64.
Definition bWord : CmmType := cmmBits W64. (* Need DynFlags here *) 

Local Open Scope Z_scope.


Definition widthFromBytes (n:Int) : Width :=
  match n with
  | Int64.mkint x _ => match x with
                       | 1 => W8
                       | 2 => W16
                       | 4 => W32
                       | 8 => W64
                       | 16 => W128
                       | 32 => W256
                       | 64 => W512
                       | _ => W80
                       end
  end.


Definition widthInBytes (w:Width) : Int :=
  Int64.repr (match w with
              | W8 => 1
              | W16 => 2
              | W32 => 4
              | W64 => 8
              | W128 => 16
              | W256 => 32
              | W512 => 64
              | _ => 0
              end)
.

Definition cmmVec (n:Int) (t:CmmType) : CmmType :=
  match t with
  | CT_CmmType cat w => CT_CmmType (VecCat n cat) (widthFromBytes (Int64.mul n (widthInBytes w)))
  end.
