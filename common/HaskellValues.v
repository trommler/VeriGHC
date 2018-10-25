Require Import compcert.lib.Integers.
Require Import compcert.lib.Floats.
Require Import compcert.common.Values. (* C Values and definition of block *)

Definition haskell_int := int64. (* TODO: Should become a parameter *)

Inductive hval : Type := (* This should be a parameter too *)
| HSundef : hval
| HSint : haskell_int -> hval
| HSsingle : float32 -> hval
| HSdouble : float -> hval
| HSptr : block -> ptrofs -> hval
.

Definition HStrue: hval := HSint Int64.one.
Definition HSfalse: hval := HSint Int64.zero.

Definition from_bool (b :bool) : hval :=
  if b then HStrue else HSfalse.

Module HaskellVal.
  
  Definition eq (x y : hval) : {x=y} + {x<>y}.
  Proof.
    decide equality.
    apply Int64.eq_dec.
    apply Float32.eq_dec.
    apply Float.eq_dec.
    apply Ptrofs.eq_dec.
    apply eq_block.
  Defined.
  Global Opaque eq.

  Definition add (v1 v2 : hval) : hval :=
    match v1, v2 with
    | HSint n1, HSint n2 => HSint (Int64.add n1 n2)
    | _, _ => HSundef
    end. (* TODO: add pointer arithmetic *)

  Definition sub (v1 v2 : hval) : hval :=
    match v1, v2 with
    | HSint n1, HSint n2 => HSint (Int64.sub n1 n2)
    | _, _ => HSundef
    end. (* TODO: add pointer arithmetic *)

  Definition mul (v1 v2 : hval) : hval :=
    match v1, v2 with
    | HSint n1, HSint n2 => HSint (Int64.mul n1 n2)
    | _, _ => HSundef
    end.

  Section COMPARISONS.

    Definition cmp_bool (c : comparison) (v1 v2 : hval) : option bool :=
      match v1, v2 with
      | HSint n1, HSint n2 => Some (Int64.cmp c n1 n2)
      | _, _ => None
      end.

    Definition of_optbool (ob: option bool): hval :=
      match ob with
      | Some true => HStrue
      | Some false => HSfalse
      | None => HSundef
      end.

    Definition cmp (c: comparison) (v1 v2: hval): hval :=
      of_optbool (cmp_bool c v1 v2).

  End COMPARISONS.

End HaskellVal.
