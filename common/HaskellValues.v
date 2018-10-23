Require Import compcert.lib.Integers.
Require Import compcert.lib.Floats.
Require Import compcert.common.Values. (* C Values and definition of block *)

Definition haskell_int := int64. (* TODO: Should become a parameter *)

Inductive hval : Type :=
| HSundef : hval
| HSint : haskell_int -> hval
| HSsingle : float32 -> hval
| HSdouble : float -> hval
| HSptr : block -> ptrofs -> hval
.

Definition HStrue: hval := HSint Int64.one.
Definition HSfalse: hval := HSint Int64.zero.




