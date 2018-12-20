Require Import BinNums.
Require Import compcert.lib.Integers.

Definition Int := int64.
Definition Integer := Z.

Definition IntToZ (i:Int) : Z :=
  Int64.unsigned i.
