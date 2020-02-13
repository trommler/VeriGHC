Require Import CmmType.

Require Import compcert.lib.Integers.
Require Import compcert.lib.Floats.
Require Import compcert.common.AST.

Module Wordsize_16.
  Definition wordsize := 16%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof. unfold wordsize; congruence. Qed.
End Wordsize_16.

Strategy opaque [Wordsize_16.wordsize].

Module Int16 := Make(Wordsize_16).

Strategy 0 [Wordsize_16.wordsize].

Notation short := Int16.int.

Notation long := Int64.int.

Definition cmmTypeDenote (t:CmmType) :=
  match t with
  | CT_CmmType BitsCat w => match w with
                            | W8 => byte
                            | W16 => short
                            | W32 => int
                            | W64 => long
                            | _ => unit
                            end
  | CT_CmmType FloatCat w => match w with
                             | W32 => float32
                             | W64 => float
                             | _ => unit
                             end
  | CT_CmmType GcPtrCat _ => long
  | CT_CmmType (VecCat _ _) _ => unit
  end.

Definition widthToChunk (w:Width) : memory_chunk :=
  match w with
  | W8  => Mint8unsigned
  | W16 => Mint16unsigned
  | W32 => Mint32
  | W64 => Mint64
  | _   => Many64 (* panic *)
  end.
(* TODO: add sign hint *)
Definition cmmTypeToChunk (t:CmmType) : memory_chunk :=
  match t with
  | CT_CmmType cat width =>
    match cat with
    | GcPtrCat => Many64 (* all pointers are 64-bit *)
    | BitsCat  => widthToChunk width
    | FloatCat => match width with
                  | W32 => Mfloat32
                  | W64 => Mfloat64
                  | _   => Many64 (* panic *)
                  end
    | VecCat l c => Many64 (* panic*)
    end
  end.
