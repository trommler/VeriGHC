(* Coq representation of compiler/cmm/CmmType.hs *)
Require Import Eqdep.

Require Import compcert.lib.Integers.
Require Import compcert.lib.Floats.

Require Import GHC.CmmType.
Require Import GHC.Int.

Definition isIntWidth (w:Width) : Prop :=
  match w with
  | W8
  | W16
  | W32
  | W64 => True
  | _ => False
  end.

Definition isFloatWidth (w:Width) : Prop :=
  match w with
  | W32
  | W64 => True
  | _ => False
  end.

Definition isCoreCmmType (t:CmmType) : Prop :=
  match t with
  | CT_CmmType c w => match c with
                      | BitsCat
                      | GcPtrCat => isIntWidth w
                      | FloatCat => isFloatWidth w
                      | VecCat _ _ => False
                      end
  end.
           
Definition CC_CmmType := sig isCoreCmmType.
  
Definition CC_cmmBits (w : {w' : Width | isIntWidth w'}) : CC_CmmType :=
  match w with
  | exist width pf => exist _ (cmmBits width) pf
  end.

Definition CC_cmmFloat (w : {w' : Width | isFloatWidth w'}) : CC_CmmType :=
  match w with
  | exist width pf => exist _ (cmmFloat width) pf
  end.


Definition b64 : CC_CmmType := CC_cmmBits (exist _ W64 I).
Definition bWord : CC_CmmType := CC_cmmBits (exist _ W64 I). (* Need DynFlags here *) 

(* Semantics *)

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

Definition CC_CmmTypeDenote (ct:CC_CmmType): Type :=
  match ct with
  | exist t pf => match t with
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
                  end
  end.

(* We want to make use of CC_CmmType proof here so we don't have to return
a bogus unit type *)
