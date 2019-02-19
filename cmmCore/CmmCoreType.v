(* Coq representation of compiler/cmm/CmmType.hs *)
Require Import Eqdep.

Require Import compcert.lib.Integers.

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
  
Definition cmmBits (w : {w' : Width | isIntWidth w'}) : CC_CmmType :=
  match w with
  | exist width pf => exist _ (CT_CmmType BitsCat width) pf
  end.

Definition cmmFloat (w : {w' : Width | isFloatWidth w'}) : CC_CmmType :=
  match w with
  | exist width pf => exist _ (CT_CmmType FloatCat width) pf
  end.


Definition b64 : CC_CmmType := cmmBits (exist _ W64 I).
Definition bWord : CC_CmmType := cmmBits (exist _ W64 I). (* Need DynFlags here *) 
