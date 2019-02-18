(* Coq representation of compiler/cmm/CmmType.hs *)
Require Import Eqdep.

Require Import compcert.lib.Integers.

Require Import GHC.CmmType.
Require Import GHC.Int.


Inductive catMatchWidth (c:CmmCat) (w:Width) : Prop :=
| cmw_Bits: c=BitsCat -> catMatchWidth c w
| cmw_Ptr: c=GcPtrCat -> catMatchWidth c w
| cmw_Float: c=FloatCat -> w=W32 -> catMatchWidth c w
| cmw_Double: c=FloatCat -> w=W64 -> catMatchWidth c w
.

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
(*  
  CCT_CmmType: forall (c:CmmCat) (w:Width), catMatchWidth c w -> CC_CmmType.
 *)
  
Definition cmmBits (w : {w' : Width | isIntWidth w'}) : CC_CmmType.
  refine (
  match w with
  | exist width pf => exist _ (CT_CmmType BitsCat width) _
  end).
  trivial.
Defined.


Definition cmmFloat (w : {w' : Width | isFloatWidth w'}) : CC_CmmType.
  refine (
  match w with
  | exist width pf => exist _ (CT_CmmType FloatCat width) _
  end).
  trivial.
Defined.

(*Definition W64_intWidth : {w' : Width | isIntWidth W64} :=
  exist _ W64 isIntWidth.
 *)

Definition intWidthW64 : isIntWidth W64.
  reflexivity.
Defined.

Definition b64 : CC_CmmType := cmmBits (exist _ W64 intWidthW64).
Definition bWord : CC_CmmType := cmmBits (exist _ W64 intWidthW64). (* Need DynFlags here *) 
