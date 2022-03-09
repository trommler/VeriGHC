(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Hoopl.Block.
Require Hoopl.Label.

(* Converted type declarations: *)

Definition Body' block (n : Hoopl.Block.oc -> Hoopl.Block.oc -> Type) :=
  (Hoopl.Label.LabelMap (block n Hoopl.Block.C Hoopl.Block.C))%type.

Section Graphs.
  Parameter e x : Hoopl.Block.oc.

  Inductive Graph' block n : Hoopl.Block.oc -> Hoopl.Block.oc -> Type
    := | GNil : Graph' block n Hoopl.Block.O Hoopl.Block.O
  |  GUnit
    : block n Hoopl.Block.O Hoopl.Block.O ->
      Graph' block n Hoopl.Block.O Hoopl.Block.O
  |  GMany
   : Hoopl.Block.MaybeO e (block n Hoopl.Block.O Hoopl.Block.C) ->
     Body' block n ->
     Hoopl.Block.MaybeO x (block n Hoopl.Block.C Hoopl.Block.O) ->
     Graph' block n e x.

Definition Graph :=
  (Graph' Hoopl.Block.Block)%type.

Definition Body n :=
  (Hoopl.Label.LabelMap (Hoopl.Block.Block n Hoopl.Block.C Hoopl.Block.C))%type.
End Graphs.

Arguments GNil {_} {_}.

(* FIXME: Check what is needed here: Arguments GUnit {_} _ {_}. *)

(* FIXME: Arguments GMany {_} {_} {_} {_}. *)

(* Converted value declarations: *)

(* Skipping all instances of class `Hoopl.Graph.NonLocal', including
   `Hoopl.Graph.NonLocal__Block' *)

(* Skipping all instances of class `Hoopl.Graph.LabelsPtr', including
   `Hoopl.Graph.LabelsPtr__list' *)

(* Skipping all instances of class `Hoopl.Graph.LabelsPtr', including
   `Hoopl.Graph.LabelsPtr__LabelSet' *)

(* Skipping all instances of class `Hoopl.Graph.LabelsPtr', including
   `Hoopl.Graph.LabelsPtr__Label' *)

(* Skipping all instances of class `Hoopl.Graph.LabelsPtr', including
   `Hoopl.Graph.LabelsPtr__C__9' *)

(* External variables:
     Type Hoopl.Block.Block Hoopl.Block.C Hoopl.Block.MaybeO Hoopl.Block.O
     Hoopl.Label.LabelMap
*)
