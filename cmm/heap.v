Require Import Peano_dec.
Require Import Compare_dec.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import compcert.common.Values.

Require Import CmmType_sem.

  (** We're going to store dynamic values -- a pair of an [stype] [t] and 
      a value of type [interp t]. *)
  Definition dynamic := sigT cmmTypeDenote.

  (** We will continue to use lists of pointers and values as the model for
      heaps.  However, to support an easy definition of disjoint union, we 
      will impose the additional constraint that the list is sorted in 
      (strictly) increasing order.  It's possible to capture this constraint by 
      defining heaps as a sigma type, where we include a proof that the heap 
      is sorted.  That makes some things easier (e.g., arguing that disjoint
      union is commutative) but makes other things harder.  For example, equality
      on sigmas would demand we need to compare proofs, and use proof-
      irrelevance.  To avoid this we can put in well-formedness
      constraints in just the right places. *)

  Definition ptr := nat.
  Definition ptr_eq := eq_nat_dec.
  Definition heap := list (ptr * dynamic).

  Definition empty_heap : heap := nil.

  (** Each pointer in h is greater than x *)
  Fixpoint list_greater (x:ptr) (h:heap) : Prop := 
    match h with 
      | nil => True
      | (y,v)::h' => x < y /\ list_greater x h' 
    end.

  (** A heap is well-formed if each pointer is less than the rest of the heap,
      and the rest of the heap is well-formed. *)
  Fixpoint wf(h:heap) : Prop := 
    match h with 
      | nil => True
      | (x,v)::h' => list_greater x h' /\ wf h'
    end.
  
  Fixpoint indom (x:ptr) (h:heap) : Prop := 
    match h with 
      | nil => False
      | (y,_)::h' => if ptr_eq x y then True else indom x h'
    end.

  (** A pointer is fresh for h when it's not in the domain of h. *)  
  Definition fresh x (h:heap) : Prop := ~ indom x h.

  Fixpoint lookup (x:ptr) (h:heap) : option dynamic := 
    match h with 
      | nil => None
      | (y,v)::h' => if ptr_eq x y then Some v else lookup x h'
    end.

  Fixpoint remove (x:ptr) (h:heap) : heap := 
    match h with 
      | nil => nil
      | (y,v)::h' => if ptr_eq x y then h' else (y,v)::(remove x h')
    end.

  (** Two heaps are disjoint when each pointer in [h1] is fresh for [h2]. *)
  Fixpoint disjoint (h1 h2:heap) : Prop := 
    match h1 with 
      | nil => True
      | (x,_)::h1' => ~indom x h2 /\ disjoint h1' h2
    end.

  (** Aha!  Insertion sort arises again. *)
  Fixpoint insert x (v:dynamic) (h:heap) : heap := 
    match h with 
      | nil => (x,v)::nil
      | (y,w)::h' => 
        if le_gt_dec x y then 
          (x,v)::(y,w)::h'
          else 
            (y,w)::(insert x v h')
    end.

  (** Merge two heaps using insertion *)
  Definition merge (h1 h2:heap) : heap := 
    List.fold_right (fun p h => insert (fst p) (snd p) h) h2 h1.
