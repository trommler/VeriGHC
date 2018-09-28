Require Import List.
Import ListNotations.

Set Asymmetric Patterns.
Set Implicit Arguments.

Section OrdList.

  Variable a : Set.

  Inductive OrdList := OL: list a -> OrdList.

  Definition nilOL : OrdList := OL nil.
  Definition isNilOL (ol : OrdList) : bool :=
    match ol with
    | OL [] => true
    | _      => false
    end.

  Definition unitOL (x : a) : OrdList :=
    OL [x].

  Fixpoint snoc (l : list a) (x : a) :=
    match l with
    | [] => [x]
    | h :: t => h :: (snoc t x)
    end.
  Definition snocOL (ol : OrdList) (x : a) : OrdList :=
    match ol with
      OL l => OL (snoc l x)
    end.

  Definition consOL (x : a) (ol : OrdList) : OrdList :=
    match ol with
      OL l => OL (x :: l)
    end.

  Definition appOL (ol1 ol2 : OrdList) : OrdList :=
    match ol1, ol2 with
      OL l1, OL l2 => OL (app l1 l2)
    end.

  Definition concatOL (ols : list OrdList) : OrdList :=
    fold_right appOL nilOL ols.

(*
  Fixpoint lastOL (ol: OrdList) : a :=
    match ol with
    | OL []     => (* panic *)
    | OL [x]    => x
    | OL h :: t => lastOL (OL t)
                          end.
  *)                

  Definition fromOL (ol : OrdList) : list a :=
    match ol with
      OL l => l
    end.

  Definition toOL (l : list a) : OrdList :=
    OL l.

End OrdList.

Section OrdListFunctions.
  Variable a b : Set.

  Definition mapOL (f : a -> b) (ol : OrdList a) : OrdList b :=
    match ol with
      OL l => OL (map f l)
    end.

  Definition foldrOL (f : a -> b -> b) (x : b) (ol : OrdList a) : b :=
    match ol with
      OL l => fold_right f x l
    end.

  Definition foldlOL (f : b -> a -> b) (x : b) (ol : OrdList a) : b :=
    match ol with
      OL l => fold_left f l x
    end.
End OrdListFunctions.

