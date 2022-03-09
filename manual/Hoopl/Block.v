
Inductive oc : Set :=
| O : oc
| C : oc.


Section Maybes.
  Parameter t : Type.

Inductive MaybeO : oc -> Type -> Type :=
  JustO    : t -> MaybeO O t
| NothingO :      MaybeO C t.
End Maybes.

Print MaybeO.

Inductive Block (n: oc -> oc -> Type) : oc -> oc -> Type :=
  BlockCO : n C O -> Block n O O          -> Block n C O
| BlockCC : n C O -> Block n O O -> n O C -> Block n C C
| BlockOC :          Block n O O -> n O C -> Block n O C
| BNil    : Block n O O
| BMiddle : n O O                      -> Block n O O
| BCat    : Block n O O -> Block n O O -> Block n O O
| BSnoc   : Block n O O -> n O O       -> Block n O O
| BCons   : n O O       -> Block n O O -> Block n O O.

Definition blockSplit {n:oc -> oc -> Type} (blk : Block n C C)
  : n C O * Block n O O * n O C :=
  match blk in Block _ e x return (match e, x with
                                   | C, C => n C%type O * Block n O O *n O C%type
                                   | _, _ => unit
                                   end) with
  | BlockCC _ f b t => (f, b, t)
  | _ => tt
  end.

Fixpoint go {n : oc -> oc -> Type} (blk : Block n O O) (acc : list (n O O))
  : list (n O O) :=
  match blk in Block _ e x return (match e, x with
                                   | O, O => list (n O O)
                                   | _, _ => unit
                                   end) with
  | BNil _       => acc
  | BMiddle _ n  => n :: acc
  | BCat _ b1 b2 => go b1 (go b2 acc)
  | BSnoc _ b1 n => go b1 (n :: acc)
  | BCons _ n b1 => n :: go b1 acc
  | _            => tt
  end.
