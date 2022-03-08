Axiom C : Type.
Axiom O : Type.

Section Maybes.
  Parameter t : Type.

Inductive MaybeO : Type -> Type -> Type :=
  JustO    : t -> MaybeO O t
| NothingO :      MaybeO C t.
End Maybes.

Inductive Block (n:Type-> Type-> Type) : Type -> Type -> Type :=
  BlockCO : n C O -> Block n O O          -> Block n C O
| BlockCC : n C O -> Block n O O -> n O C -> Block n C C
| BlockOC :          Block n O O -> n O C -> Block n O C
| BNil    : Block n O O
| BMiddle : n O O                      -> Block n O O
| BCat    : Block n O O -> Block n O O -> Block n O O
| BSnoc   : Block n O O -> n O O       -> Block n O O
| BCons   : n O O       -> Block n O O -> Block n O O.
