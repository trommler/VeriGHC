From iris.program_logic Require Export language ectx_language ectxi_language.
From stdpp Require Export strings.
From iris.algebra Require Import ofe.
From orc11 Require Export progress.

From compcert.lib Require Import Integers Floats.

From gpfsl.lang Require Import lang.

Require Import CmmType_sem. (* for Int16; TODO: Move to separate module *)

Require Import CmmExpr.
Require Import Unique.
Require Import CmmMachOp.


Axiom unique_to_string : Unique -> string.
Axiom label_to_loc : CLabel.CLabel -> loc.
Axiom rational_to_float : GHC.Real.Rational -> float.

Inductive value := VInt8 (b : byte)
                 | VInt16 (h : Int16.int)
                 | VInt32 (w : Int.int)
                 | VInt64 (d : Int64.int)
                 | VFloat (f : float32)
                 | VDouble (d : float).

(* Literals *)
Inductive lit := LitPoison
            | LitLoc (l : loc)
            | LitInt (n : Z)
            | LitFloat (f : float).

Instance lit_inhabited : Inhabited lit := populate LitPoison.

Definition cmmlit_to_lit (cl : CmmLit) : lit :=
  match cl with
  | CmmInt i _   => LitInt i
  | CmmLabel l   => LitLoc (label_to_loc l)
  | CmmFloat f _ => LitFloat (rational_to_float f)
  | _            => LitPoison
  end.
(** Expressions and values. *)

Inductive un_op := | NegOp | MinusUnOp.

Inductive bin_op := | PlusOp | MinusOp | ModOp | LeOp | LtOp | EqOp | OffsetOp.

Notation "[ ]" := (@nil binder) : binder_scope.
Notation "a :: b" := (@cons binder a%binder b%binder)
  (at level 60, right associativity) : binder_scope.
Notation "[ x1 ; x2 ; .. ; xn ]" :=
  (@cons binder x1%binder (@cons binder x2%binder
        (..(@cons binder xn%binder (@nil binder))..))) : binder_scope.
Notation "[ x ]" := (@cons binder x%binder (@nil binder)) : binder_scope.

Module base.
  (** Base expression language without views *)
  Inductive expr :=
  (* Basic operations *)
  | Lit (l : lit)
  | Var (x : string)
  | UnOp (op : un_op) (e: expr)
  | BinOp (op : bin_op) (e1 e2 : expr)
  | Case (e : expr) (el : list expr)
  (* Memory *)
  | Read (o : memOrder) (e : expr)
  | Write (o : memOrder) (e1 e2: expr)
  | CAS (e0 e1 e2 : expr) (orf or ow: memOrder)
  | FenceAcq
  | FenceRel
  | FenceSC
  | StuckE.

  Bind Scope expr_scope with expr.
  Delimit Scope expr_scope with E.

  Arguments UnOp _ _%E.
  Arguments BinOp _ _%E _%E.
  Arguments Case _%E _%E.
  Arguments Read _ _%E.
  Arguments Write _ _%E _%E.
  Arguments CAS _%E _%E _%E _ _.

Definition machop_arity (mo : MachOp) : nat :=
  match mo with
  | MO_Add _
  | MO_Sub _
  | MO_Eq _
  | MO_Ne _
  | MO_Mul _
  | MO_S_MulMayOflo _
  | MO_S_Quot _
  | MO_S_Rem _
  | MO_U_MulMayOflo _
  | MO_U_Quot _
  | MO_U_Rem _
  | MO_S_Ge _
  | MO_S_Le _
  | MO_S_Gt _
  | MO_S_Lt _
  | MO_U_Ge _
  | MO_U_Le _
  | MO_U_Gt _
  | MO_U_Lt _
  | MO_F_Add _
  | MO_F_Sub _
  | MO_F_Mul _
  | MO_F_Quot _
  | MO_F_Eq _
  | MO_F_Ne _
  | MO_F_Ge _
  | MO_F_Le _
  | MO_F_Gt _
  | MO_F_Lt _
  | MO_And _
  | MO_Or _
  | MO_Xor _
  | MO_Not _
  | MO_Shl _
  | MO_U_Shr _
  | MO_S_Shr _
    => 2%nat
  | MO_S_Neg _
  | MO_F_Neg _
  | MO_SF_Conv _ _
  | MO_FS_Conv _ _
  | MO_SS_Conv _ _
  | MO_UU_Conv _ _
  | MO_FF_Conv _ _
    => 1%nat
  | _
    => 0%nat
  end.

Definition machop_to_unop (mo : MachOp) : un_op :=
  match mo with
  | MO_S_Neg _ => MinusUnOp
  | _          => NegOp (* bogus *)
  end.

Definition cmm_unop_to_expr (mo : MachOp) (exprs : list expr) :=
  match exprs with
  | [x] => UnOp (machop_to_unop mo) x
  | _   => StuckE
  end.

Definition machop_to_binop (mo : MachOp) : bin_op :=
  match mo with
  | MO_Add _ => PlusOp
  | _        => EqOp (* bogus*)
  end.

Definition cmm_binop_to_expr (mo : MachOp) (exprs : list expr) :=
  match exprs with
  | [x1;x2] => BinOp (machop_to_binop mo) x1 x2
  | _       => StuckE
  end.

Definition cmm_machop_to_expr (op : MachOp) (exprs : list expr) : expr :=
  match machop_arity op with
  | 1%nat => cmm_unop_to_expr op exprs
  | 2%nat => cmm_binop_to_expr op exprs
  | _     => StuckE
  end.

Fixpoint cmmexpr_to_expr (ce : CmmExpr) : expr :=
  let fix cmmexprs_to_exprs (ces : list CmmExpr) : list expr :=
      match ces with
      | []         => []
      | ce :: ces' => cmmexpr_to_expr ce :: cmmexprs_to_exprs ces'
      end
  in match ce with
     | Mk_CmmLit cl          => Lit (cmmlit_to_lit cl)
     | CmmLoad ce' _         => Read NonAtomic (cmmexpr_to_expr ce')
     | Mk_CmmReg reg         => StuckE (* TODO *)
     | CmmMachOp op exprs    => cmm_machop_to_expr op (cmmexprs_to_exprs exprs)
     | CmmStackSlot area num => StuckE (* TODO *)
     | CmmRegOff reg off     => StuckE (* TODO *)
     end.

Inductive stmt := Goto (b : loc)
             | Return (e : expr)
             | IfS (e : expr) (s1 s2 : stmt)
             (* m: map from values of e to indices into bs, def: default *)
             | Switch (e : expr) (m : gmap Z nat) (bs : list stmt) (def : stmt)
             | Assign (e1 e2 : expr) (s : stmt)
             | SkipS (s : stmt)
             | StuckS (* stuck statement *)
             | ExprS (e : expr) (s : stmt)
.

Arguments Switch _%E _%E _%E.
