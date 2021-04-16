From gpfsl.lang Require Import lang.

Require Import CmmExpr.
Require Import Unique.
Require Import CmmMachOp.

Axiom unique_to_string : Unique -> string.
Axiom label_to_loc : CLabel.CLabel -> loc.

Definition cmmlit_to_lit (cl : CmmLit) : lit :=
  match cl with
  | CmmInt i _ => LitInt i
  | CmmLabel l => LitLoc (label_to_loc l)
  | _          => LitPoison
  end.

Definition machop_arity (mo : MachOp) : Z :=
  match mo with
  | MO_Add _   => 2
  | MO_S_Neg _ => 1
  | _          => 0
  end.

Definition machop_to_unop (mo : MachOp) : un_op :=
  match mo with
  | MO_S_Neg _ => MinusUnOp
  | _          => NegOp (* bogus *)
  end.

Definition cmm_unop_to_expr (mo : MachOp) (exprs : list expr) :=
  match exprs with
  | [x] => UnOp (machop_to_unop mo) x
  | _    => Var "fail"
  end.

Definition machop_to_binop (mo : MachOp) : bin_op :=
  match mo with
  | MO_Add _ => PlusOp
  | _        => EqOp (* bogus*)
  end.

Definition cmm_binop_to_expr (mo : MachOp) (exprs : list expr) :=
  match exprs with
  | [x1;x2] => BinOp (machop_to_binop mo) x1 x2
  | _       => Var "fail"
  end.

Definition cmm_machop_to_expr (op : MachOp) (exprs : list expr) : expr :=
  match machop_arity op with
  | 1 => cmm_unop_to_expr op exprs
  | 2 => cmm_binop_to_expr op exprs
  | _ => Var "fail"
  end.

Fixpoint cmmexpr_to_expr (ce : CmmExpr) : expr :=
  let fix cmmexprs_to_exprs (ces : list CmmExpr) : list expr :=
      match ces with
      | []         => []
      | ce :: ces' => cmmexpr_to_expr ce :: cmmexprs_to_exprs ces'
      end
  in match ce with
     | Mk_CmmLit cl       => Lit (cmmlit_to_lit cl)
     | CmmLoad ce' _      => Read NonAtomic (cmmexpr_to_expr ce')
     | CmmMachOp op exprs => cmm_machop_to_expr op (cmmexprs_to_exprs exprs)
     | _                  => Var "fail"
     end.
