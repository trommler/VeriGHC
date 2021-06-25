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

Inductive value := VInt8 (b : byte)
                 | VInt16 (h : Int16.int)
                 | VInt32 (w : Int.int)
                 | VInt64 (d : Int64.int)
                 | VFloat (f : float32)
                 | VDouble (d : float).

Definition cmmlit_to_lit (cl : CmmLit) : lit :=
  match cl with
  | CmmInt i _ => LitInt i
  | CmmLabel l => LitLoc (label_to_loc l)
  | _          => LitPoison
  end.

Definition machop_arity (mo : MachOp) : Z :=
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
    => 2
  | MO_S_Neg _
  | MO_F_Neg _
  | MO_SF_Conv _ _
  | MO_FS_Conv _ _
  | MO_SS_Conv _ _
  | MO_UU_Conv _ _
  | MO_FF_Conv _ _
    => 1
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
