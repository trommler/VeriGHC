Require Import Coq.Lists.List.
Import ListNotations.
Require Import ZArith.

Require Import compcert.common.Memory.
Require Import compcert.common.AST.
Require Import compcert.common.Values.

Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.

Require Import CmmExpr.
Require Import CmmType.
Require Import CmmMachOp.
Require Import Unique.
Require Import CLabel.

Require Import CmmType_sem.
Require Import Identifiers.

(* FIXME: Implement all literals *)

Axiom label_to_block : CLabel -> block.
Axiom int_to_long : Num.Int -> long.

Definition cmmLitDenote (l : CmmLit) : option val :=
  match l with
  | CmmInt n w => match w with
                  | W8  => Some (Vint (Int.repr n))
                  | W16 => Some (Vint (Int.repr n))
                  | W32 => Some (Vint (Int.repr n))
                  | W64 => Some (Vlong (Int64.repr n))
                  | _   => None
                  end
  | CmmFloat rat w => match w with
                      | W32 => None
                      | W64 => None
                      | _ => None
                      end
  | CmmLabel lab => Some (Vptr (label_to_block lab) (Ptrofs.of_int64 Int64.zero))
  | CmmLabelOff lab off => Some (Vptr (label_to_block lab)
                                      (Ptrofs.of_int64 (int_to_long off)))
  | CmmLabelDiffOff _ _ _ => None (* FIXME: See issue #6 *)
  | CmmBlock blk => None (* Some (Vptr blk (Ptrofs.of_int64 Int64.zero)) *)
  | CmmHighStackMark => None
  | _ => None (* CmmVec *)
  end.


(* FIXME: Define what valid pointers are in Cmm *)
Definition all_ptr_valid (b:block) (off:Z) : bool := true.

Definition moDenote (mo : MachOp) (ps : list (option val)) : option val :=
  match mo,ps with
  | MO_Add _, [Some v1;Some v2] => Some (Val.addl v1 v2)
  | MO_Sub _, [Some v1;Some v2] => Some (Val.subl v1 v2)
  | MO_Eq _,  [Some v1;Some v2] => Val.cmpl Ceq v1 v2
  | MO_Ne _,  [Some v1;Some v2] => Val.cmpl Cne v1 v2
  | MO_Mul _, [Some v1;Some v2] => Some (Val.mull v1 v2)
  | MO_S_MulMayOflo _, [Some v1;Some v2] => None
  | MO_S_Quot _, [Some v1;Some v2] => Val.divls v1 v2
  | MO_S_Rem _, [Some v1;Some v2] => Val.modls v1 v2
  | MO_S_Neg _, [Some v] => Some (Val.negl v)
(* Unsigned multiply/divide *)
  | MO_U_MulMayOflo _, [Some v1;Some v2] => None
  | MO_U_Quot _, [Some v1;Some v2] => Val.divlu v1 v2
  | MO_U_Rem _, [Some v1;Some v2] => Val.modlu v1 v2
(* Signed comparisons *)
  | MO_S_Ge _, [Some v1;Some v2] => Val.cmpl Cge v1 v2
  | MO_S_Le _, [Some v1;Some v2] => Val.cmpl Cle v1 v2
  | MO_S_Gt _, [Some v1;Some v2] => Val.cmpl Cgt v1 v2
  | MO_S_Lt _, [Some v1;Some v2] => Val.cmpl Clt v1 v2
(* Unsigned comparisons *)
  | MO_U_Ge _, [Some v1;Some v2] => Val.cmplu all_ptr_valid Cge v1 v2
  | MO_U_Le _, [Some v1;Some v2] => Val.cmplu all_ptr_valid Cle v1 v2
  | MO_U_Gt _, [Some v1;Some v2] => Val.cmplu all_ptr_valid Cgt v1 v2
  | MO_U_Lt _, [Some v1;Some v2] => Val.cmplu all_ptr_valid Clt v1 v2
(* Floating point arithmetic *)
  | MO_F_Add _, [Some v1;Some v2] => Some (Val.addf v1 v2)
  | MO_F_Sub _, [Some v1;Some v2] => Some (Val.subf v1 v2)
  | MO_F_Neg _, [Some v1] => None
  | MO_F_Mul _, [Some v1;Some v2] => Some (Val.mulf v1 v2)
  | MO_F_Quot _, [Some v1;Some v2] => Some (Val.divf v1 v2)
(* Floating point comparison *)
  | MO_F_Eq _, [Some v1;Some v2] => Some (Val.cmpf Ceq v1 v2)
  | MO_F_Ne _, [Some v1;Some v2] => Some (Val.cmpf Cne v1 v2)
  | MO_F_Ge _, [Some v1;Some v2] => Some (Val.cmpf Cge v1 v2)
  | MO_F_Le _, [Some v1;Some v2] => Some (Val.cmpf Cle v1 v2)
  | MO_F_Gt _, [Some v1;Some v2] => Some (Val.cmpf Cgt v1 v2)
  | MO_F_Lt _, [Some v1;Some v2] => Some (Val.cmpf Clt v1 v2)
(* Bitwise operations.  Not all of these may be supported
   at all sizes, and only integral Widths are valid. *)
  | MO_And _, [Some v1;Some v2] => Some (Val.andl v1 v2)
  | MO_Or _, [Some v1;Some v2] => Some (Val.orl v1 v2)
  | MO_Xor _, [Some v1;Some v2] => Some (Val.xorl v1 v2)
  | MO_Not _, [Some v1] => Some (Val.notl v1)
  | MO_Shl _, [Some v1;Some v2] => Some (Val.shrl v1 v2)
  | MO_U_Shr _, [Some v1;Some v2] => Some (Val.shrlu v1 v2)
  | MO_S_Shr _, [Some v1;Some v2] => Val.shrxl v1 v2
(* Conversions.  Some of these will be NOPs.
   Floating-point conversions use the signed variant. *)
  | MO_SF_Conv _ _, [Some v1] => Val.floatoflong v1
  | MO_FS_Conv _ _, [Some v1] => Val.longoffloat v1
  | MO_SS_Conv _ _, [Some v1] => Some v1
  | MO_UU_Conv _ _, [Some v1] => Some v1
  | MO_FF_Conv _ _, [Some v1] => Some v1

  | _, _ => None
  end.

Definition globalRegToChunk (g:GlobalReg) : memory_chunk :=
  match g with
  | VanillaReg _ _ => Many64
  | FloatReg _     => Mfloat32
  | DoubleReg _    => Mfloat64
  | LongReg _      => Mint64
  | BaseReg        => Many64
  | PicBaseReg     => Many64
  | _              => Many64 (* This is cheating, but TODO: semantics for Cmm Core *)
  end.

Local Open Scope Z_scope.

Definition globalRegToPtr (g:GlobalReg) : option val :=
  let off_zero := (Ptrofs.of_int64 Int64.zero)
  in match g with
     | VanillaReg r _ => match r with
                         | 1 => Some (Vptr _R1 off_zero)
                         | 2 => Some (Vptr _R2 off_zero)
                         | 3 => Some (Vptr _R3 off_zero)
                         | 4 => Some (Vptr _R4 off_zero)
                         | 5 => Some (Vptr _R5 off_zero)
                         | 6 => Some (Vptr _R6 off_zero)
                         | 7 => Some (Vptr _R7 off_zero)
                         | 8 => Some (Vptr _R8 off_zero)
                         | 9 => Some (Vptr _R9 off_zero)
                         | 10 => Some (Vptr _R10 off_zero)
                         | _ => None
                         end
     | FloatReg f     => match f with
                         | 1 => Some (Vptr _F1 off_zero)
                         | 2 => Some (Vptr _F2 off_zero)
                         | 3 => Some (Vptr _F3 off_zero)
                         | 4 => Some (Vptr _F4 off_zero)
                         | 5 => Some (Vptr _F5 off_zero)
                         | 6 => Some (Vptr _F6 off_zero)
                         | _ => None
                         end
     | DoubleReg d    => match d with
                         | 1 => Some (Vptr _D1 off_zero)
                         | 2 => Some (Vptr _D2 off_zero)
                         | 3 => Some (Vptr _D3 off_zero)
                         | 4 => Some (Vptr _D4 off_zero)
                         | 5 => Some (Vptr _D5 off_zero)
                         | 6 => Some (Vptr _D6 off_zero)
                         | _ => None
                         end
     | LongReg l      => None (* These seem to be unused now *)
     | BaseReg        => Some (Vptr _BaseReg off_zero)
     | PicBaseReg     => Some (Vptr _PicBaseReg off_zero)
     | _ => None (* All other TODO: Implement the registers in Cmm Core*)
     end.


Definition env := PTree.t val.
(* FIXME: Implement all expressions *) (*
Fixpoint cmmExprDenote (m:mem) (en:env) (sp:val) (e:CmmExpr) : option val :=
  match e with
  | CE_CmmLit l => cmmLitDenote l
  | CE_CmmLoad e' t => match (cmmExprDenote m en sp e') with
                       | None => None
                       | Some v => Mem.loadv (cmmTypeToChunk t) m v
                       end
  | CE_CmmReg r => match r with
                   | CmmLocal (LR_LocalReg u t) => PTree.get u en
                   | CmmGlobal g => match globalRegToPtr g with
                                    | None   => None
                                    | Some p => Mem.loadv (globalRegToChunk g) m p
                                    end
                   end
  | CE_CmmMachOp mo ps => moDenote mo (List.map (cmmExprDenote m en sp) ps)
  | CE_CmmStackSlot a off => Some (Val.offset_ptr sp (Ptrofs.of_int64 off)) (* TODO parameter a: What is the semantics of an Area? *)
  | CE_CmmRegOff r off => match r with
                          | CmmLocal (LR_LocalReg u t) => match PTree.get u en with
                                                          | Some v => Some(Val.offset_ptr sp (Ptrofs.of_int64 off))
                                                          | None => None
                                                          end
                          | CmmGlobal g =>
                            match globalRegToPtr g with
                            | None   => None
                            | Some p => match Mem.loadv (globalRegToChunk g) m p with
                                        | Some v => Some(Val.offset_ptr sp (Ptrofs.of_int64 off))
                                        | None => None
                                        end
                            end
                          end
  end.


(* This is much prettier in monadic notation *)
Fixpoint cmmExprListDenote (m:mem) (en:env) (sp:val) (es:list CmmExpr) : option (list val) :=
  match es with
  | [] => Some []
  | e::es' => match cmmExprDenote m en sp e with
              | None => None
              | Some v => match (cmmExprListDenote m en sp es') with
                          | Some vs => Some (v::vs)
                          | None => None
                          end
              end
  end.
*)
