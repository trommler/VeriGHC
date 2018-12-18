(* definitions from compiler/cmm/Cmm.hs *)
Require Import compcert.lib.Maps.

Require Import GHC.BlockId.
Require Import GHC.CmmNode.
Require Import GHC.CmmExpr.
Require Import GHC.Int.
Require Import GHC.Word.

(* Definition CmmBlock := list CmmNode. *)

(* TODO: Put in separate file *)
Definition Graph (n:Set) : Set := list n.

Record CmmGraph : Set := CG_CmmGraph {
                             g_entry : BlockId;
                             g_graph : Graph CmmNode;
                           }.

Inductive SectionType : Set :=
| Text
| Data
| ReadOnlyData
| RelocatableReadOnlyData
| UninitialisedData
| ReadOnlyData16
| CString
| OtherSection
.

Inductive section : Set:= S_section : SectionType -> CLabel -> section.

Definition isSecConstant (sect:section) : bool :=
  match sect with
    S_section t _ => match t with
                     | Text => true
                     | ReadOnlyData => true
                     | RelocatableReadOnlyData => true
                     | ReadOnlyData16 => true
                     | CString => true
                     | Data => false
                     | UninitialisedData => false
                     | OtherSection => false
                     end
  end.

Inductive CmmStatic : Set :=
| CmmStaticLit: CmmLit -> CmmStatic
| CmmUninitialised: Int -> CmmStatic
| CmmString: list Word8 -> CmmStatic
.

Inductive CmmStatics : Set :=
  Statics: CLabel -> list CmmStatic -> CmmStatics.

Inductive GenCmmDecl d h g :=
| CmmProc : h -> CLabel -> list GlobalReg -> g -> GenCmmDecl d h g
| CmmData : section -> d -> GenCmmDecl d h g.

Definition SMRep : Set := nat. (* actually storage manager representation *)

Record CmmInfoTable : Set := CIT_CmmInfoTable {
                                 cit_lbl  : CLabel;
                                 cit_rep  : SMRep;
                                 (* cit_prof : ProfilingInfo *)
                                 cit_srt  : option CLabel;
                                 (* cit_clo  : Maybe (Id, CostCentreStack) *)
                               }
.

Record CmmStackInfo : Set := StackInfo {
                                 arg_space : ByteOff;
                                 updfr_space : option ByteOff;
                                 do_layout : bool;
                               }
.

Definition LabelMap (a:Type) := PTree.t a.
Record CmmTopInfo : Type := TopInfo {
                               info_tbls  : LabelMap CmmInfoTable;
                               stack_info : CmmStackInfo;
                             }
.

Definition CmmDecl := GenCmmDecl CmmStatics CmmTopInfo CmmGraph.

Definition GenCmmGroup d h g := list (GenCmmDecl d h g).
Definition CmmGroup := GenCmmGroup CmmStatics CmmTopInfo CmmGraph.

Definition CmmProgram := list CmmGroup.

Definition RawCmmGroup := GenCmmGroup CmmStatics (LabelMap CmmStatics) CmmGraph.

Inductive GenBasicBlock (i:Set) : Set :=
  BasicBlock : BlockId -> list i -> GenBasicBlock i.

Inductive ListGraph (i:Set) : Set :=
  LG_ListGraph : list (GenBasicBlock i) -> ListGraph i. 

