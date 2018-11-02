(* definitions from compiler/cmm/Cmm.hs *)
Require Import GHC.BlockId.
Require Import GHC.CmmNode.
Require Import GHC.CmmExpr.

Definition CmmBlock := list CmmNode.

(* TODO: Put in separate file *)
Definition Graph (n:Set) : Set := list n.

Record CmmGraph : Set := CG_CmmGraph {
                             g_entry : BlockId;
                             g_graph : Graph CmmNode;
                           }.

Inductive SectionType :=
| Text
| Data
| ReadOnlyData
| RelocatableReadOnlyData
| UninitialisedData
| ReadOnlyData16
| CString
| OtherSection
.

Inductive section := S_section : SectionType -> CLabel -> section.

Inductive GenCmmDecl d h g :=
| CmmProc : h -> CLabel -> list GlobalReg -> g -> GenCmmDecl d h g
| CmmData : section -> d -> GenCmmDecl d h g.

(* Definition CmmDecl := GenCmmDecl CmmStatics CmmTopInfo CmmGraph. *)






Inductive GenBasicBlock (i:Set) : Set :=
  BasicBlock : BlockId -> list i -> GenBasicBlock i.

Inductive ListGraph (i:Set) : Set :=
  LG_ListGraph : list (GenBasicBlock i) -> ListGraph i. 
