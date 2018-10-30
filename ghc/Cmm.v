(* definitions from compiler/cmm/Cmm.hs *)
Require Import GHC.BlockId.
Require Import GHC.CmmNode.

Definition CmmBlock := list CmmNode.

(* TODO: Put in separate file *)
Definition Graph (n:Set) : Set := list n.

Record CmmGraph : Set := CG_CmmGraph {
                             g_entry : BlockId;
                             g_graph : Graph CmmNode;
                           }.


              






Inductive GenBasicBlock (i:Set) : Set :=
  BasicBlock : BlockId -> list i -> GenBasicBlock i.

Inductive ListGraph (i:Set) : Set :=
  LG_ListGraph : list (GenBasicBlock i) -> ListGraph i. 
