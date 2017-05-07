Require Import Setoid Arith List Omega Coq.Program.Tactics decision.
Require Import mlattice id_and_loc language LibTactics tactics.

Module Types (L: Lattice).
  Module Lang := Language L.
  Import Lang L.

  Notation "∘" := LH.L.
  Notation "•" := LH.H.

  Notation "X '≼' Y" := (ProdL.flowsto X Y) (at level 70, no associativity).
  Notation "X '⋎' Y" := (ProdL.join X Y) (at level 40, left associativity).

  Inductive type :=
  | Int: type
  | Array: sectype -> level_proj1 -> type
  with sectype  :=
       | SecType:
           type -> ProdL.T -> sectype.
  
  Scheme type_mut := Induction for type Sort Prop
                     with sectype_mut := Induction for sectype Sort Prop.


  Definition tenv  := id -> option sectype.
  Definition emptyTenv : tenv := fun _ => None.
  Definition stenv := loc -> option sectype.
  Definition emptyStenv : stenv := fun _ => None.
  
End Types.