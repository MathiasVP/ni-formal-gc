Require Import mlattice id_and_loc.
Require Import LibTactics tactics.

Require Import mlattice.
Module Language (L: Lattice).
  Import L.
  Module ProdL := ProductLattice L LH.
  Module ProdLatProp := LatticeProperties ProdL.
  Module LHLatProp := LatticeProperties LH.
  Definition level := ProdL.T.
  Definition level_proj1 := L.T.
  
  Inductive op := Plus | Mult.
  
  Inductive expr :=
  | Const: nat -> expr
  | Var: id -> expr
  | BinOp: op -> expr -> expr -> expr.
  
  Inductive cmd  :=
  | Skip: cmd
  | Stop: cmd
  | Assign: id -> expr -> cmd
  | If: expr -> cmd -> cmd -> cmd
  | While: expr -> cmd -> cmd
  | Seq: cmd -> cmd -> cmd
  | At: level_proj1 -> expr -> cmd -> cmd
  | BackAt: level_proj1 -> nat -> cmd
  | NewArr: id -> level_proj1 -> expr -> expr -> cmd
  | SetArr: id -> expr -> expr -> cmd
  | GetArr: id -> id -> expr -> cmd
  | Time: id -> cmd
  | TimeOut: cmd.
  
Notation "'STOP'" := Stop (only parsing).
Notation "'SKIP'" := Skip (only parsing).
Notation "x '::=' e" := (Assign x e) (at level 80).
Notation "c1 ';;' c2":= (Seq c1 c2)  (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (While b c) (at level 80, right associativity).
Notation "'IFB' e 'THEN' c1 'ELSE' c2 'FI'" :=
  (If e c1 c2) (at level 80, right associativity).
Notation "'AT' ℓ 'FOR' e 'DO' c" :=
  (At ℓ e c) (at level 80).
Notation "'BACKAT' ℓ 'WHEN' n 'DO' c" :=
    (BackAt ℓ n c) (at level 80).
Notation "'SET' x '[' e1 ']'  'TO' e2 " :=
  (SetArr x e1 e2) (at level 80).
Notation "'GET' x 'FROM' y '[' e ']'" :=
    (GetArr x y e) (at level 80).
Notation "'TIME' '(' x ')'" := (Time x).
Notation "'TIMEOUT'" := TimeOut.

Inductive value :=
| ValNum: nat -> value
| ValLoc: loc -> value.

End Language.