Require Import Arith decision tactics.
Require Import Coq.Classes.RelationClasses.

Inductive id :=
  Id: nat -> id.

Inductive loc :=
  | Loc: nat -> loc.

Instance eq_id_dec:
  forall id1 id2 : id,
    Decision (id1 = id2).
Proof.
  intros [n1] [n2].
  destruct (decide (n1 = n2)).
  - subst.
    left.
    reflexivity.
  - right.
    intro.
    injects.
    eauto.
Defined.

Instance eq_loc_dec:
  forall l1 l2 : loc, Decision (l1 = l2).
Proof.
  intros [n1] [n2].
  destruct (decide (n1 = n2)).
  - subst.
    left.
    reflexivity.
  - right.
    intro.
    injects.
    eauto.    
Defined.

(* TODO: Do we really need seperate lemmas for both id and
   loc with Robert's type class? *)
Theorem eq_id:
  forall (T:Type)
    (x : id)
    (p q: T),
    (if decide (x = x) then p else q) = p.
Proof.
  intros.
  destruct (decide (x = x)).
  - reflexivity.
  - exfalso; eauto.
Qed.

(* TODO: Same as above *)
Theorem neq_id:
  forall (T: Type)
    (x y : id)
    (p q: T),
    x <> y ->
    (if decide (x = y) then p else q) = q.
Proof.
  intros.
  destruct (decide (x = y)).
  - contradiction.
  - reflexivity.
Qed.

Theorem eq_loc:
  forall (T: Type)
    (x : loc)
    (p q: T),
    (if decide (x = x) then p else q) = p.
Proof.
  intros.
  destruct (decide (x = x)).
  - reflexivity.
  - exfalso; eauto.
Qed.

Theorem neq_loc:
  forall (T: Type)
    (x y: loc)
    (p q: T),
    x <> y ->
    (if decide (x = y) then p else q) = q.
Proof.
  intros.
  destruct (decide (x = y)).
  - contradiction.
  - reflexivity.
Qed.