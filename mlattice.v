Require Import Setoid Arith List Omega Coq.Program.Tactics LibTactics tactics.
Require Import Coq.Program.Equality.

(* Set Implicit Arguments. *)

Module Type Lattice.

Parameter T : Set.
Parameter join: T -> T -> T.
Parameter meet: T -> T -> T.
Parameter flowsto : T -> T -> Prop.
Parameter bot: T.
  
Notation "X ⊑ Y" := (flowsto X Y) (at level 70, no associativity).
Notation "X ⊔ Y" := (join X Y) (at level 40, left associativity).

Axiom meet_symmetry: forall a b   : T,  meet a b = meet b a.
Axiom join_symmetry: forall a b   : T,  join a b = join b a.
Axiom join_assoc   : forall a b c : T,  join a (join b c) = join (join a b) c.
Axiom meet_assoc   : forall a b c : T,  meet a (meet b c) = meet (meet a b) c.
Axiom meet_distrib : forall a b   : T,  meet a (join a b) = a.
Axiom join_distrib : forall a b   : T,  join a (meet a b) = a.
Axiom flowsto_dec  : forall a b   : T,  { a ⊑ b } + { not (a ⊑ b) }.
Axiom join_flowsto : forall a b   : T,  join a b = b <-> flowsto a b.
Axiom T_dec        : forall a b   : T,  { a = b} + { a <> b }.
Axiom join_bot_left: forall a     : T, join bot a = a.
Axiom join_bot_right: forall a    : T, join a bot = a.


Hint Resolve meet_symmetry join_symmetry join_assoc meet_assoc meet_distrib join_distrib
flowsto_dec join_flowsto T_dec join_bot_left join_bot_right.

End Lattice.

Module LatticeProperties (L: Lattice).
Import L.

Lemma idem_join:
    forall a : T,
      join a a = a.
Proof.
  intros.
  eauto.
  rewrite <- (meet_distrib a a) at 2.
  eauto.
Qed.
Local Hint Resolve idem_join.
  
Lemma idem_meet:
    forall a : T,
      meet a a = a.
Proof.
  intros.
  rewrite <- (join_distrib a a) at 2.
  eauto.
Qed.
Local Hint Resolve idem_meet.

Lemma flowsto_refl: forall a, flowsto a a.
Proof.
  intro.
  apply join_flowsto.
  eauto.
Qed.
Local Hint Resolve flowsto_refl.

Lemma flowsto_trans: 
  forall a b c,
    flowsto  a b ->
    flowsto  b c ->
    flowsto  a c.
Proof.
  intros.
  apply join_flowsto.
  apply join_flowsto in H.
  apply join_flowsto in H0.
  rewrite <- H0.
  replace  (join a(join b c)) with (join (join a b) c) by eauto.
  rewrite -> H.
  eauto.
Qed.

Hint Extern 1 (?a ⊑ ?c) =>
match goal with
| [H: a ⊑ ?b |- _] => apply (flowsto_trans a b c)
| [H: ?b ⊑ c |- _] => apply (flowsto_trans a b c)
end.
  
Lemma anti_sym:
  forall a b : T,
    a ⊑ b ->
    b ⊑ a ->
    a = b.
Proof.
  intros a b H1 H2.
  apply join_flowsto in H1.
  apply join_flowsto in H2.
  replace (join b a) with (join a b) in * by eauto.
  congruence.
Qed.
Local Hint Resolve anti_sym.

Lemma flowsto_not:
  forall ℓ₁ ℓ₂ ℓ₃,
    ℓ₁ ⊑ ℓ₂ ->
    not (ℓ₁ ⊑ ℓ₃) ->
    not (ℓ₂ ⊑ ℓ₃).
Proof.
  intros ℓ₁ ℓ₂ ℓ₃ H1 H2.
  intro H_absurd.
  contradiction (flowsto_trans _ _ _ H1 H_absurd).
Qed.
Hint Resolve flowsto_not.

Lemma flowsto_join:
  forall a b,
    a ⊑ join a b.
Proof.
  intros.
  apply join_flowsto.
  rewrite -> join_assoc.
  rewrite -> idem_join.
  reflexivity.
Qed.
  
Lemma join_flowsto_implies_flowsto:
  forall ℓ₁ ℓ₂ ℓ₃,
    join ℓ₁ ℓ₂ ⊑ ℓ₃ -> ℓ₁ ⊑ ℓ₃ /\ ℓ₂ ⊑ ℓ₃.
Proof.
  intros.
  assert (ℓ₁ ⊑ join ℓ₁ ℓ₂) by apply flowsto_join.
  assert (ℓ₂ ⊑ join ℓ₁ ℓ₂) by (rewrite -> join_symmetry; apply flowsto_join).
  split; eapply flowsto_trans; eauto.
Qed.

Ltac destruct_join_flowsto :=
  match goal with
    [H: join ?a ?b ⊑ ?c |- _] => destruct (join_flowsto_implies_flowsto a b c H); clear H
  end.

Lemma not_flowsto_implies_not_join_flowsto:
  forall a b c,
    ~ a ⊑ c ->
    ~ b ⊑ c ->
    ~ join a b ⊑ c.
Proof.
  intros.
  intro.
  rewrite <- join_flowsto in *.
  rewrite <- H1 in *.
  rewrite -> join_flowsto in *.
  rewrite <- join_assoc in *.
  contradiction H.
  eapply flowsto_join.
Qed.

Lemma implies_join_flowsto:
  forall a b c,
    a ⊑ c ->
    b ⊑ c ->
    a ⊔ b ⊑ c.
Proof.
  intros.
  rewrite <- join_flowsto.
  eapply join_flowsto in H.
  eapply join_flowsto in H0.
  rewrite <- join_assoc.
  rewrite -> H0.
  assumption.
Qed.
Hint Resolve implies_join_flowsto.

End LatticeProperties.

Module ProductLattice (A B : Lattice) <: Lattice.
  Definition T := prod A.T B.T.  

  Definition meet (x y : T) :=
    match x, y with
      (a1, b1), (a2, b2) => (A.meet a1 a2, B.meet b1 b2)
    end.

  Definition join (x y : T) :=
    match x, y with
      (a1, b1), (a2, b2) => (A.join a1 a2, B.join b1 b2)
    end.
  
  Definition flowsto (a b : T) := join a b = b.
  Local Hint Unfold flowsto.
  
  Lemma meet_symmetry: forall a b : T, meet a b = meet b a.
  Proof.
    intros.
    unfolds.
    destruct a as [a1 b1].
    destruct b as [a2 b2].
    rewrite -> A.meet_symmetry.
    rewrite -> B.meet_symmetry.
    reflexivity.
  Qed.

  Lemma join_symmetry: forall a b : T, join a b = join b a.
  Proof.
    intros.
    unfolds.
    destruct a as [a1 b1].
    destruct b as [a2 b2].
    rewrite -> A.join_symmetry.
    rewrite -> B.join_symmetry.
    reflexivity.
  Qed.

  Lemma join_assoc: forall a b c : T, join a (join b c) = join (join a b) c.
  Proof.
    intros.
    unfold join.
    destruct a as [a1 b1].
    destruct b as [a2 b2].
    destruct c as [a3 b3].
    rewrite -> A.join_assoc.
    rewrite -> B.join_assoc.
    reflexivity.
  Qed.

  Lemma meet_assoc: forall a b c : T, meet a (meet b c) = meet (meet a b) c.
  Proof.
    intros.
    unfold meet.
    destruct a as [a1 b1].
    destruct b as [a2 b2].
    destruct c as [a3 b3].
    rewrite -> A.meet_assoc.
    rewrite -> B.meet_assoc.
    reflexivity.
  Qed.

  Lemma meet_distrib: forall a b : T, meet a (join a b) = a.
  Proof.
    intros.
    unfold meet, join.
    destruct a as [a1 b1].
    destruct b as [a2 b2].
    rewrite -> A.meet_distrib.
    rewrite -> B.meet_distrib.
    reflexivity.    
  Qed.
  Hint Resolve meet_distrib.
  
  Lemma join_distrib: forall a b : T, join a (meet a b) = a.
  Proof.
    intros.
    unfold meet, join.
    destruct a as [a1 b1].
    destruct b as [a2 b2].
    rewrite -> A.join_distrib.
    rewrite -> B.join_distrib.
    reflexivity. 
  Qed.
  Hint Resolve join_distrib.
  
  Notation "X ⊑ Y" := (flowsto X Y) (at level 70, no associativity).
  Notation "X ⊔ Y" := (join X Y) (at level 40, left associativity).

  Lemma join_flowsto: forall a b: T,
      join a b = b <-> flowsto a b.
  Proof.
    split*.
  Qed.

  Lemma flowsto_pointwise_proj1:
    forall (a1 a2 : A.T)
      (b1 b2 : B.T),
      flowsto (a1, b1) (a2, b2) ->
      A.flowsto a1 a2.
  Proof.
    intros.
    rewrite <- A.join_flowsto.
    rewrite <- join_flowsto in *.
    injects.
    assumption.
  Qed.
  Hint Resolve flowsto_pointwise_proj1.

  Lemma flowsto_pointwise_proj2:
    forall (a1 a2 : A.T)
      (b1 b2 : B.T),
      flowsto (a1, b1) (a2, b2) ->
      B.flowsto b1 b2.
  Proof.
    intros.
    rewrite <- B.join_flowsto.
    rewrite <- join_flowsto in *.
    injects.
    assumption.
  Qed.
  Hint Resolve flowsto_pointwise_proj2.      

  Lemma join_is_pairwise:
    forall (a1 a2 : A.T)
      (b1 b2 : B.T),
      join (a1, b1) (a2, b2) =
      (A.join a1 a2, B.join b1 b2).
  Proof.
    intros.
    unfolds.
    reflexivity.
  Qed.

  Lemma flowsto_dec: forall a b : T,
      {a ⊑ b} + {not (a ⊑ b)}.
  Proof.
    intros a b.
    destruct a as [a1 b1].
    destruct b as [a2 b2].
    destruct (A.flowsto_dec a1 a2); destruct (B.flowsto_dec b1 b2).
    - left.
      rewrite <- join_flowsto.
      rewrite <- A.join_flowsto in * |-.
      rewrite <- B.join_flowsto in * |-.
      unfolds.
      rewrite -> f.
      rewrite -> f0.
      reflexivity.
    - right.
      intro.
      rewrite <- join_flowsto in *.
      contradict n.
      rewrite <- B.join_flowsto.
      unfolds in H.
      injects.
      assumption.
    - right.
      intro.
      rewrite <- join_flowsto in *.
      contradict n.
      rewrite <- A.join_flowsto.
      unfolds in H.
      injects.
      assumption.
    - right.
      intro.
      rewrite <- join_flowsto in *.
      unfolds in H.
      injects.
      contradict n.
      rewrite <- A.join_flowsto.
      assumption.
  Defined.

Lemma T_dec: forall a b : T, {a = b} + {a <> b}.
Proof.
  intros.
  destruct a as [a1 b1].
  destruct b as [a2 b2].
  destruct (A.T_dec a1 a2); destruct (B.T_dec b1 b2); subst.
  - left.
    reflexivity.
  - right.
    intro; injects.
    eauto.
  - right.
    intro; injects.
    eauto.
  - right.
    intro; injects.
    eauto.
Qed.

Definition bot := (A.bot, B.bot).

Lemma join_bot_left:
  forall a,
    join bot a = a.
Proof.
  intros.
  destruct a as [a b].
  unfolds.
  unfold bot.
  rewrite -> A.join_bot_left.
  rewrite -> B.join_bot_left.
  reflexivity.
Qed.
Hint Resolve join_bot_left.

Lemma join_bot_right:
  forall a,
    join a bot = a.
Proof.
  intros.
  destruct a as [a b].
  unfolds.
  unfold bot.
  rewrite -> A.join_bot_right.
  rewrite -> B.join_bot_right.
  reflexivity.
Qed.
Hint Resolve join_bot_right.

Lemma implies_flowsto:
  forall a1 a2 b1 b2,
    A.flowsto a1 a2 ->
    B.flowsto b1 b2 ->
    flowsto (a1, b1) (a2, b2).
Proof.
  intros.
  unfolds.
  rewrite -> join_is_pairwise.
  rewrite <- A.join_flowsto in *.
  rewrite <- B.join_flowsto in *.
  congruence.
Qed.
Hint Resolve implies_flowsto.
  
End ProductLattice.

Module LH <: Lattice.

Inductive LH :=
| L: LH
| H: LH.

Definition T := LH.

Definition meet (a b : LH) :=
  match a with
    | L => L
    | H => b
  end.

Definition join (a b : LH) :=
  match a with
  | L => b
  | H => H
  end.


Lemma meet_symmetry: forall a b : LH, meet a b = meet b a.
Proof.
  intros.
  unfold meet.
  case a; case b; auto.
Qed.

Lemma join_symmetry :forall a b : LH, join a b = join b a.
Proof.
  intros; unfold join. case a; case b; auto.
Qed.

Lemma join_assoc: forall a b c :LH , join a (join b c) = join ( join a b) c.
Proof.
  intros.
  unfold join.
  case a; case b; case c; auto.
Qed.

Lemma meet_assoc: forall a b c: LH, meet a (meet b c) = meet (meet a b) c.
Proof.
  intros.
  unfold join.
  case a; case b; case c; auto.
Qed.

Lemma meet_distrib: forall a b : LH, meet a (join a b) = a.
Proof.
  intros; case a; case b; auto.
Qed.

Lemma join_distrib: forall a b : LH, join a (meet a b) = a.
Proof.
  intros; case a; case b; auto.
Qed.

Definition flowsto a b := join a b = b.
Local Hint Unfold flowsto.
  
Notation "X ⊑ Y" := (flowsto X Y) (at level 70, no associativity).
Notation "X ⊔ Y" := (join X Y) (at level 20, left associativity).

Lemma flowsto_dec: forall a b : T,
    {a ⊑ b} + {not (a ⊑ b)}.
Proof.
  intros a b.
  destruct a; destruct b.
  - left; eauto.
  - left; eauto.
  - right. unfold not; intros. inversion H0.
  - left; eauto.
Defined.  

Lemma T_dec: forall a b : LH, {a = b } + {a <> b}.
Proof.
  intros.
  destruct a; destruct b; eauto; right; congruence.
Qed.

Lemma join_flowsto: forall a b: LH,
  join a b = b <-> flowsto a b.
Proof.
  split.
  - eauto.
  - intros.
    eauto.
Qed.

Definition bot := L.

Lemma join_bot_left:
  forall a,
    join bot a = a.
Proof.
  reflexivity.
Qed.
Hint Resolve join_bot_left.

Lemma join_bot_right:
  forall a,
    join a bot = a.
Proof.
  intros.
  destruct a; reflexivity.
Qed.
Hint Resolve join_bot_right.

End LH.