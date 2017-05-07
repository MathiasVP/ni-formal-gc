Require Import Coq.Program.Basics LibTactics decision tactics.

Definition left_inverse {A B : Type} (f : A -> option B) (g : B -> option A) :=
  forall (x : A) (y : B),
    f x = Some y ->
    g y = Some x.
Hint Unfold left_inverse.

Definition right_inverse {A B : Type} (f : A -> option B) (g : B -> option A) :=
  forall (x : A) (y : B),
    g y = Some x ->
    f x = Some y.
Hint Unfold right_inverse.

Definition is_inverse {A B: Type} (f: A -> option B) (g: B -> option A) :=
  left_inverse f g /\ right_inverse f g.
Hint Unfold is_inverse.

Inductive bijection (A B: Type) :=
| Bijection:
    forall (f: A -> option B) (g: B -> option A),
      left_inverse f g ->
      right_inverse f g ->
      @bijection A B.
Hint Constructors bijection.

Lemma inverse {A B: Type}:
  bijection A B ->
  bijection B A.
Proof.
  intros.
  inverts X.
  eapply Bijection; eauto.
Defined.

Lemma inverse_is_involutive {A B: Type} :
  forall φ: bijection A B,
    φ = inverse (inverse φ).
Proof.
  intros.
  unfold inverse.
  destruct φ.
  reflexivity.
Qed.

Definition fun_compose {A B C: Type} (f: B -> option C) (g: A -> option B) :=
  fun (x : A) =>
    match g x with
    | Some y => f y
    | None => None
    end.
Hint Unfold fun_compose.

Lemma left_inverse_compose {A B C: Type}:
  forall (f1: A -> option B)
         (g1: B -> option A)
         (f2: B -> option C)
         (g2: C -> option B),
    left_inverse f1 g1 ->
    left_inverse f2 g2 ->
    left_inverse (fun_compose f2 f1) (fun_compose g1 g2).
Proof.
  intros.
  unfold left_inverse in *.
  intros.
  unfold fun_compose in *.
  destruct (f1 x) eqn:H2.
  - erewrite -> H0; try eauto.
  - discriminate.
Defined.


Lemma right_inverse_compose {A B C: Type}:
  forall (f1: A -> option B)
         (g1: B -> option A)
         (f2: B -> option C)
         (g2: C -> option B),
    right_inverse f1 g1 ->
    right_inverse f2 g2 ->
    right_inverse (fun_compose f2 f1) (fun_compose g1 g2).
Proof.
  intros.
  unfold right_inverse in *.
  intros.
  unfold fun_compose in *.
  destruct (g2 y) eqn:H2.
  - erewrite -> H; try eauto.
  - discriminate.
Defined.

Lemma bijection_compose {A B C: Type}:
  bijection A B -> bijection B C -> bijection A C.
  intros.
  do 2 match goal with
       | [H: bijection ?A ?B |- _] => inversion H; clear H
       end.
  apply (Bijection A C (fun_compose f f0) (fun_compose g0 g)).
  apply left_inverse_compose; auto.
  apply right_inverse_compose; auto.
Defined.

Definition left {A B: Type} (f: bijection A B) : A -> option B :=
  match f with
    Bijection _ _ f _ _ _ => f
  end.

Definition right {A B: Type} (f: bijection A B) : B -> option A :=
  match f with
    Bijection _ _ _ f _ _ => f
  end.

Lemma inverse_compose {A B C: Type}:
  forall (f : bijection A B)
    (g : bijection B C),
    inverse (bijection_compose f g) = bijection_compose (inverse g) (inverse f).
Proof.
  intros.
  unfold inverse.
  unfold compose.
  destruct f.
  destruct g.
  reflexivity.
Qed.    
    
Lemma bijection_is_left_inverse {A B : Type}:
  forall f : bijection A B,
    left_inverse (left f) (right f).
Proof.
  intros.
  unfold left, right.
  destruct f.
  assumption.
Defined.

Lemma bijection_is_right_inverse {A B : Type}:
  forall f : bijection A B,
    right_inverse (left f) (right f).
Proof.
  intros.
  unfold left, right.
  destruct f.
  assumption.
Defined.

Lemma right_inverse_is_left {A B: Type}:
  forall (f: bijection A B),
    right (inverse f) = left f.
Proof.
  unfold inverse.
  destruct f.
  unfold left.
  unfold right.
  reflexivity.
Defined.

Lemma left_inverse_is_right {A B: Type}:
  forall (f: bijection A B),
    left (inverse f) = right f.
Proof.
  unfold inverse.
  destruct f.
  unfold right.
  unfold left.
  reflexivity.
Defined.

Lemma left_right {A B: Type}:
  forall (f: bijection A B)
         (x : B)
         (y : A),
    right f x = Some y ->
    left f y = Some x.
Proof.
  intros.
  unfold left.
  destruct f.
  auto.
Qed.

Lemma right_left {A B: Type}:
  forall (f: bijection A B)
         (x: A)
         (y: B),
    left f x = Some y ->
    right f y = Some x.
Proof.
  intro.
  unfold right.
  destruct f.
  auto.
Qed.

Lemma left_compose {A B C: Type}:
  forall (φ : bijection A B)
         (ψ: bijection B C)
         (x : A)
         (mz : option C),
    left (bijection_compose φ ψ) x = mz ->
    exists (my : option B),
      left φ x = my /\
      (forall y, my = Some y -> left ψ y = mz) /\
      (my = None -> mz = None).
Proof.
  intros.
  exists (left φ x).
  splits*.
  - intros.
    unfolds in H.
    unfold bijection_compose in H.
    destruct ψ.
    destruct φ.
    unfolds in H.
    unfold left in *.
    rewrite -> H0 in *.
    assumption.
  - intro.
    unfold left in *.
    unfold bijection_compose in *.
    destruct ψ.
    destruct φ.
    unfolds in H.
    rewrite -> H0 in H.
    auto.
Qed.

Lemma right_bijection_compose {A B C: Type}:
  forall (φ : bijection A B)
         (ψ: bijection B C)
         (z : C)
         (mx : option A),
    right (bijection_compose φ ψ) z = mx ->
    exists (my : option B),
      right ψ z = my /\
      (forall y, my = Some y -> right φ y = mx) /\
      (my = None -> mx = None).
Proof.
  intros.
  exists (right ψ z).
  splits*.
  - intros.
    unfolds in H.
    unfold bijection_compose in H.
    unfolds in H0.
    destruct ψ.
    destruct φ.
    unfolds.
    unfolds in H.
    rewrite -> H0 in *.
    assumption.
  - intro.
    unfolds in H.
    unfolds in H0.
    unfold bijection_compose in H.
    destruct ψ.
    destruct φ.
    unfolds in H.
    rewrite -> H0 in *.
    subst.
    reflexivity.
Qed.

Lemma bijection_is_injective_left {A B : Type}:
  forall (φ : bijection A B)
         (x y : A)
         (z : B),
    x <> y -> left φ x = Some z -> Some z <> left φ y.
Proof.
  intros.
  intro H_absurd.
  contradiction H.
  unfolds in H_absurd.
  destruct φ.
  unfold left in *.
  unfolds in l r.
  symmetry in H_absurd.
  remember (l x z H0).
  remember (l y z H_absurd).
  clear Heqe Heqe0.
  rewrite e in *.
  injects e0.
  reflexivity.
Qed.

Lemma bijection_is_injective_right {A B : Type}:
  forall (φ: bijection A B)
         (x y : B)
         (z : A),
    x <> y -> right φ x = Some z -> Some z <> right φ y.
Proof.
  intros.
  intro H_absurd.
  contradiction H.
  unfolds in H_absurd.
  destruct φ.
  unfold right in *.
  unfolds in l r.
  symmetry in H_absurd.
  remember (r z x H0).
  remember (r z y H_absurd).
  clear Heqe Heqe0.
  rewrite e in *.
  injects e0.
  reflexivity.
Qed.

Lemma left_inverse_extend {A B: Type}
      {DecA: forall a1 a2 : A, Decision (a1 = a2)}
      {DecB: forall b1 b2: B, Decision (b1 = b2)}:
  forall (f: A -> option B)
    (g: B -> option A)
    (l1: A)
    (l2: B),
    left_inverse f g ->
    g l2 = None ->
    left_inverse (fun l => if decide (l = l1)
                        then Some l2
                        else f l)
                 (fun l => if decide (l = l2)
                        then Some l1
                        else g l).
  Proof.
    intros f g l1 l2 H1 H2.
    unfolds.
    intros.
    destruct (decide (x = l1)); subst.
    - injects.
      destruct (decide (y = y)); subst.
      + reflexivity.
      + exfalso; eauto.
    - destruct (decide (y = l2)); subst.
      + exfalso.
        match goal with
          [H: left_inverse _ _ |- _] =>
          erewrite H in *; eauto
        end.
        discriminate.
      + eauto.
  Defined.
  Hint Resolve left_inverse_extend.

  Lemma right_inverse_extend {A B : Type}
        {DecA: forall a1 a2 : A, Decision (a1 = a2)}
        {DecB: forall b1 b2: B, Decision (b1 = b2)}:
    forall (f : A -> option B)
      (g : B -> option A)
      (l1 : A)
      (l2 : B),
    right_inverse f g ->
    f l1 = None ->
    right_inverse (fun l => if decide (l = l1)
                            then Some l2
                            else f l)
                  (fun l => if decide (l = l2)
                            then Some l1
                            else g l).
Proof.
  intros f g l1 l2 H1 H2.
  unfolds.
  intros.
  destruct (decide (y = l2)); subst.
  - rewrite_inj.
    destruct (decide (x = x)); subst.
    + reflexivity.
    + exfalso; eauto.
  - destruct (decide (x = l1)); subst.
    + match goal with
        [H: right_inverse _ _ |- _] =>
        erewrite -> H1 in *; eauto
      end.
      discriminate.
    + eauto.
Defined.
Hint Resolve right_inverse_extend.

Definition extend_bijection {A B: Type}
           {DecA: forall a1 a2 : A, Decision (a1 = a2)}
           {DecB: forall b1 b2 : B, Decision (b1 = b2)}
           (φ: bijection A B) (l3 : A) (l4 : B)
           (H1: left φ l3 = None) (H2: right φ l4 = None) :=
  Bijection A B
            (fun l : A => if decide (l = l3) then Some l4 else left φ l)
            (fun l : B => if decide (l = l4) then Some l3 else right φ l)
            (@left_inverse_extend A B DecA DecB (left φ) (right φ)
                                  l3 l4 (bijection_is_left_inverse φ) H2)
            (@right_inverse_extend A B DecA DecB (left φ) (right φ)
                                   l3 l4 (bijection_is_right_inverse φ) H1).
Hint Unfold extend_bijection.

Lemma left_inverse_reduce {A B : Type}
      {DecA: forall a1 a2 : A, Decision (a1 = a2)}
      {DecB: forall b1 b2 : B, Decision (b1 = b2)}:
  forall (φ : bijection A B) l3 l4,
    left φ l3 = Some l4 ->
    left_inverse
      (fun l : A => if decide (l = l3) then None else left φ l)
      (fun l : B => if decide (l = l4) then None else right φ l).
Proof.
  intros.
  unfolds.
  intros.
  destruct (decide (x = l3)); subst; try discriminate.
  assert (right φ y = Some x) by (destruct φ; eauto 2).
  destruct (decide (y = l4)); subst; try assumption.
  assert (Some l4 <> left φ l3)
    by eauto using bijection_is_injective_left.
  exfalso; eauto 2.
Qed.

Lemma right_inverse_reduce {A B : Type}
      {DecA: forall a1 a2 : A, Decision (a1 = a2)}
      {DecB: forall b1 b2 : B, Decision (b1 = b2)}:
  forall φ l4 l3,
    left φ l3 = Some l4 ->
    right_inverse
      (fun l : A => if decide (l = l3) then None else left φ l)
      (fun l : B => if decide (l = l4) then None else right φ l).
Proof.
  intros.
  assert (right φ l4 = Some l3) by (destruct φ; eauto).
  unfolds.
  intros.
  destruct (decide (y = l4)); subst; try discriminate.
  assert (left φ x = Some y) by (destruct φ; eauto 2).
  destruct (decide (x = l3)); subst; try assumption.
  assert (Some l3 <> right φ l4)
    by eauto using bijection_is_injective_right.
  exfalso; eauto 2.
Qed.  

Definition reduce_bijection {A B : Type}
           {DecA: forall a1 a2 : A, Decision (a1 = a2)}
           {DecB: forall b1 b2 : B, Decision (b1 = b2)}
           (φ: bijection A B) (l3 : A) (l4 : B) (H : left φ l3 = Some l4) :=
  Bijection A B
            (fun l : A => if decide (l = l3) then None
                       else left φ l)
            (fun l : B => if decide (l = l4) then None
                       else right φ l)
            (left_inverse_reduce φ l3 l4 H)
            (right_inverse_reduce φ l4 l3 H).

Lemma reduce_bijection_lookup_eq_left {A B : Type}
      {DecA: forall a1 a2 : A, Decision (a1 = a2)}
      {DecB: forall b1 b2 : B, Decision (b1 = b2)}:
  forall f (a : A) (b : B) H,
    left (reduce_bijection f a b H) a = None.
Proof.
  intros.
  unfold left.
  unfold reduce_bijection.
  destruct (decide (a = a)); subst.
  - reflexivity.
  - exfalso; eauto.
Qed.

Lemma reduce_bijection_lookup_eq_right {A B : Type}
      {DecA: forall a1 a2 : A, Decision (a1 = a2)}
      {DecB: forall b1 b2 : B, Decision (b1 = b2)}:
  forall f (a : A) (b : B) H,
    right (reduce_bijection f a b H) b = None.
Proof.
  intros.
  unfold right.
  unfold reduce_bijection.
  destruct (decide (b = b)); subst.
  - reflexivity.
  - exfalso; eauto.
Qed.

Lemma reduce_bijection_lookup_neq_left {A B : Type}
      {DecA: forall a1 a2 : A, Decision (a1 = a2)}
      {DecB: forall b1 b2 : B, Decision (b1 = b2)}:
  forall f (a1 a2 : A) (b : B) H,
    a1 <> a2 ->
    left (reduce_bijection f a1 b H) a2 = left f a2.
Proof.
  intros.
  unfold left.
  unfold reduce_bijection.
  destruct (decide (a2 = a1)); subst.
  - exfalso; eauto.
  - destruct f.
    unfold left.
    reflexivity.
Qed.

Lemma reduce_bijection_lookup_neq_right {A B : Type}
      {DecA: forall a1 a2 : A, Decision (a1 = a2)}
      {DecB: forall b1 b2 : B, Decision (b1 = b2)}:
  forall f (a : A) (b1 b2 : B) H,
    b1 <> b2 ->
    right (reduce_bijection f a b1 H) b2 = right f b2.
Proof.
  intros.
  unfold right.
  unfold reduce_bijection.
  destruct (decide (b2 = b1)); subst.
  - exfalso; eauto.
  - destruct f.
    unfold right.
    reflexivity.
Qed.

Notation "φ '[' H1 ',' H2 '⊢' a '<->' b ']'" :=
  (extend_bijection φ a b H1 H2) (at level 10, no associativity).

Lemma left_extend_bijection_eq {A B: Type}
           {DecA: forall a1 a2 : A, Decision (a1 = a2)}
           {DecB: forall b1 b2 : B, Decision (b1 = b2)}:
  forall (φ : bijection A B) loc1 loc2 H1 H2,
    left (extend_bijection φ loc1 loc2 H1 H2) loc1 = Some loc2.
Proof.
  intros.
  unfold extend_bijection in *.
  unfold left.
  destruct (decide (loc1 = loc1)); subst.
  - reflexivity.
  - exfalso; eauto.
Qed.
Hint Resolve left_extend_bijection_eq.

Lemma right_extend_bijection_eq {A B: Type}
           {DecA: forall a1 a2 : A, Decision (a1 = a2)}
           {DecB: forall b1 b2 : B, Decision (b1 = b2)}:
  forall (φ : bijection A B) loc1 loc2 H1 H2,
    right (extend_bijection φ loc1 loc2 H1 H2) loc2 = Some loc1.
Proof.
  intros.
  unfold extend_bijection in *.
  unfold right.
  destruct (decide (loc2 = loc2)); subst.
  - reflexivity.
  - exfalso; eauto.
Qed.
Hint Resolve left_extend_bijection_eq.

Lemma left_extend_bijection_neq {A B: Type}
           {DecA: forall a1 a2 : A, Decision (a1 = a2)}
           {DecB: forall b1 b2 : B, Decision (b1 = b2)}:
  forall (φ : bijection A B) loc1 loc2 loc3 H1 H2,
    loc1 <> loc3 ->
    left (extend_bijection φ loc1 loc2 H1 H2) loc3 = left φ loc3.
Proof.
  intros.
  unfold extend_bijection in *.
  unfold left in *.
  destruct (decide (loc3 = loc1)); subst.
  - exfalso; eauto.
  - destruct φ.
    reflexivity.
Qed.
Hint Resolve left_extend_bijection_neq.

Lemma right_extend_bijection_neq {A B: Type}
      {DecA: forall a1 a2 : A, Decision (a1 = a2)}
      {DecB: forall b1 b2 : B, Decision (b1 = b2)}:
  forall (φ : bijection A B) loc1 loc2 loc3 H1 H2,
    loc2 <> loc3 ->
    right (extend_bijection φ loc1 loc2 H1 H2) loc3 = right φ loc3.
Proof.
  intros.
  unfold extend_bijection in *.
  unfold right in *.
  destruct φ in *.
  unfold left in *.
  destruct (decide (loc3 = loc2)); subst.
  - exfalso; eauto.
  - reflexivity.
Qed.
Hint Resolve right_extend_bijection_neq.

Lemma identity_bijection:
  forall A,
    bijection A A.
Proof.
  intros.
  apply (Bijection A A (fun x => Some x) (fun y => Some y)).
  - unfold left_inverse; eauto.
  - unfold right_inverse; eauto.
Defined.

Lemma identity_bijection_is_identity_left:
  forall A B (φ : bijection A B) x,
    left (bijection_compose (identity_bijection A) φ) x = left φ x.
Proof.
  intros.
  unfold left.
  unfold bijection_compose.
  destruct φ.
  unfold identity_bijection.
  unfold fun_compose.
  reflexivity.
Qed.

Lemma identity_bijection_is_identity_right:
  forall A B (φ : bijection A B) x,
    right (bijection_compose (identity_bijection A) φ) x = right φ x.
Proof.
  intros.
  unfold right.
  unfold bijection_compose.
  destruct φ.
  unfold identity_bijection.
  unfold fun_compose.
  destruct (g x); reflexivity.
Qed.

Lemma inverse_identity_is_identity {A: Type}:
  inverse (identity_bijection A) = identity_bijection A.
Proof.
  reflexivity.
Qed.

Definition pred_func {A : Type} (P: A -> Prop)
           (DecP: forall a : A, {P a} + {~ P a}) :=
  fun a : A => if DecP a then Some a else None.

Lemma left_inverse_pred_func:
  forall {A : Type}
    (P : A -> Prop)
    (DecP: forall a : A, {P a} + {~ P a}),
    left_inverse (pred_func P DecP) (pred_func P DecP).
Proof.
  intros.
  unfolds.
  intros.
  unfold pred_func in *.
  destruct (DecP x).
  - rewrite_inj.
    destruct (DecP y); try contradiction.
    reflexivity.
  - discriminate.
Qed.

Lemma right_inverse_pred_func:
  forall {A : Type}
    (P : A -> Prop)
    (DecP: forall a : A, {P a} + {~ P a}),
    right_inverse (pred_func P DecP) (pred_func P DecP).
Proof.
  intros.
  unfolds.
  intros.
  unfold pred_func in *.
  destruct (DecP y).
  - rewrite_inj.
    destruct (DecP x); try contradiction.
    reflexivity.
  - discriminate.
Qed.

Definition pred_bijection {A : Type} (P : A -> Prop)
           (DecP: forall a : A, {P a} + {~ P a}) : bijection A A :=
  Bijection A A (pred_func P DecP) (pred_func P DecP)
            (left_inverse_pred_func P DecP)
            (right_inverse_pred_func P DecP).

Definition filtered {A B : Type} (P: A -> Prop) (φ: bijection A B) (ψ: bijection A B) :=
  (forall a, (~ P a -> left ψ a = None) /\
        (P a -> left ψ a = left φ a)).
Hint Unfold filtered.

Definition filtered' {A B : Type} (P: B -> Prop) (φ: bijection A B) (ψ: bijection A B) :=
  (forall b, (~ P b -> right ψ b = None) /\
        (P b -> right ψ b = right φ b)).
Hint Unfold filtered'.

Lemma pred_compose_left_some {A B : Type}:
  forall (P : A -> Prop) (DecP: forall a, {P a} + {~ P a}) (φ : bijection A B) a b,
    left (bijection_compose (pred_bijection P DecP) φ) a = Some b ->
    P a.
Proof.
  intros.
  unfold left, bijection_compose in *.
  destruct φ.
  unfold pred_bijection, fun_compose, pred_func in *.
  destruct (DecP a); [assumption | discriminate].
Qed.

Lemma pred_compose_left_some' {A B : Type}:
  forall (P : B -> Prop) (DecP: forall b, {P b} + {~ P b}) (φ : bijection A B) a b,
    left (bijection_compose φ (pred_bijection P DecP)) a = Some b ->
    P b.
Proof.
  intros.
  unfold left, bijection_compose in *.
  destruct φ.
  unfold pred_bijection, fun_compose, pred_func in *.
  assert (f a = Some b).
  {
    destruct (f a).
    - destruct (DecP b0); congruence.
    - congruence.
  }
  decide_exist in *.
  destruct (DecP b); [assumption | discriminate].
Qed.

Lemma not_pred_compose_left_implies_none {A B : Type}:
  forall (P : A -> Prop) (DecP: forall a, {P a} + {~ P a}) (φ : bijection A B) a,
    ~ P a ->
    left (bijection_compose (pred_bijection P DecP) φ) a = None.
Proof.
  intros.
  unfold left, bijection_compose in *.
  destruct φ.
  unfold pred_bijection, fun_compose, pred_func in *.
  destruct (DecP a).
  - contradiction.
  - reflexivity.
Qed.
Hint Resolve not_pred_compose_left_implies_none.

Lemma not_pred_compose_left_implies_none' {A B : Type}:
  forall (P : B -> Prop) (DecP: forall b, {P b} + {~ P b}) (φ : bijection A B) b,
    ~ P b ->
    right (bijection_compose φ (pred_bijection P DecP)) b = None.
Proof.
  intros.
  unfold right, bijection_compose in *.
  destruct φ.
  unfold pred_bijection, fun_compose, pred_func in *.
  destruct (DecP b).
  - contradiction.
  - reflexivity.
Qed.
Hint Resolve not_pred_compose_left_implies_none'.

Lemma pred_compose_left_implies_same {A B : Type}:
  forall (P : A -> Prop) (DecP: forall a, {P a} + {~ P a}) (φ : bijection A B) a,
    P a ->
    left (bijection_compose (pred_bijection P DecP) φ) a = left φ a.
Proof.
  intros.
  unfold left, bijection_compose in *.
  destruct φ.
  unfold pred_bijection, fun_compose, pred_func in *.
  destruct (DecP a).
  - reflexivity.
  - contradiction.
Qed.
Hint Resolve pred_compose_left_implies_same.

Lemma pred_compose_left_implies_same' {A B : Type}:
  forall (P : B -> Prop) (DecP: forall b, {P b} + {~ P b}) (φ : bijection A B) b,
    P b ->
    right (bijection_compose φ (pred_bijection P DecP)) b = right φ b.
Proof.
  intros.
  unfold right, bijection_compose in *.
  destruct φ.
  unfold pred_bijection, fun_compose, pred_func in *.
  destruct (DecP b).
  - reflexivity.
  - contradiction.
Qed.
Hint Resolve pred_compose_left_implies_same'.

Lemma filter_bijection {A B : Type}:
  forall (P: A -> Prop)
    (DecP : forall a, {P a} + {~ P a})
    (φ : bijection A B),
    { ψ : bijection A B | filtered P φ ψ }.
Proof.
  intros.
  exists (bijection_compose (pred_bijection P DecP) φ).
  unfolds.
  intros.
  splits; intros; eauto.
Qed.

Lemma filter_bijection' {A B : Type}:
  forall (P: B -> Prop)
    (DecP : forall b, {P b} + {~ P b})
    (φ : bijection A B),
    { ψ : bijection A B | filtered' P φ ψ }.
Proof.
  intros.
  exists (bijection_compose φ (pred_bijection P DecP)).
  unfolds.
  intros.
  splits; intros; eauto.
Qed.

Lemma filtered_eq_if {A B : Type}:
  forall a b (P : A -> Prop) (DecP: forall a, {P a} + {~ P a})
    (ψ : bijection A B) (φ : bijection A B),
    left ψ a = Some b ->
    filtered P φ ψ ->
    left φ a = Some b.
Proof.
  intros.
  destruct (DecP a).
  - assert (left ψ a = left φ a) by (eapply H0; eauto).
    congruence.
  - assert (left ψ a = None) by (eapply H0; eauto).
    congruence.
Qed.
Hint Resolve filtered_eq_if.

Lemma filtered_eq_if' {A B : Type}:
  forall a b (P : B -> Prop) (DecP: forall b, {P b} + {~ P b})
    (ψ : bijection A B) (φ : bijection A B),
    right ψ b = Some a ->
    filtered' P φ ψ ->
    right φ b = Some a.
Proof.
  intros.
  destruct (DecP b).
  - assert (right ψ b = right φ b) by (eapply H0; eauto).
    congruence.
  - assert (right ψ b = None) by (eapply H0; eauto).
    congruence.
Qed.
Hint Resolve filtered_eq_if'.

Lemma filtered_bijection_is_subset {A B : Type}:
  forall (P : A -> Prop) (DecP: forall a, {P a} + {~ P a}) (φ ψ: bijection A B) a b,
    filtered P φ ψ ->
    left ψ a = Some b ->
    left φ a = Some b.
Proof.
  intros.
  eauto.
Qed.
Hint Resolve filtered_bijection_is_subset.

Lemma filtered_bijection_is_subset' {A B : Type}:
  forall (P : B -> Prop) (DecP: forall b, {P b} + {~ P b}) (φ ψ: bijection A B) a b,
    filtered' P φ ψ ->
    right ψ b = Some a ->
    right φ b = Some a.
Proof.
  intros.
  eauto.
Qed.
Hint Resolve filtered_bijection_is_subset'.

Lemma filtered_bijection_is_subset_transpose_left {A B : Type}:
  forall (P : A -> Prop)
    (DecP: forall a, {P a} + {~ P a})
    (φ ψ : bijection A B) a,
    filtered P φ ψ ->
    left φ a = None ->
    left ψ a = None.
Proof.
  intros.
  destruct (left ψ a) eqn:H'.
  -assert (left φ a = Some b) by eauto.
   congruence.
  - reflexivity.
Qed.
Hint Resolve filtered_bijection_is_subset_transpose_left.

Lemma filtered_bijection_is_subset_transpose_right {A B : Type}:
  forall (P : B -> Prop)
    (DecP: forall b, {P b} + {~ P b})
    (φ ψ : bijection A B) b,
    filtered' P φ ψ ->
    right φ b = None ->
    right ψ b = None.
Proof.
  intros.
  destruct (right ψ b) eqn:H'.
  - assert (right φ b = Some a) by eauto.
    congruence.
  - reflexivity.
Qed.
Hint Resolve filtered_bijection_is_subset_transpose_right.

Lemma filter_true {A B : Type}:
  forall (P : A -> Prop)
    (φ ψ : bijection A B)
    a b,
    P a ->
    filtered P φ ψ ->
    left φ a = Some b ->
    left ψ a = Some b.
Proof.
  intros.
  unfold filtered in *.
  destruct (H0 a).
  assert (left ψ a = left φ a) by eauto.
  congruence.
Qed.
Hint Resolve filter_true.

Lemma filter_true' {A B : Type}:
  forall (P : B -> Prop)
    (φ ψ : bijection A B)
    a b,
    P b ->
    filtered' P φ ψ ->
    right φ b = Some a ->
    right ψ b = Some a.
Proof.
  intros.
  unfold filtered in *.
  destruct (H0 b).
  assert (right ψ b = right φ b) by eauto.
  congruence.
Qed.
Hint Resolve filter_true'.

Lemma filtered_bijection_some_implies_predicate {A B : Type}:
  forall (P : A -> Prop) (DecP : forall a, {P a} + {~ P a})
    (φ ψ : bijection A B) a b,
    filtered P φ ψ ->
    left ψ a = Some b ->
    P a.
Proof.
  intros.
  unfold filtered in *.
  destruct (H a).
  destruct (DecP a); eauto 2.
  assert (left ψ a = None) by eauto.
  congruence.
Qed.

Lemma filtered_bijection_some_implies_predicate' {A B : Type}:
  forall (P : B -> Prop) (DecP : forall b, {P b} + {~ P b})
    (φ ψ : bijection A B) a b,
    filtered' P φ ψ ->
    right ψ b = Some a ->
    P b.
Proof.
  intros.
  unfold filtered in *.
  destruct (H b).
  destruct (DecP b); eauto 2.
  assert (right ψ b = None) by eauto.
  congruence.
Qed.

Lemma implies_left_compose {A B C : Type}:
  forall (f : bijection A B) (g : bijection B C)
    x y z,
    left f x = Some y ->
    left g y = Some z ->
    left (bijection_compose f g) x = Some z.
Proof.
  intros.
  unfold left, bijection_compose.
  destruct g, f.
  unfold left, fun_compose in *.
  break_match; congruence.
Qed.
Hint Resolve implies_left_compose.

Lemma implies_right_compose {A B C : Type}:
  forall (f : bijection A B) (g : bijection B C)
    x y z,
    right f y = Some x ->
    right g z = Some y ->
    right (bijection_compose f g) z = Some x.
Proof.
  intros.
  unfold right, bijection_compose.
  destruct g, f.
  unfold right, fun_compose in *.
  break_match; congruence.
Qed.
Hint Resolve implies_right_compose.

Section BijectionProofIrrelevance.

  Require Import FunctionalExtensionality.
  
  Axiom bijection_proof_irrelevance:
    forall (A B : Type) (f g : bijection A B),
      left f = left g ->
      right f = right g ->
      f = g.
  
  Lemma compose_id_left {A B: Type}:
    forall φ: bijection A B,
      bijection_compose (identity_bijection A) φ = φ.
  Proof.
    intros.
    unfold bijection_compose.
    unfold identity_bijection.
    destruct φ.
    apply bijection_proof_irrelevance.
    - reflexivity.
    - unfold right.
      unfold fun_compose.
      extensionality x.
      destruct (g x); eauto.
  Qed.
  
  Lemma compose_id_right {A B: Type}:
    forall φ: bijection A B,
      bijection_compose φ (identity_bijection B) = φ.
  Proof.
    intros.
    unfold bijection_compose.
    unfold identity_bijection.
    destruct φ.
    apply bijection_proof_irrelevance.
    - unfold left.
      unfold fun_compose.
      extensionality x.
      destruct (f x); eauto.
    - reflexivity.
  Qed.

End BijectionProofIrrelevance.