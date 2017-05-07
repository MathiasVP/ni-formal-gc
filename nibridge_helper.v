Require Import id_and_loc augmented mmemory mimperative language mlattice bridge types bijection Coq.Program.Tactics Coq.Program.Equality Arith Omega tactics low_equivalence decision preservation Coq.Program.Basics Coq.Logic.FunctionalExtensionality.
Require Import LibTactics.
Set Implicit Arguments.

Module NIBridgeHelper (L : Lattice) (M: Memory L).
  Module Preserve := Preservation L M.
  Import Preserve LowEq B Aug Imp TDefs M T MemProp LatProp Lang L.

Inductive contains_low_backat: level_proj1 -> cmd -> Prop :=
| ContainsLowBackAt:
    forall ℓ l n,
      l ⊑ ℓ ->
      contains_low_backat ℓ (BackAt l n)
| ContainsLowBackAtSeq_left:
    forall ℓ c1 c2,
      contains_low_backat ℓ c1 -> contains_low_backat ℓ (c1;; c2)
| ContainsLowBackAtSeq_right:
    forall ℓ c1 c2,
      contains_low_backat ℓ c2 -> contains_low_backat ℓ (c1;; c2)
| ContainsLowBackAtIf_1:
    forall ℓ e c1 c2,
      contains_low_backat ℓ c1 -> contains_low_backat ℓ (If e c1 c2)
| ContainsLowBackAtIf_2:
    forall ℓ e c1 c2,
      contains_low_backat ℓ c2 -> contains_low_backat ℓ (If e c1 c2)
| ContainsLowBackAtWhile:
    forall ℓ e c,
      contains_low_backat ℓ c -> contains_low_backat ℓ (While e c)
| ContainsLowBackAtAt:
    forall ℓ ℓ_at e c,
      contains_low_backat ℓ c -> contains_low_backat ℓ (At ℓ_at e c).
Hint Constructors contains_low_backat.

Inductive ends_with_low_backat : level_proj1 -> cmd -> Prop :=
  EndsWithLowBackAtBackAt:
    forall ℓ l n,
      l ⊑ ℓ ->
      ends_with_low_backat ℓ (BackAt l n)
| EndsWithLowBackAtSeq:
    forall ℓ c1 c2,
      ~ contains_low_backat ℓ c1 ->
      ends_with_low_backat ℓ c2 -> ends_with_low_backat ℓ (c1;; c2)
| EndsWithLowBackAtAt:
    forall ℓ c1 c2 pc e,
      ~ contains_low_backat ℓ c1 ->
      ends_with_low_backat ℓ c2 -> ends_with_low_backat ℓ (At pc e c1).

Ltac invert_ends_with_backat :=
  match goal with
    [H: ends_with_low_backat _ _ |- _] =>
    inverts H
  end.

Lemma not_contains_low_backat_if:
  forall ℓ e c1 c2,
    ~ contains_low_backat ℓ (If e c1 c2) ->
    ~ contains_low_backat ℓ c1 /\
    ~ contains_low_backat ℓ c2.
Proof.
  intros.
  splits*.
Qed.
Hint Resolve not_contains_low_backat_if.

Lemma not_contains_low_backat_seq:
  forall ℓ c1 c2,
    ~ contains_low_backat ℓ c1 ->
    ~ contains_low_backat ℓ c2 ->
    ~ contains_low_backat ℓ (c1 ;; c2).
Proof.
  intros.
  intro.
  inverts H1; contradiction.
Qed.
Hint Resolve not_contains_low_backat_seq.

Inductive high : level_proj1 -> Memory -> Heap -> loc -> Prop :=
  | HighReachable:
      forall ℓ_adv m h loc,
        reach m h loc ->
        high ℓ_adv m h loc
  | HighHeapLevel:
      forall ℓ_adv m h loc ℓ μ,
        heap_lookup loc h = Some (ℓ, μ) ->
        ~ ℓ ⊑ ℓ_adv ->
        high ℓ_adv m h loc.
  Hint Constructors high.

Definition wf_taint_bijection ℓ_adv (Φ : bijection loc loc) m h :=
  forall loc, (exists loc', left Φ loc = Some loc') <-> high ℓ_adv m h loc.
Hint Unfold wf_taint_bijection.

Inductive val_taint_eq: bijection loc loc -> sectype -> value -> value -> Prop :=
  ValUntatedNum:
    forall ℓ n Φ,
      val_taint_eq Φ (SecType Int (ℓ, ∘)) (ValNum n) (ValNum n)
| ValUntaintedLoc:
    forall τ ℓ ℓ_p loc loc' Φ,
      left Φ loc = Some loc' ->
      val_taint_eq Φ (SecType (Array τ ℓ_p) (ℓ, ∘)) (ValLoc loc) (ValLoc loc')
| ValTaintedNum:
    forall ℓ n1 n2 Φ,
      val_taint_eq Φ (SecType Int (ℓ, •)) (ValNum n1) (ValNum n2)
| ValTaintedLoc:
    forall τ ℓ ℓ_p loc1 loc2 Φ,
      val_taint_eq Φ (SecType (Array τ ℓ_p) (ℓ, •)) (ValLoc loc1) (ValLoc loc2).
Hint Constructors val_taint_eq.

Definition taint_eq_mem Φ Γ m1 m2 :=
  (forall x, (exists v, memory_lookup m1 x = Some v) <-> (exists v, memory_lookup m2 x = Some v))
  /\
  (forall x τ v1 v2,
      Γ x = Some τ ->
      memory_lookup m1 x = Some v1 ->
      memory_lookup m2 x = Some v2 ->
      val_taint_eq Φ τ v1 v2).
Hint Unfold taint_eq_mem.

Definition taint_eq_heap ℓ_adv Φ Σ1 Σ2 m1 h1 m2 h2 :=
  forall loc loc' ℓ1 ℓ2 μ1 μ2 τ,
    left Φ loc = Some loc' ->
    high ℓ_adv m1 h1 loc ->
    high ℓ_adv m2 h2 loc' ->
    heap_lookup loc h1 = Some (ℓ1, μ1) ->
    heap_lookup loc' h2 = Some (ℓ2, μ2) ->
    Σ1 loc = Some τ ->
    Σ2 loc' = Some τ ->
    ℓ1 = ℓ2 /\
    length_of loc h1 = length_of loc' h2 /\
    (forall n, (exists v, lookup μ1 n = Some v) <-> (exists v, lookup μ2 n = Some v)) /\
    (forall n v1 v2,
        reach m1 h1 loc ->
        reach m2 h2 loc' ->
        lookup μ1 n = Some v1 ->
        lookup μ2 n = Some v2 ->
        val_taint_eq Φ τ v1 v2).
Hint Unfold taint_eq_heap.

Definition taint_eq_heap_domain_eq (ℓ_adv : level_proj1) (Φ: bijection loc loc)
             (m1 m2 : Memory) (h1 h2 : Heap) :=
    forall l1 l2 ℓ,
      left Φ l1 = Some l2 ->
      ((exists μ, heap_lookup l1 h1 = Some (ℓ, μ)) /\ high ℓ_adv m1 h1 l1)
      <->
      ((exists ν, heap_lookup l2 h2 = Some (ℓ, ν)) /\ high ℓ_adv m2 h2 l2).
Hint Unfold taint_eq_heap_domain_eq.
  
Definition taint_eq_reach Φ m1 h1 m2 h2 :=
  forall loc loc',
    left Φ loc = Some loc' ->
    reach m1 h1 loc <-> reach m2 h2 loc'.
Hint Unfold taint_eq_reach.

Definition taint_eq_stenv (Φ : bijection loc loc) (Σ1 Σ2 : stenv) :=
  forall loc1 loc2 τ,
    left Φ loc1 = Some loc2 ->
    (Σ1 loc1 = Some τ <-> Σ2 loc2 = Some τ).
Hint Unfold taint_eq_stenv.

Definition taint_eq_heap_size ℓ_adv h1 h2 :=
  forall l, ~ l ⊑ ℓ_adv -> size l h1 = size l h2.
Hint Unfold taint_eq_heap_size.

Lemma val_taint_eq_plus:
  forall ℓ1 ℓ2 Φ ι1 ι2 n1 n1' n2 n2',
    val_taint_eq Φ (SecType Int (ℓ1, ι1)) (ValNum n1) (ValNum n1') ->
    val_taint_eq Φ (SecType Int (ℓ2, ι2)) (ValNum n2) (ValNum n2') ->
    val_taint_eq Φ (SecType Int (ℓ1 ⊔ ℓ2, LH.join ι1 ι2)) (ValNum (n1 + n2))
                 (ValNum (n1' + n2')).
Proof.
  intros.
  destruct (LH.join ι1 ι2) eqn:H_ι.
  - assert (ι1 = ∘).
    {
      destruct ι1.
      - reflexivity.
      - discriminate.
    }
    subst.
    assert (ι2 = ∘).
    {
      destruct ι2.
      - reflexivity.
      - discriminate.
    }
    subst.
    inverts H; inverts H0.
    eauto.
  - eauto.
Qed.
Hint Resolve val_taint_eq_plus.

Lemma val_taint_eq_times:
  forall ℓ1 ℓ2 Φ ι1 ι2 n1 n1' n2 n2',
    val_taint_eq Φ (SecType Int (ℓ1, ι1)) (ValNum n1) (ValNum n1') ->
    val_taint_eq Φ (SecType Int (ℓ2, ι2)) (ValNum n2) (ValNum n2') ->
    val_taint_eq Φ (SecType Int (ℓ1 ⊔ ℓ2, LH.join ι1 ι2)) (ValNum (n1 * n2))
                 (ValNum (n1' * n2')).
Proof.
  intros.
  destruct (LH.join ι1 ι2) eqn:H_ι.
  - assert (ι1 = ∘).
    {
      destruct ι1.
      - reflexivity.
      - discriminate.
    }
    subst.
    assert (ι2 = ∘).
    {
      destruct ι2.
      - reflexivity.
      - discriminate.
    }
    subst.
    inverts H; inverts H0.
    eauto.
  - eauto.
Qed.
Hint Resolve val_taint_eq_times.

Lemma val_taint_eq_num_refl:
  forall Φ n ε,
    val_taint_eq Φ (SecType Int ε) (ValNum n) (ValNum n).
Proof.
  intros.
  destruct ε as [ℓ ι].
  destruct ι; eauto.
Qed.
Hint Resolve val_taint_eq_num_refl.

Lemma val_taint_eq_loc_refl:
  forall loc' ℓ τ ε,
    val_taint_eq (identity_bijection loc)
                 (SecType (Array τ ℓ) ε) (ValLoc loc') (ValLoc loc').
Proof.
  intros.
  destruct ε as [ℓ' ι'].
  destruct ι'; eauto.
Qed.
Hint Resolve val_taint_eq_loc_refl.

Lemma val_taint_eq_refl:
  forall τ v ε,
    (τ = Int -> exists n, v = ValNum n) ->
    (forall τ' ℓ, τ = Array τ' ℓ -> exists loc, v = ValLoc loc) ->
    val_taint_eq (identity_bijection loc) (SecType τ ε) v v.
Proof.
  intros.
  destruct τ.
  - specialize_gen.
    super_destruct; subst.
    eauto.
  - repeat specialize_gen.
    super_destruct; subst.
    eauto.
Qed.
Hint Resolve val_taint_eq_refl.

Lemma val_taint_eq_trans:
  forall Φ Ψ τ v1 v2 v3,
    val_taint_eq Φ τ v1 v2 ->
    val_taint_eq Ψ τ v2 v3 ->
    val_taint_eq (bijection.bijection_compose Φ Ψ) τ v1 v3.
Proof.
  intros.
  destruct τ as [σ [ℓ ι]].
  destruct ι.
  - inverts H; inverts H0; eauto.
  - inverts H; inverts H0; eauto.
Qed.

Ltac invert_val_taint_eq :=
  match goal with
    [H: val_taint_eq _ _ _ _ |- _] =>
    inverts H
  end.

Lemma eval_taint_eq_possibilistic:
  forall Γ Φ e σ ℓ m1 m2 ι v1,
    expr_has_type Γ e (SecType σ (ℓ, ι)) ->
    wf_tenv Γ m1 ->
    wf_tenv Γ m2 ->
    taint_eq_mem Φ Γ m1 m2 ->
    eval m1 e = Some v1 ->
    exists v2,
      eval m2 e = Some v2 /\
      val_taint_eq Φ (SecType σ (ℓ, ι)) v1 v2.
Proof.
  intros.
  revert v1 H3.
  dependent induction H; intros.
  - unfold eval in *.
    rewrite_inj.
    exists (ValNum n).
    splits*.
  - unfold eval in *.
    assert (exists v2, memory_lookup m2 x = Some v2).
    {
      eapply H2; eauto.
    }
    super_destruct; subst.
    exists v2.
    splits*.
    assert (val_taint_eq Φ (SecType σ (ℓ, ι)) v1 v2).
    {
      eapply H2; eauto.
    }
    invert_val_taint_eq; eauto.
  - destruct l1 as [ℓ1 ι1].
    destruct l2 as [ℓ2 ι2].
    rewrite -> about_eval in * |-.
    repeat break_match; try congruence.
    + repeat injects; subst.
      assert (exists v2,
                 eval m2 e1 = Some v2 /\ val_taint_eq Φ (SecType Int (ℓ1, ι1)) (ValNum n) v2) by eauto 2.
      assert (exists v2,
       eval m2 e2 = Some v2 /\ val_taint_eq Φ (SecType Int (ℓ2, ι2)) (ValNum n0) v2) by eauto 2.
      super_destruct; subst.
      do 2 invert_val_taint_eq.
      * exists (ValNum (n + n0)).
        splits*.
        rewrite -> about_eval.
        do 2 decide_exist.
        reflexivity.
      * exists (ValNum (n2 + n0)).
        splits*.
        rewrite -> about_eval.
        do 2 decide_exist.
        reflexivity.
      * exists (ValNum (n + n2)).
        splits*.
        rewrite -> about_eval.
        do 2 decide_exist.
        reflexivity.
      * exists (ValNum (n3 + n2)).
        splits*.
        rewrite -> about_eval.
        do 2 decide_exist.
        reflexivity.
    + repeat injects; subst.
      assert (exists v2,
                 eval m2 e1 = Some v2 /\ val_taint_eq Φ (SecType Int (ℓ1, ι1)) (ValNum n) v2) by eauto 2.
      assert (exists v2,
       eval m2 e2 = Some v2 /\ val_taint_eq Φ (SecType Int (ℓ2, ι2)) (ValNum n0) v2) by eauto 2.
      super_destruct; subst.
      do 2 invert_val_taint_eq.
      * exists (ValNum (n * n0)).
        splits*.
        rewrite -> about_eval.
        do 2 decide_exist.
        reflexivity.
      * exists (ValNum (n2 * n0)).
        splits*.
        rewrite -> about_eval.
        do 2 decide_exist.
        reflexivity.
      * exists (ValNum (n * n2)).
        splits*.
        rewrite -> about_eval.
        do 2 decide_exist.
        reflexivity.
      * exists (ValNum (n3 * n2)).
        splits*.
        rewrite -> about_eval.
        do 2 decide_exist.
        reflexivity.
Qed.
Hint Resolve eval_taint_eq_possibilistic.   

Lemma eval_taint_eq:
  forall Γ Φ e σ ℓ m1 m2 ι v1 v2,
    expr_has_type Γ e (SecType σ (ℓ, ι)) ->
    wf_tenv Γ m1 ->
    wf_tenv Γ m2 ->
    taint_eq_mem Φ Γ m1 m2 ->
    eval m1 e = Some v1 ->
    eval m2 e = Some v2 ->
    val_taint_eq Φ (SecType σ (ℓ, ι)) v1 v2.
Proof.
  intros.
  revert v1 v2 H3 H4.
  dependent induction H; intros.
  - eauto.
    unfold eval in *.
    rewrite_inj.
    destruct ι; eauto.
  - eapply H2; eauto.
  - destruct l1 as [ℓ1 ι1].
    destruct l2 as [ℓ2 ι2].
    rewrite -> about_eval in *.
    repeat break_match; try congruence.
    + repeat injects; subst.
      assert (val_taint_eq Φ (SecType Int (ℓ1, ι1)) (ValNum n1) (ValNum n)) by eauto 2.
      assert (val_taint_eq Φ (SecType Int (ℓ2, ι2)) (ValNum n2) (ValNum n0)) by eauto 2.
      eauto.
    + repeat injects.
      assert (val_taint_eq Φ (SecType Int (ℓ1, ι1)) (ValNum n1) (ValNum n)) by eauto 2.
      assert (val_taint_eq Φ (SecType Int (ℓ2, ι2)) (ValNum n2) (ValNum n0)) by eauto 2.
      eauto.
Qed.
Hint Resolve eval_taint_eq.

Lemma val_taint_eq_mon:
  forall ℓ1 ℓ2 ι1 ι2 v1 v2 Φ σ,
    val_taint_eq Φ (SecType σ (ℓ1, ι1)) v1 v2 ->
    LH.flowsto ι1 ι2 ->
    val_taint_eq Φ (SecType σ (ℓ2, ι2)) v1 v2.
Proof.
  intros.
  inverts H.
  - destruct ι2; eauto.
  - destruct ι2; eauto.
  - destruct ι2; eauto || discriminate.
  - destruct ι2; eauto || discriminate.
Qed.
Hint Resolve val_taint_eq_mon.

Lemma gc_preserves_taint_eq_heap:
  forall ℓ_adv c c' pc pc' m m' h h' t t' Σ Σ',
    gc_occurred c c' pc pc' m m' h h' t t' Σ Σ' ->
    wf_stenv Σ h ->
    taint_eq_heap ℓ_adv (identity_bijection loc) Σ Σ' m h m' h'.
Proof.
  intros.
  unfolds.
  intros.
  unfold left, identity_bijection in *; subst.
  injects.
  unfold gc_occurred in *.
  super_destruct; subst.
  rewrite_inj.
  destruct (heap_lookup loc' ([[h1_1_pc ⊎ h1_1_not_pc, H14] ⊎ h1_2, H13]))
           eqn:H_loc.
  - destruct p as [l μ].
    rewrite_inj.
    destruct_disjoint_heap_lookup.
    + rewrite_inj.
      splits*.
      * assert (exists length, length_of loc' ([h1_1_pc ⊎ h1_1_not_pc, H14]) = Some length).
        {
          eapply length_of_lookup_correspondance; eauto 3.
        }
        super_destruct'; subst.
        rewrite -> H.
        eapply disjoint_union_length_of.
        eauto.
      * intros.
        rewrite_inj.
        destruct τ as [σ ε].
        eapply val_taint_eq_refl.
        { intros; subst; eauto. }
        { intros; subst; eauto. }
    + assert (heap_lookup loc' ([h1_1_pc ⊎ h1_1_not_pc, H14]) = None) by eauto.
      congruence.
  - discriminate.
    Unshelve.
    eauto.
Qed.
Hint Resolve gc_preserves_taint_eq_heap.

Ltac destruct_high :=
  match goal with
    [H: high _ _ _ _ |- _] =>
    inverts H
  end.

Lemma high_iff:
  forall ℓ_adv loc1 loc2 m1 h1 m2 h2 Φ,
    taint_eq_heap_domain_eq ℓ_adv Φ m1 m2 h1 h2 ->
    taint_eq_reach Φ m1 h1 m2 h2 ->
    left Φ loc1 = Some loc2 -> 
    high ℓ_adv m1 h1 loc1 <->
    high ℓ_adv m2 h2 loc2.
Proof.
  intros.
  splits; intros.
  - destruct_high.
    + eapply HighReachable.
      firstorder 2.
    + assert ((exists μ, heap_lookup loc2 h2 = Some (ℓ, μ)) /\ high ℓ_adv m2 h2 loc2).
      {
        eapply H; eauto.
      }
      super_destruct'; subst.
      eauto.
  - destruct_high.
    + eapply HighReachable.
      firstorder 2.
    + assert ((exists μ, heap_lookup loc1 h1 = Some (ℓ, μ)) /\ high ℓ_adv m1 h1 loc1).
      {
        eapply H; eauto.
      }
      super_destruct'; subst.
      eauto.
Qed.

Lemma taint_eq_heap_trans:
  forall ℓ_adv Σ Σ' Σ'' Φ Ψ m h m' h' m'' h'',
    taint_eq_reach Ψ m' h' m'' h'' ->
    taint_eq_stenv Φ Σ Σ' ->
    dangling_pointer_free m' h' ->
    taint_eq_heap ℓ_adv Φ Σ Σ' m h m' h' ->
    taint_eq_heap ℓ_adv Ψ Σ' Σ'' m' h' m'' h'' ->
    taint_eq_heap_domain_eq ℓ_adv Ψ m' m'' h' h'' ->
    taint_eq_heap ℓ_adv (bijection.bijection_compose Φ Ψ) Σ Σ'' m h m'' h''.
Proof.
  intros.
  unfold taint_eq_heap in *.
  intros.
  _apply left_compose in *.
  super_destruct.
  destruct my; try (repeat specialize_gen; congruence).
  assert (left Ψ l = Some loc') by eauto 2.
  assert (high ℓ_adv m' h' l).
  {
    eapply high_iff; eauto 2.
  }
  assert (exists ℓ μ, heap_lookup l h' = Some (ℓ, μ)).
  {
    destruct_high; eauto.
  }
  super_destruct; subst.
  assert (Σ' l = Some τ) by firstorder 2.
  remember_simple (H2 _ _ _ _ _ _ _ H5 H6 H15 H8 H16 H10 H17).
  super_destruct; subst.
  rewrite_inj.
  remember_simple (H3 _ _ _ _ _ _ _ H14 H15 H7 H16 H9 H17 H11).
  super_destruct; subst.
  splits*.
  - intros.
    rewrite -> H19.
    eauto.
  - intros.
    rewrite -> H20.
    eauto.
  - intros.
    assert (exists u, lookup μ n = Some u) by firstorder 2.
    super_destruct; subst.
    assert (reach m' h' l) by (eapply H; eauto 2).
    eapply val_taint_eq_trans; eauto.
Qed.

Inductive taint_eq_cmd: cmd -> cmd -> Prop :=
  TaintEqSkip: taint_eq_cmd Skip Skip
| TaintEqStop: taint_eq_cmd Stop Stop
| TaintEqAssign: forall x e,
    taint_eq_cmd (Assign x e) (Assign x e)
| TaintEqIf: forall c1 c2 c1' c2' e,
    taint_eq_cmd c1 c1' ->
    taint_eq_cmd c2 c2' ->
    taint_eq_cmd (If e c1 c2) (If e c1' c2')
| TaintEqWhile: forall e c c',
    taint_eq_cmd c c' ->
    taint_eq_cmd (While e c) (While e c')
| TaintEqSeq: forall c1 c2 c1' c2',
    taint_eq_cmd c1 c1' ->
    taint_eq_cmd c2 c2' ->
    taint_eq_cmd (c1 ;; c2) (c1' ;; c2')
| TaintEqAt: forall e l c c',
      taint_eq_cmd c c' ->
      taint_eq_cmd (At l e c) (At l e c')
| TaintEqBackAt: forall n1 n2 l,
    taint_eq_cmd (BackAt l n1) (BackAt l n2)
| TaintEqNewArr: forall x l e1 e2,
    taint_eq_cmd (NewArr x l e1 e2) (NewArr x l e1 e2)
| TaintEqSetArr: forall x e1 e2,
    taint_eq_cmd (SetArr x e1 e2) (SetArr x e1 e2)
| TaintEqGetArr: forall x y e,
    taint_eq_cmd (GetArr x y e) (GetArr x y e)
| TaintEqTime: forall x,
    taint_eq_cmd (Time x) (Time x)
| TaintEqTimeOut:
    taint_eq_cmd TimeOut TimeOut.
Hint Constructors taint_eq_cmd.

Definition taint_eq ℓ_adv Φ Γ Σ1 Σ2 c1 c2 m1 h1 m2 h2 :=
  taint_eq_cmd c1 c2 /\ taint_eq_mem Φ Γ m1 m2 /\ taint_eq_reach Φ m1 h1 m2 h2 /\
  taint_eq_heap ℓ_adv Φ Σ1 Σ2 m1 h1 m2 h2 /\ taint_eq_heap_size ℓ_adv h1 h2 /\
  taint_eq_heap_domain_eq ℓ_adv Φ m1 m2 h1 h2 /\ taint_eq_stenv Φ Σ1 Σ2.

Inductive taint_eq_events: tenv -> bijection loc loc -> event -> event -> Prop :=
| TaintEqEventEmpty:
    forall Γ Φ, taint_eq_events Γ Φ EmptyEvent EmptyEvent
| TaintEqEventAssign:
    forall Γ ℓ τ ι x Φ v1 v2,
      Γ x = Some (SecType τ ι) ->
      val_taint_eq Φ (SecType τ ι) v1 v2 ->
      taint_eq_events Γ Φ (AssignEvent ℓ x v1) (AssignEvent ℓ x v2)
| TaintEqEventNew:
    forall Γ x ℓ loc loc' Φ,
      left Φ loc = Some loc' ->
      taint_eq_events Γ Φ (NewEvent ℓ x loc) (NewEvent ℓ x loc')
| TaintEqEventGet:
    forall Γ ℓ_x x τ ι y Φ v1 v2,
      Γ x = Some (SecType τ ι) ->
      val_taint_eq Φ (SecType τ ι) v1 v2 ->
      taint_eq_events Γ Φ (GetEvent ℓ_x x y v1) (GetEvent ℓ_x x y v2)
| TaintEqEventSet:
    forall Γ ℓ ℓ_p ℓ_x τ ι x n Φ v1 v2,
      Γ x = Some (SecType (Array (SecType τ (ℓ, ι)) ℓ_p) (ℓ_x, ∘)) ->
      val_taint_eq Φ (SecType τ (ℓ, ι)) v1 v2 ->
      taint_eq_events Γ Φ (SetEvent ℓ ℓ_x x n v1) (SetEvent ℓ ℓ_x x n v2)
| TaintEqEventTime:
    forall Γ ℓ x n1 n2 Φ,
      Γ x = Some (SecType Int (ℓ, •)) ->
      taint_eq_events Γ Φ (TimeEvent ℓ x n1) (TimeEvent ℓ x n2)
| TaintEqEventRestore:
    forall ℓ n1 n2 Φ Γ,
      taint_eq_events Γ Φ (RestoreEvent ℓ n1) (RestoreEvent ℓ n2).
Hint Constructors taint_eq_events.

Definition ni_bridge (n1: nat) (ℓ: level_proj1): Prop :=
  forall Γ Σ1 Σ2 Σ3 Σ1' Σ3' φ Φ pc pc1' pc2'' c c' c2 c2' m1 m2 s1 s2'' h1 h2
    w1 w2'' t t2 g2'' s1' w1' ev1 ev2 pc_end n2 t',
    wf_bijection ℓ φ Γ Σ1 m1 h1 ->
    wf_bijection ℓ (inverse φ) Γ Σ2 s1 w1 ->
    wf_taint_bijection ℓ Φ s1 w1 ->
    wf_taint_bijection ℓ (inverse Φ) s1' w1' ->
    wellformed_aux Γ Σ1 ⟨c, pc, m1, h1, t⟩ pc_end ->
    wellformed_aux Γ Σ2 ⟨c, pc, s1, w1, t⟩ pc_end ->
    wellformed_aux Γ Σ3 ⟨c', pc, s1', w1', t'⟩ pc_end ->
    state_low_eq ℓ φ m1 h1 s1 w1 Γ Σ1 Σ2 ->
    pc ⊑ ℓ ->
    taint_eq ℓ Φ Γ Σ2 Σ3 c c' s1 w1 s1' w1' ->
    ⟨c, pc, m1, h1, t⟩ ↷ [ℓ, Γ, Σ1, Σ1', ev1, n1] ⟨c2, pc1', m2, h2, t2⟩ ->
    ⟨c', pc, s1', w1', t'⟩ ↷ [ℓ, Γ, Σ3, Σ3', ev2, n2] ⟨c2', pc2'', s2'', w2'', g2''⟩ ->
    c2 <> TimeOut ->
    c2' <> TimeOut ->
    exists ev1' n1' ψ Ψ s2' w2' Σ2',
      ⟨c, pc, s1, w1, t⟩ ↷ [ℓ, Γ, Σ2, Σ2', ev1', n1'] ⟨c2, pc1', s2', w2', t2⟩ /\
      pc1' ⊑ ℓ /\
      pc2'' = pc1' /\
      state_low_eq ℓ ψ m2 h2 s2' w2' Γ Σ1' Σ2'/\
      event_low_eq ℓ (left ψ) ev1 ev1' /\
      taint_eq_events Γ Ψ ev1' ev2 /\
      wf_bijection ℓ ψ Γ Σ1' m2 h2 /\
      wf_bijection ℓ (inverse ψ) Γ Σ2' s2' w2' /\
      wf_taint_bijection ℓ Ψ s2' w2' /\
      wf_taint_bijection ℓ (inverse Ψ) s2'' w2'' /\
      taint_eq ℓ Ψ Γ Σ2' Σ3' c2 c2' s2' w2' s2'' w2''.
Hint Unfold ni_bridge.

Lemma low_event_step_seq:
  forall ℓ c1 c2 c' pc m h t pc' m' h' t' Γ Σ Σ' ev,
    low_event_step ℓ ⟨c1;; c2, pc, m, h, t⟩ ⟨c', pc', m', h', t'⟩ Γ Σ Σ' ev ->
    (exists c1', c1' <> Stop /\
            low_event_step ℓ ⟨c1, pc, m, h, t⟩ ⟨c1', pc', m', h', t'⟩ Γ Σ Σ' ev /\
            c' = (c1';; c2))
    \/ low_event_step ℓ ⟨c1, pc, m, h, t⟩ ⟨Stop, pc', m', h', t'⟩ Γ Σ Σ' ev /\ c' = c2.
Proof.
  intros.
  invert_low_event_step.
  invert_event_step.
  - left.
    exists c1'.
    splits*.    
  - eauto.
  - invert_low_event.
Qed.
Hint Resolve low_event_step_seq.

Lemma high_event_step_seq:
  forall ℓ c1 c2 c' pc m h t pc' m' h' t' Γ Σ Σ' ev,
    high_event_step ℓ ⟨c1;; c2, pc, m, h, t⟩ ⟨c', pc', m', h', t'⟩ Γ Σ Σ' ev ->
    (exists c1', c1' <> Stop /\ high_event_step ℓ ⟨c1, pc, m, h, t⟩ ⟨c1', pc', m', h', t'⟩ Γ Σ Σ' ev /\ c' = (c1';; c2))
    \/ high_event_step ℓ ⟨c1, pc, m, h, t⟩ ⟨Stop, pc', m', h', t'⟩ Γ Σ Σ' ev /\ c' = c2 \/
    (gc_occurred (c1;; c2) c' pc pc' m m' h h' t t' Σ Σ' /\ ev = EmptyEvent).
Proof.
  intros.
  invert_high_event_step.
  invert_event_step.
  - left.
    exists c1'.
    eauto.
  - right; left.
    eauto.
  - right; right.
    splits*.
    unfolds.
    splits*.
    do 7 eexists.
    splits; reflexivity || eauto.
Qed.
Hint Resolve high_event_step_seq.

Ltac high_low_steps_with_expr_is_false t :=
  invert_low_event_step; invert_high_event_step;
  do 2 invert_event_step; 
  [ do 2 invert_wf_aux;
    repeat specialize_gen;
    do 2 invert_wt_cmd;
    rewrite_inj;
    invert_lifted;
    match goal with
      [H: high_event _ _ |- _] =>
      contradiction H
    end;
    eapply t; eauto;
    invert_low_event;
    eauto
  | invert_low_event
  |  invert_low_event; eauto
  | invert_low_event ].

Ltac high_low_steps_empty_event_is_false :=
  invert_low_event_step;
  invert_high_event_step;
  do 2 invert_event_step;
  contradiction.

Ltac low_and_high_event_is_false t :=
  repeat match goal with
         | [H1: context[low_event_step], H2: context[high_event_step] |- _] =>
           invert_low_event_step;
           invert_high_event_step;
           do 2 invert_event_step;
           unfold high_event in *;
           do 2 invert_wf_aux;
           do 2 invert_wt_cmd
         | [H1: low_event _ _, H2: ~ low_event _ _ |- _] =>
           contradiction H2;
           inverts H1;
           apply t; eauto
         end.

Lemma stop_does_no_event_step:
  forall c' pc pc' m m' h h' t t' ev Γ Σ Σ',
    (⟨ STOP, pc, m, h, t ⟩) ⇒ [ev, Γ, Σ, Σ'] ⟨c', pc', m', h', t'⟩ ->
    gc_occurred Stop c' pc pc' m m' h h' t t' Σ Σ' /\ ev = EmptyEvent.
Proof.
  intros.
  invert_event_step.
  splits*.
Qed.
Hint Resolve stop_does_no_event_step.

Lemma timeout_does_no_event_step:
  forall c' pc pc' m m' h h' t t' ev Γ Σ Σ',
    (⟨TIMEOUT, pc, m, h, t ⟩) ⇒ [ev, Γ, Σ, Σ'] ⟨c', pc', m', h', t'⟩ ->
    gc_occurred TimeOut c' pc pc' m m' h h' t t' Σ Σ' /\ ev = EmptyEvent.
Proof.
  intros.
  invert_event_step.
  splits*.
Qed.
Hint Resolve timeout_does_no_event_step.

Lemma stop_does_no_low_event_step:
  forall ℓ pc m h t cfg ev Γ Σ Σ',
    low_event_step ℓ ⟨Stop, pc, m, h, t⟩ cfg Γ Σ Σ' ev -> False.
Proof.
  intros.
  invert_low_event_step.
  destruct cfg.
  _apply stop_does_no_event_step in *.
  super_destruct.
  subst.
  invert_low_event.
Qed.
Hint Resolve stop_does_no_low_event_step.

Lemma timeout_does_no_low_event_step:
  forall ℓ pc m h t cfg ev Γ Σ Σ',
    low_event_step ℓ ⟨TIMEOUT, pc, m, h, t⟩ cfg Γ Σ Σ' ev -> False.
Proof.
  intros.
  invert_low_event_step.
  destruct cfg.
  _apply timeout_does_no_event_step in *.
  super_destruct.
  subst.
  invert_low_event.
Qed.
Hint Resolve timeout_does_no_low_event_step.

Lemma stop_does_no_high_event_step:
  forall ℓ c' pc pc' m m' h h' t t' ev Γ Σ Σ',
    high_event_step ℓ ⟨Stop, pc, m, h, t⟩ ⟨c', pc', m', h', t'⟩ Γ Σ Σ' ev ->
    gc_occurred Stop c' pc pc' m m' h h' t t' Σ Σ' /\ ev = EmptyEvent.
Proof.
  intros.
  invert_high_event_step.
  _apply stop_does_no_event_step in *.
  eauto.
Qed.  
Hint Resolve stop_does_no_high_event_step.

Lemma timeout_does_no_high_event_step:
  forall ℓ c' pc pc' m m' h h' t t' ev Γ Σ Σ',
    high_event_step ℓ ⟨TimeOut, pc, m, h, t⟩ ⟨c', pc', m', h', t'⟩ Γ Σ Σ' ev ->
    gc_occurred TimeOut c' pc pc' m m' h h' t t' Σ Σ' /\ ev = EmptyEvent.
Proof.
  intros.
  invert_high_event_step.
  _apply timeout_does_no_event_step in *.
  eauto.
Qed.  
Hint Resolve timeout_does_no_high_event_step.

Lemma stop_does_no_bridge_step:
  forall pc m h t ℓ ev n c' pc' m' h' t' Γ Σ Σ',
    ⟨Stop, pc, m, h, t ⟩ ↷ [ℓ, Γ, Σ, Σ', ev, n] ⟨c', pc', m', h', t' ⟩ ->
    gc_occurred Stop c' pc pc' m m' h h' t t' Σ Σ' /\ ev = EmptyEvent.
Proof.
  intros.
  invert_bridge_step; eauto.
  - _apply stop_does_no_low_event_step in *.
    contradiction.
  - destruct cfg2.
    _apply stop_does_no_high_event_step in *.
    super_destruct.
    unfold gc_occurred in * |-.
    super_destruct.
    subst.
    exfalso; eauto.
Qed.
Hint Resolve stop_does_no_bridge_step.

Lemma timeout_does_no_bridge_step:
  forall pc m h t ℓ ev n c' pc' m' h' t' Γ Σ Σ',
    ⟨TimeOut, pc, m, h, t ⟩ ↷ [ℓ, Γ, Σ, Σ', ev, n] ⟨c', pc', m', h', t' ⟩ ->
    gc_occurred TimeOut c' pc pc' m m' h h' t t' Σ Σ' /\ ev = EmptyEvent.
Proof.
  intros.
  invert_bridge_step; eauto.
  - _apply timeout_does_no_low_event_step in *.
    contradiction.
  - destruct cfg2.
    _apply timeout_does_no_high_event_step in *.
    super_destruct.
    unfold gc_occurred in * |-.
    super_destruct.
    subst.
    exfalso; eauto.
Qed.
Hint Resolve timeout_does_no_bridge_step.

Lemma new_low_reach_implies_flowsto_low:
  forall Γ x t ℓ ℓ_x ℓ_adv l n v m h loc Σ ℓ_p H1 H2,
    Γ x = Some (SecType (Array (SecType t ℓ) ℓ_p) (ℓ_x, ∘)) ->
    dangling_pointer_free m h ->
    (forall s ℓ, t = Array s ℓ -> exists loc', v = ValLoc loc' /\ reach m h loc') ->
    (t = Int -> exists n, v = ValNum n) ->
    low_reach ℓ_adv Γ Σ
              (m [x → ValLoc loc]) (h [loc → (n × v, l), H1, H2]) loc ->
    ℓ_x ⊑ ℓ_adv.
Proof.
  intros.
  dependent induction H5.
  - destruct (decide (x = x0)); subst.
    + rewrite -> extend_memory_lookup_eq in *.
      rewrite_inj.
      eauto.
    + rewrite -> extend_memory_lookup_neq in * by solve[eauto].
      assert (exists ℓ μ, heap_lookup loc h = Some (ℓ, μ)) by eauto.
      super_destruct; subst.
      congruence.
  - destruct (decide (loc2 = loc1)); subst.
    + rewrite_inj.
      eapply IHlow_reach; eauto.
    + rewrite -> heap_lookup_extend_neq in * by solve[eauto].
      assert (reach (m [x → ValLoc loc2])
                    (h [loc2 → (n × v, l), H1, H2 ]) loc1) by eauto 2.
      assert (~ reach m h loc2).
      {
        intro.
        assert (exists ℓ μ, heap_lookup loc2 h = Some (ℓ, μ)) by eauto.
        super_destruct; subst.
        congruence.
      }
      assert (reach m h loc1).
      {
        eapply reach_extend_implies_reach_if.
        - instantiate (1 := v).
          intros; subst.
          destruct t.
          + repeat specialize_gen.
            super_destruct; discriminate.
          + specialize (H3 s l1 eq_refl).
            super_destruct; subst.
            injects.
            eauto.
        - eauto.
        - eauto.
      }
      exfalso; eauto.

      Unshelve.
      * eauto.
Qed.

Lemma memory_lookup_is_eval_of_var:
  forall m x v,
    memory_lookup m x = Some v ->
    eval m (Var x) = Some v.
Proof.
  intros.
  unfolds.
  eauto.
Qed.
Hint Resolve memory_lookup_is_eval_of_var.

Ltac apply_taint_eq_reach :=
  match goal with
    [H: context[taint_eq_reach] |- _] =>
    solve[eapply H; eauto]
  end.

Lemma taint_bijection_implies_lookup:
  forall ℓ τ m1 m2 h1 h2 n Σ1 Σ2 loc1 loc2 loc1' loc2' Φ l1 l2 μ ν,
    wf_stenv Σ1 h1 ->
    wf_stenv Σ2 h2 ->
    taint_eq_heap ℓ Φ Σ1 Σ2 m1 h1 m2 h2 ->
    Σ1 loc1 = Some τ ->
    Σ2 loc2 = Some τ ->
    reach m1 h1 loc1 ->
    reach m2 h2 loc2 ->
    heap_lookup loc1 h1 = Some (l1, μ) ->
    heap_lookup loc2 h2 = Some (l2, ν) ->
    left Φ loc1 = Some loc2 ->
    lookup μ n = Some (ValLoc loc1') ->
    left Φ loc1' = Some loc2' ->
    lookup ν n = Some (ValLoc loc2').
Proof.
  intros.
  assert (high ℓ m1 h1 loc1) by eauto 2.
  assert (high ℓ m2 h2 loc2) by eauto 2.
  remember_simple (H1 loc1 loc2 _ _ _ _ _ H8 H11 H12 H6 H7 H2 H3).
  super_destruct'; subst.
  assert (exists u, lookup ν n = Some u).
  {
    assert (exists v, lookup μ n = Some v) by eauto.
    eapply_lookup_func_domain_eq; eauto.
  }
  super_destruct; subst.
  assert (val_taint_eq Φ τ (ValLoc loc1') u) by eauto 2.
  invert_val_taint_eq.
  - rewrite_inj.
    eauto.
  - assert_wf_type.
    invert_wf_type.
Qed.

Lemma reach_in_extended_memory_and_heap:
  forall ℓ Γ Σ1 Σ2 m1 h1 m2 h2 x n1 n2 v1 v2 l1 l2 loc1 loc2 Φ ℓ_τ ℓ_p τ ℓ_x ι_τ H1 H2 H3 H4,
    Γ x = Some (SecType (Array (SecType τ (ℓ_τ, ι_τ)) ℓ_p) (ℓ_x, ∘)) ->
    wf_taint_bijection ℓ Φ m1 h1 ->
    taint_eq_mem Φ Γ m1 m2 ->
    taint_eq_reach Φ m1 h1 m2 h2 ->
    taint_eq_heap ℓ Φ Σ1 Σ2 m1 h1 m2 h2 ->
    taint_eq_stenv Φ Σ1 Σ2 ->
    reach (m1 [x → ValLoc l1]) (h1 [l1 → (n1 × v1, ℓ_p), H1, H2]) loc1 ->
    dangling_pointer_free m1 h1 ->
    dangling_pointer_free m2 h2 ->
    wf_tenv Γ m1 ->
    wf_tenv Γ m2 ->
    wf_stenv Σ1 h1 ->
    wf_stenv Σ2 h2 ->
    left Φ loc1 = Some loc2 ->
    (forall s ℓ', τ = Array s ℓ' -> exists loc', v1 = ValLoc loc' /\
                                      reach m1 h1 loc') ->
    (τ = Int -> exists n, v1 = ValNum n) ->
    val_taint_eq Φ (SecType τ (ℓ_τ, ι_τ)) v1 v2 ->
    reach (m2 [x → ValLoc l2])
          (h2 [l2 → (n2 × v2, ℓ_p), H3, H4]) loc2.
Proof.
  intros.
  revert loc2 H16.
  dependent induction H9; intros.
  - destruct (decide (x = x0)); subst.
    + rewrite extend_memory_lookup_eq in *.
      rewrite_inj.
      assert (high ℓ m1 h1 loc).
      {
        eapply H0; eauto 2.
      }
      assert (exists ℓ μ, heap_lookup loc h1 = Some (ℓ, μ)) by (destruct_high; eauto).
      super_destruct; congruence.
    + rewrite -> extend_memory_lookup_neq in * by solve[eauto].
      assert (exists v, memory_lookup m2 x0 = Some v) by firstorder 2.
      super_destruct; subst.
      assert (exists τ, Γ x0 = Some τ) by eauto 3.
      super_destruct'; subst.
      destruct τ0 as [σ [ℓ' ι']].
      assert (exists ℓ τ, σ = Array τ ℓ).
      {
        destruct σ; eauto.
        assert (exists n, ValLoc loc = ValNum n) by eauto 3.
        super_destruct; congruence.
      }
      super_destruct'; subst.
      assert (val_taint_eq Φ (SecType (Array τ0 ℓ0) (ℓ', ι')) (ValLoc loc) v).
      {
        eapply eval_taint_eq with (e := Var x0) (m1 := m1) (m2 := m2); eauto.
      }
      invert_val_taint_eq.
      * rewrite_inj.
        eapply reach_mem.
        { rewrite -> extend_memory_lookup_neq by solve[eauto].
          eauto. }
      * assert_wf_type.
        invert_wf_type.
  - destruct (decide (l1 = loc)); subst.
    + rewrite_inj.
      apply_heap_lookup_extend_eq.
      super_destruct; subst.
      rewrite_inj.
      assert (v1 = ValLoc loc') by congruence; subst.
      assert (exists ℓ' τ', τ = Array τ' ℓ').
      {
        destruct τ; eauto.
        assert (exists n, ValLoc loc' = ValNum n) by eauto.
        super_destruct'; congruence.
      }
      super_destruct'; subst.
      assert_wf_type.
      invert_wf_type.
      invert_wf_type.
      invert_val_taint_eq.
      rewrite_inj.
      apply_heap_lookup_extend_eq.
      rewrite_inj.
      remember_simple (heap_lookup_extend_eq l2 ℓ_p n2 (ValLoc loc'0) h2 H3 H4).
      super_destruct.
      eapply reach_heap.
      * eapply reach_mem; eauto.
      * eauto.
      * eauto.
    + rewrite -> heap_lookup_extend_neq in * by solve[eauto].
      assert (reach m1 h1 loc).
      {
        eapply reach_extend_implies_reach_if; eauto 3.
        intros; subst.
        destruct τ.
        - invert_val_taint_eq.
        - specialize (H18 _ _ eq_refl).
          super_destruct'; subst.
          injects.
          eauto.
      }
      assert (exists loc', left Φ loc = Some loc').
      {
        eapply H0; eauto.
      }
      super_destruct; subst.
      assert (reach m2 h2 loc'0).
      {
        apply_taint_eq_reach.
      }

      assert (exists ℓ μ, heap_lookup loc'0 h2 = Some (ℓ, μ)) by eauto 3.
      super_destruct'; subst.

      assert (exists τ, Σ1 loc = Some τ) by eauto 2.
      super_destruct'; subst.
      assert (Σ2 loc'0 = Some τ0).
      {
        eapply H8; eauto.
      }
      assert (lookup μ0 n = Some (ValLoc loc2)).
      {
        eapply taint_bijection_implies_lookup with (m1 := m1) (m2 := m2) (h1 := h1) (h2 := h2); eauto.
      }
      assert (reach m2 h2 loc2) by eauto 2.

      assert (l2 <> loc'0).
      {
        intro; congruence.
      }
      
      assert (reach (m2 [x → ValLoc l2])
                    (extend_heap v2 l2 ℓ_p n2 h2 H3 H4) loc'0).
      {
        eapply IHreach; eauto 2.
      }
      eapply reach_heap.
      * eauto.
      * rewrite -> heap_lookup_extend_neq by solve[eauto].
        eauto.
      * eauto.
        
      Unshelve.
      { eauto. }
Qed.

Lemma low_reach_in_extended_memory_and_heap:
  forall ℓ Γ Σ1 Σ2 m1 h1 m2 h2 x n1 n2 v1 v2 l1 l2 loc1 loc2 φ ℓ_τ ℓ_p τ ℓ_x ι_τ H1 H2 H3 H4,
    state_low_eq ℓ φ m1 h1 m2 h2 Γ Σ1 Σ2 ->
    Γ x = Some (SecType (Array (SecType τ (ℓ_τ, ι_τ)) ℓ_p) (ℓ_x, ∘)) ->
    wf_bijection ℓ φ Γ Σ1 m1 h1 ->
    low_reach ℓ Γ (extend_stenv l1 (SecType τ (ℓ_τ, ι_τ)) Σ1)
              (m1 [x → ValLoc l1])
              (h1 [l1 → (n1 × v1, ℓ_p), H1, H2]) loc1 ->
    dangling_pointer_free m1 h1 ->
    dangling_pointer_free m2 h2 ->
    wf_tenv Γ m1 ->
    wf_tenv Γ m2 ->
    wf_stenv Σ1 h1 ->
    wf_stenv Σ2 h2 ->
    left φ loc1 = Some loc2 ->
    (forall s ℓ', τ = Array s ℓ' -> exists loc', v1 = ValLoc loc' /\
                                      (ℓ_τ ⊑ ℓ -> low_reach ℓ Γ Σ1 m1 h1 loc') /\
                                      (~ ℓ_τ ⊑ ℓ -> reach m1 h1 loc')) ->
    (τ = Int -> exists n, v1 = ValNum n) ->
    (ℓ_τ ⊑ ℓ -> onvals (left φ) v1 = Some v2) ->
    low_reach ℓ Γ (extend_stenv l2 (SecType τ (ℓ_τ, ι_τ)) Σ2)
              (m2 [x → ValLoc l2])
              (h2 [l2 → (n2 × v2, ℓ_p), H3, H4]) loc2.
Proof.
  intros.
  revert dependent loc2.
  dependent induction H6; intros.
  - destruct (decide (x = x0)); subst.
    + rewrite extend_memory_lookup_eq in *.
      rewrite_inj.
      assert (exists ℓ μ, heap_lookup loc h1 = Some (ℓ, μ)) by eauto 2.
      super_destruct; congruence.
    + rewrite -> extend_memory_lookup_neq in * by solve[eauto].
      assert (exists v, memory_lookup m2 x0 = Some v).
      {
        invert_state_low_eq.
        eapply_low_domain_eq; eauto.
      }
      super_destruct; subst.
      assert (val_low_eq ℓ_adv (SecType (Array τ0 ℓ_p0) (l, ∘))
                         (ValLoc loc) v φ).
      {
        invert_state_low_eq.
        eauto using eval_low_eq.
      }
      invert_val_low_eq; try contradiction.
      rewrite_inj.
      eapply LowReachMem.
      * eapply H6.
      * eauto.
      * rewrite -> extend_memory_lookup_neq by solve[eauto].
        eauto.
  - destruct (decide (l1 = loc1)); subst.
    + rewrite_inj.
      rewrite -> extend_stenv_lookup_eq in *.
      rewrite_inj.
      assert (onvals (left φ) v1 = Some v2) by eauto.
      apply_heap_lookup_extend_eq.
      rewrite_inj.
      assert (v1 = ValLoc loc2) by congruence; subst.
      assert (ValLoc loc0 = v2).
      {
        unfold onvals in *.
        decide_exist in *.
        rewrite_inj.
        reflexivity.
      }
      subst.
      apply_heap_lookup_extend_eq.
      rewrite_inj.
      assert (ℓ_x ⊑ ℓ_adv).
      {
        eapply new_low_reach_implies_flowsto_low with
        (m := m1) (h := h1) (v := ValLoc loc2); eauto 2.
        intros; subst.
        injects.
        exists loc2.
        splits~.
        match goal with
          [H1: forall _ _, _ = _ -> exists _, _ = _ /\ _,
             H2: Γ ?x = Some (SecType (Array (SecType (Array ?s ?ℓ) _) _) _) |- _] =>
          specialize (H1 s ℓ eq_refl)
        end.
        super_destruct; subst.
        injects.
        destruct (flowsto_dec l ℓ_adv); eauto 3.
      }
      apply_heap_lookup_extend_eq.
      rewrite_inj.
      remember_simple (heap_lookup_extend_eq l2 ℓ_p n2 (ValLoc loc0) h2 H3 H4).
      super_destruct; rewrite_inj.
      eapply LowReachHeap.
      * eauto.
      * eauto.
      * eauto.
      * eauto.
      * eauto.
    + rewrite -> heap_lookup_extend_neq in * by solve[eauto].
      rewrite -> extend_stenv_lookup_neq in * by solve[eauto].
      assert (low_reach ℓ_adv Γ Σ1 m1 h1 loc1).
      {
        eapply (low_reach_extend_implies_low_reach_if (σ := τ) (v := v1) (ℓ := ℓ_τ)); eauto.
        intros; subst.
        match goal with
          [H1: forall _ _, _ = _ -> exists _, v1 = _ /\ _,
             H2: Γ ?x = Some (SecType (Array (SecType (Array ?s ?ℓ) _) _) _) |- _] =>
          specialize (H1 s ℓ eq_refl)
        end.
        super_destruct; subst.
        exists loc'.
        splits~.          
      }
      assert (exists loc', left φ loc1 = Some loc') by eauto.
      super_destruct; subst.
      assert (Σ2 loc' = Some (SecType (Array τ0 ℓ_p0) (l, ∘))).
      {
        invert_state_low_eq.
        eauto.
      }
      assert (low_reach ℓ_adv Γ Σ2 m2 h2 loc').
      {
        invert_state_low_eq.
        eapply H29; eauto.
      }
      
      assert ((exists μ, heap_lookup loc' h2 = Some (ℓ, μ)) /\ low ℓ_adv Γ Σ2 m2 h2 loc').
      {
        invert_state_low_eq.
        eauto.
      }
      super_destruct; subst.
      assert (lookup μ0 n = Some (ValLoc loc0)) by (invert_state_low_eq; eauto using bijection_implies_lookup).
      assert (low_reach ℓ_adv Γ Σ2 m2 h2 loc0) by eauto 2.
      assert (l2 <> loc').
      {
        intro; subst.
        congruence.
      }

      assert (low_reach ℓ_adv Γ (extend_stenv l2 (SecType τ (ℓ_τ, ι_τ)) Σ2)
                        (m2 [x → ValLoc l2])
                        (extend_heap v2 l2 ℓ_p n2 h2 H3 H4) loc').
      {
        eapply IHlow_reach; eauto 2.
      }
      eapply LowReachHeap.
      * eauto.
      * rewrite -> extend_stenv_lookup_neq by solve[eauto].
        eauto.
      * rewrite -> heap_lookup_extend_neq by solve[eauto].
        eauto.
      * eauto.
      * eauto.
        
      Unshelve.
      { eauto. }
Qed.

Lemma low_extend_implies_low_if:
  forall ℓ_adv Γ loc1 loc2 v n m h Σ ℓ_p ι τ ℓ_τ x H1 H2,
    low ℓ_adv Γ (extend_stenv loc1 (SecType τ (ℓ_τ, ι)) Σ)
        (extend_memory x (ValLoc loc1) m)
        (h [loc1 → (n × v, ℓ_p), H1, H2]) loc2 ->
    (forall s ℓ',
        τ = Array s ℓ' ->
        exists loc', v = ValLoc loc' /\ (ℓ_τ ⊑ ℓ_adv -> low_reach ℓ_adv Γ Σ m h loc')) ->
    (τ = Int -> exists n, v = ValNum n) ->
    loc1 <> loc2 ->
    low ℓ_adv Γ Σ m h loc2.
Proof.
  intros.
  destruct_low.
  - eapply LowReachable.
    eapply low_reach_extend_implies_low_reach_if; eauto.
  - rewrite -> heap_lookup_extend_neq in * by solve[eauto].
    eauto 2.
Qed.
Hint Resolve low_extend_implies_low_if.

Lemma low_extend_memory_heap_with_high:
  forall x ℓ_adv Γ Σ 
    m h loc1 loc2 v n l ℓ τ H1 H2,
    Γ x = Some (SecType (Array τ ℓ) (l, ∘)) ->
    ~ l ⊑ ℓ_adv ->
    low ℓ_adv Γ Σ m h loc1 ->
    low ℓ_adv Γ (extend_stenv loc2 τ Σ)
        (m [x → ValLoc loc2]) (h [loc2 → (n × v, ℓ), H1, H2]) loc1.
Proof.
  intros.
  destruct_low.
  - eapply LowReachable.
    eapply low_reach_extend_memory_heap_with_high; eauto.
  - eapply LowHeapLevel.
    + destruct (decide (loc = loc2)); subst.
      * congruence.
      * rewrite -> heap_lookup_extend_neq by solve[eauto].
        eauto.
    + eauto.
Qed.
Hint Resolve low_extend_memory_heap_with_high.

Lemma low_eq_stenv_extend_high:
  forall ℓ_adv φ x loc1 loc2 τ ℓ_τ ι_τ Γ m1 m2 h1 h2 ℓ_p n1 ℓ_x ι n2 v1 v2 Σ1 Σ2 H1 H2 H3 H4,
    low_eq_stenv ℓ_adv φ m1 m2 h1 h2 Γ Σ1 Σ2 ->
    left φ loc1 = None ->
    right φ loc2 = None ->
    wf_tenv Γ m1 ->
    wf_tenv Γ m2 ->
    Γ x = Some (SecType (Array (SecType τ (ℓ_τ, ι_τ)) ℓ_p) (ℓ_x, ι)) ->
    ~ ℓ_x ⊑ ℓ_adv ->
    (forall s ℓ', τ = Array s ℓ' ->
             exists loc', v1 = ValLoc loc' /\ (ℓ_τ ⊑ ℓ_adv -> low_reach ℓ_adv Γ Σ1 m1 h1 loc')) ->
    (forall s ℓ', τ = Array s ℓ' ->
             exists loc', v2 = ValLoc loc' /\ (ℓ_τ ⊑ ℓ_adv -> low_reach ℓ_adv Γ Σ2 m2 h2 loc')) ->
    (τ = Int -> exists n0, v1 = ValNum n0) ->
    (τ = Int -> exists n0, v2 = ValNum n0) ->
    low_eq_stenv ℓ_adv φ
                 (extend_memory x (ValLoc loc1) m1)
                 (extend_memory x (ValLoc loc2) m2)
                 (h1 [loc1 → (n1 × v1, ℓ_p), H1, H2])
                 (h2 [loc2 → (n2 × v2, ℓ_p), H3, H4])
                 Γ
                 (extend_stenv loc1 (SecType τ (ℓ_τ, ι_τ)) Σ1)
                 (extend_stenv loc2 (SecType τ (ℓ_τ, ι_τ)) Σ2).
Proof.
  intros.
  unfolds.
  assert (ι = ∘).
  {
    assert_wf_type.
    invert_wf_type.
    reflexivity.
  }
  subst.
  intros.
  splits.
  - intros.
    super_destruct; subst.
    destruct (decide (loc1 = loc0)); try congruence.
    assert (loc2 <> loc3).
    {
      intro; subst.
      assert (right φ loc3 = Some loc0) by (destruct φ; eauto).
      congruence.
    }
    rewrite -> extend_stenv_lookup_neq in * by solve[eauto].
    assert (low ℓ_adv Γ Σ1 m1 h1 loc0).
    {
      eapply low_extend_implies_low_if with (v := v1) (m := m1) (h := h1); eauto.
    }
    assert (Σ2 loc3 = Some τ0 /\ low ℓ_adv Γ Σ2 m2 h2 loc3).
    {
      eapply H; eauto.
    }
    super_destruct; subst.
    eauto.
  - intros.
    super_destruct; subst.
    assert (loc2 <> loc3).
    {
      intro; subst.
      assert (right φ loc3 = Some loc0) by (destruct φ; eauto).
      congruence.
    }
    assert (loc1 <> loc0).
    {
      intro; subst.
      congruence.
    }
    rewrite -> extend_stenv_lookup_neq in * by solve[eauto].
    assert (low ℓ_adv Γ Σ2 m2 h2 loc3).
    {
      eapply low_extend_implies_low_if with (v := v2) (m := m2) (h := h2); eauto.
    }
    assert (Σ1 loc0 = Some τ0 /\ low ℓ_adv Γ Σ1 m1 h1 loc0).
    {
      eapply H; eauto.
    }
    super_destruct; subst.
    splits*.
Qed.
Hint Resolve low_eq_stenv_extend_high.

Lemma low_in_extended_memory_heap_with_high_implies_low:
  forall x ℓ_adv Γ Σ m h loc1 loc2 v n l τ ι ℓ H1 H2,
    Γ x = Some (SecType (Array τ ℓ) (l, ι)) ->
    ~ l ⊑ ℓ_adv ->
    wf_tenv Γ m ->
    dangling_pointer_free m h ->
    low ℓ_adv Γ (extend_stenv loc2 τ Σ) (m [x → ValLoc loc2])
        (h [loc2 → (n × v, ℓ), H1, H2]) loc1 -> low ℓ_adv Γ Σ m h loc1.
Proof.
  intros.
  destruct_low.
  - eapply LowReachable.
    eapply low_reach_in_extended_memory_heap_with_high_implies_low_reach; eauto.
  - destruct (decide (loc = loc2)); subst.
    + assert_wf_type.
      invert_wf_type.
      apply_heap_lookup_extend_eq.
      rewrite_inj.
      exfalso; eauto 3.
    + rewrite -> heap_lookup_extend_neq in * by solve[eauto].
      eauto 2.
Qed.
Hint Resolve low_in_extended_memory_heap_with_high_implies_low.

Lemma extend_mem_with_high_preserves_low:
  forall ℓ Γ Σ m h v loc l t x ι,
    Γ x = Some (SecType t (l, ι)) ->
    ~ l ⊑ ℓ ->
    low ℓ Γ Σ m h loc -> low ℓ Γ Σ (m [x → v]) h loc.
Proof.
  intros.
  destruct_low.
  - eapply LowReachable.
    eapply extend_mem_with_high_preserves_low_reach; eauto.
  - eapply LowHeapLevel; eauto.
Qed.
Hint Resolve extend_mem_with_high_preserves_low.

Lemma low_in_extend_memory_with_high_implies_low:
  forall ℓ Γ Σ m h v loc l t x ι,
  Γ x = Some (SecType t (l, ι)) ->
  ~ l ⊑ ℓ ->
  low ℓ Γ Σ (m [x → v]) h loc -> low ℓ Γ Σ m h loc.
Proof.
  intros.
  destruct_low.
  - eapply LowReachable.
    eapply low_reach_in_extend_memory_with_high_implies_low_reach; eauto.
  - eapply LowHeapLevel; eauto.
Qed.
Hint Resolve low_in_extend_memory_with_high_implies_low.

Lemma state_low_eq_extend_high:
  forall ℓ_adv m h i v Γ Σ t l ι,
    Γ i = Some (SecType t (l, ι)) ->
    ~ l ⊑ ℓ_adv ->
    wf_tenv Γ m ->
    wf_stenv Σ h ->
    dangling_pointer_free m h ->
    (t = Int -> exists n, v = ValNum n) ->
    (forall s ℓ, t = Array s ℓ -> exists loc0, v = ValLoc loc0) ->
    state_low_eq ℓ_adv (identity_bijection loc) m h (extend_memory i v m) h Γ Σ Σ.
Proof.
  intros.
  apply StateLowEq; eauto.
  - unfolds.
    intros.
    unfold left, identity_bijection in *.
    rewrite_inj.
    splits.
    + intros.
      super_destruct; subst.
      splits*.
    + intros.
      super_destruct; subst.
      splits~.
      eapply low_in_extend_memory_with_high_implies_low; eauto.
  - unfolds.
    intros.
    destruct (decide (i = x)); subst.
    + rewrite_inj.
      contradiction.
    + rewrite -> extend_memory_lookup_neq by solve[eauto].
      splits*.      
  - unfolds.
    intros.
    unfold left, identity_bijection in *.
    rewrite_inj.
    splits~.
    + intros.
      super_destruct; subst.
      splits; eauto 3.
    + intros.
      super_destruct; subst.
      splits; eauto 3.
  - unfolds.
    intros.
    destruct (decide (i = x)); subst.
    + rewrite -> extend_memory_lookup_eq in *.
      rewrite_inj.
      destruct t.
      * assert (exists n, v1 = ValNum n) by eauto.
        specialize_gen.
        destruct_exists.
        eauto.
      * assert (exists loc0, v1 = ValLoc loc0) by eauto.
        specialize (H5 s l0 eq_refl).
        super_destruct; subst.
        eauto.
    + rewrite -> extend_memory_lookup_neq in * by solve[eauto].
      rewrite_inj.
      destruct τ.
      destruct t0.
      * assert (exists n, v2 = ValNum n) by eauto.
          destruct_exists.
          eauto.
        * assert (exists loc, v2 = ValLoc loc) by eauto.
          destruct_exists.
          eauto.
  - unfolds.
    intros.
    unfold left in *.
    unfold identity_bijection in * |-.
    rewrite_inj.
    destruct τ.
    assert (exists ℓ μ, heap_lookup loc2 h = Some (ℓ, μ)) by eauto.
    super_destruct; subst.
    destruct t0.
    + assert (heapval_low_eq ℓ_adv (SecType Int t1) loc2 loc2 m m h h (identity_bijection loc)).
      {
        eapply heapval_low_eq_num_refl; eauto.
        intros.
        match goal with
          [H: wf_stenv _ _ |- _] =>
          edestruct H; eauto
        end.
        match goal with
          [H: context[exists _, _ = ValNum _] |- _] =>
          edestruct H; eauto
        end.
        subst.
        eauto.
      }
      invert_heapval_low_eq; eauto.
    + assert (heapval_low_eq ℓ_adv (SecType (Array s l0) t1) loc2 loc2 m m h h (identity_bijection loc)).
      {
        eapply heapval_low_eq_loc_refl; eauto.
        intros.
        match goal with
          [H: wf_stenv _ _ |- _] =>
          edestruct H; eauto
        end.
        match goal with
          [H: context[exists _, _ = ValLoc _] |- _] =>
          edestruct H; eauto
        end.
        subst.
        assert (exists loc0, v0 = ValLoc loc0) by eauto.
        super_destruct'; subst.
        eauto.
      }
      invert_heapval_low_eq; eauto 3.
  - intros.
    unfold left, identity_bijection in *.
    rewrite_inj.
    reflexivity.
Qed.

Lemma bridge_if_does_not_step_to_stop:
  forall e c1 c2 pc m h t ℓ Γ Σ Σ' ev pc' m' h' t' pc'',
    wellformed_aux Γ Σ ⟨If e c1 c2, pc, m, h, t⟩ pc'' ->
    ⟨If e c1 c2, pc, m, h, t⟩ ↷ [ℓ, Γ, Σ, Σ', ev, 0] ⟨Stop, pc', m', h', t'⟩ -> False.
Proof.
  intros.
  invert_bridge_step;
    unfolds in H1;
    jauto.
Qed.
Hint Resolve bridge_if_does_not_step_to_stop.

Lemma event_step_if_stop_config_is_false:
  forall e c1 c2 pc m h t ev Γ Σ Σ' c' pc' m' h' t' pc'',
    wellformed_aux Γ Σ ⟨If e c1 c2, pc, m, h, t⟩ pc'' ->
    ⟨If e c1 c2, pc, m, h, t⟩ ⇒ [ev, Γ, Σ, Σ'] ⟨c', pc', m', h', t'⟩ ->
    is_stop_config ⟨ c', pc', m', h', t'⟩ -> False.
Proof.
  intros.
  do 2 unfolds in H1; subst.
  eauto.
Qed.
Hint Resolve event_step_if_stop_config_is_false.

Lemma event_step_implies_step:
  forall c pc m h t c' pc' m' h' t' ev Γ Σ Σ',
    ⟨c, pc, m, h, t⟩ ⇒ [ev, Γ, Σ, Σ'] ⟨c', pc', m', h', t'⟩ ->
    ⟨c, pc, m, h, t⟩ ⇒ (Γ, Σ, Σ') ⟨c', pc', m', h', t'⟩.
Proof.
  intros.
  revert pc m h t Σ Σ' c' pc' m' h' t' ev H.
  induction c; intros; invert_event_step; eauto.  
Qed.
Hint Immediate event_step_implies_step.

Lemma about_seq_step:
  forall c1 c2 pc m h t c' pc' m' h' t' Γ Σ Σ',
    ⟨c1;; c2, pc, m, h, t⟩ ⇒ (Γ, Σ, Σ') ⟨c', pc', m', h', t'⟩ ->
    (⟨c1, pc, m, h, t⟩ ⇒ (Γ, Σ, Σ') ⟨Stop, pc', m', h', t'⟩ /\ c' = c2)
    \/ (exists c1', ⟨c1, pc, m, h, t⟩ ⇒ (Γ, Σ, Σ') ⟨c1', pc', m', h', t'⟩ /\
               c1' <> Stop /\ c' = (c1';; c2))
    \/ (gc_occurred (c1;; c2) c' pc pc' m m' h h' t t' Σ Σ').
Proof.
  intros.
  invert_step.
  - left.
    eauto.
  - right; left.
    exists c1'.
    splits*.
  - (* GC step *)
    right; right.
    unfolds.
    splits*.
    do 7 eexists.
    splits; reflexivity || eauto.
Qed.
Hint Resolve about_seq_step.

Lemma about_seq_event_step:
  forall c1 c2 pc m h t ev Γ Σ Σ' c' pc' m' h' t',
    ⟨c1;; c2, pc, m, h, t⟩ ⇒ [ev, Γ, Σ, Σ'] ⟨c', pc', m', h', t'⟩ ->
    (⟨c1, pc, m, h, t⟩ ⇒ [ev, Γ, Σ, Σ'] ⟨Stop, pc', m', h', t'⟩ /\ c' = c2)
    \/ (exists c1', ⟨c1, pc, m, h, t⟩ ⇒ [ev, Γ, Σ, Σ'] ⟨c1', pc', m', h', t'⟩ /\ c1' <> Stop /\ c' = (c1';;c2))
    \/ (gc_occurred (c1;; c2) c' pc pc' m m' h h' t t' Σ Σ') /\ ev = EmptyEvent.
Proof.
  intros.
  invert_event_step; eauto 6.
  right.
  right.
  splits*.
  unfolds.
  splits*.
  do 7 eexists.
  splits; reflexivity || eauto.
Qed.
Hint Resolve about_seq_event_step.  

Lemma gc_is_empty_event:
  forall c c' pc pc' m m' h h' t t' ev Γ Σ Σ',
    ⟨c, pc, m, h, t⟩ ⇒ [ev, Γ, Σ, Σ'] ⟨c', pc', m', h', t'⟩ ->
    gc_occurred c c' pc pc' m m' h h' t t' Σ Σ' -> ev = EmptyEvent.
Proof.
  intros.
  revert pc m h t ev c' pc' m' h' t' Σ Σ' H H0.
  induction c; intros.
  - invert_event_step; eauto.
  - invert_event_step; eauto.
  - invert_event_step; eauto || unfold gc_occurred in *; super_destruct'; subst; congruence.
  - invert_event_step; eauto || unfold gc_occurred in *; super_destruct'; subst; congruence.
  - invert_event_step; eauto || unfold gc_occurred in *; super_destruct'; subst; congruence.
  - invert_event_step; try reflexivity.
    + unfold gc_occurred in *.
      super_destruct; subst.
      injects.
      eapply IHc1; eauto.
      splits*.
      do 7 eexists.
      splits; reflexivity || eauto.
    + unfold gc_occurred in *.
      super_destruct.
      contradict H; eauto.
  - invert_event_step; eauto || unfold gc_occurred in *; super_destruct'; subst; congruence.
  - invert_event_step; eauto || unfold gc_occurred in *; super_destruct'; subst; (congruence || (invert_sem_step; omega)).
  - invert_event_step; eauto.
    unfold gc_occurred in *.
    super_destruct.
    congruence.
  - invert_event_step; eauto || unfold gc_occurred in *; super_destruct'; subst; congruence.
  - invert_event_step; eauto || unfold gc_occurred in *; super_destruct'; subst; congruence.
  - invert_event_step; eauto || unfold gc_occurred in *; super_destruct'; subst; congruence.
  - invert_event_step; eauto || unfold gc_occurred in *; super_destruct'; subst; congruence.
Qed.
Hint Resolve gc_is_empty_event.

Lemma eq_expr_dec:
  forall e1 e2 : expr,
    {e1 = e2} + {e1 <> e2}.
Proof.
  intros.
  repeat decide equality.
Defined.

Lemma eq_cmd_dec:
  forall c1 c2 : cmd,
    {c1 = c2} + {c1 <> c2}.
Proof.
  intros.
  repeat decide equality.
Defined.

Lemma preservation_event_step:
  forall Γ Σ Σ' c c' pc pc' pc'' m m' h h' t t' ev,
    wellformed_aux Γ Σ ⟨c, pc, m, h, t⟩ pc'' ->
    ⟨c, pc, m, h, t⟩ ⇒ [ev, Γ, Σ, Σ'] ⟨c', pc', m', h', t'⟩ ->
    wellformed_aux Γ Σ' ⟨c', pc', m', h', t'⟩ pc''.
Proof.
  intros.
  invert_event_step; eauto using preservation.
  eapply gc_preserves_wf; eauto.
  erewrite -> disjoint_union_proof_irrelevance; eauto.
Qed.
Hint Resolve preservation_event_step.

Lemma preservation_bridge_step:
  forall n ℓ Γ Σ Σ' ev c pc m h t c' pc' m' h' t' pc'',
    wellformed_aux Γ Σ ⟨c, pc, m, h, t⟩ pc'' ->
    ⟨c, pc, m, h, t⟩ ↷ [ℓ, Γ, Σ, Σ', ev, n] ⟨c', pc', m', h', t'⟩ ->
    wellformed_aux Γ Σ' ⟨c', pc', m', h', t'⟩ pc''.
Proof.
  intros n ℓ Γ.
  induction n; intros.
  - invert_bridge_step.
    + invert_low_event_step.
      eauto.
    + invert_high_event_step.
      eauto.
  - invert_bridge_step.
    destruct cfg2.
    invert_high_event_step.
    assert (wellformed_aux Γ Σ'0 ⟨c0, pc0, memory, heap, time⟩ pc'') by eauto 2.
    eauto. (* Done by IHn *)
Qed.
Hint Resolve preservation_bridge_step.

Ltac invert_wt_timeout :=
     match goal with
    [H: wt_aux _ _ TimeOut _ |- _ ] => inverts H
  end.

Lemma about_seq_bridge_step:
  forall ℓ c1 c2 pc m h t ev Γ Σ Σ'' n c' pc' pc'' m' h' t',
    wellformed_aux Γ Σ ⟨c1;; c2, pc, m, h, t⟩ pc'' ->
    ⟨c1;; c2, pc, m, h, t⟩ ↷ [ℓ, Γ, Σ, Σ'', ev, n] ⟨c', pc', m', h', t'⟩ ->
    (exists c1', ⟨c1, pc, m, h, t⟩ ↷ [ℓ, Γ, Σ, Σ'', ev, n] ⟨c1', pc', m', h', t'⟩
                 /\ (c1' <> Stop -> c' = (c1';; c2))
                 /\ (c1' = Stop -> c' = c2)
                 /\ low_event ℓ ev)
    \/
    (exists k pc'' m'' h'' t'' ev' Σ',
        k < n /\ n > 0 /\ high_event ℓ ev' /\
        ⟨c1, pc, m, h, t⟩ ↷ [ℓ, Γ, Σ, Σ', ev', k] ⟨Stop, pc'', m'', h'', t''⟩ /\
        ⟨c2, pc'', m'', h'', t''⟩ ↷ [ℓ, Γ, Σ', Σ'', ev, n - k - 1] ⟨c', pc', m', h', t'⟩).
Proof.
  intros.
  revert c' pc' m' h' t' c1 c2 pc m h t H0 H.
  revert dependent Σ.
  induction n; intros; subst.
  (* n = 0 *)
  {
    left.
    assert (H2 := H).
    invert_bridge_step.
    {
      invert_low_event_step.
      destruct (about_seq_event_step H0).
      + exists STOP.
        splits*.
      + super_destruct; subst.
        * eexists; splits*.
        * invert_low_event.
    }
    {
      invert_high_event_step.
      unfold is_stop_config, cmd_of in *; subst.
      invert_event_step.
      - invert_wf_aux.
        do 2 specialize_gen.
        invert_wt_cmd.
        invert_wt_stop.
    }
  }
  (* n > 0 *)
  {
    invert_bridge_step.
    invert_high_event_step.
    assert (H' := H0).
    invert_event_step.
    - assert (wellformed_aux Γ Σ' ⟨c1';; c2, pc'0, m'0, h'0, t'0 ⟩ pc'') by eauto.
      destruct (IHn _ _ _ _ _ _ _ _ _ _ _ _ H12 H2).
      {        
        left.
        jauto.
      }
      {
        right.
        destruct_exists.
        super_destruct.
        exists (S k) pc''0 m'' h'' t'' ev'; exists Σ'0.
        splits*; try omega.
      }
    - right.
      exists 0 pc'0 m'0 h'0 t'0 ev1; exists Σ'.
      splits*; try omega.
      assert (S n - 0 - 1 = n) as H2 by omega.
      rewrite -> H2 in *; eauto.
    - assert (wellformed_aux Γ Σ' ⟨ c1;; c2, pc'0, m'0, ([h1_pc ⊎ h1_not_pc, H5]), t + δ⟩ pc'').
      {
        eapply gc_preserves_wf; eauto 3.
        erewrite -> disjoint_union_proof_irrelevance; eauto.
      }
      specialize (IHn _ _ _ _ _ _ _ _ _ _ _ _ H12 H7).
      super_destruct.
      + destruct (eq_cmd_dec c1' Stop); subst.
        * specialize_gen; subst.
          left.
          exists Stop.
          splits~.
          eapply bridge_trans_num with (ev1 := EmptyEvent).
          { splits; eauto 3.
            eapply EventGCStep.
            eapply step_gc; reflexivity || eauto 3.
            - intro; subst.
              invert_wf_aux.
              repeat specialize_gen.
              invert_wt_cmd.
              invert_wt_stop.
            - intro; subst.
              invert_wf_aux.
              repeat specialize_gen.
              invert_wt_cmd.
              invert_wt_timeout.
          }
          {
            intro.
            unfold is_stop_config, cmd_of in *; subst.
            invert_wf_aux.
            do 2 specialize_gen.
            invert_wt_cmd.
            invert_wt_stop.
          }
          {
            intro.
            unfold is_timeout_config, cmd_of in *; subst.
            invert_wf_aux.
            do 2 specialize_gen.
            invert_wt_cmd.
            invert_wt_timeout.
          }
          {
            eauto.
          }
        * left.
          exists c1'.
          splits~.
          eapply bridge_trans_num with (ev1 := EmptyEvent).
          { unfolds.
            splits~.
            eapply EventGCStep.
            - eapply step_gc; reflexivity || eauto 3.
              + intro; subst.
                invert_wf_aux.
                repeat specialize_gen.
                invert_wt_cmd.
                invert_wt_stop.
              + intro; subst.
                invert_wf_aux.
                repeat specialize_gen.
                invert_wt_cmd.
                invert_wt_timeout.
          }
          {
            intro.
            unfold is_stop_config, cmd_of in *; subst.
            invert_wf_aux.
            do 2 specialize_gen.
            invert_wt_cmd.
            invert_wt_stop.
          }
          {
            intro.
            unfold is_timeout_config, cmd_of in *; subst.
            invert_wf_aux.
            do 2 specialize_gen.
            invert_wt_cmd.
            invert_wt_timeout.
          }
          {
            eauto.
          }
      + right.
        exists (S k) pc''0 m'' h'' t'' ev'; exists Σ'0.
        assert (c1 <> Stop).
        {
          intro; subst.
          invert_wf_aux.
          do 2 specialize_gen.
          invert_wt_cmd.
          invert_wt_stop.
        }
        assert (c1 <> TimeOut).
        {
          intro; subst.
          invert_wf_aux.
          do 2 specialize_gen.
          invert_wt_cmd.
          invert_wt_timeout.
        }
        splits*; try omega.
        eapply bridge_trans_num.
        * unfolds.
          splits~.          
          eapply EventGCStep; reflexivity || eauto 2.
          intro; invert_low_event.
        * eauto.
        * eauto.
        * eauto.
  }
  Qed.
Hint Resolve about_seq_bridge_step.

Lemma if_bridge_properties:
  forall e c1 c2 pc m h t c' pc' m' h' t' ℓ_adv Γ Σ Σ' ev n pc'',
    wellformed_aux Γ Σ ⟨If e c1 c2, pc, m, h, t⟩ pc'' ->
    ⟨If e c1 c2, pc, m, h, t⟩ ↷ [ℓ_adv, Γ, Σ, Σ', ev, n] ⟨c', pc', m', h', t'⟩ ->
    n > 0
    /\
    ((exists p, eval m e = Some (ValNum p) /\ p <> 0 /\
           ⟨c1, pc, m, h, S t⟩ ↷ [ℓ_adv, Γ, Σ, Σ', ev, n - 1] ⟨c', pc', m', h', t'⟩)
     \/
     (eval m e = Some (ValNum 0) /\
      ⟨c2, pc, m, h, S t⟩ ↷ [ℓ_adv, Γ, Σ, Σ', ev, n - 1] ⟨c', pc', m', h', t'⟩)).
Proof.
  intros.
  dependent induction H0.
  - invert_low_event_step.
    invert_event_step; invert_low_event.
  - invert_wf_aux.
    do 2 specialize_gen.
    invert_wt_cmd.
    assert (c1 <> Stop).
    {
      intro; subst.
      invert_wt_cmd.
    }
    assert (c2 <> Stop).
    {
      intro; subst.
      invert_wt_cmd.
    }
    invert_high_event_step.
    + invert_event_step.
      * unfold is_stop_config, cmd_of in *; subst.
        invert_sem_step; exfalso; eauto 2.
      * discriminate.
  - destruct cfg2 as [c3 pc3 m3 h3 t3].
    invert_high_event_step.
    invert_event_step.
    replace (S n - 1) with n by omega.
    splits.
    + omega.
    + invert_sem_step.
      * right.
        splits~.
      * left.
        exists n0.
        splits~.
    + unfold gc_occurred in *.
      super_destruct.
      subst.
      assert (wellformed_aux Γ Σ' ⟨If e c1 c2, pc3, m3, [h1_pc ⊎ h1_not_pc, H4], t + δ ⟩ pc'').
      {
        eapply gc_preserves_wf; eauto 3.
        erewrite -> disjoint_union_proof_irrelevance; eauto 3.
      }
      edestruct (IHbridge_step_num e c1 c2 pc3 m3 ([h1_pc ⊎ h1_not_pc, H4]) (t + δ)
                                   c' pc' m' h' t'); eauto.      
      super_destruct.
      * splits~.
        left.
        exists p.
        splits~.
        replace (S n - 1) with (S (n - 1)) by omega.
        eapply bridge_trans_num.
        {
          splits~.
          - assert (c1 <> Stop).
            {
              intro; subst.
              invert_wf_aux.
              do 2 specialize_gen.
              invert_wt_cmd.
              invert_wt_stop.
            }
            assert (c1 <> TimeOut).
            {
              intro; subst.
              invert_wf_aux.
              do 2 specialize_gen.
              invert_wt_cmd.
              invert_wt_timeout.
            }
            eapply EventGCStep; reflexivity || eauto 2.
          - eauto.
        }
        { intro.
          unfold is_stop_config, cmd_of in *; subst.
          invert_wf_aux.
          repeat specialize_gen.
          invert_wt_cmd.
          invert_wt_stop.
        }
        {
          intro.
          unfold is_timeout_config, cmd_of in *; subst.
          invert_wf_aux.
          repeat specialize_gen.
          invert_wt_cmd.
          invert_wt_timeout.
        }
        { eauto. }
      * splits~.
        right.
        splits~.
        replace (S n - 1) with (S (n - 1)) by omega.
        eapply bridge_trans_num.
        {
          splits~.
          - assert (c2 <> Stop).
            {
              intro; subst.
              invert_wf_aux.
              do 2 specialize_gen.
              invert_wt_cmd.
              invert_wt_stop.
            }
            assert (c2 <> TimeOut).
            {
              intro; subst.
              invert_wf_aux.
              do 2 specialize_gen.
              invert_wt_cmd.
              invert_wt_timeout.
            }
            eapply EventGCStep; reflexivity || eauto 2.
          - eauto.
        }
        { intro.
          unfold is_stop_config, cmd_of in *; subst.
          invert_wf_aux.
          repeat specialize_gen.
          invert_wt_cmd.
          invert_wt_stop. }
        { intro.
          unfold is_timeout_config, cmd_of in *; subst.
          invert_wf_aux.
          repeat specialize_gen.
          invert_wt_cmd.
          invert_wt_timeout. }
        { eauto. }
Qed.

Lemma high_low_event_is_false:
  forall ℓ ev1 ev2 φ,
    low_event ℓ ev1 ->
    high_event ℓ ev2 ->
    event_low_eq ℓ φ ev1 ev2 -> False.
Proof.
  intros.
  unfolds in H0.
  inverts H1.
  rewrite <- H2 in H0.
  eauto.
Qed.
Hint Resolve high_low_event_is_false.

Lemma wf_stenv_update_heap:
  forall Σ h loc n v,
    wf_stenv Σ h ->
    (forall l, Σ loc = Some (SecType Int l) -> exists n0, v = ValNum n0) ->
    (forall l τ ℓ, Σ loc = Some (SecType (Array τ ℓ) l) -> exists loc0, v = ValLoc loc0) ->
    wf_stenv Σ (update_heap loc n v h).
Proof.
  intros.
  unfold wf_stenv in *.
  intros.
  splits.
  - intros.
    destruct (decide (loc0 = loc)); subst.
    + _apply heap_lookup_update_eq2 in *.
      destruct_exists.
      super_destruct; subst.
      destruct (decide (n0 = n)); subst.
      * rewrite -> lookup_update_eq in *.
        rewrite_inj.
        eauto.
      * rewrite -> lookup_update_neq in * by solve[eauto].
        eauto.
    + rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
      eauto.
  - intros.
    destruct (decide (loc0 = loc)); subst.
    + _apply heap_lookup_update_eq2 in *.
      destruct_exists.
      super_destruct; subst.
      destruct (decide (n0 = n)); subst.
      * rewrite -> lookup_update_eq in *.
        rewrite_inj.
        eauto.
      * rewrite -> lookup_update_neq in * by solve[eauto].
        eauto.
    + rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
      eauto.
  - eauto.
  - intros.
    destruct (decide (loc0 = loc)); subst.
    + _apply heap_lookup_update_eq2 in *.
      super_destruct; eauto.
    + rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
      eauto.
Qed.
Hint Resolve wf_stenv_update_heap.

Lemma reach_update_implies_reach_if:
  forall m h loc1 loc2 n v,
    reach m (update_heap loc1 n v h) loc2 ->
    (forall loc', v = ValLoc loc' -> reach m h loc') ->
    reach m h loc2.
Proof.
  intros.
  dependent induction H.
  - eauto.
  - assert (reach m h loc) by eauto.
    clear IHreach.
    destruct (decide (loc1 = loc)); subst.
    + remember_simple (heap_lookup_update_eq2 loc ℓ n v h μ H0).
      super_destruct; subst.
      destruct v.
      * eauto using reach_update_with_num.
      * assert (reach m h l) by eauto.
        clear H2.
        destruct (decide (n = n0)); subst.
        { rewrite -> lookup_update_eq in *.
          rewrite_inj.
          eauto.
        }
        { rewrite -> lookup_update_neq in * by solve[eauto].
          eauto 2. }
    + rewrite -> heap_lookup_update_neq in * by solve[eauto].
      eauto 2.

      Unshelve.
      * repeat constructor.
Qed.
Hint Resolve reach_update_implies_reach_if.

Lemma low_reach_in_updated_heap:
  forall ℓ Γ Σ1 Σ2 m1 h1 m2 h2 n1 n2 v1 v2 l1 l2 loc1 loc2 φ ℓ_τ ι l τ μ ν,
    state_low_eq ℓ φ m1 h1 m2 h2 Γ Σ1 Σ2 ->
    wf_tenv Γ m1 ->
    wf_tenv Γ m2 ->
    wf_stenv Σ1 h1 ->
    wf_stenv Σ2 h2 ->
    Σ1 l1 = Some (SecType τ (ℓ_τ, ι)) ->
    Σ2 l2 = Some (SecType τ (ℓ_τ, ι)) ->
    heap_lookup l1 h1 = Some (l, μ) ->
    heap_lookup l2 h2 = Some (l, ν) ->
    left φ l1 = Some l2 ->
    low_reach ℓ Γ Σ1 m1 (update_heap l1 n1 v1 h1) loc1 ->
    left φ loc1 = Some loc2 ->
    (forall s ℓ', τ = Array s ℓ' -> exists loc', v1 = ValLoc loc' /\
                                    (ℓ_τ ⊑ ℓ -> low_reach ℓ Γ Σ1 m1 h1 loc')) ->
    (forall s ℓ', τ = Array s ℓ' -> exists loc', v2 = ValLoc loc' /\
                                    (ℓ_τ ⊑ ℓ -> low_reach ℓ Γ Σ2 m2 h2 loc')) ->
    (τ = Int -> exists n, v1 = ValNum n) ->
    (τ = Int -> exists n, v2 = ValNum n) ->
    val_low_eq ℓ (SecType τ (ℓ_τ, ι)) v1 v2 φ ->
    val_low_eq ℓ (SecType Int (ℓ_τ, ι)) (ValNum n1) (ValNum n2) φ ->
    dangling_pointer_free m1 h1 ->
    dangling_pointer_free m2 h2 ->
    heap_level_bound Γ m1 h1 Σ1 ->
    heap_level_bound Γ m2 h2 Σ2 ->
    wf_bijection ℓ φ Γ Σ1 m1 h1 ->
    low_reach ℓ Γ Σ2 m2 (update_heap l2 n2 v2 h2) loc2.
Proof.
  intros.
  revert loc2 H10.
  match goal with
    [H: low_reach _ _ _ _ _ _ |- _] =>
    dependent induction H; intros
  end.
  - assert (memory_lookup m2 x = Some (ValLoc loc2)).
    {
      invert_state_low_eq.
      assert (exists v, memory_lookup m2 x = Some v).
      {
        eapply_low_domain_eq; eauto.
      }
      super_destruct; eauto.
      assert (val_low_eq ℓ_adv (SecType (Array τ0 ℓ_p) (l0, ∘)) (ValLoc loc) v φ) by eauto.
      invert_val_low_eq; try contradiction.
      rewrite_inj.
      eauto.
    }
    eauto 2.
  - destruct (decide (loc1 = l1)); subst.
    + rewrite_inj.
      _apply heap_lookup_update_eq2 in *.
      super_destruct'; subst.
      rewrite_inj.
      destruct (decide (n = n1)); subst.
      * rewrite -> lookup_update_eq in *.
        rewrite_inj.
        assert (ValLoc loc0 = v2).
        {
          invert_val_low_eq.
          - contradiction.
          - rewrite_inj.
            reflexivity.
        }
        subst.
        assert (low_reach ℓ_adv Γ Σ2 m2 (update_heap l2 n2 (ValLoc loc0) h2) l2)
          by eauto 2 using IHlow_reach.
        assert (low_reach ℓ_adv Γ Σ2 m2 h2 loc0).
        {
          repeat specialize_gen.
          super_destruct; subst.
          repeat injects.
          rewrite_inj.
          assert (low_reach ℓ_adv Γ Σ2 m2 h2 loc') by eauto 2.
          eauto.
        }
        eapply LowReachHeap; eauto.
      * rewrite -> lookup_update_neq in * by solve[eauto].
        assert (low_reach ℓ_adv Γ Σ2 m2 (update_heap l2 n2 v2 h2) l2) by eauto 2.
        assert (n1 = n2).
        {
          inverts H19.
          - contradiction.
          - rewrite_inj.
            reflexivity.
        }
        subst.
        clear IHlow_reach.
        assert (low ℓ_adv Γ Σ m h1 l1) by eauto 2.
        assert (low ℓ_adv Γ Σ2 m2 h2 l2).
        {
          eapply low_iff; eauto.
          destruct φ; eauto.
        }
        assert (lookup ν n = Some (ValLoc loc0)).
        {
          invert_state_low_eq.
          assert (low_reach ℓ_adv Γ Σ m h1 l1).
          {
            eapply low_reach_update_implies_low_reach_if; eauto 3.
            intros; subst.
            specialize (H14 τ0 ℓ_p eq_refl).
            super_destruct.
            injects.
            eauto.
          }
          assert (low_reach ℓ_adv Γ Σ2 m2 h2 l2).
          {
            eapply low_reach_update_implies_low_reach_if; eauto 3.
            intros; subst.
            specialize (H15 τ0 ℓ_p eq_refl).
            super_destruct.
            injects.
            eauto.
          }
          eauto 4 using bijection_implies_lookup.
        }
        eapply LowReachHeap.
        { eauto. }
        { eauto. }
        { eauto. }
        { eauto. }
        { instantiate (1 := n).
          rewrite -> lookup_update_neq by solve[eauto].
          eauto. }
    + rewrite -> heap_lookup_update_neq in * by solve[eauto].
      assert (low_reach ℓ_adv Γ Σ m h1 loc1).
      {
        destruct τ.
        - assert (exists n, v1 = ValNum n) by eauto.
          assert (exists n, v2 = ValNum n) by eauto.
          super_destruct; subst.
          eapply low_reach_update_with_num; eauto 2.
        - eapply low_reach_update_implies_low_reach_if.
          + eapply H4.
          + eauto.
          + intros; subst.
            remember_simple (H14 s l3 eq_refl).
            super_destruct; subst.
            clear IHlow_reach.
            injects.
            eauto.
      }
      assert (exists loc', left φ loc1 = Some loc') by eauto.
      super_destruct; subst.
      assert (Σ2 loc' = Some (SecType (Array τ0 ℓ_p) (l0, ∘))).
      {
        invert_state_low_eq.
        eauto.
      }
      assert (exists ν, heap_lookup loc' h2 = Some (ℓ, ν)).
      {
        invert_state_low_eq; eauto.
      }
      super_destruct'; subst.
      assert (low_reach ℓ_adv Γ Σ2 m2 h2 loc').
      {
        invert_state_low_eq.
        eapply H35; eauto.
      }
      assert (lookup ν0 n = Some (ValLoc loc0)).
      {
        invert_state_low_eq.
        eapply bijection_implies_lookup with (Σ1 := Σ) (Σ2 := Σ2) (loc1 := loc1) (loc2 := loc'); eauto 2.
      }
      assert (low_reach ℓ_adv Γ Σ2 m2 (update_heap l2 n2 v2 h2) loc')
        by eauto 2 using IHlow_reach.
      destruct (decide (loc' = l2)); subst.
      * assert (Some l2 <> left φ l1) by eauto 2 using bijection_is_injective_left.
        exfalso; eauto.
      * eapply LowReachHeap; eauto 2.
        rewrite -> heap_lookup_update_neq by solve[eauto].
        eauto.      
Qed.

Lemma low_reach_in_updated_heap_with_high_implies_low_reach:
  forall ℓ_adv Γ Σ m h loc1 loc2 n σ ℓ ι v,
    low_reach ℓ_adv Γ Σ m (update_heap loc1 n v h) loc2 ->
    Σ loc1 = Some (SecType σ (ℓ, ι)) ->
    ~ ℓ ⊑ ℓ_adv ->
    low_reach ℓ_adv Γ Σ m h loc2.
Proof.
  intros.
  dependent induction H.
  - eauto 2.
  - do 2 specialize_gen.
    assert (loc0 <> loc1) by congruence.
    rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
    eauto 2.
Qed.
Hint Resolve low_reach_in_updated_heap_with_high_implies_low_reach.


  Lemma low_update_implies_low_if:
    forall m h loc1 loc2 n v ℓ_adv Γ Σ σ ℓ ι,
      Σ loc1 = Some (SecType σ (ℓ, ι)) ->
      low ℓ_adv Γ Σ m (update_heap loc1 n v h) loc2 ->
      (forall loc' : loc, ℓ ⊑ ℓ_adv -> v = ValLoc loc' -> low_reach ℓ_adv Γ Σ m h loc') ->
      low ℓ_adv Γ Σ m h loc2.
  Proof.
    intros.
    destruct_low.
    - eapply LowReachable.
      eapply low_reach_update_implies_low_reach_if; eauto.
    - destruct (decide (loc = loc1)); subst.
      + assert (exists ν, heap_lookup loc1 h = Some (ℓ0, ν) /\ μ = update_lookup ν n v) by eauto 3.
        super_destruct; subst.
        eauto 3.
      + rewrite -> heap_lookup_update_neq in * by solve[eauto].
        eauto 3.
  Qed.
  Hint Resolve low_update_implies_low_if.

  Lemma low_reach_update_heap_with_high:
    forall ℓ_adv Γ Σ m h loc1 loc2 v n ℓ σ ι,
      low_reach ℓ_adv Γ Σ m h loc1 ->
      Σ loc2 = Some (SecType σ (ℓ, ι)) ->
      ~ ℓ ⊑ ℓ_adv ->
      low_reach ℓ_adv Γ Σ m (update_heap loc2 n v h) loc1.
  Proof.
    intros.
    dependent induction H; eauto 3.
    destruct (decide (loc1 = loc2)); subst.
    - congruence. 
    - eapply LowReachHeap.
      + eapply IHlow_reach; eauto.
      + eauto.
      + rewrite -> heap_lookup_update_neq by solve[eauto].
        eauto.
      + eauto.
      + eauto.
  Qed.
  Hint Resolve low_reach_update_heap_with_high.

  Lemma low_update_with_high:
    forall ℓ_adv Γ Σ m h loc1 loc2 v n ℓ σ ι,
      low ℓ_adv Γ Σ m h loc1 ->
      Σ loc2 = Some (SecType σ (ℓ, ι)) ->
      ~ ℓ ⊑ ℓ_adv ->
      low ℓ_adv Γ Σ m (update_heap loc2 n v h) loc1.
  Proof.
    intros.
    destruct_low.
    - eapply LowReachable.
      eapply low_reach_update_heap_with_high; eauto.
    - destruct (decide (loc2 = loc)); subst.
      + eapply LowHeapLevel; eauto.
      + eapply LowHeapLevel.
        * rewrite -> heap_lookup_update_neq by solve[eauto].
          eauto.
        * eauto.
  Qed.
  Hint Resolve low_update_with_high.

Lemma low_eq_stenv_update:
  forall ℓ_adv φ ψ m1 m2 h1 h2 Σ1 Σ2 loc1 loc2 n1 n2 ℓ σ ι v1 v2 Γ,
    state_low_eq ℓ_adv φ m1 h1 m2 h2 Γ Σ1 Σ2 ->
    wf_bijection ℓ_adv φ Γ Σ1 m1 h1 ->
    wf_bijection ℓ_adv (inverse φ) Γ Σ2 m2 h2 ->
    wf_tenv Γ m1 ->
    wf_tenv Γ m2 ->
    wf_stenv Σ1 h1 ->
    wf_stenv Σ2 h2 ->
    dangling_pointer_free m1 h1 ->
    dangling_pointer_free m2 h2 ->
    heap_level_bound Γ m1 h1 Σ1 ->
    heap_level_bound Γ m2 h2 Σ2 ->
    Σ1 loc1 = Some (SecType σ (ℓ, ι)) ->
    Σ2 loc2 = Some (SecType σ (ℓ, ι)) ->
    (σ = Int -> exists n, v1 = ValNum n) ->
    (σ = Int -> exists n, v2 = ValNum n) ->
    val_low_eq ℓ_adv (SecType σ (ℓ, ι)) v1 v2 φ ->
    (ℓ ⊑ ℓ_adv -> left φ loc1 = Some loc2) ->
    val_low_eq ℓ_adv (SecType Int (ℓ, ι)) (ValNum n1) (ValNum n2) φ ->
    (forall s ℓ',
        σ = Array s ℓ' ->
        exists loc', v1 = ValLoc loc' /\
                (ℓ ⊑ ℓ_adv -> low_reach ℓ_adv Γ Σ1 m1 h1 loc')) ->
    (forall s ℓ', σ = Array s ℓ' ->
             exists loc', v2 = ValLoc loc' /\
                     (ℓ ⊑ ℓ_adv -> low_reach ℓ_adv Γ Σ2 m2 h2 loc')) ->
    filtered (low ℓ_adv Γ Σ1 m1 (update_heap loc1 n1 v1 h1)) φ ψ ->
    low_eq_stenv ℓ_adv ψ m1 m2 (update_heap loc1 n1 v1 h1) (update_heap loc2 n2 v2 h2) Γ Σ1 Σ2.
Proof.
  intros.
  unfolds.
  intros.
  split.
  - intro.
    super_destruct.
    destruct (flowsto_dec ℓ ℓ_adv).
    + assert (low ℓ_adv Γ Σ1 m1 h1 loc0).
      {
        destruct_low.
        - eapply LowReachable.
          eapply low_reach_update_implies_low_reach_if; eauto 2.
          intros; subst.
          destruct σ.
          + assert (exists n, ValLoc loc' = ValNum n) by eauto 2.
            super_destruct; discriminate.
          + specialize (H17 s l eq_refl).
            super_destruct; subst.
            injects.
            eauto 2.
        - destruct (decide (loc = loc1)); subst.
          + assert (exists ν, heap_lookup loc1 h1 = Some (ℓ0, ν) /\
                         μ = update_lookup ν n1 v1) by eauto 2.
            super_destruct; subst.
            rewrite_inj.
            eauto 2.
          + rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
            eauto 3.
      }
      assert (Σ2 loc3 = Some τ /\ low ℓ_adv Γ Σ2 m2 h2 loc3).
      {
        invert_state_low_eq.
        match goal with
          [H: context[low_eq_stenv] |- _] =>
          solve[eapply H; eauto]
        end.
      }
      super_destruct; subst.
      assert (left φ loc0 = Some loc3) by eauto 2.

      assert (exists ℓ μ, heap_lookup loc1 h1 = Some (ℓ, μ)).
      {
        eapply bijection_implies_in_heap; eauto.
      }
      super_destruct; subst.

      assert (low ℓ_adv Γ Σ1 m1 h1 loc1).
      {
        eapply wf_bijection_proj1; eauto 2.
      }
      assert ((exists μ, heap_lookup loc2 h2 = Some (ℓ0, μ)) /\ low ℓ_adv Γ Σ2 m2 h2 loc2).
      {
        invert_state_low_eq.
        match goal with
          [H: context[low_heap_domain_eq] |- _] =>
          solve[eapply H; eauto]
        end.
      }
      super_destruct; subst.
      splits~.
      match goal with
        [H: low _ Γ Σ2 m2 h2 _ |- _] =>
        dependent destruction H
      end.
      * match goal with
          [H: low _ Γ _ _ (update_heap _ _ _ _) _ |- _] =>
          dependent destruction H
        end.
        {
          eapply LowReachable.
          eapply low_reach_in_updated_heap; eauto 2.          
        }
        {
          assert (exists ν, heap_lookup loc0 h1 = Some (ℓ0, ν)).
          {
            destruct (decide (loc0 = loc1)); subst.
            - assert (exists ν, heap_lookup loc1 h1 = Some (ℓ0, ν) /\
                           μ = update_lookup ν n1 v1) by eauto 2.
              super_destruct; subst.
              eauto.
            - rewrite -> heap_lookup_update_neq in * by solve[eauto].
              eauto.
          }
          super_destruct; subst.
          assert (exists μ, heap_lookup loc3 h = Some (ℓ0, μ)).
          {
            invert_state_low_eq.
            match goal with
              [H: context[low_heap_domain_eq] |- _] =>
              solve[eapply H; eauto]
            end.
          }
          super_destruct; subst.
          destruct (decide (loc3 = loc)); subst.
          + rewrite_inj.
            eapply LowHeapLevel; eauto.
          + eapply LowHeapLevel.
            * rewrite -> heap_lookup_update_neq by solve[eauto 2].
              eauto.
            * eauto.
        }        
      * rewrite_inj.
        destruct (decide (loc = loc3)); subst.
        {
          eapply LowHeapLevel; eauto.
        }
        {
          match goal with
            [H: low _ _ _ _ _ ?loc |- low _ _ _ _ _ ?loc] =>
            dependent destruction H
          end.
          - match goal with
              [H: low _ _ _ _ (update_heap _ _ _ _) _ |- _] =>
              dependent destruction H
            end.
            + eapply LowReachable.
              eapply low_reach_in_updated_heap; eauto 2.
            + assert (exists μ, heap_lookup loc2 h = Some (ℓ0, μ)).
              {
                destruct (decide (loc0 = loc1)); subst.
                - rewrite_inj.
                  assert (exists ν, heap_lookup loc1 h1 = Some (ℓ0, ν) /\ μ = update_lookup ν n1 v1) by eauto 2.
                  super_destruct; subst.
                  rewrite_inj.
                  invert_state_low_eq.
                  match goal with
                    [H: context[low_heap_domain_eq] |- _] =>
                    solve[eapply H; eauto]
                  end.
                - rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
                  invert_state_low_eq.
                  match goal with
                    [H: context[low_heap_domain_eq] |- _] =>
                    solve[eapply H; eauto]
                  end.
              }              
              super_destruct; subst.
              rewrite_inj.
              super_destruct; subst.
              eapply LowHeapLevel.
              { rewrite -> heap_lookup_update_neq by solve[eauto].
                eauto. }
              { eauto. }
          - rewrite_inj.
            eapply LowHeapLevel.
            + rewrite -> heap_lookup_update_neq by solve[eauto].
              eauto.
            + eauto.
        }
    + assert (low ℓ_adv Γ Σ1 m1 h1 loc0).
      {
        destruct_low.
        - eapply LowReachable.
          eapply low_reach_in_updated_heap_with_high_implies_low_reach; eauto 3.
        - destruct (decide (loc = loc1)); subst.
          + assert (exists ν, heap_lookup loc1 h1 = Some (ℓ0, ν) /\ μ = update_lookup ν n1 v1)
              by eauto 2.
            super_destruct; subst.
            rewrite_inj.
            eauto 2.
          + rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
            eauto 2.
      }
      assert (Σ2 loc3 = Some τ /\ low ℓ_adv Γ Σ2 m2 h2 loc3).
      {
        invert_state_low_eq.
        match goal with
          [H: context[low_eq_stenv] |- _] =>
          solve[eapply H; eauto]
        end.
      }
      super_destruct; subst.
      splits~.
      eapply low_update_with_high; eauto 2.
  - intro.
    super_destruct.
    destruct (flowsto_dec ℓ ℓ_adv).
    + assert (low ℓ_adv Γ Σ2 m2 h2 loc3).
      {
        destruct_low.
        - eapply LowReachable.
          eapply low_reach_update_implies_low_reach_if; eauto 2.
          intros; subst.
          destruct σ.
          + assert (exists n, ValLoc loc' = ValNum n) by eauto 2.
            super_destruct; discriminate.
          + specialize (H18 s l eq_refl).
            super_destruct; subst.
            injects.
            eauto 2.
        - destruct (decide (loc = loc2)); subst.
          + assert (exists ν, heap_lookup loc2 h2 = Some (ℓ0, ν) /\
                         μ = update_lookup ν n2 v2) by eauto 2.
            super_destruct; subst.
            rewrite_inj.
            eauto 2.
          + rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
            eauto 3.
      }
      assert (Σ1 loc0 = Some τ /\ low ℓ_adv Γ Σ1 m1 h1 loc0).
      {
        invert_state_low_eq.
        match goal with
          [H: context[low_eq_stenv] |- _] =>
          solve[eapply H; eauto]
        end.
      }
      super_destruct; subst.
      assert (left φ loc0 = Some loc3) by eauto 2.

      assert (exists ℓ μ, heap_lookup loc2 h2 = Some (ℓ, μ)).
      {
        eapply bijection_implies_in_heap; destruct φ; eauto.
      }
      super_destruct; subst.
      assert (left φ loc1 = Some loc2) by eauto 2.
      assert (low ℓ_adv Γ Σ2 m2 h2 loc2).
      {
        eapply wf_bijection_proj1; destruct φ; eauto 2.
      }
      assert ((exists μ, heap_lookup loc1 h1 = Some (ℓ0, μ)) /\ low ℓ_adv Γ Σ1 m1 h1 loc1).
      {
        invert_state_low_eq.
        match goal with
          [H: context[low_heap_domain_eq] |- _] =>
          solve[eapply H; eauto]
        end.
      }
      super_destruct; subst.
      splits~.
      match goal with
        [H: low _ Γ Σ1 m1 h1 _ |- _] =>
        dependent destruction H
      end.
      * match goal with
          [H: low _ Γ _ _ (update_heap _ _ _ _) _ |- _] =>
          dependent destruction H
        end.
        {
          eapply LowReachable.
          eapply low_reach_in_updated_heap; destruct φ; eauto 2.          
        }
        {
          assert (exists ν, heap_lookup loc1 h2 = Some (ℓ0, ν)).
          {
            destruct (decide (loc1 = loc2)); subst.
            - assert (exists ν, heap_lookup loc2 h2 = Some (ℓ0, ν) /\
                           μ = update_lookup ν n2 v2) by eauto 2.
              super_destruct; subst.
              eauto.
            - rewrite -> heap_lookup_update_neq in * by solve[eauto].
              eauto.
          }
          super_destruct; subst.
          assert (exists μ, heap_lookup loc0 h = Some (ℓ0, μ)).
          {
            invert_state_low_eq.
            match goal with
              [H: context[low_heap_domain_eq] |- _] =>
              solve[eapply H; eauto]
            end.
          }
          super_destruct; subst.
          destruct (decide (loc0 = loc)); subst.
          + rewrite_inj.
            eapply LowHeapLevel; eauto.
          + eapply LowHeapLevel.
            * rewrite -> heap_lookup_update_neq by solve[eauto 2].
              eauto.
            * eauto.
        }        
      * rewrite_inj.
        destruct (decide (loc = loc0)); subst.
        {
          eapply LowHeapLevel; eauto.
        }
        {
          match goal with
            [H: low _ _ _ _ _ ?loc |- low _ _ _ _ _ ?loc] =>
            dependent destruction H
          end.
          - match goal with
              [H: low _ _ _ _ (update_heap _ _ _ _) _ |- _] =>
              dependent destruction H
            end.
            + eapply LowReachable.
              eapply low_reach_in_updated_heap; destruct φ; eauto 2.
            + assert (exists μ, heap_lookup loc0 h = Some (ℓ0, μ)).
              {
                destruct (decide (loc2 = loc1)); subst.
                - rewrite_inj.
                  assert (exists ν, heap_lookup loc1 h2 = Some (ℓ0, ν) /\ μ = update_lookup ν n2 v2) by eauto 2.
                  super_destruct; subst.
                  rewrite_inj.
                  invert_state_low_eq.
                  match goal with
                    [H: context[low_heap_domain_eq] |- _] =>
                    solve[eapply H; eauto]
                  end.
                - rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
                  invert_state_low_eq.
                  match goal with
                    [H: context[low_heap_domain_eq] |- _] =>
                    solve[eapply H; eauto]
                  end.
              }              
              super_destruct; subst.
              rewrite_inj.
              super_destruct; subst.
              eapply LowHeapLevel.
              { rewrite -> heap_lookup_update_neq by solve[eauto].
                eauto. }
              { eauto. }
          - rewrite_inj.
            eapply LowHeapLevel.
            + rewrite -> heap_lookup_update_neq by solve[eauto].
              eauto.
            + eauto.
        }
    + assert (low ℓ_adv Γ Σ2 m2 h2 loc3).
      {
        destruct_low.
        - eapply LowReachable.
          eapply low_reach_in_updated_heap_with_high_implies_low_reach; eauto 3.
        - destruct (decide (loc = loc2)); subst.
          + assert (exists ν, heap_lookup loc2 h2 = Some (ℓ0, ν) /\ μ = update_lookup ν n2 v2)
              by eauto 2.
            super_destruct; subst.
            rewrite_inj.
            eauto 2.
          + rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
            eauto 2.
      }
      assert (Σ1 loc0 = Some τ /\ low ℓ_adv Γ Σ1 m1 h1 loc0).
      {
        invert_state_low_eq.
        match goal with
          [H: context[low_eq_stenv] |- _] =>
          solve[eapply H; eauto]
        end.
      }
      super_destruct; subst.
      splits~.
      eapply low_update_with_high; eauto 2.
Qed.

Lemma onvals_left_loc:
  forall φ loc1 loc2,
    left φ loc1 = Some loc2 ->
    onvals (left φ) (ValLoc loc1) = Some (ValLoc loc2).
Proof.
  intros.
  unfold onvals.
  rewrite -> H.
  reflexivity.
Qed.
Hint Resolve onvals_left_loc.

Lemma bridge_step_seq_low_event_in_left_stop:
  forall n Γ c1 c2 pc m h t pc' m' h' t' ℓ Σ Σ' ev,
    ⟨c1, pc, m, h, t⟩ ↷ [ℓ, Γ, Σ, Σ', ev, n]
                      ⟨STOP, pc', m', h', t'⟩ ->
    low_event ℓ ev ->
    c2 <> Stop ->
    ⟨c1;; c2, pc, m, h, t⟩ ↷ [ℓ, Γ, Σ, Σ', ev, n] ⟨c2, pc', m', h', t'⟩.
Proof.
  intros.
  dependent induction H.
  - eapply bridge_low_num.
    unfold low_event_step in *.
    super_destruct.
    splits*.
  - unfold high_event_step in *.
    super_destruct.
    contradiction.
  - unfold high_event_step in *.
    super_destruct.
    destruct cfg2.
    assert (⟨c;; c2, pc0, memory, heap, time⟩
              ↷ [l, Γ, Σ', Σ'', ev2, n]
              ⟨c2, pc', m', h', t'⟩)
      by eauto using IHbridge_step_num.
    eapply bridge_trans_num.
    + unfolds.
      splits*.
    + unfold is_stop_config.
      unfold cmd_of.
      intro; discriminate.
    + unfold is_timeout_config.
      unfold cmd_of.
      intro; discriminate.
    + eauto.
Qed.
Hint Resolve bridge_step_seq_low_event_in_left_stop.

Lemma bridge_step_seq_low_event_in_left_nonstop:
  forall Γ Σ Σ' c1 c1' c2 pc m h t pc' m' h' t' ℓ ev n,
    ⟨c1, pc, m, h, t⟩ ↷ [ℓ, Γ, Σ, Σ', ev, n]
                      ⟨c1', pc', m', h', t'⟩ ->
    low_event ℓ ev ->
    c1' <> Stop ->
    c1' <> TimeOut ->
    ⟨c1;; c2, pc, m, h, t⟩ ↷ [ℓ, Γ, Σ, Σ', ev, n]
                           ⟨c1';; c2, pc', m', h', t'⟩.
Proof.
  intros.
  dependent induction H.
  - eapply bridge_low_num.
    unfold low_event_step in *.
    super_destruct.
    splits*.
  - unfold high_event_step in *.
    super_destruct.
    contradiction.
  - unfold high_event_step in *.
    super_destruct.
    destruct cfg2.
    assert (⟨c;; c2, pc0, memory, heap, time⟩
              ↷ [l, Γ, Σ', Σ'', ev2, n]
              ⟨ c1';; c2, pc', m', h', t'⟩) by eauto.
    eapply bridge_trans_num; eauto.
    + unfold is_stop_config, cmd_of.
      intro; discriminate.
    + unfold is_timeout_config, cmd_of.
      intro; discriminate.
Qed.
Hint Resolve bridge_step_seq_low_event_in_left_nonstop.

Inductive backat_at_head: cmd -> (level_proj1 * nat) -> Prop :=
  BackAtAtHeadBackAt:
    forall l n,
      backat_at_head (BackAt l n) (l, n)
| BackAtAtHeadSeq:
    forall c1 c2 l n,
      backat_at_head c1 (l, n) ->
      backat_at_head (c1 ;; c2) (l, n).
Hint Constructors backat_at_head.

Ltac invert_backat_at_head :=
  match goal with
    [H: backat_at_head _ _ |- _] =>
    inverts H
  end.

Lemma gc_occurred_seq:
  forall c1 c1' c2 pc pc' m m' h h' t t' Σ Σ',
    gc_occurred c1 c1' pc pc' m m' h h' t t' Σ Σ' ->
    gc_occurred (c1 ;; c2) (c1' ;; c2) pc pc' m m' h h' t t' Σ Σ'.
Proof.
  intros.
  unfold gc_occurred in *.
  super_destruct; subst.
  splits~.
  - congruence.
  - congruence.
  - exists h1_2 h1_1_pc h1_1_not_pc δ H6 H7; exists H8.
    splits~.
Qed.
Hint Resolve gc_occurred_seq.

(* Describe a sequence of GC events *)
Inductive gc_trans: stenv -> stenv -> config -> config -> nat -> Prop := 
  GCTrans:
    forall c c' c'' pc pc' pc'' m m' m'' h h' h'' t t' t'' Σ Σ' Σ'' n,
      gc_occurred c c' pc pc' m m' h h' t t' Σ Σ' ->
      gc_trans Σ' Σ'' ⟨c', pc', m', h', t'⟩ ⟨c'', pc'', m'', h'', t''⟩ n ->
      gc_trans Σ Σ'' ⟨c, pc, m, h, t⟩ ⟨c'', pc'', m'', h'', t''⟩ (S n)
| GCRefl:
    forall Σ c pc m h t,
      gc_trans Σ Σ ⟨c, pc, m, h, t⟩ ⟨c, pc, m, h, t⟩ 0.
Hint Constructors gc_trans.

Lemma gc_preserves_reach:
  forall c c' pc pc' m m' h h' t t' Σ Σ',
    gc_occurred c c' pc pc' m m' h h' t t' Σ Σ' ->
    forall loc, reach m h loc <-> reach m' h' loc.
Proof.
  intros.
  unfold gc_occurred in *.
  super_destruct; subst.
  splits; eauto 2.
  intros.
  eapply reach_supset_if; eauto.
Qed.
Hint Resolve gc_preserves_reach.
  
Lemma gc_trans_preserves_reach:
  forall Σ Σ' c c' pc pc' m m' h h' t t' n,
    gc_trans Σ Σ' ⟨c, pc, m, h, t⟩ ⟨c', pc', m', h', t'⟩ n ->
    forall loc, reach m h loc <-> reach m' h' loc.
Proof.
  intros.
  dependent induction H.
  - unfold gc_occurred in *.
    super_destruct; subst.
    splits~.
    + intros.
      eapply (IHgc_trans loc).
      eapply reach_supset_if; eauto.
    + intros.
      assert (reach m'0 ([h1_1_pc ⊎ h1_1_not_pc, H8]) loc).
      {
        eapply IHgc_trans; eauto.
      }
      eapply reach_supset; eauto.
  - splits*.
Qed.

Lemma gc_trans_preservation:
  forall Γ Σ Σ' c c' m m' h h' t t' pc pc' pc'' n,
    wellformed_aux Γ Σ ⟨c, pc, m, h, t⟩ pc'' ->
    gc_trans Σ Σ' ⟨c, pc, m, h, t⟩ ⟨c', pc', m', h', t'⟩ n ->
    wellformed_aux Γ Σ' ⟨c', pc', m', h', t'⟩ pc''.
Proof.
  intros.
  dependent induction H0.
  - unfold gc_occurred in *.
    super_destruct; subst.
    eapply IHgc_trans; eauto 2.
  - eauto.
Qed.
Hint Resolve gc_trans_preservation.

Lemma gc_trans_preserves_eval:
  forall Σ Σ' c c' pc pc' m m' h h' t t' e v n,
    gc_trans Σ Σ' ⟨ c, pc, m, h, t⟩ ⟨ c', pc', m', h', t' ⟩ n ->
    eval m' e = Some v ->
    eval m e = Some v.
Proof.
  intros.
  dependent induction H; eauto.
  unfold gc_occurred in *; super_destruct; subst.
  eapply IHgc_trans; eauto.
Qed.
Hint Resolve gc_trans_preserves_eval.

Lemma while_bridge_properties:
  forall ℓ Γ Σ Σ' ev n e c pc m h t c' pc' m' h' t',
    ⟨While e c, pc, m, h, t⟩ ↷ [ℓ, Γ, Σ, Σ', ev, n] ⟨c', pc', m', h', t'⟩ ->
    (eval m e = Some (ValNum 0) /\
     c' = Stop /\
     pc = pc' /\
     m = m' /\
     ev = EmptyEvent /\
     (exists t'',
         gc_trans Σ Σ' ⟨While e c, pc, m, h, t⟩ ⟨While e c, pc, m, h', t''⟩ n /\
         t' = S t'' /\
         ⟨While e c, pc, m, h', t''⟩ ⇒ [EmptyEvent, Γ, Σ', Σ'] ⟨Stop, pc', m', h', t'⟩))
    \/
    (n > 0
     /\
     exists k, eval m e = Some (ValNum k) /\
          k <> 0 /\
          ⟨c ;; While e c, pc, m, h, S t⟩ ↷ [ℓ, Γ, Σ, Σ', ev, n - 1]
                                          ⟨c', pc', m', h', t'⟩).
Proof.
  intros.
  dependent induction H.
  - invert_low_event_step.
    invert_event_step; invert_low_event.
  - invert_high_event_step.
    invert_event_step.
    + unfold is_stop_config in *.
      unfold cmd_of in *.
      subst.
      invert_sem_step.
      left.
      splits*.
      exists t.
      splits*.
    + unfold gc_occurred in *.
      super_destruct.
      unfold is_stop_config, cmd_of in *.
      subst.
      discriminate.
  - invert_high_event_step.
    invert_event_step.
    + invert_sem_step.
      { exfalso; eauto 2. }
      { right.
        splits.
        - omega.
        - exists n0.
          replace (S n - 1) with n in * by omega.
          splits*.
      }
    + unfold gc_occurred in *.
      super_destruct.
      subst.
      specialize (IHbridge_step_num e c pc'0 m'0 ([h1_pc ⊎ h1_not_pc, H5]) (t + δ)
                                    c' pc' m' h' t' eq_refl eq_refl).
      super_destruct; subst.
      * left.
        splits*.
        exists t''.
        splits~.
        eapply GCTrans.
        { unfolds.
          splits*.
          do 7 eexists.
          splits; reflexivity || eauto 2. }
        { eauto. }
      * right.
        splits*.
        exists k.
        replace (S n - 1) with (S (n - 1)) by omega.
        splits*.
        eapply bridge_trans_num.
        { splits~.
          assert ((c;; While e c) <> Stop) by congruence.
          assert ((c;; While e c) <> TimeOut) by congruence.
          eapply EventGCStep; eauto 2.
          intro; invert_low_event.
        }
        { unfold is_stop_config, cmd_of.
          intro; discriminate.
        }
        {
          unfold is_timeout_config, cmd_of.
          intro; discriminate.
        }
        { eauto. }
Qed.

Lemma wellformed_while:
  forall Γ Σ e c pc m h t pc',
    wellformed_aux Γ Σ ⟨While e c, pc, m, h, t ⟩ pc' ->
    wellformed_aux Γ Σ ⟨c, pc, m, h, t⟩ pc'.
Proof.
  intros.
  invert_wf_aux.
  repeat specialize_gen.
  invert_wt_cmd.
  eauto.
Qed.
Hint Resolve wellformed_while.

Ltac destruct_prod_join_flowsto :=
    match goal with
      [H: ?a ⋎ ?b ≼ ?c |- _] =>
      destruct (ProdLatProp.join_flowsto_implies_flowsto a b c H); clear H
    end.
  
  Lemma same_extend_implies_same_loc:
    forall m x loc1 loc2,
      extend_memory x (ValLoc loc1) m = extend_memory x (ValLoc loc2) m ->
      loc1 = loc2.
  Proof.
    intros.
    assert (forall y, memory_lookup (extend_memory x (ValLoc loc1) m) y =
                 memory_lookup (extend_memory x (ValLoc loc2) m) y).
    {
      intros.
      rewrite -> H.
      reflexivity.
    }
    specialize_gen.
    do 2 rewrite -> extend_memory_lookup_eq in *.
    injects.
    reflexivity.
  Qed.
  Hint Resolve same_extend_implies_same_loc.

  Lemma disjoint_extend_implies_disjoint:
    forall loc l n v h1 h2 H1 H2,
      disjoint (h1 [loc → (n × v, l), H1, H2]) h2 ->
      disjoint h1 h2.
  Proof.
    intros.
    unfold disjoint in *.
    intros.
    splits; intros.
    - destruct (decide (loc0 = loc)); subst.
      + destruct (heap_lookup loc h2) eqn:H_loc; try reflexivity.
        destruct p.
        specialize (H loc l0 l1).
        super_destruct.
        specialize_gen.
        remember_simple (heap_lookup_extend_eq loc l n v h1 H1 H2).
        super_destruct; subst.
        congruence.
      + specialize (H loc0 ℓ μ).
        super_destruct.
        rewrite -> heap_lookup_extend_neq in * by solve[eauto].
        firstorder.
    - destruct (decide (loc0 = loc)); subst.
      + repeat specialize_gen.
        super_destruct.
        remember_simple (heap_lookup_extend_eq loc l n v h1 H1 H2).
        super_destruct; subst.
        specialize_gen.
        congruence.
      + specialize (H loc0 ℓ μ).
        super_destruct.
        rewrite -> heap_lookup_extend_neq in * by solve[eauto].
        firstorder.
  Qed.
  Hint Resolve disjoint_extend_implies_disjoint.

  Lemma extend_heap_assoc_ish:
    forall h1 h2 loc n v l H1 H2 H3 H4 H5 H6,
      [(h1 [loc → (n × v, l), H1, H2]) ⊎ h2, H3] =
      [h1 ⊎ (h2 [loc → (n × v, l), H4, H5]), H6].
  Proof.
    intros.
    eapply heap_extensionality.
    intros.
    
    assert (disjoint (h1 [loc → (n × v, l), H1, H2 ]) h2).
    {
      unfolds.
      intros.
      splits.
      - intros.
        destruct (decide (loc1 = loc)); subst; eauto.
        Unshelve.
        + eauto.
      - intros.
        destruct (decide (loc1 = loc)); subst; eauto.
        Unshelve.
        + eauto.
        + eauto.
    }
    assert (disjoint h1 (h2 [loc → (n × v, l), H4, H5 ])).
    {
      unfolds.
      intros.
      splits.
      - intros.
        destruct (decide (loc1 = loc)); subst; eauto.
        Unshelve.
        + eauto.
        + eauto.
      - intros.
        destruct (decide (loc1 = loc)); subst; eauto.
        Unshelve.
        eauto.
    }
    destruct (heap_lookup loc0 ([extend_heap v loc l n h1 H1 H2 ⊎ h2, H3])) eqn:H_loc0.
    - destruct p.
      symmetry.
      destruct (decide (loc0 = loc)); subst.
      + destruct (heap_lookup loc ([h1 ⊎ extend_heap v loc l n h2 H4 H5, H6])) eqn:H_loc.
        * destruct p.
          remember_simple (heap_lookup_extend_eq loc l n v h1 H1 H2).
          super_destruct; subst.
          assert ((l0, l1) = (l, μ)).
          {
            cut (heap_lookup loc ([extend_heap v loc l n h1 H1 H2 ⊎ h2, H3]) = Some (l, μ)).
            {
              congruence.
            }
            {
              eapply disjoint_union_heap_lookup; eauto 2.
            }
          }
          injects.
          assert ((l2, l3) = (l, μ)).
          {
            cut (heap_lookup loc ([h1 ⊎ extend_heap v loc l n h2 H4 H5, H6]) = Some (l, μ)).
            {
              congruence.
            }
            {
              rewrite -> disjoint_union_sym.
              eapply disjoint_union_heap_lookup.
              remember_simple (heap_lookup_extend_eq loc l n v h2 H4 H5).
              super_destruct.
              rewrite_inj.
              assert (μ = μ0) by (eapply lookupfunc_extensionality; congruence).
              subst.
              eauto.
            }
          }
          congruence.
        * destruct_disjoint_heap_lookup.
          {
            cut (heap_lookup loc ([h1 ⊎ extend_heap v loc l n h2 H4 H5, H6]) = Some (l0, l1)).
            {
              congruence.
            }
            {
              rewrite -> disjoint_union_sym.
              eapply disjoint_union_heap_lookup.
              remember_simple (heap_lookup_extend_eq loc l n v h1 H1 H2).
              super_destruct.
              rewrite_inj.
              remember_simple (heap_lookup_extend_eq loc l n v h2 H4 H5).
              super_destruct.
              rewrite_inj.
              assert (μ = μ0) by (eapply lookupfunc_extensionality; congruence).
              subst.
              eauto.
            }
          }
          {
            congruence.
          }
      + destruct_disjoint_heap_lookup.
        * rewrite -> heap_lookup_extend_neq in * by solve[eauto 2].
          eapply disjoint_union_heap_lookup; eauto 2.
        * rewrite -> disjoint_union_sym.
          eapply disjoint_union_heap_lookup.
          rewrite -> heap_lookup_extend_neq in * by solve[eauto 2].
          eauto 2.
    - destruct (decide (loc0 = loc)); subst.
      + remember_simple (heap_lookup_extend_eq loc l n v h1 H1 H2).
        super_destruct.
        rewrite_inj.
        cut (heap_lookup loc ([extend_heap v loc l n h1 H1 H2 ⊎ h2, H3]) = Some (l, μ)).
        {
          congruence.
        }
        {
          eapply disjoint_union_heap_lookup.
          eauto.
        }
      + destruct (heap_lookup loc0 ([h1 ⊎ extend_heap v loc l n h2 H4 H5, H6])) eqn:H_loc0'; try reflexivity.
        destruct p.
        destruct_disjoint_heap_lookup.
        * cut (heap_lookup loc0 ([extend_heap v loc l n h1 H1 H2 ⊎ h2, H3]) = Some (l0, l1)).
          {
            congruence.
          }
          {
            eapply disjoint_union_heap_lookup.
            rewrite -> heap_lookup_extend_neq by solve[eauto 2].
            eauto 2.
          }
        * rewrite -> heap_lookup_extend_neq in * by solve[eauto 2].
          cut (heap_lookup loc0 ([extend_heap v loc l n h1 H1 H2 ⊎ h2, H3]) = Some (l0, l1)).
          {
            congruence.
          }
          {
            rewrite -> disjoint_union_sym.
            eapply disjoint_union_heap_lookup.
            eauto 2.
          }
  Qed.
  
  Lemma extend_to_disjoint_union:
    forall loc l n v h H1 H2 H3,
      exists H4 H5,
      (h [loc → (n × v, l), H1, H2]) = ([h ⊎ (emptyHeap [loc → (n × v, l), H3, H4]), H5]).
  Proof.
    intros.
    assert (size l emptyHeap + n <= maxsize l emptyHeap).
    {
      assert (maxsize l h = maxsize l emptyHeap) by eauto using constant_maxsize.
      assert (size l emptyHeap <= size l h).
      {
        rewrite -> empty_heap_has_size_0.
        omega.
      }
      omega.
    }
    exists H.
    assert (disjoint h (extend_heap v loc l n emptyHeap H3 H)).
    {
      unfolds.
      intros.
      splits.
      - intros.
        destruct (decide (loc0 = loc)); subst.
        + eauto.
        + rewrite -> heap_lookup_extend_neq by solve[eauto].
          eauto.
      - intros.
        destruct (decide (loc0 = loc)); subst.
        + remember_simple (heap_lookup_extend_eq loc l n v emptyHeap H3).
          super_destruct; subst.
          rewrite_inj.
          eauto.
        + rewrite -> heap_lookup_extend_neq in * by solve[eauto 2].
          rewrite -> empty_heap_is_empty in *.
          discriminate.
    }
    exists H0.
    eapply heap_extensionality.
    intros.
    destruct (decide (loc0 = loc)); subst.
    - destruct (heap_lookup loc (extend_heap v loc l n h H1 H2)) eqn:H_loc.
      + destruct p.
        symmetry.
        remember_simple (heap_lookup_extend_eq loc l n v h H1 H2).
        super_destruct; subst.
        rewrite_inj.      
        destruct (heap_lookup loc ([h ⊎ extend_heap v loc l n emptyHeap H3 H, H0])) eqn:H_loc'.
        * destruct p.
          destruct_disjoint_heap_lookup.
          {
            congruence.
          }
          {
            apply_heap_lookup_extend_eq.
            rewrite_inj.
            assert (μ0 = μ).
            {
              eapply lookupfunc_extensionality; congruence.
            }
            subst.
            reflexivity.
          }
        * assert (disjoint h emptyHeap) by eauto.
          assert (heap_lookup loc emptyHeap = None) by eauto.
          assert (disjoint (h [loc → (n × v, l), H1, H2 ]) emptyHeap) by eauto.
          rewrite <- (extend_heap_assoc_ish H7 H0) in *.
          remember_simple (disjoint_union_heap_lookup (h [loc → (n × v, l), _, _ ]) emptyHeap loc l μ H7 H_loc).
          congruence.
      + remember_simple (heap_lookup_extend_eq loc l n v h H1 H2).
        super_destruct; congruence.
    - rewrite -> heap_lookup_extend_neq by solve[eauto].
      destruct (heap_lookup loc0 ([h ⊎ extend_heap v loc l n emptyHeap H3 H, H0])) eqn:H_loc0.
      + destruct p.
        assert (disjoint h (emptyHeap [loc → (n × v, l), H3, H ])) by eauto.
        destruct (disjoint_union_heap_lookup2 h (emptyHeap [loc → (n × v, l), H3, H ]) loc0 l0 l1 _ H_loc0).
        * eauto.
        * rewrite -> heap_lookup_extend_neq in * by solve[eauto].
          assert (heap_lookup loc0 emptyHeap = None) by eauto.
          congruence.
      + destruct (heap_lookup loc0 h) eqn:H_loc0'.
        * destruct p.
          remember_simple (disjoint_union_heap_lookup h (emptyHeap [loc → (n × v, l), H3, H]) loc0 l0 l1 H0 H_loc0').
          congruence.
        * reflexivity.

          Unshelve.
          { eapply extend_heap_disjoint; eauto 2. }        
  Qed.

  Lemma level_neq_size:
    forall h l1 l2,
      l1 <> l2 ->
      levels_satisfy h (eq l1) ->
      size l2 h = 0.
  Proof.
    intros.
    induction h using heap_ind.
    - eapply empty_heap_has_size_0.
    - assert (heap_lookup loc emptyHeap = None) by eauto 2.
      remember_simple (extend_to_disjoint_union n v H1 H2 H3).
      super_destruct.
      rewrite -> H4.
      rewrite -> size_heap_distr.
      assert (l1 = l).
      {
        remember_simple (heap_lookup_extend_eq loc l n v h H1 H2).
        super_destruct; subst.
        eapply H0; eauto.
      }
      subst.
      assert (levels_satisfy h (eq l)).
      {
        unfolds.
        intros.
        assert (loc0 <> loc) by (intro; subst; rewrite_inj; discriminate).
        eapply H0.
        rewrite -> heap_lookup_extend_neq by solve[eauto].
        eauto.
      }
      specialize_gen.
      rewrite IHh in *.
      rewrite -> plus_0_l.
      rewrite -> size_extend_heap_neq_level; eauto 2.
      eapply empty_heap_has_size_0.
  Qed.

  Lemma low_reach_supset:
    forall ℓ_adv m Γ Σ h1 h2 loc H,
      low_reach ℓ_adv Γ Σ m h1 loc ->
      low_reach ℓ_adv Γ Σ m ([h1 ⊎ h2, H]) loc.
  Proof.
    intros.
    induction H0; eauto 3.
  Qed.
  Hint Resolve low_reach_supset.

  Lemma low_supset:
    forall ℓ_adv Γ Σ m h1 h2 loc H,
      low ℓ_adv Γ Σ m h1 loc ->
      low ℓ_adv Γ Σ m ([h1 ⊎ h2, H]) loc.
  Proof.
    intros.
    destruct H0; eauto.
  Qed.
  Hint Resolve low_supset.
  
  Lemma empty_is_high:
    forall ℓ_adv,
      high_event ℓ_adv EmptyEvent.
  Proof.
    intros.
    intro.
    invert_low_event.
  Qed.
  Hint Resolve empty_is_high.
  
  Lemma wt_at_high_implies_high_event:
    forall Γ Σ Σ' c pc m h t pc'' c' pc' m' h' t' ℓ ev,
      ~ pc ⊑ ℓ ->
      ~ contains_low_backat ℓ c ->
      wellformed_aux Γ Σ ⟨c, pc, m, h, t⟩ pc'' ->
      ⟨c, pc, m, h, t⟩ ⇒ [ev, Γ, Σ, Σ'] ⟨c', pc', m', h', t'⟩ ->
      high_event ℓ ev.
  Proof.
    intros.
    revert pc m h t c' pc' pc'' m' h' t' ev Σ Σ' H H0 H1 H2.
    induction c; intros; subst; try solve[invert_event_step; intro; invert_low_event].
    - intro; invert_event_step; invert_low_event.
      invert_wf_aux.
      do 2 specialize_gen.
      invert_wt_cmd.
      invert_lifted.
      rewrite_inj.
      repeat destruct_prod_join_flowsto.
      eauto.
    - assert (exists pc'', wellformed_aux Γ Σ ⟨c1, pc, m, h, t⟩ pc'') by eauto 3.
      super_destruct; subst.
      assert (~ contains_low_backat ℓ c1).
      {
        intro.
        exfalso; eauto 3.
      }
      invert_event_step; eauto 2.
    - invert_wf_aux.
      do 2 specialize_gen.
      invert_wt_cmd.
      assert (~ pc'' ⊑ ℓ).
      {
        intro.
        contradict H0.
        eauto.
      }
      invert_event_step.
      + eauto.
      + intro.
        invert_low_event.
        invert_sem_step.
        * omega.
        * contradiction.
        * omega.
      + intro.
        invert_low_event.
        invert_sem_step; contradiction.
      + eauto.
    - intro; invert_event_step; invert_low_event.
      invert_wf_aux.
      do 2 specialize_gen.
      invert_wt_cmd.
      invert_sem_step.
      invert_lifted.
      rewrite_inj.
      repeat destruct_join_flowsto.
      eauto.
    - intro; invert_event_step; invert_low_event.
      invert_wf_aux.
      do 2 specialize_gen.
      invert_wt_cmd.
      invert_lifted.
      rewrite_inj.
      repeat destruct_prod_join_flowsto.
      assert_wf_type.
      invert_wf_type.
      eauto.
    - intro; invert_event_step; invert_low_event.
      invert_wf_aux.
      do 2 specialize_gen.
      invert_wt_cmd.
      invert_lifted.
      rewrite_inj.
      repeat destruct_prod_join_flowsto.
      eauto.
    - intro; invert_event_step; invert_low_event.
      invert_wf_aux.
      do 2 specialize_gen.
      invert_wt_cmd.
      invert_lifted.
      rewrite_inj.
      repeat destruct_prod_join_flowsto.
      eauto.
  Qed.
  Hint Resolve wt_at_high_implies_high_event.

Lemma no_low_backat_implies_mono_pc_upto_level:
  forall ℓ Γ Σ Σ' c c' pc pc' pc'' m m' h h' t t',
    ~ contains_low_backat ℓ c ->
    wt_aux Γ pc c pc''  ->
    ⟨ c, pc, m, h, t ⟩ ⇒ (Γ, Σ, Σ') ⟨ c', pc', m', h', t' ⟩ ->
    pc ⊑ pc' \/
    (exists ℓ' n, backat_at_head c (ℓ', n) /\ ~ ℓ' ⊑ ℓ).
Proof.
  intros.
  revert dependent pc.
  revert pc' pc'' c'.
  induction c; intros; try solve[left; invert_wt_cmd; invert_step; eapply flowsto_refl].
  - assert (~ contains_low_backat ℓ c1 /\ ~ contains_low_backat ℓ c2) by splits*.
    super_destruct.
    invert_wt_cmd.
    invert_step.
    + assert (pc ⊑ pc' \/
              (exists ℓ' n, backat_at_head c1 (ℓ', n) /\ ~ ℓ' ⊑ ℓ))
        by eauto using IHc1.
      super_destruct; subst.
      * left; eauto.
      * invert_backat_at_head.
        { invert_step.
          right.
          do 2 eexists.
          splits*. }
        { invert_step.
          invert_wt_cmd.
          invert_wt_cmd.
        }
    + assert (pc ⊑ pc' \/
              (exists ℓ' n, backat_at_head c1 (ℓ', n) /\ ~ ℓ' ⊑ ℓ))
        by eauto using IHc1.
      super_destruct; subst.
      * left; eauto.
      * invert_backat_at_head.
        {
          invert_wt_cmd.
          invert_step.
          - left; eapply flowsto_refl.
          - right; do 2 eexists; splits*.
          - exfalso; eauto 2.
          - left; eapply flowsto_refl.
        }
        {
          right; do 2 eexists; splits*.
        }
    + left; eapply flowsto_refl.
  - invert_step.
    invert_wt_cmd.
    left.
    + eauto.
    + left; eapply flowsto_refl.
  - invert_step.
    + left; eapply flowsto_refl.
    + invert_wt_cmd.
      destruct (flowsto_dec pc'' ℓ).
      * contradiction H.
        eauto.
      * destruct (flowsto_dec pc pc'').
        { left; eauto. }
        { right; do 2 eexists; splits*. }
    + destruct (flowsto_dec pc' ℓ).
      * contradict H.
        eauto.
      * right.
        do 2 eexists.
        splits*.
    + left; eapply flowsto_refl.
Qed.
Hint Resolve no_low_backat_implies_mono_pc_upto_level.
  
Lemma no_low_backat_implies_mono_pc_upto_level_event_step:
  forall ℓ Γ Σ Σ' ev c c' pc pc' pc'' m m' h h' t t',
    ~ contains_low_backat ℓ c ->
    wt_aux Γ pc c pc''  ->
    ⟨ c, pc, m, h, t ⟩ ⇒ [ev, Γ, Σ, Σ'] ⟨ c', pc', m', h', t' ⟩ ->
    pc ⊑ pc' \/
    (exists ℓ' n, backat_at_head c (ℓ', n) /\ ~ ℓ' ⊑ ℓ).
Proof.
  intros.
  invert_event_step; eauto.

  Unshelve.
  - eauto.
  - eauto.
Qed.
Hint Resolve no_low_backat_implies_mono_pc_upto_level_event_step.

Ltac invert_contains_low_backat :=
  match goal with
    [H: contains_low_backat _ _ |- _] => inverts H
  end.

Lemma no_spurious_low_backats:
  forall ℓ Γ Σ Σ' c pc m h t c' pc' m' h' t',
    ~ contains_low_backat ℓ c ->
    ~ pc ⊑ ℓ ->
    ⟨c, pc, m, h, t⟩ ⇒ (Γ, Σ, Σ') ⟨c', pc', m', h', t'⟩ ->
    ~ contains_low_backat ℓ c'.
Proof.
  intros.
  revert dependent pc.
  revert m h t c' pc' m' h' t' Σ Σ'.
  induction c; intros; try solve[invert_step; intro; invert_contains_low_backat].
  - invert_step; eauto.
  - invert_step; eauto.
    intro; invert_contains_low_backat.
  - invert_step; eauto.
    assert (~ contains_low_backat ℓ c1') by eauto using IHc1.
    eauto.
  - invert_step; eauto.
    intro.
    invert_contains_low_backat.
    + eauto.
    + invert_contains_low_backat.
      contradiction.
  - invert_step.
    + intro.
      invert_contains_low_backat.
      contradict H; eauto.
    + intro.
      invert_contains_low_backat.
    + intro.
      invert_contains_low_backat.
    + eauto.
Qed.

Lemma no_spurious_low_backats_event_step:
  forall ℓ Γ Σ Σ' c pc m h t c' pc' m' h' t' ev,
    ~ contains_low_backat ℓ c ->
    ~ pc ⊑ ℓ ->
    ⟨c, pc, m, h, t⟩ ⇒ [ev, Γ, Σ, Σ'] ⟨c', pc', m', h', t'⟩ ->
    ~ contains_low_backat ℓ c'.
Proof.
  intros.
  induction c; eauto 2 using no_spurious_low_backats.
Qed.

Lemma high_pc_and_no_low_backat_implies_high_pc:
  forall ℓ Γ Σ Σ' c c' pc pc' pc'' m m' h h' t t',
    ~ contains_low_backat ℓ c ->
    wt_aux Γ pc c pc''  ->
    ~ pc ⊑ ℓ ->
    ⟨ c, pc, m, h, t ⟩ ⇒ (Γ, Σ, Σ') ⟨ c', pc', m', h', t' ⟩ ->
    ~ pc' ⊑ ℓ.
Proof.
  intros.
  revert dependent pc.
  revert pc''.
  revert c'.
  induction c; intros.
  - invert_step; eauto.
  - invert_step; eauto.
  - invert_step; eauto.
  - invert_wt_cmd.
    invert_step; eauto.
  - invert_wt_cmd.
    invert_step; eauto.
  - invert_wt_cmd.
    invert_step.
    + eapply IHc1; eauto 2.
      intro.
      eapply H; eauto.
    + eapply IHc1; eauto 2.
      intro.
      eapply H; eauto.
    + eauto.
  - invert_wt_cmd.
    invert_step.
    + eauto.
    + eauto.
  - invert_wt_cmd.
    invert_step.
    + eauto.
    + eauto.
    + eauto.
    + eauto.
  - invert_wt_cmd.
    invert_step; eauto.
  - invert_wt_cmd.
    invert_step; eauto.
  - invert_wt_cmd.
    invert_step; eauto.
  - invert_wt_cmd.
    invert_step; eauto.
  - invert_step; eauto.
Qed.
Hint Resolve high_pc_and_no_low_backat_implies_high_pc.

Lemma high_pc_and_no_low_backat_implies_high_pc_event_step:
  forall ℓ Γ Σ Σ' c c' pc pc' pc'' m m' h h' t t' ev,
    ~ contains_low_backat ℓ c ->
    wt_aux Γ pc c pc''  ->
    ~ pc ⊑ ℓ ->
    ⟨ c, pc, m, h, t ⟩ ⇒ [ev, Γ, Σ, Σ'] ⟨ c', pc', m', h', t' ⟩ ->
    ~ pc' ⊑ ℓ.
Proof.
  intros.
  induction c; eauto 2 using high_pc_and_no_low_backat_implies_high_pc.
Qed.


Lemma high_pc_and_no_low_backat_implies_high_pc_bridge_step:
  forall ℓ Γ Σ Σ' n c c' pc pc' pc'' m m' h h' t t' ev,
    ~ contains_low_backat ℓ c ->
    wellformed_aux Γ Σ ⟨c, pc, m, h, t⟩ pc'' ->
    ~ pc ⊑ ℓ ->
    ⟨ c, pc, m, h, t ⟩ ↷ [ℓ, Γ, Σ, Σ', ev, n] ⟨ c', pc', m', h', t' ⟩ ->
    ~ pc' ⊑ ℓ.
Proof.
  intros.
  dependent induction H2; intros.
  - invert_low_event_step.
    destruct (eq_cmd_dec c Stop); subst.
    + assert (gc_occurred STOP c' pc pc' m m' h h' t t' Σ Σ' /\ ev = EmptyEvent)
        by eauto.
      unfold gc_occurred in *.
      super_destruct; subst.
      eauto.
    + destruct (eq_cmd_dec c TimeOut); subst.
      * invert_event_step.
        eauto.
      * assert (wt_aux Γ pc c pc'').
        {
          invert_wf_aux.
          do 2 specialize_gen.
          eauto.
        }
        eapply high_pc_and_no_low_backat_implies_high_pc_event_step; eauto 2.
  - invert_high_event_step.
    destruct (eq_cmd_dec c Stop); subst.
    + assert (gc_occurred STOP c' pc pc' m m' h h' t t' Σ Σ' /\ ev = EmptyEvent)
        by eauto.
      unfold gc_occurred in *.
      super_destruct; subst.
      eauto.
    + destruct (eq_cmd_dec c TimeOut); subst.
      * invert_event_step.
        eauto.
      * assert (wt_aux Γ pc c pc'').
        {
          invert_wf_aux.
          do 2 specialize_gen.
          eauto.
        }
        eapply high_pc_and_no_low_backat_implies_high_pc_event_step; eauto 2.
  - invert_high_event_step.
    destruct cfg2.
    assert (~ contains_low_backat l c0)
      by eauto 2 using no_spurious_low_backats_event_step.
    assert (wellformed_aux Γ Σ' ⟨c0, pc0, memory, heap, time⟩ pc'')
      by eauto 2 using preservation_event_step.
    destruct (eq_cmd_dec c Stop); subst.
    + assert (gc_occurred STOP c0 pc pc0 m memory h heap t time Σ Σ' /\ ev1 = EmptyEvent)
        by eauto.
      unfold gc_occurred in *.
      super_destruct; subst.
      eauto.
    + destruct (eq_cmd_dec c TimeOut); subst.
      * invert_event_step.
        eauto.
      * assert (wt_aux Γ pc c pc'')
          by (repeat invert_wf_aux; eauto).
        assert (~ pc0 ⊑ l)
          by eauto 2 using high_pc_and_no_low_backat_implies_high_pc_event_step.
        eapply IHbridge_step_num; eauto 2.
Qed.
Hint Resolve high_pc_and_no_low_backat_implies_high_pc_bridge_step.

Lemma backat_at_head_determines_pc:
  forall Γ Σ Σ' ℓ n c c' pc pc' m m' h h' t t',
    backat_at_head c (ℓ, n) ->
    ⟨c, pc, m, h, t⟩ ⇒ (Γ, Σ, Σ') ⟨c', pc', m', h', t'⟩ ->
    (t = n -> (pc' = ℓ /\ Σ' = Σ /\ m' = m /\ h' = h /\ t' = S t \/ gc_occurred c c' pc pc' m m' h h' t t' Σ Σ')) /\
    (t > n -> (pc' = ℓ /\ Σ' = Σ /\ m' = m /\ h' = h /\ t' = S t /\  c' = TimeOut \/ gc_occurred c c' pc pc' m m' h h' t t' Σ Σ')) /\
    (t < n -> pc' = pc /\ m' = m /\ h' = h /\ t' = S t /\ Σ' = Σ \/ gc_occurred c c' pc pc' m m' h h' t t' Σ Σ').
Proof.
  intros.
  revert dependent pc.
  revert m h t c' pc' m' h' t' Σ Σ'.
  induction c; intros; try invert_backat_at_head.
  - invert_step.
    remember_simple (IHc1 H2 _ _ _ _ _ _ _ _ _ _ _ H15).
    super_destruct'.
    + splits~.
      * intros; subst.
        specialize (H eq_refl).
        destruct H; eauto 2.
        { super_destruct'; subst.
          unfold gc_occurred in * |-.
          super_destruct'; subst.
          invert_backat_at_head. }
      * intro.
        specialize (H0 H3).
        destruct H0.
        { super_destruct; discriminate. }
        { unfold gc_occurred in * |-.
          super_destruct'; subst.
          exfalso; eauto 2. }
      * intros.
        specialize_gen.
        destruct H1.
        {
          super_destruct'; subst.
          left; eauto.
        }
        {
          unfold gc_occurred in * |-.
          super_destruct'; subst.
          exfalso; eauto 2.
        }
    + remember_simple (IHc1 H2 _ _ _ _ _ _ _ _ _ _ _ H15).
      super_destruct'.
      splits~.
      * intros; subst.
        specialize (H eq_refl).
        destruct H; eauto.
      * intros.
        specialize (H0 H3).
        destruct H0.
        { super_destruct'; subst.
          exfalso; eauto 2. }
        { right.
          unfold gc_occurred in *.
          super_destruct'; subst.
          splits; try congruence.
          do 7 eexists.
          splits; reflexivity || eauto 2. }
      * intros.
        specialize_gen.
        destruct H1.
        {
          super_destruct'; subst.
          left; eauto.
        }
        {
          right.
          unfold gc_occurred in *.
          super_destruct'; subst.
          splits; try congruence.
          do 7 eexists.
          splits; reflexivity || eauto 2.
        }
    + splits~.
      * intros; subst.
        right.
        splits*.
        do 7 eexists.
        splits; reflexivity || eauto.
      * intro.
        right.
        unfolds.
        splits; try congruence.
        do 7 eexists.
        splits; reflexivity || eauto.
      * intros.
        right.
        unfolds.
        splits; try congruence.
        do 7 eexists.
        splits; reflexivity || eauto 2.
  - invert_step.
    + split; intros.
      * omega.
      * splits; intros.
        { omega. }
        { left; eauto. }
    + split; intros.
      * left; eauto.
      * split; omega.
    + splits~.
      * intros; subst.
        omega.
      * intros.
        left.
        splits*.
      * intros.
        omega.
    + splits~.
      * right.
        splits*.
        do 7 eexists.
        splits; reflexivity || eauto.
      * intros.
        right.
        unfolds.
        splits; try congruence.
        do 7 eexists.
        splits; reflexivity || eauto 2.
      * right.
        unfolds.
        splits; try congruence.
        do 7 eexists.
        splits; reflexivity || eauto 2.
Qed.
Hint Resolve backat_at_head_determines_pc.

Lemma backat_at_head_determines_pc_event_step:
  forall Γ Σ Σ' ev ℓ n c c' pc pc' m m' h h' t t',
    backat_at_head c (ℓ, n) ->
    ⟨c, pc, m, h, t⟩ ⇒ [ev, Γ, Σ, Σ'] ⟨c', pc', m', h', t'⟩ ->
    (t = n -> (pc' = ℓ /\ Σ' = Σ /\ m' = m /\ h' = h /\ t' = S t \/ gc_occurred c c' pc pc' m m' h h' t t' Σ Σ')) /\
    (t > n -> (pc' = ℓ /\ Σ' = Σ /\ m' = m /\ h' = h /\ t' = S t /\  c' = TimeOut \/ gc_occurred c c' pc pc' m m' h h' t t' Σ Σ')) /\
    (t < n -> pc' = pc /\ m' = m /\ h' = h /\ t' = S t /\ Σ' = Σ \/ gc_occurred c c' pc pc' m m' h h' t t' Σ Σ').
Proof.
  intros.
  invert_event_step; eauto.

  Unshelve.
  eauto.
Qed.
Hint Resolve backat_at_head_determines_pc_event_step.

Lemma no_backat_implies_no_low_backat:
  forall c ℓ,
    ~ contains_backat c ->
    ~ contains_low_backat ℓ c.
Proof.
  intros.
  induction c; intros; try solve[intro; inverts H0; eauto 2].
  - assert (~ contains_backat c1) by eauto.
    assert (~ contains_backat c2) by eauto.
    do 2 specialize_gen.
    intro.
    inverts H2; eauto.
  - assert (~ contains_backat c) by eauto.
    specialize_gen.
    intro.
    inverts H1; eauto.
  - assert (~ contains_backat c1) by eauto.
    assert (~ contains_backat c2) by eauto.
    do 2 specialize_gen.
    eauto.
  - assert (~ contains_backat c) by eauto.
    specialize_gen.
    intro.
    inverts H1; eauto.
Qed.
Hint Resolve no_backat_implies_no_low_backat.

Lemma wt_aux_soundness_event_step:
  forall Γ Σ Σ' c pc pc' pc'' m m' h h' t t' ev,
    wt_aux Γ pc c pc'' ->
    ⟨ c, pc, m, h, t ⟩ ⇒ [ev, Γ, Σ, Σ'] ⟨ STOP, pc', m', h', t' ⟩ ->
    pc' = pc''.
Proof.
  intros.
  invert_event_step; eauto using wt_aux_soundness.
Qed.

Lemma wt_aux_soundness_bridge:
  forall n Γ Σ Σ' ℓ ev c pc pc' pc'' m m' h h' t t',
    wellformed_aux Γ Σ ⟨c, pc, m, h, t⟩ pc'' ->
    ⟨c, pc, m, h, t⟩ ↷ [ℓ, Γ, Σ, Σ', ev, n] ⟨STOP, pc', m', h', t'⟩ ->
    pc' = pc''.
Proof.
  intros n Γ.
  induction n; intros.
  - invert_bridge_step.
    + invert_low_event_step.
      destruct (eq_cmd_dec c Stop); subst.
      * invert_event_step.
        exfalso; eauto 2.
      * destruct (eq_cmd_dec c TimeOut); subst.
        { invert_event_step. }
        { assert (wt_aux Γ pc c pc'') by (repeat invert_wf_aux; eauto).
          eapply wt_aux_soundness_event_step; eauto. }
    + invert_high_event_step.
      destruct (eq_cmd_dec c Stop); subst.
      * invert_event_step.
        exfalso; eauto 2.
      * destruct (eq_cmd_dec c TimeOut); subst.
        { invert_event_step. }
        { assert (wt_aux Γ pc c pc'') by (invert_wf_aux; eauto).
          eapply wt_aux_soundness_event_step; eauto. }
  - invert_bridge_step.
    invert_high_event_step.
    destruct cfg2.
    assert (wellformed_aux Γ Σ'0 ⟨c0, pc0, memory, heap, time⟩ pc'') by eauto 2 using preservation_event_step.
    eapply IHn; eauto 2.
Qed.

Lemma bridge_step_stop_implies_high_event:
  forall c ℓ Γ Σ Σ' ev n pc pc' pc'' m m' h h' t t',
    wellformed_aux Γ Σ ⟨c, pc, m, h, t⟩ pc'' ->
    ~ contains_low_backat ℓ c ->
    ⟨c, pc, m, h, t⟩ ↷ [ℓ, Γ, Σ, Σ', ev, n] ⟨STOP, pc', m', h', t'⟩ ->
    ~ pc ⊑ ℓ ->
    high_event ℓ ev.
Proof.
  intros.
  dependent induction H1.
  - unfold low_event_step in *.
    super_destruct.
    eauto.
  - invert_high_event_step.
    eauto.
  - destruct cfg2.
    invert_high_event_step.
    destruct (eq_cmd_dec c Stop); subst.
    + assert (gc_occurred STOP c0 pc pc0 m memory h heap t time Σ Σ'
              /\ ev1 = EmptyEvent) by eauto.
      unfold gc_occurred in *.
      super_destruct; subst.
      exfalso; eauto.
    + destruct (eq_cmd_dec c TimeOut); subst.
      * invert_event_step.
        eauto.
      * assert (wellformed_aux Γ Σ' ⟨c0, pc0, memory, heap, time⟩ pc'') by eauto 2 using preservation_event_step.
        assert (wt_aux Γ pc0 c0 pc'').
        {
          repeat invert_wf_aux.
          assert (c0 <> Stop) by (intro; subst; eauto 2).
          repeat specialize_gen.
          eauto.
        }
        assert (~ contains_low_backat l c0) by eauto 2 using no_spurious_low_backats.
        assert (wt_aux Γ pc c pc'').
        {
          repeat invert_wf_aux.
          eauto.
        }
        assert (pc ⊑ pc0 \/ (exists ℓ' n, backat_at_head c (ℓ', n) /\ ~ ℓ' ⊑ l))
          by eauto.
        super_destruct.
        { assert (~ pc0 ⊑ l) by eauto.
          eapply IHbridge_step_num; eauto. }
        { assert (~ pc0 ⊑ l).
          {
            remember_simple (backat_at_head_determines_pc_event_step H11 H6).
            super_destruct'.
            destruct (lt_eq_lt_dec t n2).
            - destruct s.
              + specialize_gen; subst.
                eauto.
              + specialize_gen.
                subst.
                destruct H13.
                * subst.
                  eauto.
                * unfold gc_occurred in *.
                  super_destruct'; subst.
                  eauto.
            - specialize_gen.
              destruct H14.
              + super_destruct'; subst.
                eauto.
              + unfold gc_occurred in *.
                super_destruct'; subst.
                eauto.
          }
          eapply IHbridge_step_num; eauto.
        }
Qed.

Lemma bridge_step_nonstop_implies_high_event:
  forall c c' pc pc' pc'' m m' h h' t t' ℓ Γ Σ Σ' ev n,
    wellformed_aux Γ Σ ⟨c, pc, m, h, t⟩ pc'' ->
    ⟨c, pc, m, h, t⟩ ↷ [ℓ, Γ, Σ, Σ', ev, n] ⟨c', pc', m', h', t'⟩ ->
    c' <> Stop ->
    ~ pc ⊑ ℓ ->
    ~ contains_low_backat ℓ c ->
    high_event ℓ ev.
Proof.
  intros.
  dependent induction H0.
  - unfold low_event_step in *.
    super_destruct.
    assert (high_event l ev)
      by (eapply wt_at_high_implies_high_event; eauto 2).
    contradiction.
  - unfold high_event_step in *.
    super_destruct.
    contradiction.
  - destruct cfg2.
    unfold high_event_step in *.
    super_destruct.
    assert (wellformed_aux Γ Σ' ⟨c0, pc0, memory, heap, time⟩ pc'')
      by eauto 2.
    assert (c <> Stop).
    {
      intro; subst.
      invert_event_step.
      unfold gc_occurred in *.
      super_destruct; subst.
      eauto 2.
    }
    assert (c <> TimeOut).
    {
      intro; subst.
      invert_event_step.
      unfold gc_occurred in *.
      super_destruct; subst.
      eauto 2.
    }
    assert (wt_aux Γ pc c pc'').
    {
      repeat invert_wf_aux.
      repeat specialize_gen.
      eauto.
    }
    assert (pc ⊑ pc0 \/ (exists ℓ' n, backat_at_head c (ℓ', n) /\ ~ ℓ' ⊑ l)) by eauto.
    super_destruct.
    + assert (~ pc0 ⊑ l) by eauto.
      assert (~ contains_low_backat l c0) by eauto 2 using no_spurious_low_backats.
      eapply IHbridge_step_num; eauto.
    + assert (~ pc0 ⊑ l).
      {
        edestruct backat_at_head_determines_pc_event_step; eauto 2.
      }
      assert (~ contains_low_backat l c0) by eauto 2 using no_spurious_low_backats.
      eapply IHbridge_step_num; eauto 2.
Qed.

Lemma wf_seq_half_step_implies_wf:
  forall Γ Σ Σ' c1 c2 pc m h t pc' m' h' t' pc'',
    wellformed_aux Γ Σ ⟨c1;; c2, pc, m, h, t⟩ pc'' ->
    ⟨c1, pc, m, h, t ⟩ ⇒ (Γ, Σ, Σ') ⟨STOP, pc', m', h', t'⟩ ->
    wellformed_aux Γ Σ' ⟨c2, pc', m', h', t'⟩ pc''.
Proof.
  intros.
  assert (exists pc2, wellformed_aux Γ Σ ⟨c1, pc, m, h, t⟩ pc2) by eauto.
  destruct_exists.
  assert (pc' = pc2).
  {
    inverts H1.
    assert (c1 <> Stop).
    {
      intro; subst.
      invert_wf_aux.
      repeat specialize_gen.
      invert_wt_cmd.
      invert_wt_stop.
    }
    assert (c1 <> TimeOut).
    {
      intro; subst.
      invert_wf_aux.
      repeat specialize_gen.
      invert_wt_cmd.
      invert_wt_timeout.
    }
    do 2 specialize_gen.
    eapply wt_aux_soundness; eauto.
  }
  subst.
  assert (⟨c1;; c2, pc, m, h, t⟩ ⇒ (Γ, Σ, Σ') ⟨c2, pc2, m', h', t'⟩) by eauto.
  eapply preservation; eauto.
Qed.
Hint Resolve wf_seq_half_step_implies_wf.

Lemma wf_seq_half_step_implies_wf_event_step:
  forall Γ Σ Σ' c1 c2 pc m h t pc' m' h' t' pc'' ev,
    wellformed_aux Γ Σ ⟨c1;; c2, pc, m, h, t⟩ pc'' ->
    ⟨c1, pc, m, h, t ⟩ ⇒ [ev, Γ, Σ, Σ'] ⟨STOP, pc', m', h', t'⟩ ->
    wellformed_aux Γ Σ' ⟨c2, pc', m', h', t'⟩ pc''.
Proof.
  intros.
  invert_event_step; eauto 3 using wf_seq_half_step_implies_wf.
  - invert_wf_aux.
    do 2 specialize_gen.
    invert_wt_cmd.    
    match goal with
      [H: wt_aux _ _ (_ ;; Stop) _ |- _] =>
      inverts H; invert_wt_stop
    end.
  - invert_wf_aux.
    do 2 specialize_gen.
    invert_wt_cmd.
    invert_wt_stop.
Qed.
Hint Resolve wf_seq_half_step_implies_wf_event_step.

Lemma wf_seq_half_step_implies_wf_bridge_step:
  forall n ℓ Γ Σ Σ' c1 c2 pc m h t pc' m' h' t' pc'' ev,
    wellformed_aux Γ Σ ⟨c1;; c2, pc, m, h, t⟩ pc'' ->
    ⟨c1, pc, m, h, t ⟩ ↷ [ℓ, Γ, Σ, Σ', ev, n] ⟨Stop, pc', m', h', t'⟩ ->
    wellformed_aux Γ Σ' ⟨c2, pc', m', h', t'⟩ pc''.
Proof.
  intros.
  dependent induction H0.
  - invert_low_event_step.
    eapply wf_seq_half_step_implies_wf_event_step; eauto 2.
  - invert_high_event_step.
    eapply wf_seq_half_step_implies_wf_event_step; eauto 2.
  - destruct cfg2.
    invert_high_event_step.
    assert (exists pc0, wellformed_aux Γ Σ ⟨c1, pc, m, h, t⟩ pc0)
      by eauto 2.
    destruct_exists.
    assert (wellformed_aux Γ Σ' ⟨c, pc0, memory, heap, time⟩ pc1)
      by eauto 2.
    assert (⟨c1;; c2, pc, m, h, t⟩ ⇒ (Γ, Σ, Σ') ⟨c;; c2, pc0, memory, heap, time⟩).
    {
      invert_event_step; eauto.
    }
    eapply IHbridge_step_num; eauto 2 using preservation.
Qed.

Lemma stop_takes_no_step_many_step:
  forall c pc pc' m m' h h' t t' Γ Σ Σ',
    ⟨Stop, pc, m, h, t⟩ ⇒ * (Γ, Σ, Σ') ⟨c, pc', m', h', t'⟩ ->
    c = Stop /\ pc = pc' /\ m = m' /\ h = h' /\ t = t' /\ Σ = Σ'.
Proof.
  intros.
  dependent induction H; eauto.
  - splits*.
  - destruct cfg.
    exfalso; eauto 2 using stop_takes_no_step.
Qed.

Lemma timeout_takes_no_step_many_step:
  forall c pc pc' m m' h h' t t' Γ Σ Σ',
    ⟨TimeOut, pc, m, h, t⟩ ⇒ * (Γ, Σ, Σ') ⟨c, pc', m', h', t'⟩ ->
    c = TimeOut /\ pc = pc' /\ m = m' /\ h = h' /\ t = t' /\ Σ = Σ'.
Proof.
  intros.
  dependent induction H; eauto.
  - splits*.
  - destruct cfg.
    exfalso; eauto 2 using timeout_takes_no_step.
Qed.

Lemma wt_aux_soundness_many:
  forall Γ Σ Σ' pc c pc'' m h t pc' m' h' t',
    wellformed_aux Γ Σ ⟨c, pc, m, h, t⟩ pc'' ->
    c <> Stop ->
    c <> TimeOut ->
    ⟨c, pc, m, h, t⟩ ⇒ * (Γ, Σ, Σ') ⟨Stop, pc', m', h', t'⟩ ->
    pc' = pc''.
Proof.
  intros.
  dependent induction H2.
  - exfalso; eauto.
  - destruct cfg as [c2 pc2 m2 h2 t2].
    assert (wellformed_aux Γ Σ' ⟨c2, pc2, m2, h2, t2⟩ pc'')
      by eauto 2 using preservation.
    destruct (eq_cmd_dec c2 Stop); subst.
    + remember_simple (stop_takes_no_step_many_step H2).
      super_destruct; subst.
      assert (wt_aux Γ pc c pc'').
      {
        do 2 invert_wf_aux.
        repeat specialize_gen.
        eauto.
      }
      eauto 2 using wt_aux_soundness.
    + destruct (eq_cmd_dec c2 TimeOut); subst.
      * remember_simple (timeout_takes_no_step_many_step H2).
        super_destruct; subst.
        discriminate.
      * eapply IHstepmany; eauto 2.
Qed.
Hint Resolve wt_aux_soundness_many.

Lemma levels_satisfy_extends_implies:
  forall P h loc l n v H1 H2,
    levels_satisfy (h [loc → (n × v, l), H1, H2]) P ->
    levels_satisfy h P.
Proof.
  intros.
  unfolds.
  intros.
  unfold levels_satisfy in *.
  destruct (decide (loc0 = loc)); subst.
  - rewrite_inj.
    discriminate.
  - eapply H.
    rewrite -> heap_lookup_extend_neq by solve[eauto].
    eauto.
Qed.
Hint Resolve levels_satisfy_extends_implies.


Lemma heap_lookup_two_none_implies_disjoint_union_none:
  forall loc h1 h2 H,
    heap_lookup loc h1 = None ->
    heap_lookup loc h2 = None ->
    heap_lookup loc ([h1 ⊎ h2, H]) = None.
Proof.
  intros.
  destruct (heap_lookup loc ([h1 ⊎ h2, H])) eqn:H2; try reflexivity.
  destruct p.
  destruct (disjoint_union_heap_lookup2 _ _ _ _ _ H H2);
    rewrite_inj; discriminate.
Qed.
Hint Resolve heap_lookup_two_none_implies_disjoint_union_none.

Lemma disjoint_implies_disjoint_extend:
  forall h1 h2 loc l n v H1 H2,
    disjoint h1 h2 ->
    heap_lookup loc h2 = None ->
    disjoint (h1 [loc → (n × v, l), H1, H2]) h2.
Proof.
  intros.
  unfold disjoint.
  intros.
  splits; intros.
  - destruct (decide (loc0 = loc)); subst.
    + eauto.
    + rewrite -> heap_lookup_extend_neq in * by solve[eauto].
      eauto.
      Unshelve.
      eauto.
  - destruct (decide (loc0 = loc)); subst.
    + rewrite_inj.
      discriminate.
    + rewrite -> heap_lookup_extend_neq by solve[eauto].
      eauto.

      Unshelve.
      eauto.
Qed.
Hint Resolve disjoint_implies_disjoint_extend.

Lemma reach_disjoint_union_extend_implies_reach_disjoint_union:
  forall m h1 h2 loc1 loc2 l n v H1 H2 H3 H4,
    reach m ([h1 ⊎ h2, H1]) loc2 ->
    reach m ([h1 [loc1 → (n × v, l), H2, H3] ⊎ h2, H4]) loc2.
Proof.
  intros.
  dependent induction H; eauto 2.
  remember_simple (IHreach h1 h2 H1 H2 H3 H4 eq_refl).
  eapply reach_heap.
  - eauto.
    Unshelve.
    + eauto.
    + eauto.
    + eauto.
  - destruct (decide (loc = loc1)); subst.
    + destruct (disjoint_union_heap_lookup2 _ _ _ _ _ _ H0).
      * congruence.
      * unfold disjoint in H4.
        remember_simple (IHreach h1 h2 H1 H2 H3 H4 eq_refl).
        remember_simple (heap_lookup_extend_eq loc1 l n v h1 H2 H3).
        super_destruct'; subst.
        destruct (H4 loc1 l μ0).
        specialize_gen.
        congruence.
    + destruct (disjoint_union_heap_lookup2 _ _ _ _ _ _ H0).
      * eapply disjoint_union_heap_lookup.
        rewrite -> heap_lookup_extend_neq by solve[eauto].
        eauto.
      * rewrite -> disjoint_union_sym.
        eapply disjoint_union_heap_lookup.
        eauto.
  - eauto.
Qed.
Hint Resolve reach_disjoint_union_extend_implies_reach_disjoint_union.

Lemma low_reach_disjoint_union_extend_implies_low_reach_disjoint_union:
  forall m h1 h2 loc1 loc2 l n v ℓ_adv Σ Γ t H1 H2 H3 H4,
    low_reach ℓ_adv Γ Σ m ([h1 ⊎ h2, H1]) loc2 ->
    heap_lookup loc1 h2 = None ->
    low_reach ℓ_adv Γ (extend_stenv loc1 t Σ) m
              ([h1 [loc1 → (n × v, l), H2, H3] ⊎ h2, H4]) loc2.
Proof.
  intros.
  dependent induction H; try solve[eauto 2].
  remember_simple (IHlow_reach h1 h2 H1 H2 H3 H4 eq_refl H8).
  eapply LowReachHeap.
  - eauto.
  - destruct (decide (loc0 = loc1)); subst.
    + destruct_disjoint_heap_lookup; congruence.
    + rewrite -> extend_stenv_lookup_neq by solve[eauto].
      eauto.
  - destruct (decide (loc0 = loc1)); subst.
    + destruct_disjoint_heap_lookup; congruence.
    + destruct_disjoint_heap_lookup.
      * erewrite -> disjoint_union_heap_lookup.
        { reflexivity.  }
        { rewrite -> heap_lookup_extend_neq by solve[eauto].
          eauto. }
      * rewrite -> disjoint_union_sym.
        erewrite -> disjoint_union_heap_lookup.
        { reflexivity. }
        { eauto. }
  - eauto.
  - eauto.
Qed.
Hint Resolve low_reach_disjoint_union_extend_implies_low_reach_disjoint_union.

Lemma emptyHeap_disjoint_implies_both_emptyHeap:
  forall h1 h2 H,
    [h1 ⊎ h2, H] = emptyHeap ->
    h1 = emptyHeap /\ h2 = emptyHeap.
Proof.
  intros.
  splits.
  - eapply heap_extensionality.
    intros.
    rewrite -> empty_heap_is_empty.
    destruct (heap_lookup loc h1) eqn:H_loc; try reflexivity.
    destruct p.
    assert (heap_lookup loc ([h1 ⊎ h2, H]) = Some (l, l0)) by eauto 2.
    rewrite -> H0 in H1.
    assert (heap_lookup loc emptyHeap = None) by eauto.
    congruence.
  - eapply heap_extensionality.
    intros.
    rewrite -> empty_heap_is_empty.
    destruct (heap_lookup loc h2) eqn:H_loc; try reflexivity.
    destruct p.
    assert (heap_lookup loc ([h2 ⊎ h1, disjoint_sym _ _ H]) = Some (l, l0)) by eauto 2.
    rewrite -> disjoint_union_sym in H1.
    erewrite -> disjoint_union_proof_irrelevance in H1.
    rewrite -> H0 in H1.
    assert (heap_lookup loc emptyHeap = None) by eauto.
    congruence.
Qed.
Hint Resolve emptyHeap_disjoint_implies_both_emptyHeap.

Lemma size_is_monotone_in_heap:
  forall h l l' loc n v H1 H2,
    size l h <= size l (h [loc → (n × v, l'), H1, H2]).
Proof.
  intro.
  induction h using heap_ind; intros.
  - rewrite -> empty_heap_has_size_0.
    omega.
  - destruct (T_dec l0 l); subst.
    + rewrite -> size_extend_heap_eq_level by solve[eauto].
      assert (loc0 <> loc).
      {
        intro; subst.
        remember_simple (heap_lookup_extend_eq loc l n v h H1 H2).
        super_destruct.
        congruence.
      }
      destruct (T_dec l l'); subst.
      * do 2 rewrite -> size_extend_heap_eq_level by solve[eauto 2].
        omega.
      * rewrite -> size_extend_heap_neq_level by solve[eauto 2].
        rewrite -> size_extend_heap_eq_level by solve[eauto 2].
        omega.
    + rewrite -> size_extend_heap_neq_level by solve[eauto 2].
      destruct (T_dec l0 l'); subst.
      * rewrite -> size_extend_heap_eq_level by solve[eauto 2].
        rewrite -> size_extend_heap_neq_level by solve[eauto 2].
        omega.
      * do 2 rewrite -> size_extend_heap_neq_level by solve[eauto 2].
        omega.
Qed.

Lemma size_is_monotone_in_heap':
  forall h l loc ℓ μ,
    heap_lookup loc h = Some (ℓ, μ) ->
    size l (reduce_heap loc h) <= size l h.
Proof.
  intro.
  induction h using heap_ind; intros.
  - assert (heap_lookup loc emptyHeap = None) by eauto 2.
    congruence.
  - destruct (T_dec l0 l); subst.
    + rewrite -> size_extend_heap_eq_level by solve[eauto 2].
      destruct (decide (loc0 = loc)); subst.
      * apply_heap_lookup_extend_eq.
        rewrite_inj.
        assert (length_of loc (extend_heap v loc l n h H1 H2) = Some n) by eauto 2.
        assert (size l (extend_heap v loc l n h H1 H2) =
                size l (reduce_heap loc (extend_heap v loc l n h H1 H2)) + n)
          by eauto 2 using size_reduce_heap_eq_level.
        assert (size l (extend_heap v loc l n h H1 H2) - n =
                size l (reduce_heap loc (extend_heap v loc l n h H1 H2))) by omega.
        rewrite <- H5.
        rewrite -> size_extend_heap_eq_level; eauto 2.
        omega.
      * rewrite -> heap_lookup_extend_neq in * by solve[eauto 2].
        assert (exists k, length_of loc0 h = Some k).
        {
          eapply length_of_lookup_correspondance.
          eauto.
        }
        super_destruct.
        assert (heap_lookup loc0 (extend_heap v loc l n h H1 H2) = Some (ℓ, μ)).
        {
          rewrite -> heap_lookup_extend_neq by solve[eauto 2].
          eauto.
        }
        assert (length_of loc0 (extend_heap v loc l n h H1 H2) = Some k).
        {
          rewrite -> length_of_extend_neq by solve[eauto 2].
          eauto.
        }
        destruct (T_dec ℓ l); subst.
        {          
          assert (size l (extend_heap v loc l n h H1 H2) =
                  size l (reduce_heap loc0 (extend_heap v loc l n h H1 H2)) + k) by eauto 2.
          assert (size l (extend_heap v loc l n h H1 H2) - k =
                  size l (reduce_heap loc0 (extend_heap v loc l n h H1 H2))) by omega.
          rewrite <- H6.
          assert (size l (reduce_heap loc0 h) <= size l h) by eauto 2.
          rewrite -> size_extend_heap_eq_level by solve[eauto 2].
          omega.
        }
        {
          erewrite -> size_reduce_heap_neq_level; eauto 2.
          rewrite -> size_extend_heap_eq_level by solve[eauto 2].
          omega.
        }
    + rewrite -> size_extend_heap_neq_level by solve[eauto 2].
      destruct (decide (loc0 = loc)); subst.
      * apply_heap_lookup_extend_eq.
        rewrite_inj.
        assert (length_of loc (extend_heap v loc l n h H1 H2) = Some n) by eauto 2.
        assert (l <> l0) by eauto 2.
        erewrite -> size_reduce_heap_neq_level by solve[eauto 2].
        rewrite -> size_extend_heap_neq_level by solve[eauto 2].
        omega.
      * rewrite -> heap_lookup_extend_neq in * by solve[eauto 2].
        assert (size l0 (reduce_heap loc0 h) <= size l0 h) by eauto 2.
        assert (size l0 (reduce_heap loc0 h) = size l0 (reduce_heap loc0 (extend_heap v loc l n h H1 H2))).
        {
          assert (exists k, length_of loc0 h = Some k).
          {
            eapply length_of_lookup_correspondance.
            eauto.
          }
          super_destruct; subst.
          destruct (T_dec l0 ℓ); subst.
          - assert (size ℓ h = size ℓ (reduce_heap loc0 h) + k) by eauto 2.
            assert (size ℓ h - k = size ℓ (reduce_heap loc0 h)) by omega.
            assert (heap_lookup loc0 (extend_heap v loc l n h H1 H2) = Some (ℓ, μ)).
            {
              rewrite -> heap_lookup_extend_neq by solve[eauto 2].
              eauto.
            }
            assert (length_of loc0 (extend_heap v loc l n h H1 H2) = Some k).
            {
              rewrite -> length_of_extend_neq by solve[eauto 2].
              eauto.
            }            
            rewrite <- H5.
            assert (size ℓ (extend_heap v loc l n h H1 H2) =
                    size ℓ (reduce_heap loc0 (extend_heap v loc l n h H1 H2)) + k) by eauto 2.
            assert (size ℓ (extend_heap v loc l n h H1 H2) - k =
                    size ℓ (reduce_heap loc0 (extend_heap v loc l n h H1 H2))) by omega.
            rewrite <- H9.
            rewrite -> size_extend_heap_neq_level by solve[eauto 2].
            reflexivity.
          - erewrite -> size_reduce_heap_neq_level by solve[eauto 2].
            assert (heap_lookup loc0 (extend_heap v loc l n h H1 H2) = Some (ℓ, μ)).
            {
              rewrite -> heap_lookup_extend_neq by solve[eauto 2].
              eauto.
            }
            assert (length_of loc0 (extend_heap v loc l n h H1 H2) = Some k).
            {
              rewrite -> length_of_extend_neq by solve[eauto 2].
              eauto.
            }
            assert (ℓ <> l0) by eauto 2.
            erewrite -> (size_reduce_heap_neq_level) by solve[eauto 2].
            rewrite -> size_extend_heap_neq_level by solve[eauto 2].
            reflexivity.
        }
        omega.
Qed.

Lemma extend_reduce_id:
  forall φ loc loc' H1 H2 H3,
    left φ loc = Some loc' ->
    extend_bijection (reduce_bijection φ loc loc' H1) loc loc' H2 H3 =
    φ.
Proof.
  intros.
  eapply bijection_proof_irrelevance.
  - extensionality loc''.
    destruct (decide (loc = loc'')); subst.
    + rewrite -> left_extend_bijection_eq.
      eauto.
    + rewrite -> left_extend_bijection_neq by solve[eauto].
      rewrite -> reduce_bijection_lookup_neq_left by solve[eauto].
      reflexivity.
  - extensionality loc''.
    destruct (decide (loc' = loc'')); subst.
    + rewrite -> right_extend_bijection_eq.
      assert (right φ loc'' = Some loc) by (destruct φ; eauto).
      eauto.
    + rewrite -> right_extend_bijection_neq by solve[eauto].
      rewrite -> reduce_bijection_lookup_neq_right by solve[eauto].
      reflexivity.
Qed.
Hint Resolve extend_reduce_id.

(*
Lemma extend_heap_disjoint_union_eq:
  forall loc l n v h1 h2 h H1 H2,
    heap_lookup loc h1 = None ->
    heap_lookup loc h = None ->
    size l h1 + n <= maxsize l h1 ->
    [extend_heap loc l n v h1 ⊎ h2, H1] = extend_heap loc l n v h ->
    h = [h1 ⊎ h2, H2].
Proof.
  intros.
  eapply heap_extensionality.
  intros.
  assert (heap_lookup loc h2 = None).
  {
    assert (exists μ, heap_lookup loc (extend_heap loc l n v h1) = Some (l, μ)
                 /\ (forall n : nat, lookup μ n = Some v)) by eauto.
    super_destruct; subst.
    iauto.
    Unshelve.
    eauto.
  }
  destruct (heap_lookup loc0 ([h1 ⊎ h2, H2])) eqn:H_12.
  - destruct p.
    destruct (disjoint_union_heap_lookup2 _ _ _ _ _ _ H_12).
    + assert (loc <> loc0) by congruence.
      erewrite <- heap_lookup_extend_neq by solve[eauto].
      rewrite <- H4.
      eapply disjoint_union_heap_lookup.
      rewrite -> heap_lookup_extend_neq by solve[eauto].
      eauto.
    + assert (loc <> loc0) by congruence.
      erewrite <- heap_lookup_extend_neq by solve[eauto].
      rewrite <- H4.
      rewrite -> disjoint_union_sym.
      eapply disjoint_union_heap_lookup.
      eauto.
  - destruct (heap_lookup loc0 h) eqn:H_h; try reflexivity.
    destruct p.
    assert (loc0 <> loc) by congruence.
    erewrite <- heap_lookup_extend_neq in H_h by solve[eauto].
    rewrite <- H4 in H_h.
    assert (heap_lookup loc0 h1 = None).
    {
      destruct (heap_lookup loc0 h1) eqn:H_1; try reflexivity.
      destruct p.
      assert (heap_lookup loc0 ([h1 ⊎ h2, H2]) = Some (l2, l3)).
      {
        eapply disjoint_union_heap_lookup; eauto.
      }
      congruence.
    }
    assert (heap_lookup loc0 h2 = None).
    {
      destruct (heap_lookup loc0 h2) eqn:H_2; try reflexivity.
      destruct p.
      assert (heap_lookup loc0 ([h1 ⊎ h2, H2]) = Some (l2, l3)).
      {
        rewrite -> disjoint_union_sym.
        eapply disjoint_union_heap_lookup; eauto.
      }
      congruence.
    }
    destruct (disjoint_union_heap_lookup2 _ _ _ _ _ _ H_h).
    + rewrite -> heap_lookup_extend_neq in * by solve[eauto].
      congruence.
    + congruence.
Qed.
Hint Resolve extend_heap_disjoint_union_eq.
*)
  
  Lemma high_pc_gc_does_not_update_low_states:
    forall ℓ_adv pc Γ Σ m h_pc h_not_pc h_gc H1 H2 H3,
      ~ pc ⊑ ℓ_adv ->
      wf_tenv Γ m ->
      dangling_pointer_free m ([[h_pc ⊎ h_not_pc, H1] ⊎ h_gc, H2]) ->
      wf_stenv Σ ([[h_pc ⊎ h_not_pc, H1] ⊎ h_gc, H2]) ->
      levels_satisfy h_pc (eq pc) ->
      levels_satisfy h_not_pc (compose not (eq pc)) ->
      levels_satisfy h_gc (eq pc) ->
      (forall loc ℓ μ,
          heap_lookup loc h_gc = Some (ℓ, μ) ->
          ~ reach m ([[h_pc ⊎ h_not_pc, H1] ⊎ h_gc, H2]) loc) ->
      state_low_eq ℓ_adv (identity_bijection loc)
                   m ([[h_pc ⊎ h_not_pc, H1] ⊎ h_gc, H2])
                   m ([h_pc ⊎ h_not_pc, H3]) Γ Σ Σ.
  Proof.
    intros.
    eapply StateLowEq; eauto 2.
    - unfolds.
      intros.
      unfold left, identity_bijection in *.
      rewrite_inj.
      splits.
      + intros.
        super_destruct; subst.
        splits~.
        destruct_low.
        * assert (low_reach ℓ_adv Γ Σ m ([h_pc ⊎ h_not_pc, H1]) loc)
            by eauto 2 using low_reach_subset_if.
          erewrite -> disjoint_union_proof_irrelevance.
          eauto.
        * destruct_disjoint_heap_lookup.
          {
            erewrite -> disjoint_union_proof_irrelevance.
            eauto 2.
          }
          {
            assert (~ reach m ([[h_pc ⊎ h_not_pc, H1] ⊎ h_gc, H2]) loc) by eauto 2.
            assert (pc = ℓ) by eauto 2.
            subst.
            contradiction.
          }
      + intros.
        super_destruct; subst.
        splits~.
        eapply low_supset.
        erewrite -> disjoint_union_proof_irrelevance.
        eauto.
    - unfolds.
      intros.
      unfold left, identity_bijection in *.
      rewrite_inj.
      splits.
      + intros.
        super_destruct; subst.
        splits~.
        * destruct_low.
          {
            destruct_disjoint_heap_lookup.
            - erewrite -> disjoint_union_proof_irrelevance.
              eauto.
            - assert (~ reach m ([[h_pc ⊎ h_not_pc, H1] ⊎ h_gc, H2]) loc) by eauto 2.
              exfalso; eauto 3.
          }
          {
            rewrite_inj.
            destruct_disjoint_heap_lookup.
            - erewrite -> disjoint_union_proof_irrelevance.
              eauto.
            - assert (pc = ℓ0) by eauto 2.
              subst.
              contradiction.
          }
        * destruct_low.
          {
            destruct_disjoint_heap_lookup.
            - erewrite -> disjoint_union_proof_irrelevance.
              eauto 3.
            - assert (~ reach m ([[h_pc ⊎ h_not_pc, H1] ⊎ h_gc, H2]) loc) by eauto 2.
              exfalso; eauto 3.
          }
          {
            rewrite_inj.
            destruct_disjoint_heap_lookup.
            - erewrite -> disjoint_union_proof_irrelevance.
              eauto 2.
            - assert (pc = ℓ0) by eauto 2.
              subst.
              contradiction.
          }
      + intros.
        super_destruct; subst.
        splits~.
        * exists ν.
          eapply disjoint_union_heap_lookup.
          erewrite -> disjoint_union_proof_irrelevance.
          eauto.
        * eapply low_supset.
          erewrite -> disjoint_union_proof_irrelevance.
          eauto.
    - unfolds.
      intros.
      rewrite_inj.
      destruct τ as [τ [ℓ ι]].
      destruct τ.
      + assert (exists n, v2 = ValNum n) by eauto.
        super_destruct; subst.
        eauto.
      + assert (ι = ∘).
        {
          assert (wf_type bot (SecType (Array s l) (ℓ, ι))) by eauto.
          invert_wf_type.
          reflexivity.
        }
        subst.
        assert (exists loc, v2 = ValLoc loc) by eauto.
        super_destruct; subst.
        eauto.
    - unfolds.
      intros.
      unfold left, identity_bijection in * |-.
      rewrite_inj.
      assert (exists ℓ μ, heap_lookup loc2 ([[h_pc ⊎ h_not_pc, H1] ⊎ h_gc, H2]) = Some (ℓ, μ)) by eauto 2.
      super_destruct; subst.
      assert (heap_lookup loc2 ([h_pc ⊎ h_not_pc, H3]) = Some (ℓ, μ)).
      {
        destruct_disjoint_heap_lookup.
        - erewrite -> disjoint_union_proof_irrelevance.
          eauto.
        - assert (~ reach m ([[h_pc ⊎ h_not_pc, H1] ⊎ h_gc, H2]) loc2) by eauto.
          dependent destruction H14.
          + contradict H15.
            eapply reach_supset.
            erewrite -> disjoint_union_proof_irrelevance.
            eauto 2.
          + assert (heap_lookup loc ([[h_pc ⊎ h_not_pc, H1] ⊎ h_gc, H2]) = Some (ℓ, μ)).
            {
              eapply disjoint_union_heap_lookup.
              erewrite -> disjoint_union_proof_irrelevance.
              eauto.
            }
            rewrite_inj.
            eauto.
      }
      super_destruct; subst.
      destruct τ as [τ ε].
      eapply HeapValLowEq.
      + eauto.
      + eauto.
      + intros; splits*.
      + intros.
        rewrite_inj.
        destruct τ.
        * assert (exists n, v = ValNum n) by eauto 3.
          super_destruct; subst.
          eauto.
        * assert (exists loc, v = ValLoc loc) by eauto.
          super_destruct; subst.
          eauto.
    - unfolds.
      intros.
      unfold left, identity_bijection in *.
      rewrite_inj.
      splits.
      + intros.
        erewrite -> disjoint_union_proof_irrelevance.
        eauto 3.
      + intros.
        eapply low_reach_supset.
        erewrite -> disjoint_union_proof_irrelevance.
        eauto.
    - intros.
      assert (pc <> l) by congruence.
      repeat rewrite -> size_heap_distr.
      assert (size l h_gc = 0) by eauto using level_neq_size.
      omega.
    - intros.
      unfold left, identity_bijection in * |-.
      rewrite_inj.
      assert (heap_lookup loc' ([[h_pc ⊎ h_not_pc, H1] ⊎ h_gc, H2]) = Some (l, ν)).
      {
        eapply disjoint_union_heap_lookup.
        erewrite -> disjoint_union_proof_irrelevance.
        eauto.
      }
      rewrite_inj.
      destruct (length_of loc' ([h_pc ⊎ h_not_pc, H3])) eqn:H_loc'.
      + eapply disjoint_union_length_of.
        erewrite -> disjoint_union_proof_irrelevance.
        eauto.
      + assert (exists l μ, heap_lookup loc' ([h_pc ⊎ h_not_pc, H3]) = Some (l, μ)) by eauto.
        assert (exists n, length_of loc' ([h_pc ⊎ h_not_pc, H3]) = Some n).
        {
          eapply length_of_lookup_correspondance; eauto.
        }
        super_destruct; subst.
        congruence.
  Qed.


  Lemma state_low_eq_extend_mem_heap_high:
    forall Γ Σ m h σ l ℓ_x loc0 v n x ℓ_adv ι ℓ H1 H2,
      wf_tenv Γ m ->
      wf_stenv Σ h ->
      dangling_pointer_free m h ->
      lookup_in_bounds m h ->
      heap_level_bound Γ m h Σ ->
      consistent m h Γ Σ ->
      Γ x = Some (SecType (Array (SecType σ (ℓ, ι)) l) (ℓ_x, ∘)) ->
      ~ ℓ_x ⊑ ℓ_adv ->
      (σ = Int -> exists n, v = ValNum n) ->
      (forall τ ℓ', σ = Array τ ℓ' -> exists loc, v = ValLoc loc
                                       /\ (ℓ ⊑ ℓ_adv -> low_reach ℓ_adv Γ Σ m h loc)
                                       /\ (~ ℓ ⊑ ℓ_adv -> reach m h loc)) ->
      state_low_eq ℓ_adv (identity_bijection loc) m h
                   (m [x → ValLoc loc0])
                   (h [loc0 → (n × v, l), H1, H2]) Γ Σ
                   (extend_stenv loc0 (SecType σ (ℓ, ι)) Σ).
  Proof.
    intros.
    apply StateLowEq; eauto 2.
    - unfolds.
      intros.
      unfold left, identity_bijection in *.
      rewrite_inj.
      destruct (decide (loc0 = loc2)); subst.
      {
        splits.
        - intro.
          super_destruct.
          destruct_low.
          + assert (exists ℓ μ, heap_lookup loc h = Some (ℓ, μ)) by eauto.
            super_destruct; subst.
            congruence.
          + congruence.
        - intros.
          super_destruct.
          rewrite -> extend_stenv_lookup_eq in *.
          rewrite_inj.
          repeat destruct_join_flowsto.
          remember_simple (heap_lookup_extend_eq loc2 l n v h H1 H2).
          super_destruct; subst.
          rewrite_inj.
          assert_wf_type.
          invert_wf_type.
          assert (~ l ⊑ ℓ_adv) by eauto.
          destruct_low.
          + assert (ℓ_x ⊑ ℓ_adv).
            {
              eapply new_low_reach_implies_flowsto_low with (v := v).
              - eauto.
              - eauto.
              - intros; subst.
                match goal with
                  [H: forall _ _, Array _ _ = Array _ _ -> exists _, _ |- _] =>
                  specialize (H s ℓ0 eq_refl)
                end.
                super_destruct; subst.
                exists loc0.
                splits~.
                destruct (flowsto_dec ℓ ℓ_adv); eauto 3.
              - eauto.
              - eauto.
            }
            exfalso; eauto 3.
          + rewrite_inj.
            contradiction.
      }
      {
        rewrite -> extend_stenv_lookup_neq by solve[eauto].
        splits~.
        - intros.
          super_destruct; subst.
          splits*.
        - intros; subst.
          super_destruct; subst.
          splits~.
          eapply low_extend_implies_low_if; eauto 2.
          intros; subst.
          match goal with
            [H: forall _ _, Array _ _ = Array _ _ -> exists _, _ |- _] =>
            specialize (H s ℓ' eq_refl)
          end.
          super_destruct.
          subst.
          exists loc.
          splits; eauto 3.
      }
    - unfolds.
      intros.
      destruct (decide (x0 = x)); subst.
      { rewrite -> extend_memory_lookup_eq in *.
        rewrite_inj.
        contradiction. }
      { rewrite -> extend_memory_lookup_neq in * by solve[eauto].
        rewrite_inj.
        splits*. }
    - unfolds.
      intros.
      unfold left, identity_bijection in * |-.
      rewrite_inj.
      splits~.
      + intros.
        super_destruct; subst.
        assert (l2 <> loc0).
        {
          intro; subst.
          congruence.
        }
        rewrite -> heap_lookup_extend_neq in * by solve[eauto].
        splits*.
      + intros; subst.
        super_destruct; subst.
        destruct (decide (l2 = loc0)); subst.
        * destruct_low.
          {
            assert (ℓ_x ⊑ ℓ_adv).
            {
              eapply new_low_reach_implies_flowsto_low with (v := v).
              - eauto.
              - eauto.
              - intros; subst.
                match goal with
                  [H: forall _ _, Array _ _ = Array _ _ -> exists _, _ |- _] =>
                  specialize (H s ℓ1 eq_refl)
                end.
                super_destruct; subst.
                exists loc0.
                splits~.
                destruct (flowsto_dec ℓ ℓ_adv); eauto 3.
              - intros; subst.
                eauto.
              - eauto.
            }
            contradiction.
          }
          {
            rewrite_inj.
            apply_heap_lookup_extend_eq.
            rewrite_inj.
            assert_wf_type.
            invert_wf_type.
            exfalso; eauto 3.
          }
        * rewrite -> heap_lookup_extend_neq in * by solve[eauto].
          splits; eauto 2.
    - unfolds.
      intros.
      destruct (decide (x0 = x)); subst.
      + rewrite_inj.
        rewrite -> extend_memory_lookup_eq in *.
        rewrite_inj.
        assert (exists loc, v1 = ValLoc loc) by eauto.
        super_destruct; subst.
        eauto.
      + rewrite -> extend_memory_lookup_neq in * by solve[eauto].
        rewrite_inj.
        destruct τ as [τ ε].
        destruct τ.
        * assert (exists n, v2 = ValNum n) by eauto.
          super_destruct; subst.
          eauto.
        * assert (exists loc, v2 = ValLoc loc) by eauto.
          super_destruct; subst.
          eauto.
    - unfolds.
      intros.
      unfold left, identity_bijection in * |-.
      rewrite_inj.
      destruct (decide (loc0 = loc2)); subst.
      + rewrite -> extend_stenv_lookup_eq in *.
        rewrite_inj.
        assert (exists ℓ μ, heap_lookup loc2 h = Some (ℓ, μ)) by eauto 2.
        super_destruct; congruence.
      + rewrite -> extend_stenv_lookup_neq in * by solve[eauto].
        destruct τ as [τ ε].
        assert (exists ℓ μ, heap_lookup loc2 h = Some (ℓ, μ)) by eauto 2.
        super_destruct; subst.
        rewrite_inj.
        eapply HeapValLowEq.
        * eauto.
        * rewrite -> heap_lookup_extend_neq by solve[eauto].
          eauto.
        * intros.
          splits*.
        * intros.
          rewrite_inj.
          destruct τ.
          {
            assert (exists n, v0 = ValNum n) by eauto.
            super_destruct; subst.
            eauto.
          }
          {
            assert (exists loc, v0 = ValLoc loc) by eauto.
            super_destruct; subst.
            eauto.
          }
    - unfolds.
      intros.
      unfold left, identity_bijection in * |-.
      rewrite_inj.
      splits; eauto 2.
    - intros.
      destruct (T_dec l0 l); subst.
      {
        assert_wf_type.
        invert_wf_type.
        assert (~ l ⊑ ℓ_adv) by eauto.
        contradiction.
      }
      {
        rewrite -> size_extend_heap_neq_level by solve[eauto].
        reflexivity.
      }
    - intros.
      unfold left, identity_bijection in *.
      rewrite_inj.
      destruct (decide (loc' = loc0)); subst.
      {
        congruence.
      }
      {
        rewrite -> length_of_extend_neq by solve[eauto].
        reflexivity.
      }
  Qed.

  Lemma state_low_eq_update_heap_high:
    forall Γ Σ m h loc0 v n σ ℓ ι ℓ_adv length,
      wf_tenv Γ m ->
      wf_stenv Σ h ->
      dangling_pointer_free m h ->
      lookup_in_bounds m h ->
      heap_level_bound Γ m h Σ ->
      consistent m h Γ Σ ->
      (σ = Int -> exists n, v = ValNum n) ->
      Σ loc0 = Some (SecType σ (ℓ, ι)) ->
      ~ ℓ ⊑ ℓ_adv ->
      length_of loc0 h = Some length ->
      0 <= n ->
      n < length ->
      reach m h loc0 ->
      (forall τ ℓ', σ = Array τ ℓ' -> exists loc, v = ValLoc loc) ->
      state_low_eq ℓ_adv (identity_bijection loc) m h m (update_heap loc0 n v h) Γ Σ Σ.
  Proof.
    intros.
    eapply StateLowEq; eauto.
    - unfolds.
      intros.
      unfold left, identity_bijection in *.
      rewrite_inj.            
      splits.
      {
        intros.
        super_destruct; subst.
        splits~.
        destruct_low.
        {
          eapply low_update_with_high; eauto.
        }
        {
          destruct (decide (loc = loc0)); subst.
          - eapply LowHeapLevel; eauto.
          - eapply LowHeapLevel.
            rewrite -> heap_lookup_update_neq by solve[eauto].
            + eauto.
            + eauto.
        }
      }
      {
        intros.
        super_destruct; subst.
        splits~.
        eapply low_update_implies_low_if.
        - eauto.
        - eauto.
        - intros; subst.
          contradiction.
      }
    - unfolds.
      intros.
      unfolds.
      intros.
      unfold left, identity_bijection in * |-.
      rewrite_inj.
      splits.
      {
        intros.
        super_destruct; subst.
        splits~.
        - destruct (decide (l2 = loc0)); subst.
          + eauto.
          + rewrite -> heap_lookup_update_neq by solve[eauto].
            eauto.
        - eapply low_update_with_high; eauto.
      }
      {
        intros.
        super_destruct; subst.
        destruct (decide (l2 = loc0)); subst.
        - assert (exists ν0, heap_lookup loc0 h = Some (ℓ0, ν0) /\ ν = update_lookup ν0 n v) by eauto 2.
          super_destruct; subst.
          splits.
          + eauto.
          + eapply low_update_implies_low_if.
            * eauto.
            * eauto.
            * intros; subst.
              contradiction.
        - rewrite -> heap_lookup_update_neq in * by solve[eauto].
          splits.
          + eauto.
          + eapply low_update_implies_low_if.
            * eauto.
            * eauto.
            * intros; subst.
              contradiction.
      }
    - unfolds.
      intros.
      rewrite_inj.
      destruct τ as [τ ε].
      destruct τ.
      {
        assert (exists n, v2 = ValNum n) by eauto.
        super_destruct; subst.
        eauto.
      }
      {
        assert (exists loc, v2 = ValLoc loc) by eauto.
        super_destruct; subst.
        eauto.
      }
    - unfolds.
      intros.
      unfold left, identity_bijection in * |-.
      rewrite_inj.
      assert (exists ℓ μ, heap_lookup loc2 h = Some (ℓ, μ)) by eauto 2.
      super_destruct; subst.
      assert (exists μ, heap_lookup loc2 (update_heap loc0 n v h) = Some (ℓ0, μ)).
      {
        destruct (decide (loc2 = loc0)); subst.
        - eauto.
        - rewrite -> heap_lookup_update_neq by solve[eauto].
          eauto.
      }
      super_destruct; subst.
      destruct (decide (loc2 = loc0)); subst.
      {              
        assert (exists ν0, heap_lookup loc0 h = Some (ℓ0, ν0) /\ μ0 = update_lookup ν0 n v) by eauto 2.
        super_destruct; subst.
        rewrite_inj.
        eapply HeapValLowEq; eauto.
        - intros.
          splits.
          + intros.
            destruct (decide (n = n0)); subst.
            * eauto.
            * rewrite -> lookup_update_neq by solve[eauto].
              eauto.
          + intros.
            super_destruct; subst.
            destruct (decide (n = n0)); subst.
            * unfold lookup_in_bounds in *.
              rewrite -> lookup_update_eq in *.
              eauto.
            * rewrite -> lookup_update_neq in * by solve[eauto].
              eauto.
        - intros.
          destruct (decide (n = n0)); subst.
          + rewrite -> lookup_update_eq in *.
            rewrite_inj.
            destruct σ.
            * assert (exists n, u = ValNum n) by eauto.
              assert (exists n, v0 = ValNum n) by eauto.
              super_destruct; subst.
              eauto.
            * assert (exists loc, u = ValLoc loc) by eauto.
              assert (exists loc, v0 = ValLoc loc) by eauto.
              super_destruct; subst.
              eauto.
          + rewrite -> lookup_update_neq in * by solve[eauto].
            rewrite_inj.
            destruct σ.
            * assert (exists n, v0 = ValNum n) by eauto.
              super_destruct; subst.
              eauto.
            * assert (exists loc, v0 = ValLoc loc) by eauto.
              super_destruct; subst.
              eauto.
      }
      {
        rewrite -> heap_lookup_update_neq in * by solve[eauto].
        rewrite_inj.
        destruct τ.
        eapply HeapValLowEq.
        - eauto.
        - rewrite -> heap_lookup_update_neq by solve[eauto].
          eauto.
        - intros; splits*.
        - intros.
          rewrite_inj.
          destruct t.
          + assert (exists n, v0 = ValNum n) by eauto.
            super_destruct; subst.
            eauto.
          + assert (exists loc, v0 = ValLoc loc) by eauto.
            super_destruct; subst.
            eauto.
      }
    - unfolds.
      intros.
      unfold left, identity_bijection in * |-.
      rewrite_inj.
      splits; intros.
      {
        eapply low_reach_update_heap_with_high; eauto.
      }
      {
        intros.
        eapply low_reach_update_implies_low_reach_if; eauto 3.
        intros.
        contradiction.
      }
    - intros.
      rewrite -> size_update_heap.
      reflexivity.
    - intros.
      rewrite -> length_of_update.
      unfold left, identity_bijection in *.
      rewrite_inj.
      reflexivity.
  Qed.

  Lemma low_eq_stenv_extend:
    forall ℓ_adv φ ψ m1 m2 h1 h2 Σ1 Σ2 loc1 loc2 H1 H2 Γ n1 n2 v1 v2 τ ℓ_p ℓ ι x ℓ' ι' H3 H4 H5 H6,
      Γ x = Some (SecType (Array (SecType τ (ℓ, ι)) ℓ_p) (ℓ', ι')) ->
      state_low_eq ℓ_adv φ m1 h1 m2 h2 Γ Σ1 Σ2 ->
      dangling_pointer_free m1 h1 ->
      dangling_pointer_free m2 h2 ->
      wf_tenv Γ m1 ->
      wf_tenv Γ m2 ->
      wf_stenv Σ1 h1 ->
      wf_stenv Σ2 h2 ->
      wf_bijection ℓ_adv φ Γ Σ1 m1 h1 ->
      wf_bijection ℓ_adv (inverse φ) Γ Σ2 m2 h2 ->
      (τ = Int -> exists n, v1 = ValNum n) ->
      (τ = Int -> exists n, v2 = ValNum n) ->
      (ℓ ⊑ ℓ_adv -> onvals (left φ) v1 = Some v2) ->
      (forall (s : sectype) (ℓ0 : level_proj1),
          τ = Array s ℓ0 -> exists loc', v1 = ValLoc loc'
                                   /\ (ℓ ⊑ ℓ_adv -> low_reach ℓ_adv Γ Σ1 m1 h1 loc') /\
                                   (~ ℓ ⊑ ℓ_adv -> reach m1 h1 loc')) ->
      (forall (s : sectype) (ℓ0 : level_proj1),
          τ = Array s ℓ0 -> exists loc', v2 = ValLoc loc'
                                   /\ (ℓ ⊑ ℓ_adv -> low_reach ℓ_adv Γ Σ2 m2 h2 loc')
                                   /\ (~ ℓ ⊑ ℓ_adv -> reach m2 h2 loc')) ->
      filtered
        (low ℓ_adv Γ (extend_stenv loc1 (SecType τ (ℓ, ι)) Σ1)
             (extend_memory x (ValLoc loc1) m1)
             (h1 [loc1 → (n1 × v1, ℓ_p), H3, H4])) φ ψ ->
      low_eq_stenv ℓ_adv
                   (extend_bijection ψ loc1 loc2 H1 H2)
                   (extend_memory x (ValLoc loc1) m1)
                   (extend_memory x (ValLoc loc2) m2)
                   (h1 [loc1 → (n1 × v1, ℓ_p), H3, H4])
                   (h2 [loc2 → (n2 × v2, ℓ_p), H5, H6])
                   Γ
                   (extend_stenv loc1 (SecType τ (ℓ, ι)) Σ1)
                   (extend_stenv loc2 (SecType τ (ℓ, ι)) Σ2).
  Proof.
    intros.
    unfolds.
    intros.
    split.
    - intro.
      super_destruct.
      destruct (decide (loc1 = loc0)); subst.
      + rewrite -> extend_stenv_lookup_eq in *.
        rewrite_inj.
        _rewrite -> left_extend_bijection_eq in *.
        rewrite_inj.
        rewrite -> extend_stenv_lookup_eq.
        splits~.
        destruct_low.
        * eapply LowReachable.
          assert (ι' = ∘).
          {
            assert_wf_type.
            invert_wf_type.
            reflexivity.
          }
          subst.
          assert (ℓ' ⊑ ℓ_adv).
          {
            eapply new_low_reach_implies_flowsto_low with (h := h1) (v := v1); eauto.
            intros; subst.
            match goal with
              [H1: forall _ _, _ = _ -> exists _, v1 = _ /\ _,
                 H2: Γ ?x = Some (SecType (Array (SecType (Array ?s ?ℓ) _) _) _) |- _] =>
              specialize (H1 s ℓ eq_refl)
            end.
            super_destruct; subst.
            exists loc'.
            super_destruct; subst.
            splits~.
            destruct (flowsto_dec ℓ ℓ_adv).
            - eauto 3.
            - eauto.
          }
          eauto.
        * apply_heap_lookup_extend_eq.
          rewrite_inj.
          remember_simple (heap_lookup_extend_eq loc3 ℓ_p n2 v2 h2 H22 H6).
          super_destruct; subst.
          rewrite_inj.
          eauto 2.
      + _rewrite -> left_extend_bijection_neq in * by solve[eauto].
        assert (loc2 <> loc3).
        {
          intro; subst.
          assert (left φ loc0 = Some loc3).
          {
            eapply filtered_bijection_is_subset; eauto.
          }
          assert (right ψ loc3 = Some loc0) by (destruct ψ; eauto).
          congruence.
        }
        rewrite -> extend_stenv_lookup_neq in * by solve[eauto].
        splits~.
        * destruct_low.
          {
            assert (low_reach ℓ_adv Γ Σ1 m1 h1 loc).
            {
              eapply low_reach_extend_implies_low_reach_if with (σ := τ) (v := v1) (ℓ := ℓ); eauto.
              intros; subst.
              match goal with
                [H1: forall _ _, _ = _ -> exists _, v1 = _ /\ _,
                   H2: Γ ?x = Some (SecType (Array (SecType (Array ?s ?ℓ) _) _) _) |- _] =>
                specialize (H1 s ℓ eq_refl)
              end.
              super_destruct; subst.
              exists loc'.
              splits~.
            }
            invert_state_low_eq.
            eapply H26; eauto.
          }
          {
            rewrite -> heap_lookup_extend_neq in * by solve[eauto].
            invert_state_low_eq.
            eapply H26; eauto.
          }
        * destruct_low.
          {
            eapply LowReachable.
            assert (ι' = ∘).
            {
              assert_wf_type.
              invert_wf_type.
              reflexivity.
            }
            subst.
            eapply low_reach_in_extended_memory_and_heap with (φ := φ); eauto.
          }
          {
            rewrite -> heap_lookup_extend_neq in * by solve[eauto].
            assert ((exists ν, heap_lookup loc3 h2 = Some (ℓ0, ν)) /\ low ℓ_adv Γ Σ2 m2 h2 loc3).
            {
              invert_state_low_eq.
              eapply H28; eauto.
            }
            super_destruct; subst.
            eapply LowHeapLevel.
            - rewrite -> heap_lookup_extend_neq by solve[eauto].
              eauto.
            - eauto.
          }
    - intro.
      super_destruct.
      destruct (decide (loc1 = loc0)); subst.
      + rewrite -> extend_stenv_lookup_eq in *.
        rewrite_inj.
        _rewrite -> left_extend_bijection_eq in *.
        rewrite_inj.
        rewrite -> extend_stenv_lookup_eq in *.
        rewrite_inj.
        splits~.
        destruct_low.
        * eapply LowReachable.
          assert (ι' = ∘).
          {
            assert_wf_type.
            invert_wf_type.
            reflexivity.
          }
          subst.
          assert (ℓ' ⊑ ℓ_adv).
          {
            eapply new_low_reach_implies_flowsto_low with (h := h2) (v := v2); eauto.
            intros; subst.
            match goal with
              [H1: forall _ _, _ = _ -> exists _, v2 = _ /\ _,
                 H2: Γ ?x = Some (SecType (Array (SecType (Array ?s ?ℓ) _) ℓ_p) _) |- _] =>
              specialize (H1 s ℓ eq_refl)
            end.
            super_destruct; subst.
            exists loc'.
            splits~.
            destruct (flowsto_dec ℓ ℓ_adv).
            - eauto 3.
            - eauto. 
          }
          eauto.
        * apply_heap_lookup_extend_eq.
          rewrite_inj.
          remember_simple (heap_lookup_extend_eq loc0 ℓ_p n1 v1 h1 H3 H4).
          super_destruct; subst.
          rewrite_inj.
          eauto 2.
      + _rewrite -> left_extend_bijection_neq in * by solve[eauto].
        assert (left φ loc0 = Some loc3) by eauto 2.
        assert (loc2 <> loc3).
        {
          intro; subst.          
          assert (right ψ loc3 = Some loc0) by (destruct ψ; eauto).
          congruence.
        }
        rewrite -> extend_stenv_lookup_neq in * by solve[eauto].
        splits~.
        * destruct_low.
          {
            assert (low_reach ℓ_adv Γ Σ2 m2 h2 loc).
            {
              eapply low_reach_extend_implies_low_reach_if with (σ := τ) (v := v2) (ℓ := ℓ); eauto.
              intros; subst.
              match goal with
                [H1: forall _ _, _ = _ -> exists _, v2 = _ /\ _,
                   H2: Γ ?x = Some (SecType (Array (SecType (Array ?s ?ℓ) _) ℓ_p) _) |- _] =>
                specialize (H1 s ℓ eq_refl)
              end.
              super_destruct'; subst.
              exists loc'.
              splits~.
            }
            invert_state_low_eq.
            eapply H27; eauto.
          }
          {
            rewrite -> heap_lookup_extend_neq in * by solve[eauto].
            invert_state_low_eq.
            eapply H27; eauto.
          }
        * destruct_low.
          {
            eapply LowReachable.
            assert (ι' = ∘).
            {
              assert_wf_type.
              invert_wf_type.
              reflexivity.
            }
            subst.
            eapply low_reach_in_extended_memory_and_heap with (φ := inverse φ); eauto.
            - destruct φ; eauto.
            - destruct φ; eauto.
          }
          {
            rewrite -> heap_lookup_extend_neq in * by solve[eauto].
            unfold low_heap_domain_eq in *.
            assert ((exists ν, heap_lookup loc0 h1 = Some (ℓ0, ν)) /\ low ℓ_adv Γ Σ1 m1 h1 loc0).
            {
              invert_state_low_eq.
              eapply H29; eauto.
            }
            super_destruct; subst.
            eapply LowHeapLevel.
            - rewrite -> heap_lookup_extend_neq by solve[eauto].
              eauto.
            - eauto.
          }
  Qed.
  
  Lemma low_heap_domain_eq_extend:
    forall ℓ_adv φ ψ x n1 n2 v1 v2 ℓ m1 m2 h1 h2 Γ Σ1 Σ2 ι ι' ℓ_p τ ℓ' loc1 loc2 H1 H2 H3 H4 H5 H6,
      state_low_eq ℓ_adv φ m1 h1 m2 h2 Γ Σ1 Σ2 ->
      Γ x = Some (SecType (Array (SecType τ (ℓ, ι)) ℓ_p) (ℓ', ι')) ->
      dangling_pointer_free m1 h1 ->
      dangling_pointer_free m2 h2 ->
      wf_tenv Γ m1 ->
      wf_tenv Γ m2 ->
      wf_stenv Σ1 h1 ->
      wf_stenv Σ2 h2 ->
      wf_bijection ℓ_adv φ Γ Σ1 m1 h1 ->
      wf_bijection ℓ_adv (inverse φ) Γ Σ2 m2 h2 ->
      (τ = Int -> exists n, v1 = ValNum n) ->
      (τ = Int -> exists n, v2 = ValNum n) ->
      (ℓ ⊑ ℓ_adv -> onvals (left φ) v1 = Some v2) ->
      (forall (s : sectype) (ℓ0 : level_proj1),
          τ = Array s ℓ0 -> exists loc', v1 = ValLoc loc'
                                   /\ (ℓ ⊑ ℓ_adv -> low_reach ℓ_adv Γ Σ1 m1 h1 loc') /\
                                   (~ ℓ ⊑ ℓ_adv -> reach m1 h1 loc')) ->
      (forall (s : sectype) (ℓ0 : level_proj1),
          τ = Array s ℓ0 -> exists loc', v2 = ValLoc loc'
                                   /\ (ℓ ⊑ ℓ_adv -> low_reach ℓ_adv Γ Σ2 m2 h2 loc')
                                   /\ (~ ℓ ⊑ ℓ_adv -> reach m2 h2 loc')) ->
      filtered
        (low ℓ_adv Γ (extend_stenv loc1 (SecType τ (ℓ, ι)) Σ1)
             (extend_memory x (ValLoc loc1) m1)
             (h1 [loc1 → (n1 × v1, ℓ_p), H3, H4])) φ ψ ->
      low_heap_domain_eq
        ℓ_adv
        (extend_bijection ψ loc1 loc2 H1 H2)
        (extend_memory x (ValLoc loc1) m1)
        (extend_memory x (ValLoc loc2) m2)
        (h1 [loc1 → (n1 × v1, ℓ_p), H3, H4]) (h2 [loc2 → (n2 × v2, ℓ_p), H5, H6])
        Γ
        (extend_stenv loc1 (SecType τ (ℓ, ι)) Σ1) (extend_stenv loc2 (SecType τ (ℓ, ι)) Σ2).
  Proof.
    intros.
    unfolds.
    intros.
    assert (ι' = ∘).
    {
      assert_wf_type.
      invert_wf_type.
      reflexivity.
    }
    subst.
    splits.
    - intros.
      super_destruct; subst.
      destruct (decide (l1 = loc1)); subst.
      + _rewrite -> left_extend_bijection_eq in *.
        rewrite_inj.
        apply_heap_lookup_extend_eq.
        rewrite_inj.
        remember_simple (heap_lookup_extend_eq l2 ℓ_p n2 v2 h2 H5 H6).
        super_destruct; subst.
        splits~; eauto 2.
        destruct_low.
        * assert (ℓ' ⊑ ℓ_adv).
          {
            eapply new_low_reach_implies_flowsto_low with (v := v1) (m := m1) (h := h1); eauto 2.
            intros; subst.
            match goal with
              [H1: forall _ _, _ = _ -> exists _, v1 = _ /\ _,
                 H2: Γ ?x = Some (SecType (Array (SecType (Array ?s ?ℓ) _) ℓ_p) _) |- _] =>
              specialize (H1 s ℓ eq_refl)
            end.
            super_destruct; subst.
            exists loc'.
            splits~.
            destruct (flowsto_dec ℓ ℓ_adv).
            - eauto 3.
            - eauto. 
          }
          eapply LowReachable.
          eauto 2.
        * rewrite_inj.
          eauto 2.
      + _rewrite -> left_extend_bijection_neq in * by solve[eauto].
        assert (left φ l1 = Some l2) by eauto 2.
        assert (l2 <> loc2).
        {
          intro; subst.
          assert (right ψ loc2 = Some l1) by (destruct ψ; eauto).
          congruence.
        }
        rewrite -> heap_lookup_extend_neq in * by solve[eauto].
        destruct_low.
        * assert (low_reach ℓ_adv Γ Σ1 m1 h1 loc).
          {
            eapply low_reach_extend_implies_low_reach_if with (v := v1); eauto.
            intros; subst.
            match goal with
              [H1: forall _ _, _ = _ -> exists _, v1 = _ /\ _,
                 H2: Γ ?x = Some (SecType (Array (SecType (Array ?s ?ℓ) _) ℓ_p) _) |- _] =>
              specialize (H1 s ℓ eq_refl)
            end.
            super_destruct; subst.
            exists loc'.
            splits~.
          }
          assert (low ℓ_adv Γ Σ1 m1 h1 loc) by eauto.
          assert ((exists ν, heap_lookup l2 h2 = Some (ℓ0, ν)) /\ low ℓ_adv Γ Σ2 m2 h2 l2).
          {
            invert_state_low_eq.
            eapply H30; eauto.
          }
          super_destruct; subst.
          splits~; eauto 2.
          eapply LowReachable.
          eapply low_reach_in_extended_memory_and_heap; eauto.
        * rewrite -> heap_lookup_extend_neq in * by solve[eauto].
          rewrite_inj.
          assert ((exists ν, heap_lookup l2 h2 = Some (ℓ1, ν)) /\ low ℓ_adv Γ Σ2 m2 h2 l2).
          {
            invert_state_low_eq.
            eapply H28; eauto.
          }
          super_destruct; subst.
          splits~; eauto 2.
          eapply LowHeapLevel.
          { rewrite -> heap_lookup_extend_neq by solve[eauto].
            eauto. }
          { eauto. }
    - intros.
      super_destruct; subst.
      assert (right (extend_bijection ψ loc1 loc2 H1 H2) l2 = Some l1).
      {
        destruct ((extend_bijection ψ loc1 loc2 H1 H2)); eauto.
      }
      destruct (decide (l2 = loc2)); subst.
      + _rewrite -> right_extend_bijection_eq in *.
        rewrite_inj.
        apply_heap_lookup_extend_eq.
        rewrite_inj.
        remember_simple (heap_lookup_extend_eq l1 ℓ_p n1 v1 h1 H3 H4).
        super_destruct; subst.
        splits~; eauto 2.
        destruct_low.
        * assert (ℓ' ⊑ ℓ_adv).
          {
            eapply new_low_reach_implies_flowsto_low with (v := v2) (m := m2) (h := h2); eauto 2.
            intros; subst.
            match goal with
              [H1: forall _ _, _ = _ -> exists _, v2 = _ /\ _,
                 H2: Γ ?x = Some (SecType (Array (SecType (Array ?s ?ℓ) _) ℓ_p) _) |- _] =>
              specialize (H1 s ℓ eq_refl)
            end.
            super_destruct; subst.
            exists loc'.
            splits~.
            destruct (flowsto_dec ℓ ℓ_adv).
            - eauto 3.
            - eauto.
          }
          eapply LowReachable.
          eauto 2.
        * rewrite_inj.
          eauto 2.
      + _rewrite -> right_extend_bijection_neq in * by solve[eauto].
        assert (l1 <> loc1).
        {
          intro; subst.
          _rewrite -> left_extend_bijection_eq in *.
          congruence.
        }
        rewrite -> heap_lookup_extend_neq in * by solve[eauto].
        assert (left ψ l1 = Some l2) by (destruct ψ; eauto 2).
        assert (left φ l1 = Some l2) by eauto 2.
        destruct_low.
        * assert (low_reach ℓ_adv Γ Σ2 m2 h2 loc).
          {
            eapply low_reach_extend_implies_low_reach_if with (v := v2); eauto.
            intros; subst.
            match goal with
              [H1: forall _ _, _ = _ -> exists _, v2 = _ /\ _,
                 H2: Γ ?x = Some (SecType (Array (SecType (Array ?s ?ℓ) _) ℓ_p) _) |- _] =>
              specialize (H1 s ℓ eq_refl)
            end.
            super_destruct; subst.
            exists loc'.
            splits~.
          }
          assert (low ℓ_adv Γ Σ2 m2 h2 loc) by eauto.
          assert ((exists ν, heap_lookup l1 h1 = Some (ℓ0, ν)) /\ low ℓ_adv Γ Σ1 m1 h1 l1).
          {
            invert_state_low_eq.            
            eapply H32; eauto.
          }
          super_destruct; subst.
          splits~; eauto 2.
          eapply LowReachable.
          eapply low_reach_in_extended_memory_and_heap; destruct φ; eauto.
        * rewrite -> heap_lookup_extend_neq in * by solve[eauto].
          rewrite_inj.
          assert ((exists ν, heap_lookup l1 h1 = Some (ℓ1, ν)) /\ low ℓ_adv Γ Σ1 m1 h1 l1).
          {
            invert_state_low_eq.
            eapply H30; destruct φ; eauto.
          }
          super_destruct; subst.
          splits~; eauto 2.
          eapply LowHeapLevel.
          { rewrite -> heap_lookup_extend_neq by solve[eauto].
            eauto. }
          { eauto. }
  Qed.
  Hint Resolve low_heap_domain_eq_extend.

  Lemma state_low_eq_extend_EVERYTHING:
    forall ℓ_adv ε_x φ ψ m1 h1 m2 h2 Γ Σ1 Σ2 l1 l2 v1 v2 n1 n2 x τ ℓ_τ ℓ_p ι H1 H2 H3 H4 H5 H6,
      state_low_eq ℓ_adv φ m1 h1 m2 h2 Γ Σ1 Σ2 ->
      dangling_pointer_free m1 h1 ->
      dangling_pointer_free m2 h2 ->
      dangling_pointer_free
        (m1 [x → ValLoc l1])
        (h1 [l1 → (n1 × v1, ℓ_p), H3, H4]) ->
      heap_level_bound Γ m1 h1 Σ1 ->
      heap_level_bound Γ m2 h2 Σ2 ->
      heap_level_bound
        Γ
        (extend_memory x (ValLoc l1) m1)
        (h1 [l1 → (n1 × v1, ℓ_p), H3, H4])
        (extend_stenv l1 (SecType τ (ℓ_τ, ι)) Σ1) ->
      wf_tenv Γ m1 ->
      wf_tenv Γ m2 ->
      wf_tenv Γ (extend_memory x (ValLoc l1) m1) ->
      wf_stenv Σ1 h1 ->
      wf_stenv Σ2 h2 ->
      wf_stenv (extend_stenv l1 (SecType τ (ℓ_τ, ι)) Σ1) (h1 [l1 → (n1 × v1, ℓ_p), H3, H4]) ->
      wf_bijection ℓ_adv φ Γ Σ1 m1 h1 ->
      wf_bijection ℓ_adv (inverse φ) Γ Σ2 m2 h2 ->
      Γ x = Some (SecType (Array (SecType τ (ℓ_τ, ι)) ℓ_p) ε_x) ->
      (τ = Int -> exists n_v, v1 = ValNum n_v) ->
      (forall s ℓ, τ = Array s ℓ -> exists l_v, v1 = ValLoc l_v
                                     /\ (ℓ_τ ⊑ ℓ_adv -> low_reach ℓ_adv Γ Σ1 m1 h1 l_v)
                                     /\ (~ ℓ_τ ⊑ ℓ_adv -> reach m1 h1 l_v)) ->
      (τ = Int -> exists n_v, v2 = ValNum n_v) ->
      (forall s ℓ, τ = Array s ℓ -> exists l_v, v2 = ValLoc l_v
                                     /\ (ℓ_τ ⊑ ℓ_adv -> low_reach ℓ_adv Γ Σ2 m2 h2 l_v)
                                     /\ (~ ℓ_τ ⊑ ℓ_adv -> reach m2 h2 l_v)) ->
      (ℓ_τ ⊑ ℓ_adv -> onvals (left φ) v1 = Some v2) ->
      (ℓ_p ⊑ ℓ_adv -> n1 = n2) ->
      filtered
        (low ℓ_adv Γ (extend_stenv l1 (SecType τ (ℓ_τ, ι)) Σ1)
             (m1 [x → ValLoc l1])
             (h1 [l1 → (n1 × v1, ℓ_p), H3, H4])) φ ψ ->
        state_low_eq ℓ_adv
                   (extend_bijection ψ l1 l2 H1 H2)
                   (extend_memory x (ValLoc l1) m1)
                   (h1 [l1 → (n1 × v1, ℓ_p), H3, H4])
                   (extend_memory x (ValLoc l2) m2)
                   (h2 [l2 → (n2 × v2, ℓ_p), H5, H6]) Γ
                   (extend_stenv l1 (SecType τ (ℓ_τ, ι)) Σ1)
                   (extend_stenv l2 (SecType τ (ℓ_τ, ι)) Σ2).
  Proof.
    intros.
    apply StateLowEq; eauto 2.
    - destruct ε_x as [ℓ_x ι_x].
      eapply low_eq_stenv_extend; eauto 3.
    - invert_state_low_eq.
      eapply low_domain_eq_extend; eauto 3.
    - destruct ε_x as [ℓ_x ι_x].
      eapply low_heap_domain_eq_extend; eauto 3.
    - unfolds.
      intros.
      destruct (decide (x = x0)); subst.
      + rewrite -> extend_memory_lookup_eq in *.
        rewrite_inj.
        destruct ε_x as [ℓ_x ι_x].
        destruct (flowsto_dec ℓ_x ℓ_adv); eauto.
      + rewrite -> extend_memory_lookup_neq in * by solve[eauto].
        invert_state_low_eq.
        eapply val_low_eq_extend; eauto.
        assert (val_low_eq ℓ_adv τ0 v0 v3 φ) by eauto 2.
        invert_val_low_eq; eauto 3.
        assert_wf_type.
        invert_wf_type.
        assert (low ℓ_adv Γ (extend_stenv l1 (SecType τ (ℓ_τ, ι)) Σ1)
             (m1 [x → ValLoc l1])
             (h1 [l1 → (n1 × v1, ℓ_p), H3, H4]) l0).
        {
          eapply LowReachable.          
          eapply LowReachMem; eauto 3.
          rewrite -> extend_memory_lookup_neq by solve[eauto].
          eauto.
        }
        eauto 3.
    - unfolds.
      intros.
      destruct (decide (l1 = loc1)); subst.
      + remember_simple (heap_lookup_extend_eq loc1 ℓ_p n1 v1 h1 H3 H4).
        super_destruct; subst.
        rewrite -> extend_stenv_lookup_eq in *.
        rewrite_inj.
        _rewrite -> left_extend_bijection_eq in *.
        rewrite_inj.
        remember_simple (heap_lookup_extend_eq loc2 ℓ_p n2 v2 h2 H5 H6).
        super_destruct; subst.
        rewrite -> extend_stenv_lookup_eq in *.
        rewrite_inj.
        eapply HeapValLowEq; eauto.
        * intros; splits*.
        * intros.
          destruct τ.
          { repeat match goal with
                     [H: ?X = ?X -> _ |- _ ] =>
                     specialize (H eq_refl)
                   end.
            destruct_exists.
            repeat specialize_gen.
            rewrite_inj.
            unfold onvals in *.
            rewrite_inj.          
            destruct (flowsto_dec ℓ_τ ℓ_adv); eauto.
            assert (Some (ValNum n_v0) = Some (ValNum n_v)) by eauto.
            rewrite_inj.
            eauto.
          }
          {
            repeat match goal with
                     [H: forall _ _, _ = _ -> exists _, _ |- _] =>
                     specialize (H s l eq_refl)
                   end.
            super_destruct; subst.
            assert (u = ValLoc l_v0) by congruence.
            assert (v = ValLoc l_v) by congruence.
            subst.
            destruct (flowsto_dec ℓ_τ ℓ_adv); eauto 2.
            assert (onvals (left φ) (ValLoc l_v0) = Some (ValLoc l_v)) by eauto.
            eapply ValLocLowEqL.
            - eauto.
            - destruct (decide (loc1 = l_v0)); subst.
              + assert (left φ l_v0 = Some l_v).
                {
                  unfold onvals in *.
                  destruct (left φ l_v0) eqn:H_l_v0; congruence.
                }
                assert (low_reach ℓ_adv Γ Σ1 m1 h1 l_v0) by eauto 2.
                assert (exists ℓ μ, heap_lookup l_v0 h1 = Some (ℓ, μ)) by eauto 3.
                super_destruct; subst.
                congruence.
              + rewrite -> left_extend_bijection_neq by solve[eauto].
                
                assert (left φ l_v0 = Some l_v).
                {
                  unfold onvals in *.
                  destruct (left φ l_v0) eqn:H_lv0; congruence.
                }
                assert (low ℓ_adv Γ
                            (extend_stenv loc1 (SecType (Array s l) (ℓ_τ, ι)) Σ1)
                            (m1 [x → ValLoc loc1])
                            (extend_heap (ValLoc l_v0) loc1 ℓ_p n1 h1 H3 H4) l_v0).
                {
                  assert (low_reach ℓ_adv Γ Σ1 m1 h1 l_v0) by eauto 2.
                  eapply LowReachable.
                  destruct ε_x as [ℓ_x ι_x].
                  assert_wf_type.
                  invert_wf_type.
                  invert_wf_type.
                  destruct (flowsto_dec ℓ_x ℓ_adv).
                  - eapply LowReachHeap; eauto 2.
                  - eapply low_reach_extend_memory_heap_with_high; eauto 2.
                }
                eauto 2.
          }
      + _rewrite -> left_extend_bijection_neq in * by solve[eauto].
        destruct (decide (loc2 = l2)); subst.
        { assert (left φ loc1 = Some l2) by eauto 2.
          assert (right ψ l2 = Some loc1) by (destruct ψ; eauto).
          congruence.
        }
        rewrite -> extend_stenv_lookup_neq in * by solve[eauto].

        assert (low ℓ_adv Γ Σ2 m2 h2 loc2).
        {
          eapply low_extend_implies_low_if.
          - eauto.
          - intros.
            subst.
            match goal with
              [H1: forall _ _, _ = _ -> exists _, v2 = _ /\ _,
                 H2: Γ ?x = Some (SecType (Array (SecType (Array ?s ?ℓ) _) ℓ_p) _) |- _] =>
              specialize (H1 s ℓ eq_refl)
            end.
            super_destruct; subst.
            exists l_v.
            splits~.
          - eauto.
          - eauto.
        }
        
        assert (heapval_low_eq ℓ_adv τ0 loc1 loc2 m1 m2 h1 h2 φ).
        {
          destruct τ0.
          invert_state_low_eq.
          eauto.
        }
        invert_heapval_low_eq.
        assert (heap_lookup loc1 (extend_heap v1 l1 ℓ_p n1 h1 H3 H4) = Some (ℓ, μ)).
        {
          rewrite -> heap_lookup_extend_neq by solve[eauto].
          eauto.
        }
        assert (heap_lookup loc2 (extend_heap v2 l2 ℓ_p n2 h2 H5 H6) = Some (ℓ, ν)).
        {
          rewrite -> heap_lookup_extend_neq by solve[eauto].
          eauto.
        }
        eapply HeapValLowEq; eauto 3.
        intros.
        assert (reach m1 h1 loc1).
        {
          eapply reach_extend_implies_reach_if; eauto 2.
          intros; subst.
          destruct τ.
          - assert (exists n_v, ValLoc loc' = ValNum n_v) by eauto.
            super_destruct; discriminate.
          - specialize (H22 s l eq_refl).
            super_destruct; subst.
            injects.
            destruct (flowsto_dec ℓ_τ ℓ_adv); eauto 3.
        }
        assert (reach m2 h2 loc2).
        {
          eapply reach_extend_implies_reach_if; eauto 2.
          intros; subst.
          destruct τ.
          - assert (exists n_v, ValLoc loc' = ValNum n_v) by eauto.
            super_destruct; discriminate.
          - specialize (H24 s l eq_refl).
            super_destruct; subst.
            injects.
            destruct (flowsto_dec ℓ_τ ℓ_adv); eauto 3.
        }
        assert (val_low_eq ℓ_adv (SecType τ1 ℓ_τ0) u v φ) by eauto 2.
        eapply val_low_eq_extend; eauto.
        invert_val_low_eq; eauto 3.
        assert_wf_type.
        invert_wf_type.
        assert (low ℓ_adv Γ (extend_stenv l1 (SecType τ (ℓ_τ, ι)) Σ1)
                    (m1 [x → ValLoc l1])
                    (extend_heap v1 l1 ℓ_p n1 h1 H3 H4) l0).
        {
          match goal with
            [H: low _ _ _ _ _ loc1 |- _] =>
            dependent destruction H
          end.
          - eapply LowReachable.
            eapply LowReachHeap.
            + eauto.
            + rewrite -> extend_stenv_lookup_neq by solve[eauto].
              eauto.
            + rewrite -> heap_lookup_extend_neq by solve[eauto].
              eauto.
            + eauto.
            + eauto.
          - rewrite_inj.
            assert (low_reach ℓ_adv Γ (extend_stenv l1 (SecType τ (ℓ_τ, ι)) Σ1)
                              (m1 [x → ValLoc l1])
                              (extend_heap v1 l1 ℓ_p n1 h1 H3 H4) loc).
            {
              eapply low_reach_adequacy; eauto.
            }
            eapply LowReachable.
            eapply LowReachHeap with (l := ℓ1); eauto 3.
            rewrite -> extend_stenv_lookup_neq by solve[eauto].
            eauto.
        }
        eauto 3.
    - unfolds.
      intros.
      splits.
      + intros.
        destruct ε_x as [ℓ_x ι_x].
        assert (ι_x = ∘).
        {
          assert_wf_type.
          invert_wf_type.
          reflexivity.
        }
        subst.
        destruct (decide (loc = l1)); subst.
        * _rewrite -> left_extend_bijection_eq in *.
          rewrite_inj.
          assert (ℓ_x ⊑ ℓ_adv).
          {
            eapply new_low_reach_implies_flowsto_low with (v := v1) (m := m1) (h := h1); eauto 2.
            intros; subst.
            match goal with
              [H1: forall _ _, _ = _ -> exists _, v1 = _ /\ _,
                 H2: Γ ?x = Some (SecType (Array (SecType (Array ?s ?ℓ) _) ℓ_p) _) |- _] =>
              specialize (H1 s ℓ eq_refl)
            end.
            super_destruct; subst.
            exists l_v.
            splits~.
            destruct (flowsto_dec ℓ_τ ℓ_adv); eauto 3.
          }
          eauto.
        * _rewrite -> left_extend_bijection_neq in * by solve[eauto].
          eapply low_reach_in_extended_memory_and_heap; eauto.
      + intros.
        destruct ε_x as [ℓ_x ι_x].
        assert (ι_x = ∘).
        {
          assert_wf_type.
          invert_wf_type.
          reflexivity.
        }
        subst.
        destruct (decide (loc = l1)); subst.
        * _rewrite -> left_extend_bijection_eq in *.
          rewrite_inj.
          assert (ℓ_x ⊑ ℓ_adv).
          {
            eapply new_low_reach_implies_flowsto_low with (v := v2) (m := m2) (h := h2); eauto 2.
            intros; subst.
            match goal with
              [H1: forall _ _, _ = _ -> exists _, v2 = _ /\ _,
                 H2: Γ ?x = Some (SecType (Array (SecType (Array ?s ?ℓ) _) ℓ_p) _) |- _] =>
              specialize (H1 s ℓ eq_refl)
            end.
            super_destruct; subst.
            exists l_v.
            splits~.
            destruct (flowsto_dec ℓ_τ ℓ_adv); eauto 3.
          }
          eauto.
        * _rewrite -> left_extend_bijection_neq in * by solve[eauto].
          assert (left φ loc = Some loc') by eauto 2.
          eapply low_reach_in_extended_memory_and_heap; eauto.
          { destruct φ; eauto. }
          { destruct φ; eauto. }
    - intros.
      destruct (T_dec l ℓ_p); subst.
      + assert (n1 = n2) by eauto 2; subst.
        repeat rewrite -> size_extend_heap_eq_level by solve[eauto].
        invert_state_low_eq; eauto with arith.
      + repeat rewrite -> size_extend_heap_neq_level by solve[eauto].
        invert_state_low_eq; eauto.
    - intros.
      destruct (decide (loc = l1)); subst.
      + apply_heap_lookup_extend_eq.
        rewrite_inj.
        revert H30; intros.
        apply_heap_lookup_extend_eq.
        rewrite_inj.
        _rewrite -> left_extend_bijection_eq in *.
        rewrite_inj.
        do 2 rewrite -> length_of_extend_eq.
        eauto.
      + _rewrite -> left_extend_bijection_neq in * by solve[eauto].
        assert (left φ loc = Some loc') by eauto 2.
        assert (loc' <> l2).
        {
          intro; subst.
          assert (right ψ l2 = Some loc) by (destruct ψ; eauto).
          congruence.
        }
        rewrite -> heap_lookup_extend_neq in * by solve[eauto].
        repeat rewrite -> length_of_extend_neq by solve[eauto].
        invert_state_low_eq; eauto.
  Qed.
  
Lemma state_low_eq_extend_EVERYTHING_high:
  forall ℓ ℓ_x φ ψ m1 h1 m2 h2 Γ Σ1 Σ2 l1 l2 v1 v2 n1 n2 ℓ_p x ι τ ℓ_τ ι_τ H1 H2 H3 H4,
    state_low_eq ℓ φ m1 h1 m2 h2 Γ Σ1 Σ2 ->
    dangling_pointer_free m1 h1 ->
    dangling_pointer_free m2 h2 ->
    heap_level_bound Γ m1 h1 Σ1 ->
    heap_level_bound Γ m2 h2 Σ2 ->
    wf_bijection ℓ φ Γ Σ1 m1 h1 ->
    wf_bijection ℓ (inverse φ) Γ Σ2 m2 h2 ->
    wf_tenv Γ m1 ->
    wf_tenv Γ m2 ->
    wf_stenv Σ1 h1 ->
    wf_stenv Σ2 h2 ->
    Γ x = Some (SecType (Array (SecType τ (ℓ_τ, ι_τ)) ℓ_p) (ℓ_x, ι)) ->
    ~ ℓ_x ⊑ ℓ ->
    (τ = Int -> exists n_v, v1 = ValNum n_v) ->
    (forall s ℓ', τ = Array s ℓ' -> exists l_v, v1 = ValLoc l_v /\
                                     (ℓ_τ ⊑ ℓ -> low_reach ℓ Γ Σ1 m1 h1 l_v) /\
                                     (~ ℓ_τ ⊑ ℓ -> reach m1 h1 l_v)) ->
    (τ = Int -> exists n_v, v2 = ValNum n_v) ->
    (forall s ℓ', τ = Array s ℓ' -> exists l_v, v2 = ValLoc l_v /\
                                     (ℓ_τ ⊑ ℓ -> low_reach ℓ Γ Σ2 m2 h2 l_v) /\
                                     (~ ℓ_τ ⊑ ℓ -> reach m2 h2 l_v)) ->
    (ℓ_p ⊑ ℓ -> onvals (left φ) v1 = Some v2) ->
    filtered
      (low ℓ Γ (extend_stenv l1 (SecType τ (ℓ_τ, ι_τ)) Σ1)
           (extend_memory x (ValLoc l1) m1)
           (h1 [l1 → (n1 × v1, ℓ_p), H1, H2])) φ ψ ->
    state_low_eq ℓ
                 ψ
                 (extend_memory x (ValLoc l1) m1)
                 (h1 [l1 → (n1 × v1, ℓ_p), H1, H2])
                 (extend_memory x (ValLoc l2) m2)
                 (h2 [l2 → (n2 × v2, ℓ_p), H3, H4])
                 Γ
                 (extend_stenv l1 (SecType τ (ℓ_τ, ι_τ)) Σ1)
                 (extend_stenv l2 (SecType τ (ℓ_τ, ι_τ)) Σ2).
Proof.
  intros.
  assert (left φ l1 = None).
  {
    destruct (left φ l1) eqn:H_l1; try reflexivity.
    assert (exists ℓ μ, heap_lookup l1 h1 = Some (ℓ, μ)) by eauto 2.
    super_destruct; subst.
    congruence.
  }
  assert (right φ l2 = None).
  {
    destruct (right φ l2) eqn:H_l1; try reflexivity.
    assert (left (inverse φ) l2 = Some l) by (destruct φ; eauto).
    assert (exists ℓ μ, heap_lookup l2 h2 = Some (ℓ, μ)) by eauto 2.
    super_destruct; subst.
    congruence.
  }
  eapply StateLowEq; eauto 2.
  - invert_state_low_eq.
    eapply low_eq_stenv_extend_high; eauto.
    + destruct (right ψ l2) eqn:H_l2; try reflexivity.
      rename l into l2'.
      assert (left ψ l2' = Some l2) by (destruct ψ; eauto 2).
      assert (left φ l2' = Some l2) by eauto 2.
      assert (left (inverse φ) l2 = Some l2') by (destruct φ; eauto 2).
      assert (exists ℓ μ, heap_lookup l2 h2 = Some (ℓ, μ)) by eauto 2.
      super_destruct; subst.
      congruence.
    + intros; subst.
      do 2 match goal with
             [H: forall _ _, Array _ _ = Array _ _ -> exists _, _ = _ /\ _ |- _] =>
             specialize (H s ℓ' eq_refl); super_destruct; subst
           end.
      eauto.
    + intros; subst.
      do 2 match goal with
             [H: forall _ _, Array _ _ = Array _ _ -> exists _, _ = _ /\ _ |- _] =>
             specialize (H s ℓ' eq_refl); super_destruct; subst
           end.
      eauto.
  - invert_state_low_eq.
    eapply low_domain_eq_extend; eauto.
  - unfolds.
    intros.
    assert (ι = ∘).
    {
      assert_wf_type.
      invert_wf_type.
      reflexivity.
    }
    subst.
    assert (left φ l0 = Some l3) by eauto 2.
    splits.
    + intros.
      super_destruct; subst.
      assert (l0 <> l1).
      {
        intro; subst.        
        congruence.
      }
      assert (l2 <> l3).
      {
        intro; subst.
        assert (right φ l3 = Some l0) by (destruct φ; eauto).
        congruence.
      }
      rewrite -> heap_lookup_extend_neq in * by solve[eauto].
      assert (low ℓ Γ Σ1 m1 h1 l0) by eauto 3.
      assert ((exists ν, heap_lookup l3 h2 = Some (ℓ0, ν)) /\
              low ℓ Γ Σ2 m2 h2 l3).
      {
        invert_state_low_eq.
        match goal with
          [H: context[low_heap_domain_eq] |- _ ] =>
          solve[eapply H; eauto]
        end.
      }
      super_destruct; subst.
      splits~; eauto 2.
    + intros.
      super_destruct; subst.
      assert (l0 <> l1).
      {
        intro; subst.
        congruence.
      }
      assert (l2 <> l3).
      {
        intro; subst.
        assert (right φ l3 = Some l0) by (destruct φ; eauto).
        congruence.
      }
      rewrite -> heap_lookup_extend_neq in * by solve[eauto].
      assert (low ℓ Γ Σ2 m2 h2 l3) by eauto 3.
      assert ((exists ν, heap_lookup l0 h1 = Some (ℓ0, ν)) /\
              low ℓ Γ Σ1 m1 h1 l0).
      {
        invert_state_low_eq.
        match goal with
          [H: context[low_heap_domain_eq] |- _ ] =>
          solve[eapply H; eauto]
        end.
      }
      super_destruct; subst.
      splits~; eauto 2.
  - unfolds.
    intros.
    destruct (decide (x = x0)); subst.
    + rewrite -> extend_memory_lookup_eq in *.
      rewrite_inj.
      eauto.
    + rewrite -> extend_memory_lookup_neq in * by solve[eauto].
      invert_state_low_eq.
      assert (val_low_eq ℓ τ0 v0 v3 φ) by eauto 2.
      invert_val_low_eq; eauto 3.
      assert (low ℓ Γ (extend_stenv l1 (SecType τ (ℓ_τ, ι_τ)) Σ1)
                  (m1 [x → ValLoc l1])
                  (extend_heap v1 l1 ℓ_p n1 h1 H1 H2) l0).
      {
        assert_wf_type.
        invert_wf_type.
        eapply LowReachable.
        eapply LowReachMem.
        - eauto.
        - eauto.
        - rewrite -> extend_memory_lookup_neq by solve[eauto 2].
          eauto.
      }
      eauto 3.
  - unfolds.
    intros.
    assert (left φ loc1 = Some loc2) by eauto 2.
    assert (loc1 <> l1).
    {
      intro; subst.
      assert (exists ℓ μ, heap_lookup l1 h1 = Some (ℓ, μ)) by eauto 2.
      super_destruct'; subst.
      congruence.
    }
    assert (loc2 <> l2).
    {
      intro; subst.
      assert (left (inverse φ) l2 = Some loc1) by (destruct φ; eauto).
      assert (exists ℓ μ, heap_lookup l2 h2 = Some (ℓ, μ)) by eauto 2.
      super_destruct'; subst.
      congruence.
    }
    rewrite -> extend_stenv_lookup_neq in * by solve[eauto].
    assert (low ℓ Γ Σ1 m1 h1 loc1) by eauto 3 using low_in_extended_memory_heap_with_high_implies_low.
    assert (low ℓ Γ Σ2 m2 h2 loc2) by eauto 3 using low_in_extended_memory_heap_with_high_implies_low.
    invert_state_low_eq.
    assert (heapval_low_eq ℓ τ0 loc1 loc2 m1 m2 h1 h2 φ) by eauto.
    invert_heapval_low_eq; eauto.
    eapply HeapValLowEq; eauto 2.
    + rewrite -> heap_lookup_extend_neq by solve[eauto].
      eauto.
    + rewrite -> heap_lookup_extend_neq by solve[eauto].
      eauto.
    + intros.
      assert (reach m1 h1 loc1).
      {
        eapply reach_extend_implies_reach_if; eauto 3.
        intros; subst.
        destruct τ.
        - assert (exists n, ValLoc loc' = ValNum n) by eauto.
          super_destruct; discriminate.
        - do 2 match goal with
                 [H: forall _ _, Array _ _ = Array _ _ -> exists _, _ = _ /\ _ |- _] =>
                 specialize (H s l eq_refl); super_destruct; subst
               end.
          injects.
          destruct (flowsto_dec ℓ_τ ℓ); eauto 3.
      }
      assert (reach m2 h2 loc2).
      {
        eapply reach_extend_implies_reach_if; eauto 3.
        intros; subst.
        destruct τ.
        - assert (exists n, ValLoc loc' = ValNum n) by eauto.
          super_destruct; discriminate.
        - do 2 match goal with
                 [H: forall _ _, Array _ _ = Array _ _ -> exists _, _ = _ /\ _ |- _] =>
                 specialize (H s l eq_refl); super_destruct; subst
               end.
          injects.
          destruct (flowsto_dec ℓ_τ ℓ); eauto 3.
      }
      assert (val_low_eq ℓ (SecType τ1 ℓ_τ0) u v φ) by eauto 2.
      invert_val_low_eq; eauto 3.

      assert (low ℓ Γ Σ1 m1 h1 l0) by eauto 3.
      
      assert (low ℓ Γ (extend_stenv l1 (SecType τ (ℓ_τ, ι_τ)) Σ1)
                  (m1 [x → ValLoc l1])
                  (extend_heap v1 l1 ℓ_p n1 h1 H1 H2) l0).
      {
        destruct_low.
        - eapply LowReachable.
          assert (wf_type bot (SecType (Array (SecType τ (ℓ_τ, ι_τ)) ℓ_p) (ℓ_x, ι))) by eauto 2.
          invert_wf_type.
          eapply low_reach_extend_memory_heap_with_high; eauto 3.          
        - eapply LowHeapLevel.
          + assert (loc <> l1) by congruence.
            rewrite -> heap_lookup_extend_neq by solve[eauto].
            eauto.
          + eauto.
      }
      eauto 3.
  - unfolds.
    intros.
    assert (left φ loc = Some loc') by eauto 2.
    assert (ι = ∘).
    {
      assert_wf_type.
      invert_wf_type.
      reflexivity.
    }
    subst.
    split.
    + intros.
      assert (low_reach ℓ Γ Σ1 m1 h1 loc) by eauto 2.
      assert (low_reach ℓ Γ Σ2 m2 h2 loc').
      {
        invert_state_low_eq.
        match goal with
          [H: context[low_reach_NI] |- _] =>
          solve[eapply H; eauto]
        end.
      }
      eapply low_reach_extend_memory_heap_with_high; eauto.
    + intros.
      assert (low_reach ℓ Γ Σ2 m2 h2 loc') by eauto 2.
      assert (low_reach ℓ Γ Σ1 m1 h1 loc).
      {
        invert_state_low_eq.
        match goal with
          [H: context[low_reach_NI] |- _] =>
          solve[eapply H; eauto]
        end.
      }      
      eapply low_reach_extend_memory_heap_with_high; eauto.
  - intros.
    destruct (T_dec l ℓ_p); subst.
    + assert_wf_type.
      invert_wf_type.
      exfalso; eauto.
    + do 2 rewrite -> size_extend_heap_neq_level by solve[eauto].
      invert_state_low_eq; eauto.
  - intros.
    assert_wf_type.
    invert_wf_type.
    destruct (decide (loc = l1)); subst.
    + apply_heap_lookup_extend_eq.
      rewrite_inj.
      exfalso; eauto.
    + destruct (decide (loc' = l2)); subst.
      * apply_heap_lookup_extend_eq.
        rewrite_inj.
        exfalso; eauto.
      * do 2 rewrite -> length_of_extend_neq by solve[eauto].
        repeat rewrite -> heap_lookup_extend_neq in * by solve[eauto].
        invert_state_low_eq.
        eauto.
Qed.

Lemma low_eq_heap_domain_update:
  forall ℓ_adv φ ψ m1 m2 h1 h2 Σ1 Σ2 loc1 loc2 n1 n2 ℓ σ ι v1 v2 Γ,
    state_low_eq ℓ_adv φ m1 h1 m2 h2 Γ Σ1 Σ2 ->
    wf_bijection ℓ_adv φ Γ Σ1 m1 h1 ->
    wf_bijection ℓ_adv (inverse φ) Γ Σ2 m2 h2 ->
    wf_tenv Γ m1 ->
    wf_tenv Γ m2 ->
    wf_stenv Σ1 h1 ->
    wf_stenv Σ2 h2 ->
    dangling_pointer_free m1 h1 ->
    dangling_pointer_free m2 h2 ->
    heap_level_bound Γ m1 h1 Σ1 ->
    heap_level_bound Γ m2 h2 Σ2 ->
    Σ1 loc1 = Some (SecType σ (ℓ, ι)) ->
    Σ2 loc2 = Some (SecType σ (ℓ, ι)) ->
    (σ = Int -> exists n, v1 = ValNum n) ->
    (σ = Int -> exists n, v2 = ValNum n) ->
    val_low_eq ℓ_adv (SecType σ (ℓ, ι)) v1 v2 φ ->
    (ℓ ⊑ ℓ_adv -> left φ loc1 = Some loc2) ->
    val_low_eq ℓ_adv (SecType Int (ℓ, ι)) (ValNum n1) (ValNum n2) φ ->
    (forall s ℓ',
        σ = Array s ℓ' ->
        exists loc', v1 = ValLoc loc' /\
                (ℓ ⊑ ℓ_adv -> low_reach ℓ_adv Γ Σ1 m1 h1 loc')) ->
    (forall s ℓ', σ = Array s ℓ' ->
             exists loc', v2 = ValLoc loc' /\
                     (ℓ ⊑ ℓ_adv -> low_reach ℓ_adv Γ Σ2 m2 h2 loc')) ->
    filtered (low ℓ_adv Γ Σ1 m1 (update_heap loc1 n1 v1 h1)) φ ψ ->
    low_heap_domain_eq ℓ_adv ψ m1 m2 (update_heap loc1 n1 v1 h1)
                       (update_heap loc2 n2 v2 h2) Γ Σ1 Σ2.
Proof.
  intros.
  unfolds.
  intros.
  assert (left φ l1 = Some l2) by eauto 2.
  splits.
  - intro.
    super_destruct.
    assert (exists ν, heap_lookup l1 h1 = Some (ℓ0, ν)).
    {
      destruct (decide (l1 = loc1)); subst.
      - assert (exists ν, heap_lookup loc1 h1 = Some (ℓ0, ν) /\ μ = update_lookup ν n1 v1) by eauto 2.
        super_destruct; subst.
        eauto.
      - rewrite -> heap_lookup_update_neq in * by solve[eauto].
        eauto.
    }
    destruct (flowsto_dec ℓ ℓ_adv).
    + assert (left φ loc1 = Some loc2) by eauto 2.
      assert (exists ℓ μ, heap_lookup loc1 h1 = Some (ℓ, μ)) by eauto 2.
      assert (low ℓ_adv Γ Σ1 m1 h1 loc1) by eauto 2.
      super_destruct; subst.
      assert ((exists ν, heap_lookup loc2 h2 = Some (ℓ1, ν)) /\ low ℓ_adv Γ Σ2 m2 h2 loc2).
      {
        invert_state_low_eq.
        match goal with
          [H: context[low_heap_domain_eq] |- _] =>
          solve[eapply H; eauto]
        end.
      }
      super_destruct; subst.
      
      assert (low ℓ_adv Γ Σ1 m1 h1 l1).
      {
        match goal with
          [H: low _ _ _ _ (update_heap _ _ _ _) _ |- _] =>
          dependent destruction H
        end.
        - eapply LowReachable.
          eapply low_reach_update_implies_low_reach_if; eauto 2.
          intros; subst.
          destruct σ.
          + assert (exists n, ValLoc loc' = ValNum n) by eauto 2.
            super_destruct; discriminate.
          + specialize (H17 s l eq_refl).
            super_destruct; subst.
            injects.
            eauto 2.
        - destruct (decide (loc = loc1)); subst.
          + assert (exists ν, heap_lookup loc1 h1 = Some (ℓ0, ν) /\
                         μ = update_lookup ν n1 v1) by eauto 2.
            super_destruct; subst.
            rewrite_inj.
            eauto 2.
          + rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
            eauto 3.
      }
      assert ((exists ν, heap_lookup l2 h2 = Some (ℓ0, ν)) /\ low ℓ_adv Γ Σ2 m2 h2 l2).
      {
        invert_state_low_eq.
        match goal with
          [H: context[low_heap_domain_eq] |- _] =>
          solve[eapply H; eauto]
        end.
      }
      super_destruct; subst.
      splits.
      * destruct (decide (l2 = loc2)); subst.
        { eauto. }
        { rewrite -> heap_lookup_update_neq by solve[eauto].
          eauto. }
      * match goal with
          [H: low _ Γ Σ2 m2 h2 _ |- _] =>
          dependent destruction H
        end.
        {
          match goal with
            [H: low _ Γ _ _ (update_heap _ _ _ _) _ |- _] =>
            dependent destruction H
          end.
          - eapply LowReachable.
            eapply low_reach_in_updated_heap; eauto 2.
          - rewrite_inj.
            destruct (decide (loc2 = loc)); subst.
            + rewrite_inj.
              eapply LowHeapLevel; eauto 2.
            + eapply LowHeapLevel.
              * rewrite -> heap_lookup_update_neq by solve[eauto].
                eauto.
              * eauto.
        }
        {
          rewrite_inj.
          destruct (decide (loc = loc2)); subst.
          - rewrite_inj.
            eauto 3.
          - eapply LowHeapLevel.
            + rewrite -> heap_lookup_update_neq by solve[eauto 2].
              eauto.
            + eauto.
        }
    + assert (low ℓ_adv Γ Σ1 m1 h1 l1).
      {
        destruct_low.
        - eapply LowReachable.
          eapply low_reach_in_updated_heap_with_high_implies_low_reach; eauto 3.
        - destruct (decide (loc = loc1)); subst.
          + assert (exists ν, heap_lookup loc1 h1 = Some (ℓ0, ν) /\ μ = update_lookup ν n1 v1)
              by eauto 2.
            super_destruct; subst.
            rewrite_inj.
            eauto 2.
          + rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
            eauto 2.
      }
      assert ((exists μ, heap_lookup l2 h2 = Some (ℓ0, μ)) /\ low ℓ_adv Γ Σ2 m2 h2 l2).
      {
        invert_state_low_eq.
        match goal with
          [H: context[low_heap_domain_eq] |- _] =>
          solve[eapply H; eauto]
        end.
      }
      super_destruct; subst.
      splits.
      * destruct (decide (l2 = loc2)); subst.
        {
          eauto 3.
        }
        {
          rewrite -> heap_lookup_update_neq by solve[eauto 2].
          eauto.
        }
      * eapply low_update_with_high; eauto 2.
  - intro.
    super_destruct.
    assert (exists ν, heap_lookup l2 h2 = Some (ℓ0, ν)).
    {
      destruct (decide (l2 = loc2)); subst.
      - assert (exists μ, heap_lookup loc2 h2 = Some (ℓ0, μ) /\ ν = update_lookup μ n2 v2) by eauto 2.
        super_destruct; subst.
        eauto.
      - rewrite -> heap_lookup_update_neq in * by solve[eauto].
        eauto.
    }
    destruct (flowsto_dec ℓ ℓ_adv).
    + assert (left φ loc1 = Some loc2) by eauto 2.
      assert (exists ℓ μ, heap_lookup loc2 h2 = Some (ℓ, μ)) by (destruct φ; eauto 3).
      assert (low ℓ_adv Γ Σ2 m2 h2 loc2) by (destruct φ; eauto 3).
      super_destruct; subst.
      assert ((exists ν, heap_lookup loc1 h1 = Some (ℓ1, ν)) /\ low ℓ_adv Γ Σ1 m1 h1 loc1).
      {
        invert_state_low_eq.
        match goal with
          [H: context[low_heap_domain_eq] |- _] =>
          solve[eapply H; eauto]
        end.
      }
      super_destruct; subst.
      
      assert (low ℓ_adv Γ Σ2 m2 h2 l2).
      {
        match goal with
          [H: low _ _ _ _ (update_heap _ _ _ _) _ |- _] =>
          dependent destruction H
        end.
        - eapply LowReachable.
          eapply low_reach_update_implies_low_reach_if; eauto 2.
          intros; subst.
          destruct σ.
          + assert (exists n, ValLoc loc' = ValNum n) by eauto 2.
            super_destruct; discriminate.
          + specialize (H18 s l eq_refl).
            super_destruct; subst.
            injects.
            eauto 2.
        - rewrite_inj.
          destruct (decide (loc = loc2)); subst.
          + assert (exists ν, heap_lookup loc2 h2 = Some (ℓ1, ν) /\
                         μ = update_lookup ν n2 v2) by eauto 2.
            super_destruct; subst.
            rewrite_inj.
            eauto 2.
          + rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
            eauto 3.
      }
      assert ((exists ν, heap_lookup l1 h1 = Some (ℓ0, ν)) /\ low ℓ_adv Γ Σ1 m1 h1 l1).
      {
        invert_state_low_eq.
        match goal with
          [H: context[low_heap_domain_eq] |- _] =>
          solve[eapply H; eauto]
        end.
      }
      super_destruct; subst.
      splits.
      * destruct (decide (l1 = loc1)); subst.
        { eauto. }
        { rewrite -> heap_lookup_update_neq by solve[eauto].
          eauto. }
      * match goal with
          [H: low _ Γ Σ1 m1 h1 _ |- _] =>
          dependent destruction H
        end.
        {
          match goal with
            [H: low _ Γ _ _ (update_heap _ _ _ _) _ |- _] =>
            dependent destruction H
          end.
          - eapply LowReachable.
            eapply low_reach_in_updated_heap; destruct φ; eauto 2.
          - rewrite_inj.
            destruct (decide (loc1 = loc)); subst.
            + rewrite_inj.
              eapply LowHeapLevel; eauto 2.
            + eapply LowHeapLevel.
              * rewrite -> heap_lookup_update_neq by solve[eauto].
                eauto.
              * eauto.
        }
        {
          rewrite_inj.
          destruct (decide (loc = loc1)); subst.
          - rewrite_inj.
            eauto 3.
          - eapply LowHeapLevel.
            + rewrite -> heap_lookup_update_neq by solve[eauto 2].
              eauto.
            + eauto.
        }
    + assert (low ℓ_adv Γ Σ2 m2 h2 l2).
      {
        destruct_low.
        - eapply LowReachable.
          eapply low_reach_in_updated_heap_with_high_implies_low_reach; eauto 3.
        - destruct (decide (loc = loc2)); subst.
          + rewrite_inj.
            assert (exists ν, heap_lookup loc2 h2 = Some (ℓ1, ν) /\ μ = update_lookup ν n2 v2)
              by eauto 2.
            super_destruct; subst.
            rewrite_inj.
            eauto 2.
          + rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
            eauto 2.
      }
      assert ((exists μ, heap_lookup l1 h1 = Some (ℓ0, μ)) /\ low ℓ_adv Γ Σ1 m1 h1 l1).
      {
        invert_state_low_eq.
        match goal with
          [H: context[low_heap_domain_eq] |- _] =>
          solve[eapply H; eauto]
        end.
      }
      super_destruct; subst.
      splits.
      * destruct (decide (l1 = loc1)); subst.
        {
          eauto 3.
        }
        {
          rewrite -> heap_lookup_update_neq by solve[eauto 2].
          eauto.
        }
      * eapply low_update_with_high; eauto 2.
Qed.

Lemma state_low_eq_update_heap:
  forall ℓ_adv φ ψ m1 h1 m2 h2 Γ Σ1 Σ2 loc1 loc2 n1 n2 v1 v2 τ ι ℓ_τ length1 length2,
    state_low_eq ℓ_adv φ m1 h1 m2 h2 Γ Σ1 Σ2 ->
    wf_tenv Γ m1 ->
    wf_tenv Γ m2 ->
    wf_stenv Σ1 h1 ->
    wf_stenv Σ1 (update_heap loc1 n1 v1 h1) ->
    wf_stenv Σ2 h2 ->
    lookup_in_bounds m1 h1 ->
    lookup_in_bounds m2 h2 ->
    dangling_pointer_free m1 h1 ->
    dangling_pointer_free m2 h2 ->
    heap_level_bound Γ m1 h1 Σ1 ->
    heap_level_bound Γ m2 h2 Σ2 ->
    heap_level_bound Γ m1 (update_heap loc1 n1 v1 h1) Σ1 ->
    Σ1 loc1 = Some (SecType τ (ℓ_τ, ι)) ->
    Σ2 loc2 = Some (SecType τ (ℓ_τ, ι)) ->
    wf_bijection ℓ_adv φ Γ Σ1 m1 h1 ->
    wf_bijection ℓ_adv (inverse φ) Γ Σ2 m2 h2 ->
    (τ = Int -> exists n_v, v1 = ValNum n_v) ->
    (forall s ℓ, τ = Array s ℓ -> exists l_v, v1 = ValLoc l_v
                                   /\ (ℓ_τ ⊑ ℓ_adv -> low_reach ℓ_adv Γ Σ1 m1 h1 l_v)
                                   /\ (~ ℓ_τ ⊑ ℓ_adv -> reach m1 h1 l_v)) ->
    (τ = Int -> exists n_v, v2 = ValNum n_v) ->
    (forall s ℓ, τ = Array s ℓ -> exists l_v, v2 = ValLoc l_v
                                   /\ (ℓ_τ ⊑ ℓ_adv -> low_reach ℓ_adv Γ Σ2 m2 h2 l_v)
                                   /\ (~ ℓ_τ ⊑ ℓ_adv -> reach m2 h2 l_v)) ->
    val_low_eq ℓ_adv (SecType Int (ℓ_τ, ι)) (ValNum n1) (ValNum n2) φ ->
    val_low_eq ℓ_adv (SecType τ (ℓ_τ, ι)) v1 v2 φ ->
    filtered (low ℓ_adv Γ Σ1 m1 (update_heap loc1 n1 v1 h1)) φ ψ ->
    (ℓ_τ ⊑ ℓ_adv -> left φ loc1 = Some loc2) ->
    length_of loc1 h1 = Some length1 ->
    length_of loc2 h2 = Some length2 ->
    0 <= n1 ->
    n1 < length1 ->
    0 <= n2 ->
    n2 < length2 ->
    reach m1 h1 loc1 ->
    reach m2 h2 loc2 ->
    state_low_eq ℓ_adv ψ
                 m1 (update_heap loc1 n1 v1 h1)
                 m2 (update_heap loc2 n2 v2 h2)
                 Γ Σ1 Σ2.
Proof.
  intros.
  eapply StateLowEq ; try solve[invert_state_low_eq; eauto 2].
  - eapply low_eq_stenv_update; eauto 2.
    + intros; subst.
      specialize (H17 s ℓ' eq_refl).
      super_destruct; subst.
      eexists; splits*.
    + intros; subst.
      specialize (H19 s ℓ' eq_refl).
      super_destruct; subst.
      eexists; splits*.
  - eapply low_eq_heap_domain_update; eauto 2.
    + intros; subst.
      specialize (H17 s ℓ' eq_refl).
      super_destruct; subst.
      eexists; splits*.
    + intros; subst.
      specialize (H19 s ℓ' eq_refl).
      super_destruct; subst.
      eexists; splits*.
  - invert_state_low_eq; eauto 2.
    unfolds.
    intros.
    assert (val_low_eq ℓ_adv τ0 v0 v3 φ) by eauto 3.
    invert_val_low_eq; eauto 3.
    assert (low ℓ_adv Γ Σ1 m1 (update_heap loc1 n1 v1 h1) l1).
    {
      eapply LowReachable.
      assert_wf_type.
      invert_wf_type.
      eauto 2.
    }
    eauto 3.
  - unfolds.
    intros.
    assert (left φ loc0 = Some loc3) by eauto 2.
    assert (low ℓ_adv Γ Σ1 m1 h1 loc0).
    {
      match goal with
        [H: low _ _ _ _ _ ?loc |- low _ _ _ _ _ ?loc] =>
        dependent destruction H
      end.
      - eapply LowReachable.
        eapply low_reach_update_implies_low_reach_if; eauto 3.
        intros; subst.
        destruct τ.
        + assert (exists n, ValLoc loc' = ValNum n) by eauto 2.
          super_destruct; discriminate.
        + specialize (H17 s l eq_refl).
          super_destruct; subst.
          injects.
          eauto.
      - destruct (decide (loc = loc1)); subst.
        + assert (exists ν, heap_lookup loc1 h1 = Some (ℓ, ν) /\ μ = update_lookup ν n1 v1)
            by eauto 2.
          super_destruct; subst.
          rewrite_inj.
          eauto 3.
        + rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
          eauto 3.
    }
    assert (exists ℓ μ, heap_lookup loc0 h1 = Some (ℓ, μ)) by eauto 3.
    super_destruct; subst.
    assert ((exists ν, heap_lookup loc3 h2 = Some (ℓ, ν)) /\ low ℓ_adv Γ Σ2 m2 h2 loc3).
    {
      invert_state_low_eq.
      match goal with
        [H: context[low_heap_domain_eq] |- _] =>
        solve[eapply H; eauto]
      end.
    }
    super_destruct; subst.

    assert (exists μ, heap_lookup loc0 (update_heap loc1 n1 v1 h1) = Some (ℓ, μ)).
    {
      destruct (decide (loc0 = loc1)); subst.
      - eauto 3.
      - rewrite -> heap_lookup_update_neq by solve[eauto 2].
        eauto.
    }
    assert (exists ν, heap_lookup loc3 (update_heap loc2 n2 v2 h2) = Some (ℓ, ν)).
    {
      destruct (decide (loc2 = loc3)); subst.
      - eauto 3.
      - rewrite -> heap_lookup_update_neq by solve[eauto 2].
        eauto.
    }
    
    assert (heapval_low_eq ℓ_adv τ0 loc0 loc3 m1 m2 h1 h2 φ) by (invert_state_low_eq; eauto 3).
    invert_heapval_low_eq.
    super_destruct; subst.
    rewrite_inj.
    eapply HeapValLowEq.
    + eauto.
    + eauto.
    + intros.
      splits.
      * intros.
        destruct (decide (loc3 = loc2)); subst.
        {
          assert ( exists ν2, heap_lookup loc2 h2 = Some (ℓ0, ν2) /\ ν1 = update_lookup ν2 n2 v2) by eauto 2.
          super_destruct; subst.
          rewrite_inj.
          destruct (decide (n2 = n)); subst.
          - eauto.
          - rewrite -> lookup_update_neq by solve[eauto].
            eapply_lookup_func_domain_eq.
            destruct (decide (loc0 = loc1)); subst.
            + assert (exists ν, heap_lookup loc1 h1 = Some (ℓ0, ν) /\
                           μ1 = update_lookup ν n1 v1) by eauto 2.
              super_destruct; subst.
              rewrite_inj.
              destruct (decide (n = n1)); subst.
              * rewrite_inj.
                eauto.
              * rewrite -> lookup_update_neq in * by solve[eauto].
                eauto.
            + rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
              rewrite_inj.
              eauto.
        }
        rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
        rewrite_inj.
        destruct (decide (loc0 = loc1)); subst.
        {
          assert (exists ν, heap_lookup loc1 h1 = Some (ℓ0, ν) /\ μ1 = update_lookup ν n1 v1) by eauto 2.
          super_destruct; subst.
          rewrite_inj.
          destruct (decide (n1 = n)); subst.
          - eapply_lookup_func_domain_eq.
            rewrite_inj.
            eauto.
          - rewrite -> lookup_update_neq in * by solve[eauto 2].
            firstorder 2.
        }
        {
          rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
          rewrite_inj.
          firstorder 2.
        }
      * intros.
        destruct (decide (loc0 = loc1)); subst.
        {
          assert (exists μ, heap_lookup loc1 h1 = Some (ℓ0, μ) /\ μ1 = update_lookup μ n1 v1) by eauto 2.
          super_destruct; subst.
          rewrite_inj.
          destruct (decide (n1 = n)); subst.
          - eauto.
          - rewrite -> lookup_update_neq by solve[eauto].
            eapply_lookup_func_domain_eq.
            destruct (decide (loc3 = loc2)); subst.
            + assert (exists ν, heap_lookup loc2 h2 = Some (ℓ0, ν) /\
                           ν1 = update_lookup ν n2 v2) by eauto 2.
              super_destruct; subst.
              rewrite_inj.
              destruct (decide (n = n2)); subst.
              * rewrite_inj.
                eauto.
              * rewrite -> lookup_update_neq in * by solve[eauto].
                eauto.
            + rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
              rewrite_inj.
              eauto.
        }
        rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
        rewrite_inj.
        destruct (decide (loc3 = loc2)); subst.
        {
          assert (exists ν, heap_lookup loc2 h2 = Some (ℓ0, ν) /\ ν1 = update_lookup ν n2 v2) by eauto 2.
          super_destruct; subst.
          rewrite_inj.
          destruct (decide (n2 = n)); subst.
          - eapply_lookup_func_domain_eq.
            rewrite_inj.
            eauto.
          - rewrite -> lookup_update_neq in * by solve[eauto 2].
            firstorder 2.
        }
        {
          rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
          rewrite_inj.
          firstorder 2.
        }
    + intros; subst.
      rewrite_inj.
      assert (reach m1 h1 loc0).
      {
        eapply reach_update_implies_reach_if.
        - eauto.
        - intros; subst.
          destruct τ.
          + assert (exists n, ValLoc loc' = ValNum n) by eauto 2.
            super_destruct; discriminate.
          + specialize (H17 s l eq_refl).
            super_destruct; subst.
            injects.
            destruct (flowsto_dec ℓ_τ ℓ_adv); eauto 3.
      }
      assert (reach m2 h2 loc3).
      {
        eapply reach_update_implies_reach_if.
        - eauto.
        - intros; subst.
          destruct τ.
          + assert (exists n, ValLoc loc' = ValNum n) by eauto 2.
            super_destruct; discriminate.
          + specialize (H19 s l eq_refl).
            super_destruct; subst.
            injects.
            destruct (flowsto_dec ℓ_τ ℓ_adv); eauto 3.
      }
      
      assert (val_low_eq ℓ_adv (SecType τ1 ℓ_τ0) u v φ).
      {
        destruct (decide (loc0 = loc1)); subst.
        - assert (exists ν, heap_lookup loc1 h1 = Some (ℓ0, ν) /\ μ1 = update_lookup ν n1 v1) by eauto 2.
          super_destruct; subst.
          rewrite_inj.
          destruct (flowsto_dec ℓ_τ ℓ_adv).
          + assert (n1 = n2).
            {
              repeat invert_val_low_eq; eauto 2 || contradiction.
            }
            subst.
            assert (left φ loc1 = Some loc2).
            {
              repeat invert_val_low_eq; eauto 2 || contradiction.
            }
            rewrite_inj.
            assert (exists ν, heap_lookup loc2 h2 = Some (ℓ0, ν) /\ ν1 = update_lookup ν n2 v2) by eauto 2.
            super_destruct; subst.
            rewrite_inj.
            destruct (decide (n = n2)); subst.
            * rewrite -> lookup_update_eq in *.
              rewrite_inj.
              eauto.
            * rewrite -> lookup_update_neq in * by solve[eauto 2].
              eauto 2.
          + destruct τ1.
            * assert (exists n, u = ValNum n).
              {
                destruct (decide (n1 = n)); subst.
                - eauto.
                - rewrite -> lookup_update_neq in * by solve[eauto].
                  eauto 3.
              }
              assert (exists n, v = ValNum n).
              {
                destruct (decide (loc3 = loc2)); subst.
                - assert (exists ν, heap_lookup loc2 h2 = Some (ℓ0, ν) /\ ν1 = update_lookup ν n2 v2)
                    by eauto 2.
                  super_destruct; subst.
                  rewrite_inj.
                  destruct (decide (n2 = n)); subst.
                  + rewrite -> lookup_update_eq in *.
                    rewrite_inj.
                    eauto 2.
                  + rewrite -> lookup_update_neq in * by solve[eauto 2].
                    eauto 3.
                - rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
                  eauto 3.
              }
              super_destruct; subst.
              eauto.
            * assert (exists loc, u = ValLoc loc).
              {
                destruct (decide (n1 = n)); subst.
                - eauto.
                - rewrite -> lookup_update_neq in * by solve[eauto].
                  eauto 3.
              }
              assert (exists loc, v = ValLoc loc).
              {
                destruct (decide (loc3 = loc2)); subst.
                - assert (exists ν, heap_lookup loc2 h2 = Some (ℓ0, ν) /\ ν1 = update_lookup ν n2 v2)
                    by eauto 2.
                  super_destruct; subst.
                  rewrite_inj.
                  destruct (decide (n2 = n)); subst.
                  + rewrite -> lookup_update_eq in *.
                    rewrite_inj.
                    invert_val_low_eq; eauto.
                  + rewrite -> lookup_update_neq in * by solve[eauto 2].
                    eauto 3.
                - rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
                  eauto 3.
              }
              super_destruct; subst.
              eauto.
        - rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
          rewrite_inj.
          destruct (flowsto_dec ℓ_τ ℓ_adv).
          + assert (left φ loc1 = Some loc2).
            {
              repeat invert_val_low_eq; eauto 2 || contradiction.
            }
            assert (Some loc3 <> left φ loc1) by eauto 3 using bijection_is_injective_left.
            assert (loc2 <> loc3) by congruence.
            rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
            assert (n1 = n2).
            {
              repeat invert_val_low_eq; contradiction || eauto 2.
            }
            subst.
            destruct (decide (n2 = n)); subst.
            * rewrite_inj.
              eauto 3.
            * rewrite_inj.
              eauto 3.
          + destruct (decide (loc2 = loc3)); subst.
            * rewrite_inj.
              {
                assert (exists ν, heap_lookup loc3 h2 = Some (ℓ0, ν) /\ ν1 = update_lookup ν n2 v2)
                  by eauto 2.
                super_destruct; subst.
                rewrite_inj.
                destruct τ.
                - assert (exists n, u = ValNum n) by eauto 3.
                  assert (exists n, v = ValNum n).
                  {
                    destruct (decide (n2 = n)); subst.
                    + rewrite -> lookup_update_eq in *.
                      rewrite_inj.
                      eauto 2.
                    + rewrite -> lookup_update_neq in * by solve[eauto 2].
                      eauto 3.
                  }
                  super_destruct; subst.
                  eauto.
                - assert (exists loc, u = ValLoc loc) by eauto 3.
                  assert (exists loc, v = ValLoc loc).
                  {
                    destruct (decide (n2 = n)); subst.
                    + rewrite -> lookup_update_eq in *.
                      rewrite_inj.
                      match goal with
                        [H: val_low_eq _ _ _ ?v _ |- exists _, ?v = _] =>
                        inverts H; eauto
                      end.
                    + rewrite -> lookup_update_neq in * by solve[eauto 2].
                      eauto 3.
                  }
                  super_destruct; subst.
                  eauto.
              }
            * rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
              rewrite_inj.
              eauto 2.
      }
      invert_val_low_eq; eauto 3.
      assert_wf_type.
      invert_wf_type.
      assert (low ℓ_adv Γ Σ1 m1 (update_heap loc1 n1 v1 h1) l1).
      {
        dependent destruction H35.
        - eapply LowReachable.
          eapply LowReachHeap with (loc1 := loc); eauto.
        - rewrite_inj.
          assert (low_reach ℓ_adv Γ Σ m (update_heap loc1 n1 v1 h1) loc).
          {
            eapply low_reach_adequacy; eauto 3.
          }
          eapply LowReachable.
          eapply LowReachHeap; eauto.
      }
      eauto 3.
  - unfolds.
    intros.
    assert (exists ℓ μ, heap_lookup loc1 h1 = Some (ℓ, μ)) by eauto 3.
    super_destruct; subst.
    rewrite_inj.
    splits; intros.
    + destruct (flowsto_dec ℓ_τ ℓ_adv).
      * assert (left φ loc1 = Some loc2).
        {
          repeat invert_val_low_eq; eauto 2 || contradiction.
        }
        assert (low ℓ_adv Γ Σ1 m1 h1 loc1) by eauto 2.
        assert (exists ν, heap_lookup loc2 h2 = Some (ℓ, ν)).
        {
          invert_state_low_eq.
          eapply H39; eauto.
        }
        super_destruct; subst.
        eapply low_reach_in_updated_heap; eauto 3.
        {
          intros; subst.
          specialize (H17 s ℓ' eq_refl).
          super_destruct; subst.
          eexists; splits*.          
        }
        {
          intros; subst.
          specialize (H19 s ℓ' eq_refl).
          super_destruct; subst.
          eexists; splits*.
        }
      * assert (left φ loc = Some loc') by eauto 2.
        assert (low_reach ℓ_adv Γ Σ1 m1 h1 loc) by eauto 3.
        assert (low_reach ℓ_adv Γ Σ2 m2 h2 loc').
        {
          invert_state_low_eq.
          match goal with
            [H: context[low_reach_NI] |- _] =>
            solve[eapply H; eauto]
          end.
        }
        eauto 3.
    + destruct (flowsto_dec ℓ_τ ℓ_adv).
      * assert (left φ loc1 = Some loc2).
        {
          repeat invert_val_low_eq; eauto 2 || contradiction.
        }
        assert (left φ loc = Some loc') by eauto 2.

        assert (low ℓ_adv Γ Σ1 m1 h1 loc1) by eauto 2.
        assert (exists ν, heap_lookup loc2 h2 = Some (ℓ, ν)).
        {
          invert_state_low_eq.
          eapply H40; eauto.
        }
        super_destruct; subst.
        eapply low_reach_in_updated_heap; try solve[destruct φ; eauto 3].
        {
          intros; subst.
          specialize (H19 s ℓ' eq_refl).
          super_destruct; subst.
          eexists; splits*.         
        }
        {
          intros; subst.
          specialize (H17 s ℓ' eq_refl).
          super_destruct; subst.
          eexists; splits*.
        }
      * assert (left φ loc = Some loc') by eauto 2.
        assert (low_reach ℓ_adv Γ Σ2 m2 h2 loc') by eauto 3.
        assert (low_reach ℓ_adv Γ Σ1 m1 h1 loc).
        {
          invert_state_low_eq.
          match goal with
            [H: context[low_reach_NI] |- _] =>
            solve[eapply H; eauto]
          end.
        }
        eauto 3.
  - intros.
    do 2 rewrite -> size_update_heap.
    invert_state_low_eq; eauto.
  - intros.
    repeat rewrite -> length_of_update.
    destruct (decide (loc = loc1)); subst.
    + assert (exists ν, heap_lookup loc1 h1 = Some (l, ν) /\ μ = update_lookup ν n1 v1) by eauto.
      super_destruct; subst.
      destruct (decide (loc' = loc2)); subst.
      * assert (exists ν2, heap_lookup loc2 h2 = Some (l, ν2) /\ ν = update_lookup ν2 n2 v2) by eauto.
        super_destruct; subst.
        invert_state_low_eq; eauto.
      * rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
        invert_state_low_eq; eauto.
    + rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
      destruct (decide (loc' = loc2)); subst.
      * assert (exists ν2, heap_lookup loc2 h2 = Some (l, ν2) /\ ν = update_lookup ν2 n2 v2) by eauto.
        super_destruct; subst.
        invert_state_low_eq; eauto.
      * rewrite -> heap_lookup_update_neq in * by solve[eauto].
        invert_state_low_eq; eauto.
Qed.
  
  Lemma high_pc_does_not_update_low_states:
    forall c c' pc pc' pc'' m m' h h' t t' Σ Σ' Γ ℓ,
      ~ pc ⊑ ℓ ->
      wellformed_aux Γ Σ ⟨c, pc, m, h, t⟩ pc'' ->
      ⟨c, pc, m, h, t⟩ ⇒ (Γ, Σ, Σ') ⟨c', pc', m', h', t'⟩ ->
      state_low_eq ℓ (identity_bijection loc) m h m' h' Γ Σ Σ'.
  Proof.

    Ltac handle_gc :=
      eapply high_pc_gc_does_not_update_low_states;
      solve[eauto] ||
           solve[erewrite -> disjoint_union_proof_irrelevance; eauto].
    
    intros.
    invert_wf_aux.
    revert dependent c'.
    revert dependent pc''.
    revert pc' m' h' t t'.
    induction c; intros; subst.
    - invert_step; solve[eauto || handle_gc].
    - invert_step; solve[eauto || handle_gc].
    - do 2 specialize_gen.
      invert_wt_cmd.
      invert_lifted.
      destruct_prod_join_flowsto.
      destruct l2 as [l2 ι].
      assert (~ l2 ⊑ ℓ) by eauto.
      invert_step.
      + rewrite_inj.
        eapply state_low_eq_extend_high; eauto.
        * intros; subst.
          eauto using wt_int_e_is_num.
        * intros; subst.
          assert (exists loc, v = ValLoc loc) by eauto using wt_array_e_is_loc.
          super_destruct; subst.
          assert (exists x, memory_lookup m x = Some (ValLoc loc) /\ e = Var x) by eauto.
          exists loc.
          super_destruct; subst.
          reflexivity.
      + handle_gc.
    - invert_step; solve[eauto || handle_gc].
    - invert_step; solve[eauto || handle_gc].
    - invert_step.
      + assert ((c1;; c') <> Stop) by congruence.
        assert ((c1;; c') <> TimeOut) by congruence.
        do 2 specialize_gen.
        invert_wt_cmd.
        eauto.  (* Done by IHc1 *)
      + assert ((c1;; c2) <> Stop) by congruence.
        assert ((c1;; c2) <> TimeOut) by congruence.
        do 2 specialize_gen.
        invert_wt_cmd.
        eauto. (* Done by IHc1 *)
      + handle_gc.
    - assert (At l e c <> Stop) by congruence.
      assert (At l e c <> TimeOut) by congruence.
      do 2 specialize_gen.
      invert_wt_cmd.
      invert_step; solve[eauto || handle_gc].
    - assert (BackAt l n <> Stop) by congruence.
      assert (BackAt l n <> TimeOut) by congruence.
      do 2 specialize_gen.
      invert_wt_cmd.
      invert_step; solve[eauto || handle_gc].
    - do 2 specialize_gen.
      invert_wt_cmd.
      invert_step.
      + rewrite_inj.
        destruct_join_flowsto.
        destruct τ0 as [τ0 [ℓ' ι']].
        eapply state_low_eq_extend_mem_heap_high; eauto 3.
        * intros; subst.
          eauto.
        * intros; subst.
          assert (exists loc, v = ValLoc loc) by eauto.
          super_destruct; subst.
          exists loc.
          splits~.
          { intros; subst.
            assert (ι' = ∘).
            {
              assert_wf_type.
              do 2 invert_wf_type.
              reflexivity.
            }
            assert (exists x, memory_lookup m x = Some (ValLoc loc) /\ e0 = Var x) by eauto.
            super_destruct; subst.
            invert_var_typing.
            eauto 2.
          }
          {
            intros.
            assert (exists x, memory_lookup m x = Some (ValLoc loc) /\ e0 = Var x) by eauto.
            super_destruct; subst.
            eauto.
          }
      + handle_gc.
    - do 2 specialize_gen.
      invert_wt_cmd.
      invert_lifted.
      invert_step.
      + destruct ε_x as [ℓ_x ι_x].
        destruct ε_idx as [ℓ_idx ι_idx].
        assert (ℓ_idx ⊔ pc' ⊑ ℓ_x) by eauto.
        destruct_join_flowsto.
        assert (~ ℓ_x ⊑ ℓ) by eauto.
        destruct l2 as [ℓ2 ι2].
        destruct ε as [ℓ' ι'].
        assert (ℓ_x ⊔ ℓ' ⊑ ℓ2) by eauto.
        destruct_join_flowsto.
        assert (~ ℓ2 ⊑ ℓ) by eauto.
        assert (Σ' l0 = Some (SecType σ (ℓ2, ι2))) by eauto.
        eapply state_low_eq_update_heap_high; eauto 2.
        * intros; subst; eauto.
        * intros; subst; eauto.
      + handle_gc.
    - do 2 specialize_gen.
      invert_wt_cmd.
      invert_lifted.
      repeat destruct_join_flowsto.
      rewrite_inj.
      destruct l2 as [l2 ι].
      destruct ε_idx as [ℓ_idx ι_idx].
      destruct ε_y as [ℓ_y ι_y].
      assert (pc'' ⊔ ℓ_idx ⊑ ℓ_y) by eauto.
      destruct ε as [ℓ_0 ι_0].
      rewrite -> ProdL.join_is_pairwise in *.
      repeat destruct_join_flowsto.
      assert (ℓ_0 ⊔ ℓ_y ⊑ l2) by eauto.
      repeat destruct_join_flowsto.
      assert (~ l2 ⊑ ℓ) by eauto.
      invert_step.
      + rewrite_inj.
        eapply state_low_eq_extend_high; eauto 2.
        * intros; subst.
          eauto.
        * intros; subst.
          eauto.
      + handle_gc.
    - do 2 specialize_gen.
      invert_step.
      + invert_wt_cmd.
        rewrite_inj.
        eapply state_low_eq_extend_high; eauto 2.
        intros; subst; discriminate.
      + handle_gc.
    - invert_step.
      handle_gc.
  Qed.
  Hint Resolve high_pc_does_not_update_low_states.

Lemma high_pc_does_not_update_low_states_event_step_helper:
  forall c c' pc pc' pc'' m m' h h' t t' ℓ Γ Σ Σ' ev,
    ~ pc ⊑ ℓ ->
    wellformed_aux Γ Σ ⟨c, pc, m, h, t⟩ pc'' ->
    ⟨c, pc, m, h, t⟩ ⇒ [ev, Γ, Σ, Σ'] ⟨c', pc', m', h', t'⟩ ->
    state_low_eq ℓ (identity_bijection loc) m h m' h' Γ Σ Σ'.
Proof.
  intros.
  invert_event_step; eauto.
  invert_wf_aux.
  eapply high_pc_gc_does_not_update_low_states; eauto ||
                                                      (erewrite -> disjoint_union_proof_irrelevance; eauto).
Qed.
Hint Resolve high_pc_does_not_update_low_states_event_step_helper.

Lemma high_pc_does_not_update_low_states_event_step:
  forall c c' pc pc' pc'' m m' h h' t t' ℓ Γ Σ Σ' ev,
    ~ pc ⊑ ℓ ->
    ~ contains_low_backat ℓ c ->
    wellformed_aux Γ Σ ⟨c, pc, m, h, t⟩ pc'' ->
    ⟨c, pc, m, h, t⟩ ⇒ [ev, Γ, Σ, Σ'] ⟨c', pc', m', h', t'⟩ ->
    state_low_eq ℓ (identity_bijection loc) m h m' h' Γ Σ Σ' /\
    high_event ℓ ev.
Proof.
  intros.
  assert (H3 := H1).
  eapply high_pc_does_not_update_low_states_event_step_helper in H1.
  - splits*.
  - eauto.
  - eauto.
Qed.
Hint Resolve high_pc_does_not_update_low_states_event_step.

Lemma high_pc_lemma:
  forall n c t t' pc pc' pc'' m m' h h' c' Γ Σ Σ' ℓ ev,
    ~ pc ⊑ ℓ ->
    ~ contains_low_backat ℓ c ->
    wellformed_aux Γ Σ ⟨c, pc, m, h, t⟩ pc'' ->
    ⟨c, pc, m, h, t⟩ ↷ [ℓ, Γ, Σ, Σ', ev, n] ⟨c', pc', m', h', t'⟩ ->
    c' = Stop /\
    high_event ℓ ev /\
    state_low_eq ℓ (identity_bijection loc) m h m' h' Γ Σ Σ'.
Proof.
  intro n.
  induction n; intros.
  - invert_bridge_step.
    + invert_low_event_step.
      eapply wt_at_high_implies_high_event in H1; eauto.
      contradiction.
    + invert_high_event_step.
      unfold is_stop_config in *.
      unfold cmd_of in *.
      subst.
      eapply high_pc_does_not_update_low_states_event_step in H1; eauto.
      super_destruct.
      eauto.
  - invert_bridge_step.
    invert_high_event_step.
    destruct cfg2.
    assert (wellformed_aux Γ Σ'0 ⟨c0, pc0, memory, heap, time⟩ pc'')
      by eauto 2.
    destruct (eq_cmd_dec c Stop); subst.
    + assert (gc_occurred STOP c0 pc pc0 m memory h heap t time Σ Σ'0 /\
              ev1 = EmptyEvent) by eauto.
      unfold gc_occurred in *.
      super_destruct; subst.
      exfalso; eauto.
    + destruct (eq_cmd_dec c TimeOut); subst.
      * assert (gc_occurred TimeOut c0 pc pc0 m memory h heap t time Σ Σ'0 /\
              ev1 = EmptyEvent) by eauto.
      unfold gc_occurred in *.
      super_destruct; subst.
      exfalso; eauto.
      * assert (wellformed_aux Γ Σ' ⟨c', pc', m', h', t'⟩ pc'') by eauto 2.

        assert (identity_bijection loc =
                bijection.bijection_compose (identity_bijection loc) (identity_bijection loc))
          as H_id by (rewrite -> compose_id_left; reflexivity).
        rewrite -> H_id.
        clear H_id.
          
        assert (state_low_eq ℓ (identity_bijection loc) m h memory heap Γ Σ Σ'0
                /\ high_event ℓ ev1)
          by (eapply high_pc_does_not_update_low_states_event_step; eauto).

        assert (~ contains_low_backat ℓ c0)
          by eauto 2 using no_spurious_low_backats.
        
        assert (pc ⊑ pc0 \/ (exists ℓ' n, backat_at_head c (ℓ', n) /\ ~ ℓ' ⊑ ℓ))
          by (repeat invert_wf_aux; eauto). 
      super_destruct.
      { assert (c' = STOP /\
                high_event ℓ ev /\
                state_low_eq ℓ (identity_bijection loc) memory heap m' h' Γ Σ'0 Σ') by eauto 3.
        super_destruct.
        splits*.
        eapply state_low_eq_trans; (eauto || (repeat invert_wf_aux); eauto).
      }
      { remember_simple (backat_at_head_determines_pc_event_step H10 H2).
        super_destruct'.
        destruct (lt_eq_lt_dec t n2).
        - destruct s.
          + specialize_gen.
            destruct H16.
            * super_destruct'; subst.
              assert (c' = STOP /\
                    high_event ℓ ev /\
                    state_low_eq ℓ (identity_bijection loc) m h m' h' Γ Σ Σ')
              by eauto 2 using IHn.
            super_destruct'; subst.
            splits*.
            rewrite -> compose_id_left.
            eauto.
            * unfold gc_occurred in H16.
              super_destruct'; subst.
              specialize (IHn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H H0 H4 H14).
              super_destruct'.
              splits~.
              eapply state_low_eq_trans; (eauto || (repeat invert_wf_aux); eauto).
          + subst.
            match goal with
              [H: ?X = ?X -> _ |- _] =>
              specialize (H eq_refl)
            end.
            destruct H13.
            * super_destruct'; subst.
              specialize (IHn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H11 H9 H4 H14).
              super_destruct'; subst.
              splits*.
              eapply state_low_eq_trans; (eauto || (repeat invert_wf_aux); eauto).
            * unfold gc_occurred in H13.
              super_destruct'; subst.
              specialize (IHn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H H0 H4 H14).
              super_destruct'; subst.
              splits*.
              eapply state_low_eq_trans; (eauto 2 || (repeat invert_wf_aux); eauto 2).
        - specialize_gen.
          destruct H15.
          + super_destruct'; subst.
            exfalso; eauto 2.
          + unfold gc_occurred in H15.
            super_destruct'; subst.
            specialize (IHn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H H0 H4 H14).
            super_destruct'; subst.
            splits*.
            eapply state_low_eq_trans; (eauto 2 || (repeat invert_wf_aux); eauto 2).
      }
Qed.


Lemma low_reach_implies_low_reach_extend:
  forall ℓ_adv Γ Σ m loc1 loc2 l n v h H1 H2,
    low_reach ℓ_adv Γ Σ m h loc2 ->
    low_reach ℓ_adv Γ Σ m (h [loc1 → (n × v, l), H1, H2]) loc2.
Proof.
  intros.
  dependent induction H; eauto 2.
  specialize_gen.
  assert (loc0 <> loc1) by congruence.
  eapply LowReachHeap; eauto 2.
  rewrite -> heap_lookup_extend_neq by solve[eauto 2].
  eauto.
Qed.
Hint Resolve low_reach_implies_low_reach_extend.

Lemma low_implies_low_extend:
  forall ℓ_adv Γ Σ m loc1 loc2 l n v h H1 H2,
    low ℓ_adv Γ Σ m h loc2 ->
    heap_lookup loc1 h = None ->
    low ℓ_adv Γ Σ m (h [loc1 → (n × v, l), H1, H2]) loc2.
Proof.
  intros.
  destruct_low.
  - eapply LowReachable.
    eapply low_reach_implies_low_reach_extend; eauto 2.
  - assert (loc <> loc1) by congruence.
    eapply LowHeapLevel.
    + rewrite -> heap_lookup_extend_neq by solve[eauto 2].
      eauto.
    + eauto.
Qed.
Hint Resolve low_implies_low_extend.

Lemma skip_step:
  forall c pc pc' m m' h h' t t' Γ Σ Σ',
    ⟨Skip, pc, m, h, t⟩ ⇒ (Γ, Σ, Σ') ⟨c, pc', m', h', t'⟩ ->
    (c = Stop /\ pc = pc' /\ m = m' /\ h = h' /\ t' = S t /\ Σ = Σ') \/ gc_occurred Skip c pc pc' m m' h h' t t' Σ Σ'.
Proof.
  intros.
  invert_step.
  - left.
    splits*.
  - right.
    unfolds.
    splits~.
    do 7 eexists.
    splits; reflexivity || eauto.
Qed.

Lemma skip_many_steps_pc:
  forall pc pc' m m' h h' t t' Γ Σ Σ',
    ⟨Skip, pc, m, h, t⟩ ⇒ * (Γ, Σ, Σ') ⟨Stop, pc', m', h', t'⟩ ->
    pc = pc' /\ m = m' /\ Σ = Σ'.
Proof.
  intros.
  dependent induction H.
  destruct cfg as [c2 pc2 m2 h2 t2].
  remember_simple (skip_step H).
  super_destruct; subst.
  - remember_simple (stop_takes_no_step_many_step H0).
    super_destruct; subst.
    splits*.
  - unfold gc_occurred in *.
    super_destruct; subst.
    eauto.
Qed.

Definition gc_occurred_no_ex (c1 c2 : cmd) pc1 pc2 m1 m2 h1 h2 t1 t2 (Σ Σ' : stenv)
           h1_gc h1_pc h1_not_pc δ H1 H2 H3 :=
  c1 = c2 /\ c1 <> Stop /\ c1 <> TimeOut /\ m1 = m2 /\ pc1 = pc2 /\ Σ = Σ' /\
  h1 = [h2 ⊎ h1_gc, H1] /\
  disjoint h2 h1_gc /\
  (forall loc ℓ μ, heap_lookup loc h1_gc = Some (ℓ, μ) -> ~ reach m1 h1 loc) /\
  levels_satisfy h1_gc (eq pc1) /\
  h2 = [h1_pc ⊎ h1_not_pc, H2] /\
  levels_satisfy h1_pc (eq pc1) /\
  levels_satisfy h1_not_pc (compose not (eq pc1)) /\
  gc m1 ([h1_pc ⊎ h1_gc, H3]) δ h1_pc /\
  t2 = t1 + δ.
Hint Unfold gc_occurred_no_ex.

Lemma gc_occurred_no_ex_implies_gc_occurred:
  forall c c' pc pc' m m' h h' t t' Σ Σ' h_gc h_pc h_not_pc δ H1 H2 H3,
    @gc_occurred_no_ex c c' pc pc' m m' h h' t t' Σ Σ' h_gc h_pc h_not_pc δ H1 H2 H3 ->
    gc_occurred c c' pc pc' m m' h h' t t' Σ Σ'.
Proof.
  intros.
  unfold gc_occurred_no_ex in *.
  super_destruct; subst.
  splits*.
  exists h_gc h_pc h_not_pc δ H1 H2; exists H3.
  splits*.
Qed.
Hint Resolve gc_occurred_no_ex_implies_gc_occurred.

Lemma gc_occurred_implies_gc_occurred_no_ex:
  forall c c' pc pc' m m' h h' t t' Σ Σ',
    gc_occurred c c' pc pc' m m' h h' t t' Σ Σ' ->
    exists h_gc h_pc h_not_pc δ H1 H2 H3,
      @gc_occurred_no_ex c c' pc pc' m m' h h' t t' Σ Σ' h_gc h_pc h_not_pc δ H1 H2 H3.
Proof.
  intros.
  unfold gc_occurred in *.
  super_destruct; subst.
  exists h1_2 h1_1_pc h1_1_not_pc δ H6 H7; exists H8.
  unfold gc_occurred_no_ex.
  splits*.
Qed.
Hint Resolve gc_occurred_implies_gc_occurred_no_ex.

Lemma filter_heap:
  forall (P : loc -> T -> Prop)
    (DecP : forall loc ℓ, { P loc ℓ } + { ~ P loc ℓ })
    (h : Heap),
    { h' : Heap | (forall loc ℓ μ,
                      heap_lookup loc h' = Some (ℓ, μ) ->
                      heap_lookup loc h = Some (ℓ, μ))
                  /\
                  (forall loc ℓ μ,
                      heap_lookup loc h' = Some (ℓ, μ) -> P loc ℓ)
                  /\
                  (forall loc ℓ μ,
                      P loc ℓ ->
                      heap_lookup loc h = Some (ℓ, μ) ->
                      heap_lookup loc h' = Some (ℓ, μ))
                  /\
                  (forall l, size l h' <= size l h) }.
Proof.
  intros.
  induction h using heap_rec.
  - exists emptyHeap.
    splits*.
    intros.
    assert (heap_lookup loc emptyHeap = None) by eauto 2.
    congruence.
  - super_destruct'; subst.
    destruct (DecP loc l).
    + assert (heap_lookup loc h' = None).
      {
        destruct (heap_lookup loc h') eqn:H_loc; try reflexivity.
        destruct p0.
        assert (heap_lookup loc h = Some (l0, l1)) by eauto 2.
        congruence.
      }
      assert (size l h' + n <= maxsize l h').
      {
        cut (size l h' + n <= size l h + n).
        {
          intros.
          erewrite <- (constant_maxsize h).
          omega.
        }
        { eauto 2 with arith. }
      }
      exists (extend_heap v loc l n h' H5 H6).
      splits; intros.
      * destruct (decide (loc0 = loc)); subst.
        {
          apply_heap_lookup_extend_eq.
          rewrite_inj.
          remember_simple (heap_lookup_extend_eq loc l n v h H1 H2).
          super_destruct'; subst.
          assert (μ0 = μ).
          {
            eapply lookupfunc_extensionality; eauto 2.
            congruence.
          }
          subst.
          eauto 2.
        }
        {
          rewrite -> heap_lookup_extend_neq in * by solve[eauto 2].
          eauto.
        }
      * destruct (decide (loc0 = loc)); subst.
        {
          remember_simple (heap_lookup_extend_eq loc l n v h' H5 H6).
          super_destruct'; subst.
          rewrite_inj.
          eauto 2.
        }
        rewrite -> heap_lookup_extend_neq in * by solve[eauto 2].
        eauto.
      * destruct (decide (loc0 = loc)); subst.
        {
          apply_heap_lookup_extend_eq.
          rewrite_inj.
          remember_simple (heap_lookup_extend_eq loc l n v h' H5 H6).
          super_destruct'; subst.
          assert (μ0 = μ) by (eapply lookupfunc_extensionality; congruence).
          subst.
          eauto 2.
        }
        {
          repeat rewrite -> heap_lookup_extend_neq in * by solve[eauto 2].
          eauto 2.
        }
      * destruct (T_dec l0 l); subst.
        {
          assert (heap_lookup loc h' = None).
          {
            destruct (heap_lookup loc h') eqn:H_loc; try reflexivity.
            destruct p0 as [ℓ μ].
            assert (heap_lookup loc h = Some (ℓ, μ)) by eauto 2.
            congruence.
          }
          do 2 rewrite -> size_extend_heap_eq_level by solve[eauto 2].
          eauto 2 with arith.
        }
        {
          do 2 rewrite -> size_extend_heap_neq_level by solve[eauto 2].
          eauto 2.
        }
    + exists h'.
      splits; intros.
      * cut (loc0 <> loc).
        {
          intros.
          rewrite -> heap_lookup_extend_neq by solve[eauto 2].
          eauto 2.
        }
        {
          intro; subst.
          assert (heap_lookup loc h = Some (ℓ, μ)) by eauto 2.
          congruence.
        }
      * eauto 2.
      * destruct (decide (loc0 = loc)); subst.
        {
          destruct (T_dec l ℓ).
          - subst.
            contradiction.
          - remember_simple (heap_lookup_extend_eq loc l n v h H1 H2).
            super_destruct'; subst.
            rewrite_inj.
            congruence.
        }
        {
          repeat rewrite -> heap_lookup_extend_neq in * by solve[eauto 2].
          eauto 2.
        }
      * assert (size l0 h' <= size l0 h) by eauto 2.
        assert (size l0 h <= size l0 (extend_heap v loc l n h H1 H2)).
        {
          eapply size_is_monotone_in_heap; eauto 2.
        }
        omega.
Defined.

Lemma disjoint_parts_implies_disjoint_union:
  forall h1 h2 h3 H,
    disjoint h1 h2 ->
    disjoint h1 h3 ->
    disjoint h1 ([h2 ⊎ h3, H]).
Proof.
  intros.
  unfold disjoint.
  intros.
  splits; intros.
  - eapply heap_lookup_two_none_implies_disjoint_union_none; firstorder.
  - destruct (disjoint_union_heap_lookup2 _ _ _ _ _ _ H2); firstorder.
Qed.
Hint Resolve disjoint_parts_implies_disjoint_union.

Lemma levels_satisfy_exists:
  forall p (DecP : forall l, {p l} + {~ p l}) (h : Heap),
    { h' | levels_satisfy h' p /\
           (forall l, size l h' <= size l h) /\
           (forall loc l μ, heap_lookup loc h' = Some (l, μ) ->
                       heap_lookup loc h = Some (l, μ)) /\
           (forall loc l μ, heap_lookup loc h = Some (l, μ) ->
                       p l ->
                       heap_lookup loc h' = Some (l, μ)) }.
Proof.
  intros.
  induction h using heap_rec.
  - exists emptyHeap.
    splits*.
    unfolds.
    intros.
    rewrite -> empty_heap_is_empty in *.
    discriminate.
  - super_destruct; subst.
    destruct (DecP l).
    + assert (heap_lookup loc h' = None).
      {
        destruct (heap_lookup loc h') eqn:H_loc; try reflexivity.
        destruct p1.
        assert (heap_lookup loc h = Some (l0, l1)) by eauto 2.
        congruence.
      }
      assert (size l h' + n <= maxsize l h').
      {
        assert (size l h' + n <= maxsize l h).
        {
          specialize (H0 l).
          omega.
        }
        rewrite -> (constant_maxsize h h' l) in *.
        assumption.
      }
      exists (extend_heap v loc l n h' H5 H6).
      
      splits.
      * unfolds.
        intros.
        destruct (decide (loc0 = loc)); subst.
        {
          apply_heap_lookup_extend_eq.
          rewrite_inj.
          assumption.
        }
        {
          rewrite -> heap_lookup_extend_neq in * by solve[eauto].
          eauto.
        }
      * intros.
        assert (heap_lookup loc h' = None).
        {
          destruct (heap_lookup loc h') eqn:H_loc; try reflexivity.
          - destruct p1.
            assert (heap_lookup loc h = Some (l1, l2)) by eauto.
            congruence.
        }
        destruct (T_dec l0 l); subst.
        {
          do 2 rewrite -> size_extend_heap_eq_level by solve[eauto].
          specialize (H0 l).
          omega.
        }
        {
          do 2 rewrite -> size_extend_heap_neq_level by solve[eauto].
          eauto.
        }
      * intros.
        destruct (decide (loc0 = loc)); subst.
        {
          apply_heap_lookup_extend_eq.
          rewrite_inj.

          remember_simple (heap_lookup_extend_eq loc l n v h H1 H2).
          super_destruct; subst.
          assert (μ = μ0).
          {
            eapply lookupfunc_extensionality.
            congruence.
          }
          subst.
          assumption.
        }
        {
          rewrite -> heap_lookup_extend_neq in * by solve[eauto].
          eauto.
        }
      * intros.
        destruct (decide (loc0 = loc)); subst.
        {
          apply_heap_lookup_extend_eq.
          rewrite_inj.
          remember_simple (heap_lookup_extend_eq loc l n v h' H5 H6).
          super_destruct; subst.
          assert (μ = μ0).
          {
            eapply lookupfunc_extensionality.
            congruence.
          }
          subst.
          assumption.
        }
        {
          rewrite -> heap_lookup_extend_neq in * by solve[eauto].
          eauto.
        }
    + exists h'.
      splits.
      * assumption.
      * intros.
        specialize (H0 l0).
        assert (size l0 h <= size l0 (extend_heap v loc l n h H1 H2)).
        {
          eapply size_is_monotone_in_heap; eauto.
        }
        omega.
      * intros.
        destruct (decide (loc0 = loc)); subst.
        {
          assert (heap_lookup loc h = Some (l0, μ)) by eauto.
          congruence.
        }
        {
          rewrite -> heap_lookup_extend_neq by solve[eauto].
          eauto.
        }
      * intros.
        destruct (decide (loc0 = loc)); subst.
        {
          apply_heap_lookup_extend_eq.
          congruence.
        }
        {
          rewrite -> heap_lookup_extend_neq in * by solve[eauto].
          eauto.
        }
Defined.

Lemma levels_satisfy_extend:
  forall loc l n v h p H1 H2,
    levels_satisfy h p ->
    p l ->
    levels_satisfy (extend_heap v loc l n h H1 H2) p.
Proof.
  intros.
  unfolds.
  intros.
  destruct (decide (loc0 = loc)); subst.
  - apply_heap_lookup_extend_eq.
    rewrite_inj.
    assumption.
  - rewrite -> heap_lookup_extend_neq in * by solve[eauto].
    eauto.
Qed.
Hint Resolve levels_satisfy_extend.

Lemma disjoint_disjoint_union_implies_disjoint_union:
  forall h1 h2 h3 H,
    disjoint ([h1 ⊎ h2, H]) h3 ->
    disjoint h1 h3.
Proof.
  intros.
  unfolds.
  intros.
  splits; intros.
  - assert (heap_lookup loc ([h1 ⊎ h2, H]) = Some (ℓ, μ)) by solve[eauto].
    eapply H0; eauto.
  - eapply disjoint_sym in H0.
    assert (heap_lookup loc ([h1 ⊎ h2, H]) = None) by solve[eauto].
    destruct (heap_lookup loc h1) eqn:H_loc; try reflexivity.
    destruct p.
    assert (heap_lookup loc ([h1 ⊎ h2, H]) = Some (l, l0)) by eauto.
    congruence.
    
    Unshelve.
    assumption.
Qed.
Hint Resolve disjoint_disjoint_union_implies_disjoint_union.



Lemma remove_gc'd_locations:
  forall h (φ: bijection loc loc),
    exists (ψ : bijection loc loc),
      (forall loc ℓ μ, heap_lookup loc h = Some (ℓ, μ) -> right ψ loc = None) /\
      (forall loc loc', left ψ loc = Some loc' -> left φ loc = Some loc') /\
      (forall loc loc', right ψ loc' = Some loc -> right φ loc' = Some loc) /\
      (forall loc, heap_lookup loc h = None -> right φ loc = right ψ loc).
Proof.
  intros.
  assert (forall a : loc, {heap_lookup a h = None} + {heap_lookup a h <> None}).
  {
    intros.
    destruct (heap_lookup a h).
    - right.
      congruence.
    - left.
      congruence.
  }
  destruct (filter_bijection' (fun loc => heap_lookup loc h = None) H φ) as [ψ H_ψ].
  unfold filtered' in *.
  exists ψ.
  splits.
  - intros.
    specialize (H_ψ loc).
    super_destruct.
    eapply H1; congruence.
  - intros.
    assert (right ψ loc' = Some loc) by (destruct ψ; eauto 2).
    assert (right φ loc' = Some loc).
    {
      eapply filtered_bijection_is_subset'.
      - eapply H.
      - eauto.
      - eauto.
    }
    destruct φ; eauto 2.
  - intros.
    eapply filtered_eq_if'.
    + eapply H.
    + eauto.
    + eauto.
  - intros.
    specialize (H_ψ loc).
    super_destruct.
    eauto using eq_sym.
Qed.

Lemma low_subset_if:
  forall ℓ_adv Γ φ ψ Σ1 m1 h1_pc h1_not_pc h1_gc h2_gc loc loc' H1 H2,
    low ℓ_adv Γ Σ1 m1 ([[h1_pc ⊎ h1_not_pc, H1] ⊎ h1_gc, H2]) loc ->
    left ψ loc = Some loc' ->
    (forall loc ℓ μ,
        heap_lookup loc h2_gc = Some (ℓ, μ) -> right ψ loc = None) ->
    (forall loc loc' : id_and_loc.loc,
        left ψ loc = Some loc' -> left φ loc = Some loc') ->
    (forall loc loc' ℓ μ,
        left φ loc = Some loc' ->
        heap_lookup loc h1_gc = Some (ℓ, μ) ->
        (exists ν, heap_lookup loc' h2_gc = Some (ℓ, ν))) ->
    (forall loc ℓ μ,
        heap_lookup loc h1_gc = Some (ℓ, μ) ->
        ~ reach m1 ([[h1_pc ⊎ h1_not_pc, H1] ⊎ h1_gc, H2]) loc) ->
    low ℓ_adv Γ Σ1 m1 ([h1_pc ⊎ h1_not_pc, H1]) loc.
Proof.
  intros.
  destruct_low.
  - eapply LowReachable.
    eapply low_reach_subset_if; eauto 2.
  - destruct_disjoint_heap_lookup.
    + eauto 2.
    + assert (exists ν, heap_lookup loc' h2_gc = Some (ℓ, ν)) by eauto.
      super_destruct; subst.
      assert (right ψ loc' = Some loc) by (destruct ψ; eauto).
      assert (right ψ loc' = None) by eauto 2.
      congruence.
Qed.
Hint Resolve low_subset_if.

Lemma low_eq_stenv_gc:
  forall ℓ_adv φ ψ Γ Σ1 Σ2 m1 m2 h1_pc h2_pc h1_not_pc h2_not_pc h1_gc h2_gc
    H1 H1' H2 H2',
    wf_bijection ℓ_adv ψ Γ Σ1 m1 ([h1_pc ⊎ h1_not_pc, H1]) ->
    (forall loc loc', left ψ loc = Some loc' -> left φ loc = Some loc') ->
    wf_bijection ℓ_adv (inverse ψ) Γ Σ2 m2 ([h2_pc ⊎ h2_not_pc, H2]) ->
    state_low_eq ℓ_adv φ m1 ([[h1_pc ⊎ h1_not_pc, H1] ⊎ h1_gc, H1']) m2
                 ([[h2_pc ⊎ h2_not_pc, H2] ⊎ h2_gc, H2']) Γ Σ1 Σ2 ->
    low_eq_stenv ℓ_adv ψ m1 m2 ([h1_pc ⊎ h1_not_pc, H1]) ([h2_pc ⊎ h2_not_pc, H2]) Γ Σ1 Σ2.
Proof.
  intros.
  unfolds.
  intros.
  assert (left φ loc1 = Some loc2) by eauto 2.
  splits.
  + intros.
    super_destruct.
    assert (low ℓ_adv Γ Σ1 m1 ([[h1_pc ⊎ h1_not_pc, H1] ⊎ h1_gc, H1']) loc1)
      by eauto 2.
    assert (Σ2 loc2 = Some τ /\
            low ℓ_adv Γ Σ2 m2 ([[h2_pc ⊎ h2_not_pc, H2] ⊎ h2_gc, H2']) loc2).
    {
      invert_state_low_eq.
      match goal with
        [H: context[low_eq_stenv] |- _] =>
        eapply H; eauto
      end.
    }
    super_destruct; subst.
    splits~.
    eapply wf_bijection_proj1; destruct ψ; eauto.
  + intros.
    super_destruct.
    assert (low ℓ_adv Γ Σ2 m2 ([[h2_pc ⊎ h2_not_pc, H2] ⊎ h2_gc, H2']) loc2)
      by eauto 2.
    assert (Σ1 loc1 = Some τ /\
            low ℓ_adv Γ Σ1 m1 ([[h1_pc ⊎ h1_not_pc, H1] ⊎ h1_gc, H1']) loc1).
    {
      invert_state_low_eq.
      match goal with
        [H: context[low_eq_stenv] |- _] =>
        eapply H; eauto
      end.
    }
    super_destruct; subst.
    splits~.
    eapply wf_bijection_proj1; destruct ψ; eauto.
Qed.
Hint Resolve low_eq_stenv_gc.

Lemma state_low_eq_gc:
  forall ℓ_adv ℓ φ ψ Γ Σ1 Σ2 m1 m2 h1_pc h2_pc h1_not_pc h2_not_pc h1_gc h2_gc
    H1 H1' H2 H2',
    ℓ ⊑ ℓ_adv ->
    (forall loc ℓ μ, heap_lookup loc h1_gc = Some (ℓ, μ) ->
                ~ reach m1 ([[h1_pc ⊎ h1_not_pc, H1] ⊎ h1_gc, H1']) loc) ->
    (forall loc ℓ μ, heap_lookup loc h2_gc = Some (ℓ, μ) ->
                ~ reach m2 ([[h2_pc ⊎ h2_not_pc, H2] ⊎ h2_gc, H2']) loc) ->
    (forall loc ℓ μ, heap_lookup loc h2_gc = Some (ℓ, μ) -> right ψ loc = None) ->
    (forall loc loc', left ψ loc = Some loc' -> left φ loc = Some loc') ->
    (forall loc, heap_lookup loc h2_gc = None -> right φ loc = right ψ loc) ->
    (forall loc1 loc2 ℓ, left φ loc1 = Some loc2 ->
                    (exists μ, heap_lookup loc1 h1_gc = Some (ℓ, μ)) <->
                    (exists ν, heap_lookup loc2 h2_gc = Some (ℓ, ν))) ->
    levels_satisfy h1_pc (eq ℓ) ->
    levels_satisfy h2_pc (eq ℓ) ->
    levels_satisfy h1_gc (eq ℓ) ->
    levels_satisfy h2_gc (eq ℓ) ->
    levels_satisfy h1_not_pc (compose not (eq ℓ)) ->
    levels_satisfy h2_not_pc (compose not (eq ℓ)) ->
    wf_bijection ℓ_adv φ Γ Σ1 m1 ([[h1_pc ⊎ h1_not_pc, H1] ⊎ h1_gc, H1']) ->
    wf_bijection ℓ_adv (inverse φ) Γ Σ2 m2 ([[h2_pc ⊎ h2_not_pc, H2] ⊎ h2_gc, H2']) ->
    wf_bijection ℓ_adv ψ Γ Σ1 m1 ([h1_pc ⊎ h1_not_pc, H1]) ->
    wf_bijection ℓ_adv (inverse ψ) Γ Σ2 m2 ([h2_pc ⊎ h2_not_pc, H2]) ->
    dangling_pointer_free m1 ([[h1_pc ⊎ h1_not_pc, H1] ⊎ h1_gc, H1']) ->
    dangling_pointer_free m2 ([[h2_pc ⊎ h2_not_pc, H2] ⊎ h2_gc, H2']) ->
    state_low_eq ℓ_adv φ m1 ([[h1_pc ⊎ h1_not_pc, H1] ⊎ h1_gc, H1']) m2
                 ([[h2_pc ⊎ h2_not_pc, H2] ⊎ h2_gc, H2']) Γ Σ1 Σ2 ->
    state_low_eq ℓ_adv ψ m1 ([h1_pc ⊎ h1_not_pc, H1]) m2 ([h2_pc ⊎ h2_not_pc, H2]) Γ
                 Σ1 Σ2.
Proof.
  intros.
  eapply StateLowEq; try solve[invert_state_low_eq; eauto 2].
  - eauto.
  - unfolds.
    intros.
    assert (left φ l1 = Some l2) by eauto 2.
    splits.
    + intros.
      super_destruct.
      assert (low ℓ_adv Γ Σ1 m1 ([[h1_pc ⊎ h1_not_pc, H1] ⊎ h1_gc, H1']) l1)
        by eauto 2.
      assert ((exists ν, heap_lookup l2 ([[h2_pc ⊎ h2_not_pc, H2] ⊎ h2_gc, H2'])
                    = Some (ℓ0, ν)) /\
              low ℓ_adv Γ Σ2 m2 ([[h2_pc ⊎ h2_not_pc, H2] ⊎ h2_gc, H2']) l2).
      {
        invert_state_low_eq.
        match goal with
          [H: context[low_heap_domain_eq] |- _] =>
          eapply H; eauto
        end.
      }
      super_destruct; subst.
      destruct (disjoint_union_heap_lookup2 _ _ _ _ _ _ H26).
      * splits~; eauto 2.
        dependent destruction H27.
        {
          eapply LowReachable.
          eapply low_reach_subset_if; eauto.
        }
        {
          rewrite_inj.
          eauto 3.
        }
      * assert (right ψ l2 = None) by eauto 2.
        assert (right ψ l2 = Some l1) by (destruct ψ; eauto 2).
        congruence.
    + intros.
      super_destruct.
      assert (low ℓ_adv Γ Σ2 m2 ([[h2_pc ⊎ h2_not_pc, H2] ⊎ h2_gc, H2']) l2)
        by eauto 2.
      assert ((exists ν, heap_lookup l1 ([[h1_pc ⊎ h1_not_pc, H1] ⊎ h1_gc, H1'])
                    = Some (ℓ0, ν)) /\
              low ℓ_adv Γ Σ1 m1 ([[h1_pc ⊎ h1_not_pc, H1] ⊎ h1_gc, H1']) l1).
      {
        invert_state_low_eq.
        match goal with
          [H: context[low_heap_domain_eq] |- _] =>
          eapply H; eauto
        end.
      }
      super_destruct; subst.
      splits~; eauto 2.
      destruct (disjoint_union_heap_lookup2 _ _ _ _ _ _ H26).
      * eauto.
      * assert (exists ν, heap_lookup l2 h2_gc = Some (ℓ0, ν)).
        {
          eapply H7; eauto.
        }
        super_destruct; subst.
        assert (right ψ l2 = None) by eauto 2.
        assert (right ψ l2 = Some l1) by (destruct ψ; eauto).
        congruence.
  - unfolds.
    intros.
    assert (val_low_eq ℓ_adv τ v1 v2 φ) by (invert_state_low_eq; eauto 2).
    invert_val_low_eq; eauto 3.
    assert (reach m2 ([[h2_pc ⊎ h2_not_pc, H2] ⊎ h2_gc, H2']) l2) by eauto 2.
    assert (heap_lookup l2 h2_gc = None).
    {
      destruct (heap_lookup l2 h2_gc) eqn:H_l2; eauto.
      destruct p.
      assert (~ reach m2 ([[h2_pc ⊎ h2_not_pc, H2] ⊎ h2_gc, H2']) l2) by eauto 2.
      contradiction.
    }
    assert (right φ l2 = right ψ l2) by eauto 2.
    assert (right φ l2 = Some l1) by (destruct φ; eauto).
    assert (right ψ l2 = Some l1) by congruence.
    assert (left ψ l1 = Some l2) by (destruct ψ; eauto).
    eauto 2.
  - unfolds.
    intros.
    assert (left φ loc1 = Some loc2) by eauto 2.
    assert (low ℓ_adv Γ Σ1 m1 ([[h1_pc ⊎ h1_not_pc, H1] ⊎ h1_gc, H1']) loc1)
      by eauto 2.
    assert (low ℓ_adv Γ Σ2 m2 ([[h2_pc ⊎ h2_not_pc, H2] ⊎ h2_gc, H2']) loc2)
      by eauto 2.
    assert (heapval_low_eq ℓ_adv τ loc1 loc2 m1 m2
                           ([[h1_pc ⊎ h1_not_pc, H1] ⊎ h1_gc, H1'])
                           ([[h2_pc ⊎ h2_not_pc, H2] ⊎ h2_gc, H2']) φ).
    {
      invert_state_low_eq.
      match goal with
        [H: context[heap_lookup_low_eq] |- _] =>
        solve[eapply H; eauto]
      end.
    }
    invert_heapval_low_eq.

    assert (heap_lookup loc1 ([h1_pc ⊎ h1_not_pc, H1]) = Some (ℓ0, μ)).
    {
      destruct (disjoint_union_heap_lookup2 _ _ _ _ _ _ H30).
      - eauto.
      - assert (exists ν, heap_lookup loc2 h2_gc = Some (ℓ0, ν)).
        {
          eapply H7; eauto.
        }
        super_destruct; subst.
        assert (right ψ loc2 = None) by eauto 2.
        assert (right ψ loc2 = Some loc1) by (destruct ψ; eauto).
        congruence.
    }

    assert (heap_lookup loc2 ([h2_pc ⊎ h2_not_pc, H2]) = Some (ℓ0, ν)).
    {
      destruct (disjoint_union_heap_lookup2 _ _ _ _ _ _ H31).
      - eauto.
      - assert (right ψ loc2 = None) by eauto 2.
        assert (right ψ loc2 = Some loc1) by (destruct ψ; eauto).
        congruence.
    }
    
    eapply HeapValLowEq; eauto 2.
    intros.
    assert (reach m1 ([[h1_pc ⊎ h1_not_pc, H1] ⊎ h1_gc, H1']) loc1) by eauto 2.
    assert (reach m2 ([[h2_pc ⊎ h2_not_pc, H2] ⊎ h2_gc, H2']) loc2) by eauto 2.
    assert (val_low_eq ℓ_adv (SecType τ0 ℓ_τ) u v φ) by eauto 2.
    invert_val_low_eq; eauto 3.
    assert (left ψ l1 = Some l2).
    {
      assert (reach m2 ([[h2_pc ⊎ h2_not_pc, H2] ⊎ h2_gc, H2']) l2) by eauto 2.
      assert (heap_lookup l2 h2_gc = None).
      {
        destruct (heap_lookup l2 h2_gc) eqn:H_l2; eauto.
        destruct p.
        assert (~ reach m2 ([[h2_pc ⊎ h2_not_pc, H2] ⊎ h2_gc, H2']) l2) by eauto 2.
        contradiction.
      }
      assert (right φ l2 = right ψ l2) by eauto 2.
      assert (right φ l2 = Some l1) by (destruct φ; eauto).
      assert (right ψ l2 = Some l1) by congruence.
      destruct ψ; eauto.
    }
    eauto 2.
  - unfolds.
    intros.
    splits.
    + intros.
      assert (low_reach ℓ_adv Γ Σ1 m1 ([[h1_pc ⊎ h1_not_pc, H1] ⊎ h1_gc, H1']) loc) by eauto 2.
      assert (low_reach ℓ_adv Γ Σ2 m2 ([[h2_pc ⊎ h2_not_pc, H2] ⊎ h2_gc, H2']) loc').
      {
        invert_state_low_eq.
        match goal with
          [H: context[low_reach_NI] |- _] =>
          solve[eapply H; eauto]
        end.
      }
      eauto 3.
    + intros.
      assert (low_reach ℓ_adv Γ Σ2 m2 ([[h2_pc ⊎ h2_not_pc, H2] ⊎ h2_gc, H2']) loc') by eauto 2.
      assert (low_reach ℓ_adv Γ Σ1 m1 ([[h1_pc ⊎ h1_not_pc, H1] ⊎ h1_gc, H1']) loc).
      {
        invert_state_low_eq.
        match goal with
          [H: context[low_reach_NI] |- _] =>
          solve[eapply H; eauto]
        end.
      }
      eauto 3.
  - intros.
    assert (size l ([[h1_pc ⊎ h1_not_pc, H1] ⊎ h1_gc, H1']) = size l ([[h2_pc ⊎ h2_not_pc, H2] ⊎ h2_gc, H2'])).
    {
      invert_state_low_eq; eauto.
    }
    rewrite -> (size_heap_distr l ([h1_pc ⊎ h1_not_pc, H1]) h1_gc H1') in *.
    rewrite -> (size_heap_distr l ([h2_pc ⊎ h2_not_pc, H2]) h2_gc H2') in *.
    assert (size l h1_gc = size l h2_gc).
    {
      eapply implies_same_size with (φ := φ).
      - intros.
        super_destruct; subst.
        destruct (length_of loc2 h2_gc) eqn:H_loc2.
        + assert (exists l μ, heap_lookup loc2 h2_gc = Some (l, μ)).
          {
            eapply length_of_lookup_correspondance; eauto.
          }
          super_destruct; subst.
          assert (ℓ = l0) by eauto 2; subst.
          assert (heap_lookup loc2 ([[h2_pc ⊎ h2_not_pc, H2] ⊎ h2_gc, H2'])
                  = Some (l0, μ)).
          {
            rewrite -> disjoint_union_sym by solve[eauto 2].
            eapply disjoint_union_heap_lookup.
            eauto.
          }
          assert (exists ν, heap_lookup loc1 ([[h1_pc ⊎ h1_not_pc, H1] ⊎ h1_gc, H1'])
                       = Some (l0, ν)).
          {
            invert_state_low_eq.
            match goal with
              [H: context[low_heap_domain_eq] |- _] =>
              solve[eapply H; eauto]
            end.
          }
          super_destruct; subst.
          assert (length_of loc1 ([[h1_pc ⊎ h1_not_pc, H1] ⊎ h1_gc, H1']) =
                  length_of loc2 ([[h2_pc ⊎ h2_not_pc, H2] ⊎ h2_gc, H2']))
            by (invert_state_low_eq; eauto 2).
          assert (length_of loc2 ([[h2_pc ⊎ h2_not_pc, H2] ⊎ h2_gc, H2']) = Some n).
          {
            rewrite -> disjoint_union_sym by solve[eauto 2].
            eapply disjoint_union_length_of.
            eauto.
          }
          rewrite -> H28 in *.
          destruct (length_of loc1 h1_gc) eqn:H_loc1.
          * assert (length_of loc1 ([[h1_pc ⊎ h1_not_pc, H1] ⊎ h1_gc, H1']) = Some n0).
            {
              rewrite -> disjoint_union_sym by solve[eauto 2].
              eapply disjoint_union_length_of.
              eauto.
            }
            congruence.
          * assert (exists μ, heap_lookup loc1 h1_gc = Some (l0, μ)).
            {
              eapply H7; eauto.
            }
            super_destruct; subst.
            assert (exists n, length_of loc1 h1_gc = Some n).
            {
              eapply length_of_lookup_correspondance; eauto.
            }
            super_destruct.
            congruence.
        + destruct (length_of loc1 h1_gc) eqn:H_loc1; eauto 2.
          assert (exists ℓ μ, heap_lookup loc1 h1_gc = Some (ℓ, μ)).
          {
            eapply length_of_lookup_correspondance; eauto.
          }
          super_destruct; subst.
          assert (exists ν, heap_lookup loc2 h2_gc = Some (ℓ0, ν)).
          {
            eapply H7; eauto.
          }
          super_destruct; subst.
          assert (exists n, length_of loc2 h2_gc = Some n).
          {
            eapply length_of_lookup_correspondance; eauto.
          }
          super_destruct; congruence.
      - intros.
        assert (exists ℓ μ, heap_lookup loc h1_gc = Some (ℓ, μ)).
        {
          eapply length_of_lookup_correspondance; eauto 2.
        }
        super_destruct; subst.
        assert (ℓ = ℓ0) by eauto 2.
        subst.
        eapply H14; eauto 2.
        eapply LowHeapLevel; eauto 2.
        rewrite -> disjoint_union_sym.
        eauto 2.
      - intros.
        assert (exists ℓ μ, heap_lookup loc h2_gc = Some (ℓ, μ)).
        {
          eapply length_of_lookup_correspondance; eauto 2.
        }
        super_destruct; subst.
        assert (ℓ = ℓ0) by eauto 2.
        subst.
        cut (exists loc', left (inverse φ) loc = Some loc').
        {
          intros.
          super_destruct; subst.
          destruct φ; eauto.
        }
        {
          eapply H15; eauto 2.
          eapply LowHeapLevel; eauto 2.
          rewrite -> disjoint_union_sym.
          eauto 2.
        }
    }
    omega.        
  - intros.
    assert (heap_lookup loc ([[h1_pc ⊎ h1_not_pc, H1] ⊎ h1_gc, H1']) = Some (l, μ))
      by eauto 2.
    assert (heap_lookup loc' ([[h2_pc ⊎ h2_not_pc, H2] ⊎ h2_gc, H2']) = Some (l, ν))
      by eauto 2.
    assert (left φ loc = Some loc') by eauto 2.
    assert (length_of loc ([[h1_pc ⊎ h1_not_pc, H1] ⊎ h1_gc, H1']) =
            length_of loc' ([[h2_pc ⊎ h2_not_pc, H2] ⊎ h2_gc, H2'])).
    {
      invert_state_low_eq.
      eauto.
    }
    assert (length_of loc ([h1_pc ⊎ h1_not_pc, H1]) = length_of loc ([[h1_pc ⊎ h1_not_pc, H1] ⊎ h1_gc, H1'])).
    {
      destruct (length_of loc ([h1_pc ⊎ h1_not_pc, H1])) eqn:H_loc.
      - symmetry.
        eapply disjoint_union_length_of.
        eauto.
      - destruct (length_of loc ([[h1_pc ⊎ h1_not_pc, H1] ⊎ h1_gc, H1']))
                 eqn:H_loc'; eauto.
        symmetry in H24.
        assert (exists n, length_of loc ([h1_pc ⊎ h1_not_pc, H1]) = Some n).
        {
          eapply length_of_lookup_correspondance; eauto.
        }
        super_destruct; congruence.
    }
    assert (length_of loc' ([h2_pc ⊎ h2_not_pc, H2]) = length_of loc' ([[h2_pc ⊎ h2_not_pc, H2] ⊎ h2_gc, H2'])).
    {
      destruct (length_of loc' ([h2_pc ⊎ h2_not_pc, H2])) eqn:H_loc.
      - symmetry.
        eapply disjoint_union_length_of.
        eauto.
      - destruct (length_of loc' ([[h2_pc ⊎ h2_not_pc, H2] ⊎ h2_gc, H2']))
                 eqn:H_loc'; eauto.
        assert (exists n, length_of loc' ([h2_pc ⊎ h2_not_pc, H2]) = Some n).
        {
          eapply length_of_lookup_correspondance; eauto.
        }
        super_destruct; congruence.
    }
    congruence.
Qed.

Lemma partition_heap:
  forall (P : loc -> Prop)
    (DecP: forall loc, {P loc} + {~ P loc})
    (h : Heap),
    { h' : Heap &
           { h1 : Heap &
                  { h2 : Heap &
                         { H : disjoint h1 h2 &
                               h' = ([h1 ⊎ h2 , H]) /\
                               (forall loc ℓ μ, heap_lookup loc h1 = Some (ℓ, μ) ->
                                           heap_lookup loc h = Some (ℓ, μ)) /\
                               (forall loc ℓ μ, heap_lookup loc h2 = Some (ℓ, μ) ->
                                           heap_lookup loc h = Some (ℓ, μ)) /\
                               (forall loc ℓ μ, heap_lookup loc h = Some (ℓ, μ) ->
                                           heap_lookup loc h1 = Some (ℓ, μ) \/
                                           heap_lookup loc h2 = Some (ℓ, μ)) /\
                               (forall loc ℓ μ, heap_lookup loc h1 = Some (ℓ, μ) -> P loc) /\
                               (forall loc ℓ μ, heap_lookup loc h2 = Some (ℓ, μ) -> ~ P loc) /\
                               (forall l, size l h1 + size l h2 = size l h)
                               
    } } } }.

Proof.
  intros.
  induction h using heap_rec; intros.
  - exists emptyHeap.
    exists emptyHeap emptyHeap.
    exists (disjoint_empty_heap emptyHeap).
    splits~.
    + intros.
      assert (heap_lookup loc emptyHeap = None) by eauto 2.
      congruence.
    + intros.
      assert (heap_lookup loc emptyHeap = None) by eauto 2.
      congruence.
    + intros.
      rewrite -> empty_heap_has_size_0.
      omega.
  - super_destruct; subst.
    rename x0 into h1'.
    rename x1 into h2'.
    rename x2 into H'.
    destruct (DecP loc).
    + assert (heap_lookup loc h1' = None).
      {
        destruct (heap_lookup loc h1') eqn:H_loc; try reflexivity.
        destruct p0.
        assert (heap_lookup loc h = Some (l0, l1)) by eauto 2.
        congruence.
      }
      assert (size l h1' + n <= maxsize l h1').
      {
        assert (size l h1' + size l h2' = size l h) by eauto 2.
        rewrite <- (constant_maxsize h).
        omega.
      }
      assert (disjoint (extend_heap v loc l n h1' H H8) h2') as H1'.
      {
        eapply disjoint_implies_disjoint_extend; eauto 2.
        destruct (heap_lookup loc h2') eqn:H_loc; try reflexivity.
        destruct p0.
        assert (~ P loc) by eauto 2.
        contradiction.
      }
      exists ([extend_heap v loc l n h1' H H8 ⊎ h2', H1']).
      exists (extend_heap v loc l n h1' H H8).
      exists h2'.
      exists H1'.
      splits~; intros.
      * 
        destruct (decide (loc0 = loc)); subst.
        {
          apply_heap_lookup_extend_eq.
          rewrite_inj.
          remember_simple (heap_lookup_extend_eq loc l n v h H1 H2).
          super_destruct; subst.
          assert (μ0 = μ).
          {
            eapply lookupfunc_extensionality; congruence.
          }
          subst.
          eauto 2.
        }
        {
          repeat rewrite -> heap_lookup_extend_neq in * by solve[eauto 2].
          eauto 2.
        }
      * assert (~ P loc0) by eauto 2.
        assert (loc0 <> loc) by congruence.
        rewrite -> heap_lookup_extend_neq by solve[eauto 2].
        eauto 2.
      * destruct (decide (loc0 = loc)); subst.
        {
          left.
          remember_simple (heap_lookup_extend_eq loc l n v h H1 H2).
          super_destruct'; subst.
          rewrite_inj.
          remember_simple (heap_lookup_extend_eq loc l n v h1' H H8).
          super_destruct'; subst.
          assert (μ0 = μ).
          {
            eapply lookupfunc_extensionality; congruence.
          }
          subst.
          eauto 2.
        }
        {
          repeat rewrite -> heap_lookup_extend_neq in * by solve[eauto 2].
          eauto 2.
        }
      * destruct (decide (loc0 = loc)); subst.
        {
          eauto 2.
        }
        {
          rewrite -> heap_lookup_extend_neq in * by solve[eauto 2].
          eauto 2.
        }
      * destruct (T_dec l0 l).
        {
          subst.
          repeat rewrite -> size_extend_heap_eq_level.
          - assert (size l h1' + size l h2' = size l h) by eauto 2.
            omega.
        }
        {
          repeat rewrite -> size_extend_heap_neq_level; eauto 2.
        }
    + assert (heap_lookup loc h2' = None).
      {
        destruct (heap_lookup loc h2') eqn:H_loc; try reflexivity.
        destruct p.
        assert (heap_lookup loc h = Some (l0, l1)) by eauto 2.
        congruence.
      }
      assert (size l h2' + n <= maxsize l h2').
      {
        assert (size l h1' + size l h2' = size l h) by eauto 2.
        rewrite <- (constant_maxsize h).
        omega.
      }
      assert (disjoint h1' (extend_heap v loc l n h2' H H8)) as H1'.
      {
        eapply disjoint_sym.
        eapply disjoint_sym in H'.
        eapply disjoint_implies_disjoint_extend; eauto 2.
        destruct (heap_lookup loc h1') eqn:H_loc; try reflexivity.
        destruct p.
        assert (P loc) by eauto 2.
        contradiction.
      }
      exists ([h1' ⊎ (extend_heap v loc l n h2' H H8), H1']).
      exists h1'.
      exists (extend_heap v loc l n h2' H H8).
      exists H1'.
      splits~; intros.
      * assert (P loc0) by eauto 2.
        assert (loc0 <> loc) by congruence.
        rewrite -> heap_lookup_extend_neq by solve[eauto 2].
        eauto 2.
      * assert (size l h2' + n <= maxsize l h2').
        {
          assert (size l h1' + size l h2' = size l h) by eauto 2.
          rewrite <- (constant_maxsize h).
          omega.
        }
        destruct (decide (loc0 = loc)); subst.
        {
          apply_heap_lookup_extend_eq.
          rewrite_inj.
          remember_simple (heap_lookup_extend_eq loc l n v h H1 H2).
          super_destruct; subst.
          assert (μ0 = μ).
          {
            eapply lookupfunc_extensionality; congruence.
          }
          subst.
          eauto 2.
        }
        {
          repeat rewrite -> heap_lookup_extend_neq in * by solve[eauto 2].
          eauto 2.
        }
      * destruct (decide (loc0 = loc)); subst.
        {
          right.
          remember_simple (heap_lookup_extend_eq loc l n v h H1 H2).
          super_destruct'; subst.
          rewrite_inj.
          remember_simple (heap_lookup_extend_eq loc l n v h2' H H8).
          super_destruct'; subst.
          assert (μ0 = μ).
          {
            eapply lookupfunc_extensionality; congruence.
          }
          subst.
          eauto 2.
        }
        {
          repeat rewrite -> heap_lookup_extend_neq in * by solve[eauto 2].
          eauto 2.
        }
      * destruct (decide (loc0 = loc)); subst.
        {
          eauto 2.
        }
        {
          rewrite -> heap_lookup_extend_neq in * by solve[eauto 2].
          eauto 2.
        }
      * destruct (T_dec l0 l).
        {
          subst.
          repeat rewrite -> size_extend_heap_eq_level.
          - assert (size l h1' + size l h2' = size l h) by eauto 2.
            omega.
        }
        {
          repeat rewrite -> size_extend_heap_neq_level; eauto 2.
        }
Qed.

Lemma gc_noninterference:
  forall ℓ_adv φ m1 m1' h1 h1' m2 h2 Γ Σ1 Σ2 c c' pc pc1' t1 t1' Σ1'
    h1_gc h1_pc h1_not_pc δ H1 H2 H3,
    wf_bijection ℓ_adv φ Γ Σ1 m1 h1 ->
    wf_bijection ℓ_adv (inverse φ) Γ Σ2 m2 h2 ->
    state_low_eq ℓ_adv φ m1 h1 m2 h2 Γ Σ1 Σ2 ->
    pc ⊑ ℓ_adv ->
    wf_tenv Γ m1 ->
    wf_tenv Γ m2 ->
    wf_stenv Σ1 h1 ->
    wf_stenv Σ2 h2 ->
    heap_level_bound Γ m1 h1 Σ1 ->
    heap_level_bound Γ m2 h2 Σ2 ->
    dangling_pointer_free m1 h1 ->
    dangling_pointer_free m2 h2 ->
    @gc_occurred_no_ex c c' pc pc1' m1 m1' h1 h1' t1 t1' Σ1 Σ1'
                      h1_gc h1_pc h1_not_pc δ H1 H2 H3 ->
    exists ψ m2' h2' Σ2' t2' pc2' h2_gc h2_pc h2_not_pc, exists H1' H2' H3',
      @gc_occurred_no_ex c c' pc pc2' m2 m2' h2 h2' t1 t2' Σ2 Σ2'
                          h2_gc h2_pc h2_not_pc δ H1' H2' H3' /\
      wf_bijection ℓ_adv ψ Γ Σ1' m1' h1' /\
      wf_bijection ℓ_adv (inverse ψ) Γ Σ2' m2' h2' /\
      state_low_eq ℓ_adv ψ m1' h1' m2' h2' Γ Σ1' Σ2'.
Proof.
  intros.
  unfold gc_occurred_no_ex in * |-.
  super_destruct; subst.
  assert (loc -> forall ℓ : T, {ℓ = pc1'} + {ℓ <> pc1'}) as H'.
  {
    intros _ ℓ.
    eapply T_dec; eauto 2.
  }
  remember_simple (filter_heap (fun _ ℓ => ℓ = pc1') H' h2).
  clear H'.
  super_destruct'; subst.
  rename h' into h2_pc_gc.
  assert ((forall loc0 : loc,
              {(exists loc' ℓ μ,
                   left φ loc' = Some loc0 /\ heap_lookup loc' h1_pc = Some (ℓ, μ))} +
              {~
                 (exists loc' ℓ μ,
                     left φ loc' = Some loc0 /\ heap_lookup loc' h1_pc = Some (ℓ, μ))}))
         as H'.
  {
    intros.
    destruct (right φ loc0) eqn:H_loc0.
    - assert (left φ l = Some loc0) by (destruct φ; eauto 2).
      destruct (heap_lookup l h1_pc) eqn:H_l.
      + destruct p.
        left; eauto.
      + right.
        intro.
        super_destruct; subst.
        assert (right φ loc0 = Some loc') by (destruct φ; eauto 2).
        congruence.
    - right.
      intro.
      super_destruct; subst.
      assert (right φ loc0 = Some loc') by (destruct φ; eauto 2).
      congruence.        
  }            
  remember_simple (partition_heap (fun loc =>
                                     exists loc' ℓ μ, left φ loc' = Some loc /\
                                                 heap_lookup loc' h1_pc = Some (ℓ, μ))
                                  H' h2_pc_gc).
  super_destruct; subst.
  rename x0 into h2_pc.
  rename x1 into h2_gc.
  
  assert (forall loc1 loc2 ℓ μ,
             left φ loc1 = Some loc2 ->
             heap_lookup loc1 h1_gc = Some (ℓ, μ) ->
             exists ν, heap_lookup loc2 h2_gc = Some (ℓ, ν)).
  {
    intros.
    assert (pc1' = ℓ) by eauto 2.
    subst.
    assert (~ reach m2 h2 loc2).
    {
      assert (~ low_reach ℓ_adv Γ Σ2 m2 h2 loc2).
      {
        assert (~ reach m1' ([[h1_pc ⊎ h1_not_pc, H2] ⊎ h1_gc, H1]) loc1) by eauto 2.
        assert (~ low_reach ℓ_adv Γ Σ1' m1' ([[h1_pc ⊎ h1_not_pc, H2] ⊎ h1_gc, H1]) loc1).
        {
          intro; subst.
          eauto 3.
        }
        intro.
        invert_state_low_eq.
        assert (low_reach ℓ_adv Γ Σ1' m1' ([[h1_pc ⊎ h1_not_pc, H2] ⊎ h1_gc, H1]) loc1).
        {
          match goal with
            [H: context[low_reach_NI] |- _] =>
            eapply H; eauto 2
          end.
        }
        eauto 2.
      }
      intro.
      assert (exists μ, heap_lookup loc2 h2 = Some (ℓ, μ)).
      {
        invert_state_low_eq.
        match goal with
          [H: context[low_heap_domain_eq] |- _] =>
          eapply H
        end.
        - eauto 2.
        - splits; eauto 2.
          exists μ.
          rewrite -> disjoint_union_sym.
          eapply disjoint_union_heap_lookup; eauto 2.
      }
      super_destruct'; subst.
      assert (low_reach ℓ_adv Γ Σ2 m2 h2 loc2).
      {
        eapply low_reach_adequacy; eauto 2.
      }
      eauto 2.
    }
    
    assert (heap_lookup loc1 ([[h1_pc ⊎ h1_not_pc, H2] ⊎ h1_gc, H1]) = Some (ℓ, μ)).
    {
      rewrite -> disjoint_union_sym.
      eapply disjoint_union_heap_lookup; eauto 2.
    }
    assert (exists ν, heap_lookup loc2 h2 = Some (ℓ, ν)).
    {
      invert_state_low_eq.
      match goal with
        [H: context[low_heap_domain_eq] |- _] =>
        solve[eapply H; eauto 4]
      end.
    }
    super_destruct'; subst.
    exists ν.
    assert (heap_lookup loc2 h2_pc_gc = Some (ℓ, ν)) by eauto 2.
    remember_simple (H29 _ _ _ H37).
    destruct H38; eauto 2.
    remember_simple (H30 _ _ _ H38).
    super_destruct'; subst.
    assert (loc1 = loc').
    {
      assert (right φ loc2 = Some loc') by (destruct φ; eauto 2).
      assert (right φ loc2 = Some loc1) by (destruct φ; eauto 2).
      congruence.
    }
    subst.
    assert (heap_lookup loc' h1_pc = None).
    {
      match goal with
        [H: disjoint h1_pc h1_gc |- _] =>
        solve[eapply H; eauto]
      end.
    }
    congruence.
  }
  
  assert (forall loc1 loc2 ℓ μ,
             left φ loc1 = Some loc2 ->
             heap_lookup loc1 h1_pc = Some (ℓ, μ) ->
             exists ν, heap_lookup loc2 h2_pc = Some (ℓ, ν)).
  {
    intros.
    assert (pc1' = ℓ) by eauto 2.
    subst.
    assert (exists ν, heap_lookup loc2 h2 = Some (ℓ, ν)).
    {
      assert (heap_lookup loc1 ([[h1_pc ⊎ h1_not_pc, H2] ⊎ h1_gc, H1]) = Some (ℓ, μ)).
      {
        eauto 3.
      }
      invert_state_low_eq.
      match goal with
        [H: context[low_heap_domain_eq] |- _] =>
        solve[eapply H; eauto 4]
      end.
    }
    super_destruct'; subst.
    assert (heap_lookup loc2 h2_pc_gc = Some (ℓ, ν)) by eauto 2.
    exists ν.
    remember_simple (H29 _ _ _ H36).
    destruct H37; eauto 2.
    remember_simple (H31 _ _ _ H37).
    assert (exists loc' ℓ μ,
               left φ loc' = Some loc2 /\ heap_lookup loc' h1_pc = Some (ℓ, μ)).
    {
      exists loc1 ℓ μ.
      splits*.
    }
    contradiction.
  }
  
  remember_simple (remove_gc'd_locations h2_gc φ).
  super_destruct; subst.
  exists ψ.
  exists m2.

  assert (forall l : level_proj1, {compose not (eq pc1') l} + {~ compose not (eq pc1') l}) as H''.
  {
    intros; destruct (T_dec pc1' l); subst; eauto 4.
  }
  remember_simple (levels_satisfy_exists (compose not (eq pc1')) H'' h2).
  clear H''.
  super_destruct; subst.
  rename h' into h2_not_pc.

  unfold compose in *.
  
  assert (disjoint h2_pc h2_not_pc).
  {
    unfolds.
    intros.
    splits; intros.
    - destruct (heap_lookup loc h2_not_pc) eqn:H_loc; try reflexivity.
      destruct p.
      assert (heap_lookup loc h2 = Some (ℓ, μ)) by eauto 3.
      assert (heap_lookup loc h2 = Some (l, l0)) by eauto 3.
      rewrite_inj.
      assert (pc1' <> l) by eauto 2.
      remember_simple (H30 _ _ _ H42).
      super_destruct; subst.
      assert (pc1' = ℓ) by eauto 2.
      subst.
      assert (heap_lookup loc' ([[h1_pc ⊎ h1_not_pc, H2] ⊎ h1_gc, H1]) = Some (ℓ, μ)).
      {
        eauto 3.
      }
      assert (exists ν, heap_lookup loc h2 = Some (ℓ, ν)).
      {
        invert_state_low_eq.
        match goal with
          [H: context[low_heap_domain_eq] |- _] =>
          solve[eapply H; eauto 4]
        end.
      }
      super_destruct; subst.
      congruence.
    - destruct (heap_lookup loc h2_pc) eqn:H_loc; try reflexivity.
      destruct p.
      assert (heap_lookup loc h2 = Some (ℓ, μ)) by eauto 2.
      assert (heap_lookup loc h2 = Some (l, l0)) by eauto 3.
      rewrite_inj.
      assert (pc1' <> l) by eauto 2.
      remember_simple (H30 _ _ _ H_loc).
      super_destruct; subst.
      assert (heap_lookup loc' ([[h1_pc ⊎ h1_not_pc, H2] ⊎ h1_gc, H1]) = Some (ℓ, μ))
        by eauto 3.
      assert (exists ν, heap_lookup loc h2 = Some (ℓ, ν)).
      {
        invert_state_low_eq.
        match goal with
          [H: context[low_heap_domain_eq] |- _] =>
          solve[eapply H; eauto 4]
        end.
      }
      super_destruct; subst.
      assert (pc1' = ℓ) by eauto 2.
      congruence.
  }
  exists ([h2_pc ⊎ h2_not_pc, H42]).

  exists Σ2.
  exists (t1 + δ).
  exists pc1'.
  exists h2_gc.
  exists h2_pc.
  exists h2_not_pc.

  assert (disjoint h2_gc h2_not_pc).
  {
    unfolds.
    intros.
    splits; intros.
    - destruct (heap_lookup loc h2_not_pc) eqn:H_loc; try reflexivity.
      destruct p.
      assert (heap_lookup loc h2 = Some (ℓ, μ)) by eauto 3.
      assert (heap_lookup loc h2 = Some (l, l0)) by eauto 3.
      rewrite_inj.
      assert (pc1' <> l) by eauto 2.
      assert (l = pc1') by eauto.
      subst.
      congruence.
    - assert (pc1' <> ℓ) by eauto 3.
      destruct (heap_lookup loc h2_gc) eqn:H_loc; try reflexivity.
      destruct p.
      assert (heap_lookup loc h2_pc_gc = Some (l, l0)) by eauto 2.
      assert (l = pc1') by eauto 2.
      subst.
      assert (heap_lookup loc h2 = Some (ℓ, μ)) by eauto 3.
      assert (heap_lookup loc h2 = Some (pc1', l0)) by eauto 3.
      congruence.
  }
  assert (disjoint ([h2_pc ⊎ h2_not_pc, H42]) h2_gc) by eauto 4.
  exists H44.
  exists H42.
  
  exists x2.
  assert (h2 = ([[h2_pc ⊎ h2_not_pc, H42] ⊎ h2_gc, H44])).
  {
    eapply heap_extensionality.
    intros.
    destruct (heap_lookup loc ([[h2_pc ⊎ h2_not_pc, H42] ⊎ h2_gc, H44])) eqn:H_loc.
    - destruct p.
      destruct_disjoint_heap_lookup.
      + destruct_disjoint_heap_lookup; eauto 3.
      + eauto 3.
    - destruct (heap_lookup loc h2) eqn:Hloc'; try reflexivity.
      destruct p.
      assert (heap_lookup loc h2_pc = None).
      {
        destruct (heap_lookup loc h2_pc) eqn:H_loc''; try reflexivity.
        destruct p.
        assert (heap_lookup loc ([[h2_pc ⊎ h2_not_pc, H42] ⊎ h2_gc, H44]) = Some (l1, l2)) by eauto 3.
        congruence.
      }
      assert (heap_lookup loc h2_gc = None).
      {
        destruct (heap_lookup loc h2_gc) eqn:H_loc''; try reflexivity.
        destruct p.
        assert (heap_lookup loc ([[h2_pc ⊎ h2_not_pc, H42] ⊎ h2_gc, H44]) = Some (l1, l2)).
        {
          rewrite -> disjoint_union_sym; eauto 3.
        }
        congruence.
      }
      assert (heap_lookup loc h2_not_pc = None).
      {
        destruct (heap_lookup loc h2_not_pc) eqn:H_loc''; try reflexivity.
        destruct p.
        assert (heap_lookup loc ([[h2_pc ⊎ h2_not_pc, H42] ⊎ h2_gc, H44]) = Some (l1, l2)).
        {
          eapply disjoint_union_heap_lookup.
          rewrite -> disjoint_union_sym; eauto 3.
        }
        congruence.
      }
      destruct (T_dec l pc1').
      + subst.
        assert (heap_lookup loc h2_pc_gc = Some (pc1', l0)) by eauto 2.
        remember_simple (H29 _ _ _ H48).
        destruct H49; congruence.
      + assert (pc1' <> l) by eauto 2.
        assert (heap_lookup loc h2_not_pc = Some (l, l0)) by eauto 2.
        congruence.
  }
  subst.

  assert (levels_satisfy h2_gc (eq pc1')).
  {
    unfolds.
    intros.
    assert (heap_lookup loc h2_pc_gc = Some (ℓ, μ)) by eauto 2.
    symmetry; eauto 2.
  }
  assert (levels_satisfy h2_pc (eq pc1')).
  {
    unfolds.
    intros.
    assert (heap_lookup loc h2_pc_gc = Some (ℓ, μ)) by eauto 2.
    symmetry; eauto 2.
  }
  
  assert (forall loc loc' ℓ,
             left φ loc = Some loc' ->
             (exists μ, heap_lookup loc h1_gc = Some (ℓ, μ)) <->
             (exists ν, heap_lookup loc' h2_gc = Some (ℓ, ν))).
  {
    intros.
    splits.
    - intros.
      super_destruct; subst.
      assert (ℓ = pc1') by (symmetry; eauto 2).
      subst.
      eauto.
    - intros.
      super_destruct'; subst.
      assert (pc1' = ℓ) by eauto 2.
      subst.
      remember_simple (H31 _ _ _ H48).
      assert (heap_lookup loc h1_pc = None).
      {
        destruct (heap_lookup loc h1_pc) eqn:H_loc.
        - destruct p.
          match goal with
            [H: ~ (exists _ _ _, _ /\ _) |- _] =>
            solve[contradict H; eauto]
          end.
        - reflexivity.
      }
      destruct (heap_lookup loc h1_gc) eqn:H_loc.
      + destruct p as [ℓ' μ'].
        assert (ℓ = ℓ') by eauto 2.
        subst.
        eauto 2.
       + assert (heap_lookup loc' h2_pc_gc = Some (ℓ, ν)) by eauto 2.
         assert (heap_lookup loc' ([[h2_pc ⊎ h2_not_pc, H42] ⊎ h2_gc, H44]) = Some (ℓ, ν)) by eauto 2.
         assert (exists μ, heap_lookup loc ([[h1_pc ⊎ h1_not_pc, H2] ⊎ h1_gc, H1]) = Some (ℓ, μ)).
         {
           invert_state_low_eq.
           match goal with
             [H: context[low_heap_domain_eq] |- _] =>
             solve[eapply H; eauto 4]
           end.
         }
         super_destruct'; subst.
         destruct_disjoint_heap_lookup; try congruence.
         destruct_disjoint_heap_lookup; try congruence.
         assert (ℓ <> ℓ) by eauto 2.
         congruence.
  }

  assert (forall loc loc' ℓ,
             left φ loc = Some loc' ->
             (exists μ, heap_lookup loc h1_pc = Some (ℓ, μ)) <->
             (exists ν, heap_lookup loc' h2_pc = Some (ℓ, ν))).
  {
    intros.
    splits; intros.
    - super_destruct'; subst.
      eauto 3.
    - super_destruct'; subst.
      remember_simple (H30 _ _ _ H49).
      super_destruct; subst.
      assert (loc = loc'0).
      {
        assert (right φ loc' = Some loc'0) by (destruct φ; eauto 2).
        assert (right φ loc' = Some loc) by (destruct φ; eauto 2).
        congruence.
      }
      subst.
      exists μ.
      assert (exists ν, heap_lookup loc' h2_pc = Some (ℓ0, ν)) by eauto 2.
      super_destruct; subst.
      congruence.
  }
  
  assert (forall loc ℓ μ,
             heap_lookup loc h2_gc = Some (ℓ, μ) ->
             ~ reach m2 ([[h2_pc ⊎ h2_not_pc, H42] ⊎ h2_gc, H44]) loc).
  {
    intros.
    intro.
    assert (pc1' = ℓ) by eauto 2.
    subst.
    assert (low_reach ℓ_adv Γ Σ2 m2 ([[h2_pc ⊎ h2_not_pc, H42] ⊎ h2_gc, H44]) loc).
    {
      eapply low_reach_adequacy; eauto 2.
      rewrite -> disjoint_union_sym.
      eauto 2.
    }
    assert (exists loc', left φ loc' = Some loc).
    {
      assert (exists loc', left (inverse φ) loc = Some loc') by eauto 3.
      super_destruct; destruct φ; eauto 3.
    }
    super_destruct; subst.
    assert (exists ν, heap_lookup loc' h1_gc = Some (ℓ, ν)).
    {
      match goal with
        [H: _ |- _] =>
        solve[eapply H; eauto]
      end.
    }
    super_destruct; subst.
    assert (low_reach ℓ_adv Γ Σ1' m1' ([[h1_pc ⊎ h1_not_pc, H2] ⊎ h1_gc, H1]) loc').
    {
      invert_state_low_eq.
      match goal with
        [H: context[low_reach_NI] |- _] =>
        solve[eapply H; eauto]
      end.
    }
    assert (~ reach m1' ([[h1_pc ⊎ h1_not_pc, H2] ⊎ h1_gc, H1]) loc') by eauto 2.
    eauto 3.
  }
  
  assert (([h2_pc ⊎ h2_gc, x2]) ⇝ (m2, δ) h2_pc).
  {
    eapply gc_axiom with (φ := φ) (m1 := m1') (h1 := [h1_pc ⊎ h1_gc, H3]) (h1' := h1_pc)
    ; eauto 2.
    - intros.
      splits; intros.
      + super_destruct'; subst.
        destruct_disjoint_heap_lookup.
        * assert (exists ν, heap_lookup loc2 h2_pc = Some (ℓ, ν)) by eauto 2.
          super_destruct; eauto.
        * assert (exists ν, heap_lookup loc2 h2_gc = Some (ℓ, ν)) by eauto 2.
          rewrite -> disjoint_union_sym.
          super_destruct; eauto.
      + super_destruct'; subst.
        destruct_disjoint_heap_lookup.
        * assert (exists ν, heap_lookup loc1 h1_pc = Some (ℓ, ν)).
          {
            eapply H48; eauto 2.
          }
          super_destruct; eauto.
        * assert (exists ν, heap_lookup loc1 h1_gc = Some (ℓ, ν)).
          {
            eapply H47; eauto 2.
          }
          rewrite -> disjoint_union_sym.
          super_destruct; eauto.
    - intros.
      assert (pc1' = ℓ).
      {
        destruct_disjoint_heap_lookup; eauto 2.
      }
      subst.
      assert (low ℓ_adv Γ Σ1' m1' ([[h1_pc ⊎ h1_not_pc, H2] ⊎ h1_gc, H1]) loc).
      {
        destruct_disjoint_heap_lookup.
        - eapply LowHeapLevel with (ℓ := ℓ) (μ := μ); eauto 2.
          do 2 eapply disjoint_union_heap_lookup.
          eauto 2.
        - eapply LowHeapLevel with (ℓ := ℓ) (μ := μ); eauto 2.
          rewrite -> disjoint_union_sym.
          eauto 2.
      }
      eauto 2.
    - intros.
      assert (pc1' = ℓ).
      {
        destruct_disjoint_heap_lookup; eauto 2.
      }
      subst.
      assert (low ℓ_adv Γ Σ2 m2 ([[h2_pc ⊎ h2_not_pc, H42] ⊎ h2_gc, H44]) loc).
      {
        destruct_disjoint_heap_lookup.
        - eapply LowHeapLevel with (ℓ := ℓ) (μ := μ); eauto 2.
          do 2 eapply disjoint_union_heap_lookup.
          eauto 2.
        - eapply LowHeapLevel with (ℓ := ℓ) (μ := μ); eauto 2.
          rewrite -> disjoint_union_sym.
          eauto 2.
      }
      assert (exists loc', left (inverse φ) loc = Some loc') by eauto 2.
      super_destruct.
      destruct φ; eauto.
  }

  assert (wf_bijection ℓ_adv ψ Γ Σ1' m1' ([h1_pc ⊎ h1_not_pc, H2])).
  {
    unfolds.
    intros.
    splits.
    + intros.
      super_destruct; subst.
      assert (left φ loc = Some loc') by eauto 2.
      assert (low ℓ_adv Γ Σ1' m1' ([[h1_pc ⊎ h1_not_pc, H2] ⊎ h1_gc, H1]) loc)
        by eauto 2.
      eapply low_subset_if with (ψ := ψ) (φ := φ); eauto.
    + intros.
      assert (low ℓ_adv Γ Σ1' m1' ([[h1_pc ⊎ h1_not_pc, H2] ⊎ h1_gc, H1]) loc)
        by eauto 2.
      assert (exists loc', left φ loc = Some loc') by eauto 2.
      super_destruct; subst.
      destruct (left ψ loc) eqn:H_loc; eauto.
      
      assert (heap_lookup loc h1_gc = None).
      {
        destruct (heap_lookup loc h1_gc) eqn:H'''; eauto.
        destruct p as [ℓ μ].
        destruct_low.
        - assert (~ reach m ([[h1_pc ⊎ h1_not_pc, H2] ⊎ h1_gc, H1]) loc) by eauto 2.
          exfalso; eauto 4.
        - assert (heap_lookup loc h1_gc = None).
          {
            assert (exists ℓ μ, heap_lookup loc ([h1_pc ⊎ h1_not_pc, H2]) = Some (ℓ, μ)).
            {
              destruct_low; eauto 4.
            }
            super_destruct'; subst.
            match goal with
              [H: disjoint ([_ ⊎ _, _]) _ |- _] =>
              solve[eapply H; eauto]
            end.
          }
          congruence.
      }
      assert (right ψ loc' = Some loc).
      {
        assert (right φ loc' = right ψ loc').
        {
          match goal with
            [H: context[right φ _ = right ψ _] |- _] =>
            eapply H
          end.
          destruct (heap_lookup loc' h2_gc) eqn:H_loc'; eauto.
          destruct p as [ℓ μ].
          assert (exists ν, heap_lookup loc h1_gc = Some (ℓ, ν)).
          {
            match goal with
              [H: forall _ _ _, left φ _ = Some _ -> _ <-> _ |- _] =>
              solve[eapply H; eauto]
            end.
          }
          super_destruct; congruence.
        }
        assert (right φ loc' = Some loc) by (destruct φ; eauto).
        rewrite_inj.
        assert (left ψ loc = Some loc') by (destruct ψ; eauto).
        congruence.
      }
      assert (left ψ loc = Some loc') by (destruct ψ; eauto).
      congruence.
  }

  assert (wf_bijection ℓ_adv (inverse ψ) Γ Σ2 m2 ([h2_pc ⊎ h2_not_pc, H42])).
  {
    unfolds.
    intros.
    splits.
    + intros.
      super_destruct; subst.
      assert (left (inverse φ) loc = Some loc').
      {
        rewrite -> left_inverse_is_right in *.
        _rewrite -> left_inverse_is_right in *.
        eauto.
      }
      assert (low ℓ_adv Γ Σ2 m2 ([[h2_pc ⊎ h2_not_pc, H42] ⊎ h2_gc, H44]) loc)
        by eauto 2.

      destruct_low.
      * eapply LowReachable.
        eapply low_reach_subset_if; eauto 2.
      * destruct_disjoint_heap_lookup.
        { eauto 2. }
        { assert (exists ν, heap_lookup loc' h1_gc = Some (ℓ, ν)).
          {
            match goal with
              [H: forall _ _ _, left _ _ = Some _ -> _ <-> _ |- _] =>
              solve[eapply H; destruct φ; eauto 2]
            end.
          }
          assert (right ψ loc = Some loc') by (destruct ψ; eauto).
          assert (right ψ loc = None) by eauto 2.
          congruence.
        }
    + intros.
      assert (low ℓ_adv Γ Σ2 m2 ([[h2_pc ⊎ h2_not_pc, H42] ⊎ h2_gc, H44]) loc)
        by eauto 2.
      assert (exists loc', left (inverse φ) loc = Some loc') by eauto 2.
      super_destruct; subst.
      destruct (left (inverse ψ) loc) eqn:H_loc; eauto.
      
      assert (heap_lookup loc h2_gc = None).
      {
        destruct (heap_lookup loc h2_gc) eqn:H'''; eauto.
        destruct p as [ℓ μ].
        destruct_low.
        - assert (~ reach m ([[h2_pc ⊎ h2_not_pc, H42] ⊎ h2_gc, H44]) loc) by eauto 2.
          exfalso; eauto 4.
        - assert (heap_lookup loc h2_gc = None).
          {
            assert (exists ℓ μ, heap_lookup loc ([h2_pc ⊎ h2_not_pc, H42]) = Some (ℓ, μ)).
            {
              destruct_low; eauto 4.
            }
            super_destruct'; subst.
            match goal with
              [H: disjoint ([_ ⊎ _, _]) _ |- _] =>
              solve[eapply H; eauto]
            end.
          }
          congruence.
      }
      assert (right ψ loc = Some loc').
      {
        assert (right φ loc = right ψ loc).
        {
          eauto.
        }
        assert (right φ loc = Some loc') by (destruct φ; eauto).
        rewrite_inj.
        assert (left ψ loc' = Some loc) by (destruct ψ; eauto).
        congruence.
      }
      assert (left (inverse ψ) loc = Some loc') by (destruct ψ; eauto).
      congruence.
  }

  
  splits.
  - unfold gc_occurred_no_ex.
    splits~.
    splits*.
  - eauto.    
  - eauto.
  - eapply state_low_eq_gc; eauto.
Qed.

Lemma preservation_many_steps:
    forall Γ Σ Σ' c1 pc1 m1 h1 t1 c2 pc2 m2 h2 t2 pc',
    wellformed_aux Γ Σ ⟨c1, pc1, m1, h1, t1⟩ pc' ->
    ⟨c1, pc1, m1, h1, t1⟩ ⇒ * (Γ, Σ, Σ') ⟨c2, pc2, m2, h2, t2⟩ ->
    wellformed_aux Γ Σ' ⟨c2, pc2, m2, h2, t2⟩ pc'.
Proof.
  intros.
  dependent induction H0.
  - assumption.
  - destruct cfg as [c pc m h t].
    assert (wellformed_aux Γ Σ' ⟨c, pc, m, h, t⟩ pc') by eauto 2 using preservation.
    eapply IHstepmany; eauto 2.
Qed.
Hint Resolve preservation_many_steps.

Lemma assign_step:
  forall c' pc pc' m m' h h' t t' Γ Σ Σ' x e,
    ⟨x ::= e, pc, m, h, t⟩ ⇒ (Γ, Σ, Σ') ⟨c', pc', m', h', t'⟩ ->
    (exists v, pc = pc' /\ c' = Stop /\ m' = extend_memory x v m /\ eval m e = Some v /\ Σ = Σ')
    \/ gc_occurred (x ::= e) c' pc pc' m m' h h' t t' Σ Σ'.
Proof.
  intros.
  invert_step.
  - left.
    revert v H14.
    induction e; intros.
    + unfold eval in *.
      rewrite_inj.
      exists (ValNum n).
      splits*.
    + unfold eval in *.
      rewrite_inj.
      exists v.
      splits*.
    + rewrite -> about_eval in * |-.
      destruct (eval m e1) eqn:H_e1; try discriminate.
      destruct (eval m e2) eqn:H_e2; try discriminate.
      remember_simple (IHe1 v0 eq_refl).
      remember_simple (IHe2 v1 eq_refl).
      super_destruct; subst.
      rewrite_inj.
      destruct v3; destruct v2; destruct o; try discriminate.
      * rewrite_inj.
        eexists; splits*.
        rewrite -> about_eval.
        rewrite -> H_e1, H_e2.
        reflexivity.
      * rewrite_inj.
        eexists; splits*.
        rewrite -> about_eval.
        rewrite -> H_e1, H_e2.
        reflexivity.
      * destruct v0; discriminate.
  - right.
    splits*.
    exists h2 h1_pc h1_not_pc δ.
    do 3 eexists.
    splits*.
Qed.
Hint Resolve assign_step.

Lemma assign_step_many:
  forall pc pc' m m' h h' t t' Γ Σ Σ' x e,
    ⟨x ::= e, pc, m, h, t⟩ ⇒ * (Γ, Σ, Σ') ⟨Stop, pc', m', h', t'⟩ ->
    exists v,
      pc = pc' /\ m' = extend_memory x v m /\ eval m e = Some v /\ Σ = Σ'.
Proof.
  intros.
  dependent induction H.
  - destruct cfg.
    remember_simple (assign_step H).
    super_destruct; subst.
    + invert_step.
      remember_simple (stop_takes_no_step_many_step H0).
      super_destruct; subst.
      exists v.
      splits~.
    + unfold gc_occurred in *.
      super_destruct; subst.
      eauto.
Qed.
Hint Resolve assign_step_many.

Lemma low_reach_extend:
  forall x loc1 loc2 m h Γ ℓ Σ,
    low_reach ℓ Γ Σ (extend_memory x (ValLoc loc1) m) h loc2 ->
    low_reach ℓ Γ Σ m h loc1 -> low_reach ℓ Γ Σ m h loc2.
Proof.
  intros.
  dependent induction H; eauto 3.
  destruct (decide (x = x0)); subst.
  - rewrite -> extend_memory_lookup_eq in *.
    rewrite_inj.
    eauto.
  - rewrite -> extend_memory_lookup_neq in * by solve[eauto].
    eapply LowReachMem; eauto 2.
Qed.
Hint Resolve low_reach_extend.

Lemma low_extend:
  forall x loc1 loc2 m h Γ ℓ Σ,
    low ℓ Γ Σ (extend_memory x (ValLoc loc1) m) h loc2 ->
    low_reach ℓ Γ Σ m h loc1 -> low ℓ Γ Σ m h loc2.
Proof.
  intros.
  destruct_low; eauto.
Qed.
Hint Resolve low_extend.

Lemma extend_memory_preserves_low_reach:
  forall ℓ Γ Σ1 Σ2 τ x loc1 loc2 loc1' loc2' φ m s h w,
    state_low_eq ℓ φ m h s w Γ Σ1 Σ2 ->
    Γ x = Some τ ->
    wf_tenv Γ m ->
    wf_tenv Γ s ->
    wf_stenv Σ1 h ->
    wf_stenv Σ2 w ->
    heap_level_bound Γ m h Σ1 ->
    heap_level_bound Γ s w Σ2 ->
    dangling_pointer_free m h ->
    dangling_pointer_free s w ->
    left φ loc1 = Some loc2 ->
    left φ loc1' = Some loc2' ->
    wf_bijection ℓ φ Γ Σ1 m h ->
    low_reach ℓ Γ Σ1 m h loc1 ->
    low_reach ℓ Γ Σ2 s w loc2 ->
    low_reach ℓ Γ Σ1 m h loc1' ->
    low_reach ℓ Γ Σ1 (m [x → ValLoc loc1']) h loc1 ->
    low_reach ℓ Γ Σ2 (s [x → ValLoc loc2']) w loc2.
Proof.
  intros.
  revert loc2 H9 H13.
  dependent induction H15; intros.
  - eapply LowReachMem.
    + eauto.
    + eauto.
    + destruct (decide (x = x0)); subst.
      * rewrite -> extend_memory_lookup_eq in *.
        rewrite_inj.
        reflexivity.
      * rewrite -> extend_memory_lookup_neq in * by solve[eauto].
        assert (exists u, memory_lookup s x0 = Some u).
        {
          invert_state_low_eq.
          match goal with
            [H: low_domain_eq _ _ _ _ |- _] =>
            edestruct H; eauto
          end.
        }
        destruct_exists.
        invert_state_low_eq.
        assert (val_low_eq ℓ_adv (SecType (Array τ0 ℓ_p) (l, ∘)) (ValLoc loc) u φ)
          by eauto.
        invert_val_low_eq.
        { exfalso; eauto. }
        { congruence. }
  - assert (low_reach ℓ_adv Γ Σ m h loc1) by eauto 2.
    assert (exists loc1'', left φ loc1 = Some loc1'' /\ Σ2 loc1'' = Some (SecType (Array τ0 ℓ_p) (l, ∘)) /\ low_reach ℓ_adv Γ Σ2 s w loc1'').
    {
      assert (exists loc1'', left φ loc1 = Some loc1'') by eauto.
      super_destruct; subst.
      exists loc1''.

      assert (Σ2 loc1'' = Some (SecType (Array τ0 ℓ_p) (l, ∘))).
      {
        eapply implies_same_store_typing;
          (invert_state_low_eq; eauto).
      }
      
      splits~.
      invert_state_low_eq.
      match goal with
        [H: context[low_reach_NI] |- _] =>
        solve[eapply H; eauto]
      end.
    }
    super_destruct; subst.
    assert (low_reach ℓ_adv Γ Σ2 (s [x → ValLoc loc2']) w loc1'')
      by eauto 2 using IHlow_reach.
    
    invert_state_low_eq.
    assert (low ℓ_adv Γ Σ m h loc1) by eauto 2.
    assert (low ℓ_adv Γ Σ2 s w loc1'') by eauto 2.
    assert (reach m h loc1) by eauto 2.
    assert (reach s w loc1'') by eauto 2.
    assert (exists ν, heap_lookup loc1'' w = Some (ℓ, ν)).
    {
      eapply H27; eauto.
    }
    super_destruct; subst.
    assert (lookup ν n = Some (ValLoc loc0)) by eauto 2 using bijection_implies_lookup.
    eapply LowReachHeap; eauto.
Qed.
Hint Resolve extend_memory_preserves_low_reach.

Lemma low_extend_with_num:
  forall ℓ_adv Γ Σ x n m h loc,
    low ℓ_adv Γ Σ (m [x → ValNum n]) h loc -> low ℓ_adv Γ Σ m h loc.
Proof.
  intros.
  destruct_low; eauto 3.
  eapply LowReachable; eauto using low_reach_extend_mem_with_num.
Qed.
Hint Resolve low_extend_with_num.

Lemma low_extend_mem_with_num2:
  forall ℓ Γ Σ m h loc x n l,
  wf_tenv Γ m ->
  Γ x = Some (SecType Int l) ->
  low ℓ Γ Σ m h loc -> low ℓ Γ Σ (m [x → ValNum n]) h loc.
Proof.
  intros.
  destruct_low; eauto 3 using low_reach_extend_mem_with_num2.
  Unshelve.
  - eauto.
  - eauto.
Qed.
Hint Resolve low_extend_mem_with_num2.

Lemma low_reach_in_extended_memory:
  forall ℓ_adv Γ Σ1 Σ2 m1 h1 m2 h2 x v1 v2 loc1 loc2 φ l ι t,
    state_low_eq ℓ_adv φ m1 h1 m2 h2 Γ Σ1 Σ2 ->
    Γ x = Some (SecType t (l, ι)) ->
    val_low_eq ℓ_adv (SecType t (l, ι)) v1 v2 φ ->
    wf_bijection ℓ_adv φ Γ Σ1 m1 h1 ->
    wf_bijection ℓ_adv (inverse φ) Γ Σ2 m2 h2 ->
    low_reach ℓ_adv Γ Σ1 (m1 [x → v1]) h1 loc1 ->
    dangling_pointer_free m1 h1 ->
    dangling_pointer_free m2 h2 ->
    wf_tenv Γ m1 ->
    wf_tenv Γ m2 ->
    wf_stenv Σ1 h1 ->
    wf_stenv Σ2 h2 ->
    left φ loc1 = Some loc2 ->
    (forall s ℓ', t = Array s ℓ' -> exists loc', v1 = ValLoc loc' /\
                                      (l ⊑ ℓ_adv -> low_reach ℓ_adv Γ Σ1 m1 h1 loc')) ->
    (t = Int -> exists n, v1 = ValNum n) ->
    low_reach ℓ_adv Γ Σ2 (m2 [x → v2]) h2 loc2.
Proof.
  intros.
  revert dependent loc2.
  dependent induction H4; intros.
  - destruct (decide (x = x0)); subst.
    + rewrite -> extend_memory_lookup_eq in *.
      rewrite_inj.
      invert_val_low_eq; try contradiction.
      rewrite_inj.
      eauto 2.
    + rewrite -> extend_memory_lookup_neq in * by solve[eauto].
      invert_state_low_eq.
      assert (memory_lookup m2 x0 = Some (ValLoc loc2)).
      {
        assert (exists u, memory_lookup m2 x0 = Some u).
        {
          match goal with
            [H: context[low_domain_eq] |- _] =>
            solve[eapply H; eauto]
          end.
        }
        super_destruct; subst.
        assert (val_low_eq ℓ_adv (SecType (Array τ ℓ_p) (l0, ∘)) (ValLoc loc) u φ) by eauto.
        invert_val_low_eq; try contradiction.
        congruence.
      }
      eapply LowReachMem with (x := x0); eauto.
      rewrite -> extend_memory_lookup_neq by solve[eauto].
      eauto.
  - assert (low_reach ℓ_adv Γ Σ m1 h loc1).
    {
      destruct t.
      - assert (exists n1, v1 = ValNum n1) by eauto 3.
        super_destruct; subst.
        eapply low_reach_extend_mem_with_num; eauto 2.
      - specialize (H15 s l1 eq_refl).
        super_destruct; subst.
        destruct (flowsto_dec l ℓ_adv).
        + assert (low_reach ℓ_adv Γ Σ m1 h loc') by eauto 3.
          super_destruct; subst.
          eapply low_reach_extend; eauto.
        + eauto 3.
    }
    assert (exists loc', left φ loc1 = Some loc') by eauto.
    super_destruct; subst.
    assert (low_reach ℓ_adv Γ Σ2 (m2 [x → v2]) h2 loc') by eauto 2.
    assert (Σ2 loc' = Some (SecType (Array τ ℓ_p) (l0, ∘))) by (invert_state_low_eq; eauto).
    assert (low ℓ_adv Γ Σ m1 h loc1) by eauto.
    assert (low ℓ_adv Γ Σ2 m2 h2 loc').
    {
      assert (left (inverse φ) loc' = Some loc1) by (destruct φ; eauto).
      eauto 2.
    }
    assert (exists ν, heap_lookup loc' h2 = Some (ℓ, ν)).
    {
      invert_state_low_eq.
      match goal with
        [H: context[low_heap_domain_eq] |- _] =>
        solve[eapply H; eauto]
      end.
    }
    super_destruct; subst.
    invert_state_low_eq.
    assert (low_reach ℓ_adv Γ Σ2 m2 h2 loc').
    {
      eapply H30; eauto.
    }
    assert (lookup ν n = Some (ValLoc loc0)).
    {
      eapply bijection_implies_lookup with (Σ1 := Σ) (Σ2 := Σ2) (loc1 := loc1); eauto 2.
    }
    eauto 3.
Qed.

Lemma low_eq_stenv_extend_memory:
  forall φ ψ m1 h1 m2 h2 Γ Σ1 Σ2 x v1 v2 t l ι ℓ_adv,
    state_low_eq ℓ_adv φ m1 h1 m2 h2 Γ Σ1 Σ2 ->
    Γ x = Some (SecType t (l, ι)) ->
    val_low_eq ℓ_adv (SecType t (l, ι)) v1 v2 φ ->
    (forall s ℓ, t = Array s ℓ -> exists loc, v1 = ValLoc loc /\
                                   (l ⊑ ℓ_adv -> low_reach ℓ_adv Γ Σ1 m1 h1 loc)) ->
    (forall s ℓ, t = Array s ℓ -> exists loc, v2 = ValLoc loc /\
                                   (l ⊑ ℓ_adv -> low_reach ℓ_adv Γ Σ2 m2 h2 loc)) ->
    (t = Int -> exists n, v1 = ValNum n) ->
    (t = Int -> exists n, v2 = ValNum n) ->
    wf_tenv Γ m1 ->
    wf_tenv Γ m2 ->
    wf_stenv Σ1 h1 ->
    wf_stenv Σ2 h2 ->
    dangling_pointer_free m1 h1 ->
    dangling_pointer_free m2 h2 ->
    heap_level_bound Γ m1 h1 Σ1 ->
    heap_level_bound Γ m2 h2 Σ2 ->
    wf_bijection ℓ_adv φ Γ Σ1 m1 h1 ->
    wf_bijection ℓ_adv (inverse φ) Γ Σ2 m2 h2 ->
    filtered (low ℓ_adv Γ Σ1 (extend_memory x v1 m1) h1) φ ψ ->
    low_eq_stenv ℓ_adv ψ
                 (extend_memory x v1 m1)
                 (extend_memory x v2 m2) h1 h2 Γ Σ1 Σ2.
Proof.
  intros.
  unfolds.
  intros.
  splits~.
  - intros.
    super_destruct; subst.
    assert (left φ loc1 = Some loc2) by eauto.
    destruct t.
    + assert (exists n1, v1 = ValNum n1) by eauto.
      assert (exists n2, v2 = ValNum n2) by eauto.
      super_destruct; subst.
      assert (low ℓ_adv Γ Σ1 m1 h1 loc1) by eauto 2.
      assert (Σ2 loc2 = Some τ /\ low ℓ_adv Γ Σ2 m2 h2 loc2).
      {
        invert_state_low_eq.
        match goal with
          [H: context[low_eq_stenv] |- _] =>
          solve[eapply H; eauto]
        end.
      }
      super_destruct; subst.
      splits~.
      eapply low_extend_mem_with_num2; eauto.
    + specialize (H2 s l0 eq_refl).
      specialize (H3 s l0 eq_refl).
      super_destruct; subst.
      assert (low ℓ_adv Γ Σ1 m1 h1 loc1) by eauto 2.
      assert (Σ2 loc2 = Some τ /\ low ℓ_adv Γ Σ2 m2 h2 loc2).
      {
        invert_state_low_eq.
        match goal with
          [H: context[low_eq_stenv] |- _] =>
          solve[eapply H; eauto]
        end.
      }
      super_destruct; subst.
      splits~.
      assert_wf_type.
      invert_wf_type.
      destruct s as [σ [ℓ ι]].
      dependent destruction H19.
      * destruct (flowsto_dec l ℓ_adv).
        {
          eapply LowReachable.
          eapply low_reach_in_extended_memory with (loc1 := loc1); eauto 3.          
        }
        {
          assert (low_reach ℓ_adv Γ Σ m1 h loc1) by eauto 2.
          assert (low_reach ℓ_adv Γ Σ2 m2 h2 loc2).
          {
            invert_state_low_eq.
            match goal with
              [H: context[low_reach_NI] |- _] =>
              solve[eapply H; eauto]
            end.
          }
          eauto.
        }        
      * assert ((exists ν, heap_lookup loc2 h2 = Some (ℓ0, ν)) /\
                low ℓ_adv Γ Σ2 m2 h2 loc2).
        {
          invert_state_low_eq.
          match goal with
            [H: context[low_heap_domain_eq] |- _] =>
            solve[eapply H; eauto]
          end.
        }
        super_destruct; subst.
        eapply LowHeapLevel; eauto.
  - intros.
    super_destruct; subst.
    assert (left φ loc1 = Some loc2) by eauto.
    destruct t.
    + assert (exists n1, v1 = ValNum n1) by eauto.
      assert (exists n2, v2 = ValNum n2) by eauto.
      super_destruct; subst.
      assert (low ℓ_adv Γ Σ2 m2 h2 loc2) by eauto 2.
      assert (Σ1 loc1 = Some τ /\ low ℓ_adv Γ Σ1 m1 h1 loc1).
      {
        invert_state_low_eq.
        match goal with
          [H: context[low_eq_stenv] |- _] =>
          solve[eapply H; eauto]
        end.
      }
      super_destruct; subst.
      splits~; eauto 3.
    + specialize (H2 s l0 eq_refl).
      specialize (H3 s l0 eq_refl).
      super_destruct; subst.
      assert (low ℓ_adv Γ Σ2 m2 h2 loc2).
      {
        destruct φ; eauto 3.
      }
      assert (Σ1 loc1 = Some τ /\ low ℓ_adv Γ Σ1 m1 h1 loc1).
      {
        invert_state_low_eq.
        match goal with
          [H: context[low_eq_stenv] |- _] =>
          solve[eapply H; eauto]
        end.
      }
      super_destruct; subst.
      splits~.
      assert_wf_type.
      invert_wf_type.
      destruct s as [σ [ℓ ι]].
      dependent destruction H19.
      * destruct (flowsto_dec l ℓ_adv).
        {
          eapply LowReachable.
          eapply low_reach_in_extended_memory; destruct φ; eauto.
        }
        {
          assert (low_reach ℓ_adv Γ Σ m2 h loc2) by eauto 2.
          assert (low_reach ℓ_adv Γ Σ1 m1 h1 loc1).
          {
            invert_state_low_eq.
            match goal with
              [H: context[low_reach_NI] |- _] =>
              solve[eapply H; eauto]
            end.
          }
          eauto.
        }      
      * assert ((exists ν, heap_lookup loc1 h1 = Some (ℓ0, ν)) /\
                low ℓ_adv Γ Σ1 m1 h1 loc1).
        {
          invert_state_low_eq.
          match goal with
            [H: context[low_heap_domain_eq] |- _] =>
            solve[eapply H; eauto]
          end.
        }
        super_destruct; subst.
        eapply LowHeapLevel; eauto.
Qed.

Lemma low_domain_eq_extend_memory:
  forall ℓ_adv Γ x v1 v2 m1 m2,
    low_domain_eq ℓ_adv Γ m1 m2 ->
    low_domain_eq ℓ_adv Γ (extend_memory x v1 m1) (extend_memory x v2 m2).
Proof.
  intros.
  unfolds.
  intros.
  splits~.
  + intros.
    super_destruct; subst.
    destruct (decide (x = x0)); subst.
    * rewrite -> extend_memory_lookup_eq in *.
      rewrite_inj.
      eauto.
    * rewrite -> extend_memory_lookup_neq in * by solve[eauto].
      match goal with
        [H: context[low_domain_eq] |- _] =>
        solve[eapply H; eauto]
      end.
  + intros.
    super_destruct; subst.
    destruct (decide (x = x0)); subst.
    * rewrite -> extend_memory_lookup_eq in *.
      rewrite_inj.
      eauto.
    * rewrite -> extend_memory_lookup_neq in * by solve[eauto].
      match goal with
        [H: context[low_domain_eq] |- _] =>
        solve[eapply H; eauto]
      end.
Qed.
Hint Resolve low_domain_eq_extend_memory.

Lemma low_heap_domain_eq_extend_memory:
  forall φ ψ m1 h1 m2 h2 Γ Σ1 Σ2 x v1 v2 t l ι ℓ_adv,
    state_low_eq ℓ_adv φ m1 h1 m2 h2 Γ Σ1 Σ2 ->
    Γ x = Some (SecType t (l, ι)) ->
    val_low_eq ℓ_adv (SecType t (l, ι)) v1 v2 φ ->
    (forall s ℓ, t = Array s ℓ -> exists loc, v1 = ValLoc loc /\
                                   (l ⊑ ℓ_adv -> low_reach ℓ_adv Γ Σ1 m1 h1 loc)) ->
    (forall s ℓ, t = Array s ℓ -> exists loc, v2 = ValLoc loc /\
                                   (l ⊑ ℓ_adv -> low_reach ℓ_adv Γ Σ2 m2 h2 loc)) ->
    (t = Int -> exists n, v1 = ValNum n) ->
    (t = Int -> exists n, v2 = ValNum n) ->
    wf_tenv Γ m1 ->
    wf_tenv Γ m2 ->
    wf_stenv Σ1 h1 ->
    wf_stenv Σ2 h2 ->
    dangling_pointer_free m1 h1 ->
    dangling_pointer_free m2 h2 ->
    heap_level_bound Γ m1 h1 Σ1 ->
    heap_level_bound Γ m2 h2 Σ2 ->
    wf_bijection ℓ_adv φ Γ Σ1 m1 h1 ->
    wf_bijection ℓ_adv (inverse φ) Γ Σ2 m2 h2 ->
    filtered (low ℓ_adv Γ Σ1 (extend_memory x v1 m1) h1) φ ψ ->
    low_heap_domain_eq ℓ_adv ψ (m1 [x → v1])
                       (m2 [x → v2]) h1 h2 Γ Σ1 Σ2.
Proof.
  intros.
  unfolds.
  intros.
  splits.
  - intros.
    assert (left φ l1 = Some l2) by eauto.
    super_destruct; subst.
    destruct t.
    + assert (exists n1, v1 = ValNum n1) by eauto.
      assert (exists n2, v2 = ValNum n2) by eauto.
      super_destruct; subst.
      assert (low ℓ_adv Γ Σ1 m1 h1 l1) by eauto 2.
      assert ((exists ν, heap_lookup l2 h2 = Some (ℓ, ν)) /\ low ℓ_adv Γ Σ2 m2 h2 l2).
      {
        invert_state_low_eq.
        match goal with
          [H: context[low_heap_domain_eq] |- _] =>
          solve[eapply H; eauto]
        end.
      }
      super_destruct; subst.
      splits; eauto 3.
    + specialize (H2 s l0 eq_refl).
      specialize (H3 s l0 eq_refl).
      super_destruct; subst.
      assert (low ℓ_adv Γ Σ1 m1 h1 l1) by eauto 2.
      assert ((exists ν, heap_lookup l2 h2 = Some (ℓ, ν)) /\ low ℓ_adv Γ Σ2 m2 h2 l2).
      {
        invert_state_low_eq.
        match goal with
          [H: context[low_heap_domain_eq] |- _] =>
          solve[eapply H; eauto]
        end.
      }
      super_destruct; subst.
      splits~; eauto 3.
      assert_wf_type.
      invert_wf_type.
      dependent destruction H20.
      * destruct (flowsto_dec l ℓ_adv).
        {
          eapply LowReachable.
          eapply low_reach_in_extended_memory; eauto.
        }
        {
          assert (low_reach ℓ_adv Γ Σ m1 h loc1) by eauto 2.
          assert (low_reach ℓ_adv Γ Σ2 m2 h2 l2).
          {
            invert_state_low_eq.
            match goal with
              [H: context[low_reach_NI] |- _] =>
              solve[eapply H; eauto]
            end.
          }
          eauto.
        }  
      * assert ((exists μ, heap_lookup l2 h2 = Some (ℓ, μ)) /\ low ℓ_adv Γ Σ2 m2 h2 l2).
        {
          invert_state_low_eq.
          match goal with
            [H: context[low_heap_domain_eq] |- _] =>
            solve[eapply H; eauto]
          end.
        }
        super_destruct; subst.
        rewrite_inj.
        eauto 2.
  - intros.
    super_destruct; subst.
    assert (left φ l1 = Some l2) by eauto.
    destruct t.
    + assert (exists n1, v1 = ValNum n1) by eauto.
      assert (exists n2, v2 = ValNum n2) by eauto.
      super_destruct; subst.
      assert (low ℓ_adv Γ Σ2 m2 h2 l2) by eauto 2.
      assert ((exists ν, heap_lookup l1 h1 = Some (ℓ, ν)) /\ low ℓ_adv Γ Σ1 m1 h1 l1).
      {
        invert_state_low_eq.
        match goal with
          [H: context[low_heap_domain_eq] |- _] =>
          solve[eapply H; eauto]
        end.
      }
      super_destruct; subst.
      splits; eauto 3.
    + specialize (H2 s l0 eq_refl).
      specialize (H3 s l0 eq_refl).
      super_destruct; subst.
      assert (low ℓ_adv Γ Σ2 m2 h2 l2) by (destruct φ; eauto 3).
      assert ((exists ν, heap_lookup l1 h1 = Some (ℓ, ν)) /\ low ℓ_adv Γ Σ1 m1 h1 l1).
      {
        invert_state_low_eq.
        match goal with
          [H: context[low_heap_domain_eq] |- _] =>
          solve[eapply H; eauto]
        end.
      }
      super_destruct; subst.
      splits~; eauto 3.
      assert_wf_type.
      invert_wf_type.
      dependent destruction H19.
      * destruct (flowsto_dec l ℓ_adv).
        {
          eapply LowReachable.
          eapply low_reach_in_extended_memory; destruct φ; eauto.
        }
        {
          assert (low_reach ℓ_adv Γ Σ m2 h loc1) by eauto 2.
          assert (low_reach ℓ_adv Γ Σ1 m1 h1 l1).
          {
            invert_state_low_eq.
            match goal with
              [H: context[low_reach_NI] |- _] =>
              solve[eapply H; eauto]
            end.
          }
          eauto.
        }      
      * assert ((exists μ, heap_lookup l1 h1 = Some (ℓ, μ)) /\ low ℓ_adv Γ Σ1 m1 h1 l1).
        {
          invert_state_low_eq.
          match goal with
            [H: context[low_heap_domain_eq] |- _] =>
            solve[eapply H; eauto]
          end.
        }
        super_destruct; subst.
        rewrite_inj.
        eauto 2.
Qed.

Lemma low_reach_NI_extend_memory:
  forall φ ψ m1 h1 m2 h2 Γ Σ1 Σ2 x v1 v2 t l ι ℓ_adv,
    state_low_eq ℓ_adv φ m1 h1 m2 h2 Γ Σ1 Σ2 ->
    Γ x = Some (SecType t (l, ι)) ->
    l ⊑ ℓ_adv ->
    val_low_eq ℓ_adv (SecType t (l, ι)) v1 v2 φ ->
    (forall s ℓ, t = Array s ℓ -> exists loc, v1 = ValLoc loc /\ low_reach ℓ_adv Γ Σ1 m1 h1 loc) ->
    (forall s ℓ, t = Array s ℓ -> exists loc, v2 = ValLoc loc /\ low_reach ℓ_adv Γ Σ2 m2 h2 loc) ->
    (t = Int -> exists n, v1 = ValNum n) ->
    (t = Int -> exists n, v2 = ValNum n) ->
    wf_tenv Γ m1 ->
    wf_tenv Γ m2 ->
    wf_stenv Σ1 h1 ->
    wf_stenv Σ2 h2 ->
    dangling_pointer_free m1 h1 ->
    dangling_pointer_free m2 h2 ->
    heap_level_bound Γ m1 h1 Σ1 ->
    heap_level_bound Γ m2 h2 Σ2 ->
    wf_bijection ℓ_adv φ Γ Σ1 m1 h1 ->
    wf_bijection ℓ_adv (inverse φ) Γ Σ2 m2 h2 ->
    filtered (low ℓ_adv Γ Σ1 (extend_memory x v1 m1) h1) φ ψ ->
    low_reach_NI ℓ_adv ψ (extend_memory x v1 m1) h1
                 (extend_memory x v2 m2) h2 Γ Σ1 Σ2.
Proof.
  intros.
  unfolds.
  intros.
  assert (left φ loc = Some loc') by eauto.
  splits.
  - intros.
    destruct t.
    + assert (exists n1, v1 = ValNum n1) by eauto.
      assert (exists n2, v2 = ValNum n2) by eauto.
      super_destruct; subst.
      assert (low_reach ℓ_adv Γ Σ1 m1 h1 loc) by eauto 2 using low_reach_extend_mem_with_num.
      assert (low_reach ℓ_adv Γ Σ2 m2 h2 loc').
      * invert_state_low_eq.
        match goal with
          [H: context[low_reach_NI] |- _] =>
          solve[eapply H; eauto]
        end.
      * eauto 2 using low_reach_extend_mem_with_num2.
    + assert (exists loc1, v1 = ValLoc loc1 /\ low_reach ℓ_adv Γ Σ1 m1 h1 loc1) by eauto.
      assert (exists loc2, v2 = ValLoc loc2 /\ low_reach ℓ_adv Γ Σ2 m2 h2 loc2) by eauto.
      super_destruct; subst.
      assert (low_reach ℓ_adv Γ Σ1 m1 h1 loc) by eauto 2.
      assert (low_reach ℓ_adv Γ Σ2 m2 h2 loc').
      {
        invert_state_low_eq.
        match goal with
          [H: context[low_reach_NI] |- _] =>
          solve[eapply H; eauto]
        end.
      }
      eapply low_reach_in_extended_memory; eauto.
  - intros.
    destruct t.
    + assert (exists n1, v1 = ValNum n1) by eauto.
      assert (exists n2, v2 = ValNum n2) by eauto.
      super_destruct; subst.
      assert (low_reach ℓ_adv Γ Σ2 m2 h2 loc')
        by eauto 2 using low_reach_extend_mem_with_num.
      assert (low_reach ℓ_adv Γ Σ1 m1 h1 loc).
      {
        invert_state_low_eq.
        match goal with
          [H: context[low_reach_NI] |- _] =>
          solve[eapply H; eauto]
        end.
      }
      eauto 2 using low_reach_extend_mem_with_num2.
    + assert (exists loc1, v1 = ValLoc loc1 /\ low_reach ℓ_adv Γ Σ1 m1 h1 loc1) by eauto.
      assert (exists loc2, v2 = ValLoc loc2 /\ low_reach ℓ_adv Γ Σ2 m2 h2 loc2) by eauto.
      super_destruct; subst.
      assert (low_reach ℓ_adv Γ Σ2 m2 h2 loc') by eauto 2.
      assert (low_reach ℓ_adv Γ Σ1 m1 h1 loc).
      {
        invert_state_low_eq.
        match goal with
          [H: context[low_reach_NI] |- _] =>
          solve[eapply H; eauto]
        end.
      }
      eapply low_reach_in_extended_memory; destruct φ; eauto.
Qed.
Hint Resolve low_reach_NI_extend_memory.

Lemma state_low_eq_extend_memory:
  forall φ m1 h1 m2 h2 Γ Σ1 Σ2 x v1 v2 t l ι ℓ_adv ψ,
    state_low_eq ℓ_adv φ m1 h1 m2 h2 Γ Σ1 Σ2 ->
    Γ x = Some (SecType t (l, ι)) ->
    val_low_eq ℓ_adv (SecType t (l, ι)) v1 v2 φ ->
    (forall s ℓ, t = Array s ℓ -> exists loc, v1 = ValLoc loc /\ 
                                   (l ⊑ ℓ_adv -> low_reach ℓ_adv Γ Σ1 m1 h1 loc)) ->
    (forall s ℓ, t = Array s ℓ -> exists loc, v2 = ValLoc loc /\
                                   (l ⊑ ℓ_adv -> low_reach ℓ_adv Γ Σ2 m2 h2 loc)) ->
    (t = Int -> exists n, v1 = ValNum n) ->
    (t = Int -> exists n, v2 = ValNum n) ->
    wf_tenv Γ m1 ->
    wf_tenv Γ m2 ->
    wf_tenv Γ (extend_memory x v1 m1) ->
    wf_tenv Γ (extend_memory x v2 m2) ->
    wf_stenv Σ1 h1 ->
    wf_stenv Σ2 h2 ->
    dangling_pointer_free m1 h1 ->
    dangling_pointer_free m2 h2 ->
    heap_level_bound Γ m1 h1 Σ1 ->
    heap_level_bound Γ m2 h2 Σ2 ->
    heap_level_bound Γ (extend_memory x v1 m1) h1 Σ1 ->
    wf_bijection ℓ_adv φ Γ Σ1 m1 h1 ->
    wf_bijection ℓ_adv (inverse φ) Γ Σ2 m2 h2 ->
    filtered (low ℓ_adv Γ Σ1 (extend_memory x v1 m1) h1) φ ψ ->
    state_low_eq ℓ_adv ψ (extend_memory x v1 m1) h1 (extend_memory x v2 m2) h2 Γ Σ1 Σ2.
Proof.
  intros.
  apply StateLowEq; eauto 3.
  - eapply low_eq_stenv_extend_memory; eauto.
  - invert_state_low_eq.
    eapply low_domain_eq_extend_memory; eauto.
  - eapply low_heap_domain_eq_extend_memory; eauto 2.
  - unfolds.
    intros.
    destruct (decide (x = x0)); subst.
    + rewrite -> extend_memory_lookup_eq in *.
      rewrite_inj.
      invert_val_low_eq; eauto 3.

      assert (low_reach ℓ_adv Γ Σ1 m1 h1 l1).
      {
        specialize (H2 τ ℓ_p eq_refl).
        super_destruct; subst.
        assert (exists loc, ValLoc l1 = ValLoc loc /\
                       low_reach ℓ_adv Γ Σ1 m1 h1 loc) by eauto.
        super_destruct; subst.
        injects.
        eauto.
      }
      assert_wf_type.
      invert_wf_type.
      assert (low ℓ_adv Γ Σ1 (m1 [x0 → ValLoc l1]) h1 l1) by eauto 3.
      assert (left ψ l1 = Some l2) by eauto.
      eauto.
    + rewrite -> extend_memory_lookup_neq in * by solve[eauto].
      assert (val_low_eq ℓ_adv τ v0 v3 φ) by (invert_state_low_eq; eauto).
      invert_val_low_eq; eauto 3.

      assert_wf_type.
      invert_wf_type.
      assert (low ℓ_adv Γ Σ1 (m1 [x → v1]) h1 l1).
      {
        eapply LowReachable.
        eapply LowReachMem; eauto.
        rewrite -> extend_memory_lookup_neq by solve[eauto].
        eauto.
      }
      eauto 3.
  - unfolds.
    intros.
    assert (low ℓ_adv Γ Σ1 m1 h1 loc1) by eauto 3.
    assert (left φ loc1 = Some loc2) by eauto.
    assert (low ℓ_adv Γ Σ2 m2 h2 loc2).
    {
      eapply low_iff; destruct φ; eauto.
    }
    invert_state_low_eq.
    assert (heapval_low_eq ℓ_adv τ loc1 loc2 m1 m2 h1 h2 φ) by eauto.
    invert_heapval_low_eq.
    eapply HeapValLowEq; eauto.
    intros.

    destruct (low_reach_dec ℓ_adv Γ Σ1 m1 h1 loc1).
    + assert (low_reach ℓ_adv Γ Σ2 m2 h2 loc2).
      {
        match goal with
          [H: context[low_reach_NI] |- _] =>
          solve[eapply H; eauto]
        end.
      }
      assert (val_low_eq ℓ_adv (SecType τ0 ℓ_τ) u v φ) by eauto 4.
      invert_val_low_eq; eauto 3.
      assert_wf_type.
      invert_wf_type.
      assert (low ℓ_adv Γ Σ1 m1 h1 l2) by eauto 2.
      assert (low_reach ℓ_adv Γ Σ1 (m1 [x → v1]) h1 loc1).
      {
        match goal with
          [H: low ℓ_adv Γ Σ1 (m1 [x → v1]) _ loc1 |- _] =>
          dependent destruction H; eauto 3
        end.
        rewrite_inj.
        eapply low_reach_adequacy; eauto 3.
      }
      assert (low ℓ_adv Γ Σ1 (m1 [x → v1]) h1 l2) by eauto 3.
      assert (left ψ l2 = Some l3) by eauto.
      eauto 2.
    + match goal with
        [H: low ℓ_adv Γ Σ1 m1 h1 loc1 |- _] =>
        dependent destruction H; try contradiction
      end.
      rewrite_inj.
      assert (~ reach m h loc).
      {
        intro.
        assert (low_reach ℓ_adv Γ Σ m h loc).
        {
          eapply low_reach_adequacy; eauto.
        }
        contradiction.
      }
      assert (low_reach ℓ_adv Γ Σ (m [x → v1]) h loc).
      {
        match goal with
          [H: low ℓ_adv Γ Σ (m [x → v1]) h loc |- _] =>
          dependent destruction H; eauto 3
        end.
        rewrite_inj.
        eapply low_reach_adequacy; eauto 3.
      }
      destruct t.
      * assert (exists n, v1 = ValNum n) by eauto.
        assert (exists n, v2 = ValNum n) by eauto.
        super_destruct; subst.
        assert (reach m h loc) by eauto using reach_extend_with_num.
        assert (reach m2 h2 loc2) by eauto 2 using reach_extend_with_num.
        assert (val_low_eq ℓ_adv (SecType τ0 ℓ_τ) u v φ) by eauto 4.
        invert_val_low_eq; eauto 3.
        assert (low ℓ_adv Γ Σ m h l1) by eauto 2.
        assert (low ℓ_adv Γ Σ (m [x → ValNum n2]) h l1) by eauto 3.
        assert (left ψ l1 = Some l2) by eauto.
        eauto 2.
      * specialize (H2 s l0 eq_refl).
        specialize (H3 s l0 eq_refl).
        super_destruct; subst.
        destruct (decide (loc1 = loc)); subst.
        {
          destruct (flowsto_dec l ℓ_adv).
          - assert (low_reach ℓ_adv Γ Σ m h loc) by eauto.
            exfalso; eauto 3.
          - assert (low_reach ℓ_adv Γ Σ m h loc) by eauto 3.
            assert (reach m h loc) by eauto 2.
            contradiction.
        }
        {
          destruct (flowsto_dec l ℓ_adv).
          - assert (low_reach ℓ_adv Γ Σ m h loc1) by eauto 2.
            exfalso; eauto 3.
          - assert (low_reach ℓ_adv Γ Σ m h loc) by eauto 3.
            assert (reach m h loc) by eauto 2.
            contradiction.
        }
  - unfolds.
    intros.
    destruct (flowsto_dec l ℓ_adv).
    + splits.
      * intros.
        assert (low_reach ℓ_adv Γ Σ1 m1 h1 loc).
        {
          destruct t.
          - assert (exists n, v1 = ValNum n) by eauto 2.
            super_destruct; subst.
            eauto 2 using low_reach_extend_mem_with_num.
          - specialize (H2 s l0 eq_refl).
            super_destruct; subst.
            eauto 3.
        }
        assert (low_reach ℓ_adv Γ Σ2 m2 h2 loc').
        {
          invert_state_low_eq.
          eapply H28; eauto.
        }
        destruct t.
        { assert (exists n, v2 = ValNum n) by eauto.
          super_destruct; subst.
          eauto 2 using low_reach_extend_mem_with_num2. }
        { specialize (H3 s l0 eq_refl).
          super_destruct; subst.
          assert (low_reach ℓ_adv Γ Σ2 m2 h2 loc0) by eauto.
          eapply low_reach_in_extended_memory; eauto 3. }
      * intros.
        assert (low_reach ℓ_adv Γ Σ2 m2 h2 loc').
        {
          destruct t.
          - assert (exists n, v2 = ValNum n) by eauto 2.
            super_destruct; subst.
            eauto 2 using low_reach_extend_mem_with_num.
          - specialize (H3 s l0 eq_refl).
            super_destruct; subst.
            eauto 3.
        }
        assert (low_reach ℓ_adv Γ Σ1 m1 h1 loc).
        {
          invert_state_low_eq.
          eapply H28; eauto.
        }
        destruct t.
        { assert (exists n, v1 = ValNum n) by eauto.
          super_destruct; subst.
          eauto 2 using low_reach_extend_mem_with_num2. }
        { specialize (H2 s l0 eq_refl).
          super_destruct; subst.
          assert (low_reach ℓ_adv Γ Σ1 m1 h1 loc0) by eauto.
          eapply low_reach_in_extended_memory; eauto 3.
          - rewrite <- inverse_is_involutive.
            eauto.
          - assert (left φ loc = Some loc') by eauto.
            destruct φ; eauto. }
    + assert (left φ loc = Some loc') by eauto.
      splits; intros.
      * assert (low_reach ℓ_adv Γ Σ1 m1 h1 loc) by eauto 2.
        assert (low_reach ℓ_adv Γ Σ2 m2 h2 loc').
        {
          invert_state_low_eq.
          eapply H29; eauto.
        }
        eauto 2.
      * assert (low_reach ℓ_adv Γ Σ2 m2 h2 loc') by eauto 2.
        assert (low_reach ℓ_adv Γ Σ1 m1 h1 loc).
        {
          invert_state_low_eq.
          eapply H29; eauto.
        }
        eauto 2.
  - invert_state_low_eq; eauto.
  - invert_state_low_eq; eauto.
Qed.

Lemma low_event_low_eq_implies_low_event:
  forall ℓ ev1 ev2 φ,
    low_event ℓ ev1 ->
    event_low_eq ℓ φ ev1 ev2 ->
    low_event ℓ ev2.
Proof.
  intros.
  invert_low_event;
    unfolds in H0;
    super_destruct;
    eapply H;
    eauto.
Qed.
Hint Resolve low_event_low_eq_implies_low_event.

Lemma new_step:
  forall x level e e_init pc m h t Γ Σ Σ' c' pc' m' h' t' τ,
    ⟨NewArr x level e e_init, pc, m, h, t⟩ ⇒ (Γ, Σ, Σ') ⟨c', pc', m', h', t'⟩ ->
    Γ x = Some τ ->
    (c' = Stop /\ pc = pc' /\ t' = S t /\
     exists n loc H1 H2, eval m e = Some (ValNum n) /\
              m' = (m [x → ValLoc loc]) /\
              exists v, eval m e_init = Some v /\
                   h' = extend_heap v loc level n h H1 H2) \/
    gc_occurred (NewArr x level e e_init) c' pc pc' m m' h h' t t' Σ Σ'.
Proof.
  intros.
  invert_step.
  - left.
    rewrite_inj.
    splits*.
    exists n l0 H1 H2.
    splits*.
  - right.
    unfolds.
    splits*.
    exists h2 h1_pc h1_not_pc δ.
    do 3 eexists.
    splits*.
Qed.

Lemma new_step_many:
  forall x e e_init pc m h t Γ Σ Σ'' pc'' m'' h'' t'' τ ℓ ε_x,
    ⟨NewArr x ℓ e e_init, pc, m, h, t⟩
      ⇒ * (Γ, Σ, Σ'') ⟨Stop, pc'', m'', h'', t''⟩ ->
    Γ x = Some (SecType (Array τ ℓ) ε_x) ->
    (pc = pc'' /\
     exists n loc, eval m e = Some (ValNum n) /\
              m'' = (m [x → ValLoc loc]) /\
              exists Σ' c' pc' m' h' t' n',
                gc_trans Σ Σ' ⟨NewArr x ℓ e e_init, pc, m, h, t⟩
                         ⟨c', pc', m', h', t'⟩ n' /\
                size ℓ h' + n <= maxsize ℓ h' /\
                exists v, eval m' e_init = Some v /\
                     heap_lookup loc h' = None /\
                     exists μ, heap_lookup loc h'' = Some (ℓ, μ) /\
                          forall n, lookup μ n = Some v).
Proof.
  intros.
  dependent induction H.
  - destruct cfg.
    eapply new_step in H; eauto 2.
    super_destruct; subst.
    + eapply stop_takes_no_step_many_step in H0.
      super_destruct; subst.
      splits*.
      exists n loc.
      splits*.
      exists Σ (NewArr x ℓ e e_init) pc'' m h t; exists 0.
      splits*.
    + unfold gc_occurred in *.
      super_destruct; subst.
      match goal with
        [H: ?Γ ?x = Some _ |- _] =>
        remember_simple (IHstepmany x e e_init pc0 memory ([h1_1_pc ⊎ h1_1_not_pc, H9]) (t + δ) pc'' m'' h'' t'' ℓ eq_refl eq_refl H1)
      end.
      super_destruct; subst.
      splits*.
      exists n loc.
      splits*.
      exists Σ'0 c' pc' m' h' t'; exists (S n').
      splits*.
      * eapply GCTrans.
        { unfolds.
          splits*.
          exists h1_2 h1_1_pc h1_1_not_pc δ.
          do 3 eexists.
          splits*. }
        { eauto. }
      * exists v.
        splits*.
Qed.

Lemma gc_trans_preserves_heap_size_neq_pc:
  forall Σ Σ' c c' pc pc' m m' h h' t t' n,
    gc_trans Σ Σ' ⟨c, pc, m, h, t ⟩ ⟨c', pc', m', h', t'⟩ n ->
    forall l, l <> pc -> size l h = size l h'.
Proof.
  intros.
  dependent induction H.
  - unfold gc_occurred in *.
    super_destruct; subst.
    assert (size l ([h1_1_pc ⊎ h1_1_not_pc, H9]) = size l h') by eauto using IHgc_trans.
    rewrite -> size_heap_distr by eauto.
    assert (size l h1_2 = 0) by eauto using level_neq_size.
    omega.
  - eauto.
Qed.

Lemma gc_occurred_length_of:
  forall c c' pc pc' m m' h h' t t' Σ Σ' loc length,
    gc_occurred c c' pc pc' m m' h h' t t' Σ Σ' ->
    length_of loc h' = Some length ->
    length_of loc h = Some length.
Proof.
  intros.
  unfold gc_occurred in *.
  super_destruct; subst.
  eapply disjoint_union_length_of; eauto.
Qed.
Hint Resolve gc_occurred_length_of.

Lemma gc_trans_length_of:
  forall Σ Σ' c c' pc pc' m m' h h' t t' length loc n,
    gc_trans Σ Σ' ⟨c, pc, m, h, t⟩ ⟨c', pc', m', h', t'⟩ n ->
    length_of loc h' = Some length ->
    length_of loc h = Some length.
Proof.
  intros.
  dependent induction H; eauto.
Qed.
Hint Resolve gc_trans_length_of.

Lemma low_reach_update_implies_low_reach_if:
  forall m h loc1 loc2 n v ℓ Γ Σ,
    low_reach ℓ Γ Σ m (update_heap loc1 n v h) loc2 ->
    (forall loc', v = ValLoc loc' -> low_reach ℓ Γ Σ m h loc') ->
    low_reach ℓ Γ Σ m h loc2.
Proof.
  intros.
  dependent induction H.
  - eauto 2.
  - assert (low_reach ℓ_adv Γ Σ m h loc0) by eauto.
    clear IHlow_reach.
    destruct (decide (loc1 = loc0)); subst.
    + assert (exists ν, heap_lookup loc0 h = Some (ℓ, ν) /\ μ = update_lookup ν n v)
        by eauto 2.
      super_destruct; subst.
      destruct v.
      * eauto.
      * assert (low_reach ℓ_adv Γ Σ m h l0) by eauto.
        destruct (decide (n = n0)); subst.
        { rewrite -> lookup_update_eq in *.
          rewrite_inj.
          eauto.
        }
        { rewrite -> lookup_update_neq in * by solve[eauto].
          eauto 3. }
    + rewrite -> heap_lookup_update_neq in * by solve[eauto].
      eauto 3.
Qed.
Hint Resolve low_reach_update_implies_low_reach_if.

Lemma eval_implies_reach:
  forall Γ m h e loc t,
    eval m e = Some (ValLoc loc) ->
    expr_has_type Γ e t ->
    wf_tenv Γ m ->
    reach m h loc.
Proof.
  intros.
  assert (exists x, memory_lookup m x = Some (ValLoc loc) /\ e = Var x)
    by eauto 2.
  super_destruct; subst.
  eauto.
Qed.
Hint Resolve eval_implies_reach.

Lemma eval_low_implies_low_reach:
  forall ℓ_adv Γ m h e loc Σ σ l ι,
    eval m e = Some (ValLoc loc) ->
    expr_has_type Γ e (SecType σ (l, ι)) ->
    l ⊑ ℓ_adv ->
    wf_tenv Γ m ->
    low_reach ℓ_adv Γ Σ m h loc.
Proof.
  intros.
  assert (exists x, memory_lookup m x = Some (ValLoc loc) /\ e = Var x) by eauto 2.
  super_destruct; subst.
  invert_var_typing.
  destruct σ.
  - assert (exists n, ValLoc loc = ValNum n) by eauto.
    super_destruct.
    discriminate.
  - assert_wf_type.
    invert_wf_type.
    eauto.
Qed.

Lemma wf_bijection_extend_mem1:
  forall ℓ_adv φ ψ Σ Γ m σ ℓ ι x v h,
    wf_bijection ℓ_adv φ Γ Σ m h ->
    (σ = Int -> exists n, v = ValNum n) ->
    Γ x = Some (SecType σ (ℓ, ι)) ->
    (forall τ ℓ', σ = Array τ ℓ' -> exists loc, v = ValLoc loc /\
                                     (ℓ ⊑ ℓ_adv -> low_reach ℓ_adv Γ Σ m h loc)) ->
    filtered (low ℓ_adv Γ Σ (m [x → v]) h) φ ψ ->
    wf_bijection ℓ_adv ψ Γ Σ (m [ x → v]) h.
Proof.
  intros.
  unfolds.
  intros.
  splits.
  - intros.
    super_destruct; subst.
    assert (low ℓ_adv Γ Σ m h loc) by eauto 3.
    eapply filtered_bijection_some_implies_predicate; eauto.
  - intros.
    assert (low ℓ_adv Γ Σ m h loc).
    {
      destruct σ.
      - assert (exists n, v = ValNum n) by eauto 2.
        super_destruct; subst.
        eauto 2.
      - specialize (H2 s l eq_refl).
        super_destruct; subst.
        destruct (flowsto_dec ℓ ℓ_adv).
        + assert (low_reach ℓ_adv Γ Σ m h loc0) by eauto 2.
          super_destruct; subst.                  
          eauto 3.
        + destruct_low; eauto 3.
    }
    assert (exists loc', left φ loc = Some loc') by eauto 2.
    super_destruct; subst.
    assert (left ψ loc = Some loc') by eauto 2.
    eauto.

    Unshelve.
    + eauto.
    + constructor.
Qed.
Hint Resolve wf_bijection_extend_mem1.

Lemma wf_bijection_extend_mem2:
  forall ℓ_adv ψ φ Γ Σ1 Σ2 m1 m2 σ ℓ ι x v1 v2 h1 h2,
    state_low_eq ℓ_adv φ m1 h1 m2 h2 Γ Σ1 Σ2 ->
    state_low_eq ℓ_adv ψ (m1 [x → v1]) h1
                 (m2 [x → v2]) h2 Γ Σ1 Σ2 ->
    filtered (low ℓ_adv Γ Σ1 (m1 [x → v1]) h1) φ ψ ->
    dangling_pointer_free m1 h1 ->
    dangling_pointer_free m2 h2 ->
    wf_tenv Γ m1 ->
    wf_tenv Γ m2 ->
    wf_stenv Σ1 h1 ->
    wf_stenv Σ2 h2 ->
    Γ x = Some (SecType σ (ℓ, ι)) ->
    val_low_eq ℓ_adv (SecType σ (ℓ, ι)) v1 v2 φ ->
    (σ = Int -> exists n, v2 = ValNum n) ->
    (forall τ ℓ', σ = Array τ ℓ' -> exists loc, v2 = ValLoc loc /\
                                     (ℓ ⊑ ℓ_adv -> low_reach ℓ_adv Γ Σ2 m2 h2 loc)) ->
    wf_bijection ℓ_adv φ Γ Σ1 m1 h1 ->
    wf_bijection ℓ_adv (inverse φ) Γ Σ2 m2 h2 ->
    wf_bijection ℓ_adv ψ Γ Σ1 (m1 [x → v1]) h1 ->
    wf_bijection ℓ_adv (inverse ψ) Γ Σ2 (m2 [x → v2]) h2.
Proof.
  intros.
  unfolds.
  intros.
  splits.
  - intros.
    super_destruct; subst.                
    assert (left ψ loc' = Some loc) by (destruct ψ; eauto 2).
    assert (left φ loc' = Some loc).
    { eapply filtered_eq_if; eauto. }
    rewrite <- (low_iff _ H0 H16).
    assert (low ℓ_adv Γ Σ1 m1 h1 loc') by eauto 3.
    eapply filtered_bijection_some_implies_predicate; eauto.
  - intros.
    assert (low ℓ_adv Γ Σ2 m2 h2 loc).
    {
      destruct σ.
      - assert (exists n, v2 = ValNum n) by eauto 2.
        super_destruct; subst.
        eauto 2.
      - destruct (flowsto_dec ℓ ℓ_adv).
        + specialize (H11 s l eq_refl).
          super_destruct; subst.
          assert (low_reach ℓ_adv Γ Σ2 m2 h2 loc0) by eauto 2.
          super_destruct; subst.
          eapply low_extend; eauto.
        + destruct_low; eauto 3.
    }
    
    assert (exists loc', left (inverse φ) loc = Some loc') by eauto 2.
    super_destruct; subst.
    assert (left φ loc' = Some loc) by (destruct φ; eauto).
    assert (low ℓ_adv Γ Σ1 m1 h1 loc').
    {
      eapply low_iff; eauto.
    }
    
    assert (low ℓ_adv Γ Σ1 (m1 [x → v1]) h1 loc').
    {
      dependent destruction H15.
      - eapply LowReachable.
        eapply low_reach_in_extended_memory with (v1 := v2); eauto 2.
        rewrite <- inverse_is_involutive.
        eauto.
      - inverts H.
        assert ((exists ν, heap_lookup loc' h1 = Some (ℓ0, ν)) /\
                low ℓ_adv Γ Σ1 m1 h1 loc').
        {
          assert (low_heap_domain_eq ℓ_adv (inverse φ) m2 m1 h h1 Γ Σ Σ1) by eauto 3.
          eapply H; eauto.
        }
        super_destruct; subst.
        eapply LowHeapLevel; eauto.
    }
    
    assert (exists loc'', left ψ loc' = Some loc'') by eauto 2.
    super_destruct; subst.
    assert (loc = loc'').
    {
      assert (left φ loc' = Some loc'') by eauto.
      congruence.
    }
    subst.
    destruct ψ; eauto.

    Unshelve.
    * eauto.
    * constructor.
Qed.
Hint Resolve wf_bijection_extend_mem2.

Lemma wf_bijection_extend_mem_and_heap1:
  forall ℓ_adv ψ φ loc1 loc2 m τ l ℓ ℓ' ι' n v h H1 H2 Γ Σ x H3 H4,
    Γ x = Some (SecType (Array (SecType τ (ℓ', ι')) l) (ℓ, ∘)) ->
    ℓ ⊑ ℓ_adv ->
    wf_tenv Γ m ->
    (forall s ℓ,
        τ = Array s ℓ ->
        exists loc', v = ValLoc loc' /\ (ℓ' ⊑ ℓ_adv -> low_reach ℓ_adv Γ Σ m h loc')) ->
    (τ = Int -> exists n, v = ValNum n) ->
    filtered
      (low ℓ_adv Γ (extend_stenv loc1 (SecType τ (ℓ', ι')) Σ)
           (m [x → ValLoc loc1])
           (extend_heap v loc1 l n h H3 H4)) φ ψ ->
    wf_bijection ℓ_adv φ Γ Σ m h ->
    wf_bijection ℓ_adv (extend_bijection ψ loc1 loc2 H1 H2) Γ
                 (extend_stenv loc1 (SecType τ (ℓ', ι')) Σ)
                 (m [x → ValLoc loc1]) 
                 (extend_heap v loc1 l n h H3 H4).
Proof.
  intros.
  unfolds.
  intros.
  splits.
  - intros.
    super_destruct; subst.
    destruct (decide (loc = loc1)); subst.
    + _rewrite -> left_extend_bijection_eq in *.
      rewrite_inj.
      eauto 3.
    + _rewrite -> left_extend_bijection_neq in * by solve[eauto].
      eapply filtered_bijection_some_implies_predicate; eauto 2.
  - intros.
    destruct (decide (loc = loc1)); subst.
    + eauto.
    + rewrite -> left_extend_bijection_neq by solve[eauto].
      assert (low ℓ_adv Γ Σ m h loc).
      {
        eapply low_extend_implies_low_if; eauto.
      }
      assert (exists loc', left φ loc = Some loc') by eauto 3.
      super_destruct; subst.
      eauto 3.
Qed.
Hint Resolve wf_bijection_extend_mem_and_heap1.

Lemma wf_bijection_extend_mem_and_heap2:
  forall ℓ_adv ψ φ loc1 loc2 Γ Σ1 Σ2 ℓ ℓ' ι' τ l n v1 v2 m1 m2 h1 h2 x H1 H2 H3 H4 H5 H6,
    Γ x = Some (SecType (Array (SecType τ (ℓ', ι')) l) (ℓ, ∘)) ->
    ℓ ⊑ ℓ_adv ->
    state_low_eq ℓ_adv φ m1 h1 m2 h2 Γ Σ1 Σ2 ->
    state_low_eq ℓ_adv (extend_bijection ψ loc1 loc2 H1 H2)
                 (m1 [x → ValLoc loc1])
                 (extend_heap v1 loc1 l n h1 H3 H4)
                 (m2 [x → ValLoc loc2])
                 (extend_heap v2 loc2 l n h2 H5 H6) Γ
                 (extend_stenv loc1 (SecType τ (ℓ', ι')) Σ1)
                 (extend_stenv loc2 (SecType τ (ℓ', ι')) Σ2) ->
    wf_bijection ℓ_adv φ Γ Σ1 m1 h1 ->
    wf_bijection ℓ_adv (inverse φ) Γ Σ2 m2 h2 ->
    dangling_pointer_free m1 h1 ->
    dangling_pointer_free m2 h2 ->
    wf_tenv Γ m1 ->
    wf_tenv Γ m2 ->
    wf_stenv Σ1 h1 ->
    wf_stenv Σ2 h2 ->
    (τ = Int -> exists n, v1 = ValNum n) ->
    (τ = Int -> exists n, v2 = ValNum n) ->
    (forall s ℓ, τ = Array s ℓ ->
            exists loc, v1 = ValLoc loc /\
                   (ℓ' ⊑ ℓ_adv -> low_reach ℓ_adv Γ Σ1 m1 h1 loc) /\
                   (~ ℓ' ⊑ ℓ_adv -> reach m1 h1 loc)) ->
    (forall s ℓ, τ = Array s ℓ ->
            exists loc, v2 = ValLoc loc /\
                   (ℓ' ⊑ ℓ_adv -> low_reach ℓ_adv Γ Σ2 m2 h2 loc) /\
                   (~ ℓ' ⊑ ℓ_adv -> reach m2 h2 loc)) ->
    (ℓ' ⊑ ℓ_adv -> onvals (left φ) v1 = Some v2) ->
    left φ loc1 = None ->
    right φ loc2 = None ->
    filtered
      (low ℓ_adv Γ (extend_stenv loc1 (SecType τ (ℓ', ι')) Σ1)
           (m1 [x → ValLoc loc1])
           (extend_heap v1 loc1 l n h1 H3 H4)) φ ψ ->
    wf_bijection ℓ_adv (extend_bijection ψ loc1 loc2 H1 H2) Γ
                 (extend_stenv loc1 (SecType τ (ℓ', ι')) Σ1)
                 (m1 [x → ValLoc loc1])
                 (extend_heap v1 loc1 l n h1 H3 H4) ->
    wf_bijection ℓ_adv (inverse (extend_bijection ψ loc1 loc2 H1 H2)) Γ
                 (extend_stenv loc2 (SecType τ (ℓ', ι')) Σ2)
                 (m2 [x → ValLoc loc2])
                 (extend_heap v2 loc2 l n h2 H5 H6).
Proof.
  intros.
  unfolds.
  intros.
  splits.
  intros.
  - intros.
    super_destruct; subst.
    _rewrite -> left_inverse_is_right in *.
    destruct (decide (loc2 = loc)); subst.
    + _rewrite -> right_extend_bijection_eq in *.
      rewrite_inj.
      eapply LowReachable.
      eapply LowReachMem; eauto.
    + assert (left (extend_bijection ψ loc1 loc2 H1 H2) loc' = Some loc).
      {
        destruct (extend_bijection ψ loc1 loc2 H1 H2); eauto.
      }
      _rewrite -> right_extend_bijection_neq in * by solve[eauto].
      assert (left ψ loc' = Some loc) by (destruct ψ; eauto).
      assert (left φ loc' = Some loc) by eauto 2.
      assert (low ℓ_adv Γ Σ1 m1 h1 loc') by eauto 2.
      assert (low ℓ_adv Γ Σ2 m2 h2 loc).
      {
        eapply low_iff; destruct φ; eauto 2.
      }
      assert (low ℓ_adv Γ (extend_stenv loc1 (SecType τ (ℓ', ι')) Σ1)
                  (m1 [x → ValLoc loc1]) 
                  (extend_heap v1 loc1 l n h1 H3 H4) loc') by eauto 2.
      match goal with
        [H: low _ _ _ _ (extend_heap _ _ _ _ _ _ _) _ |- _] =>
        dependent destruction H
      end.
      * eapply LowReachable.
        eapply low_reach_in_extended_memory_and_heap; eauto 3.
      * rewrite_inj.
        assert ((exists μ, heap_lookup loc0 (extend_heap v1 loc1 l n h1 H3 H4) =
                      Some (ℓ0, μ)) /\
                low ℓ_adv Γ (extend_stenv loc1 (SecType τ (ℓ', ι')) Σ1)
                    (m1 [x → ValLoc loc1]) 
                    (extend_heap v1 loc1 l n h1 H3 H4) loc0).
        {
          splits~; eauto 3.
        }
        
        assert ((exists ν, heap_lookup loc (extend_heap v2 loc2 l n h2 H5 H6) =
                      Some (ℓ0, ν)) /\
                low ℓ_adv Γ (extend_stenv loc2 (SecType τ (ℓ', ι')) Σ2)
                    (m2 [x → ValLoc loc2])
                    (extend_heap v2 loc2 l n h2 H5 H6) loc).
        {
          repeat invert_state_low_eq.
          match goal with
            [H: context[low_heap_domain_eq] |- _] =>
            solve[eapply H; eauto]
          end.
        }
        super_destruct; subst.
        eapply LowHeapLevel.
        { eauto. }
        { eauto. }
  - intros.
    rewrite -> left_inverse_is_right.
    destruct (decide (loc = loc2)); subst.
    {
      rewrite -> right_extend_bijection_eq.
      eauto.
    }
    assert (low ℓ_adv Γ Σ2 m2 h2 loc).
    {
      match goal with
        [H: low _ _ _ _ (extend_heap _ _ _ _ _ _ _) _ |- _] =>
        dependent destruction H
      end.
      - eapply LowReachable.
        eapply low_reach_extend_implies_low_reach_if with (v := v2) (σ := τ) (ℓ := ℓ').
        + intros; subst.
          specialize (H20 s ℓ'0 eq_refl).
          super_destruct; subst.
          exists loc0.
          splits; eauto 4.
        + eauto.
        + eauto.
        + eauto.
      - rewrite -> heap_lookup_extend_neq in * by solve[eauto 2].
        eauto 3.
    }
    assert (exists loc', left (inverse φ) loc = Some loc').
    {
      eauto 3.
    }
    super_destruct; subst.
    assert (loc1 <> loc').
    {
      intro; subst.
      rewrite_inj.
      assert (left φ loc' = Some loc) by (destruct φ; eauto 3).
      congruence.
    }
    assert (low ℓ_adv Γ (extend_stenv loc1 (SecType τ (ℓ', ι')) Σ1)
                (m1 [x → ValLoc loc1])
                (extend_heap v1 loc1 l n h1 H3 H4) loc').
    {
      match goal with
        [H: low _ _ _ _ (extend_heap _ _ _ _ _ _ _) _ |- _] =>
        dependent destruction H
      end.
      - eapply LowReachable.
        eapply low_reach_in_extended_memory_and_heap; eauto 3.
        intros.
        rewrite -> left_inverse_is_right.
        rewrite <- onvals_sym.
        eauto.
      - rewrite -> heap_lookup_extend_neq in * by solve[eauto 2].
        assert (exists μ, heap_lookup loc' (extend_heap v1 loc1 l n h1 H3 H4) = Some (ℓ0, μ)).
        {
          assert (exists μ, heap_lookup loc' h1 = Some (ℓ0, μ)).
          {
            inverts H7.
            eapply H33; destruct φ; eauto 3.
          }
          rewrite -> heap_lookup_extend_neq by solve[eauto].
          eauto.
        }
        super_destruct; subst.
        eauto 3.
    }
    assert (exists loc'', left (extend_bijection ψ loc1 loc2 H1 H2)
                          loc' = Some loc'') by eauto 3.
    super_destruct; subst.
    assert (left φ loc' = Some loc) by (destruct φ; eauto 2).
    assert (loc = loc'').
    {
      _rewrite -> left_extend_bijection_neq in * by solve[eauto 2].
      assert (left φ loc' = Some loc'') by eauto 3.
      congruence.
    }
    subst.
    assert (right (extend_bijection ψ loc1 loc2 H1 H2) loc'' = Some loc').
    {
      destruct (extend_bijection ψ loc1 loc2 H1 H2); eauto 2.
    }
    eauto 3.

    Unshelve.
    + eauto.
    + eauto.
    + repeat constructor; eauto.
    + eauto.
    + eauto.
    + repeat constructor; eauto.
Qed.

Lemma wf_bijection_extend_mem_and_heap_high1:
  forall ℓ_adv ψ φ Γ loc1 m1 τ Σ1 l x h1 n ℓ v H1 H2,
    Γ x = Some (SecType (Array τ l) (ℓ, ∘)) ->
    ~ ℓ ⊑ ℓ_adv ->
    wf_bijection ℓ_adv φ Γ Σ1 m1 h1 ->
    left φ loc1 = None ->
    wf_tenv Γ m1 ->
    dangling_pointer_free m1 h1 ->
    filtered
      (low ℓ_adv Γ (extend_stenv loc1 τ Σ1)
           (m1 [x → ValLoc loc1])
           (extend_heap v loc1 l n h1 H1 H2)) φ ψ ->
    wf_bijection ℓ_adv ψ Γ (extend_stenv loc1 τ Σ1)
                 (m1 [x → ValLoc loc1])
                 (extend_heap v loc1 l n h1 H1 H2).
Proof.
  intros.
  unfolds.
  intros.
  splits.
  {
    intros.
    super_destruct; subst.
    assert (left φ loc = Some loc') by eauto 2.
    assert (low ℓ_adv Γ Σ1 m1 h1 loc) by eauto 2.
    assert (loc <> loc1) by congruence.
    destruct_low.
    - eapply LowReachable.
      eapply low_reach_extend_memory_heap_with_high; eauto 2.
    - eapply LowHeapLevel.
      + rewrite -> heap_lookup_extend_neq by solve[eauto].
        eauto.
      + eauto.
  }
  {
    intros.
    assert (low ℓ_adv Γ Σ1 m1 h1 loc).
    {
      eapply low_in_extended_memory_heap_with_high_implies_low; eauto 2.
    }
    assert (exists loc', left φ loc = Some loc') by eauto 2.
    super_destruct; subst.
    eauto 3.
  }
Qed.

Lemma wf_bijection_extend_mem_and_heap_high2:
  forall ℓ_adv ψ φ Γ loc1 loc2 τ Σ1 Σ2 m1 m2 h1 h2 ℓ x l n1 n2 v1 v2 H1 H2 H3 H4,
    state_low_eq ℓ_adv φ m1 h1 m2 h2 Γ Σ1 Σ2 ->
    Γ x = Some (SecType (Array τ l) (ℓ, ∘)) ->
    ~ ℓ ⊑ ℓ_adv ->
    wf_tenv Γ m2 ->
    dangling_pointer_free m2 h2 ->
    filtered
      (low ℓ_adv Γ (extend_stenv loc1 τ Σ1)
           (m1 [x → ValLoc loc1])
           (extend_heap v1 loc1 l n1 h1 H1 H2 )) φ ψ ->
    wf_bijection ℓ_adv φ Γ Σ1 m1 h1 ->
    wf_bijection ℓ_adv (inverse φ) Γ Σ2 m2 h2 ->
    wf_bijection ℓ_adv (inverse ψ) Γ (extend_stenv loc2 τ Σ2)
                 (m2 [x → ValLoc loc2])
                 (extend_heap v2 loc2 l n2 h2 H3 H4).
Proof.
  intros.
  unfolds.
  intros.
  splits.
  {
    intros.
    super_destruct; subst.
    assert (left ψ loc' = Some loc) by (destruct ψ; eauto 3).
    assert (left φ loc' = Some loc) by eauto 2.
    assert (low ℓ_adv Γ Σ1 m1 h1 loc') by eauto 2.
    assert (low ℓ_adv Γ Σ2 m2 h2 loc).
    {
      eapply low_iff; destruct φ; eauto 3.
    }
    eapply low_extend_memory_heap_with_high; eauto 2.
  }
  {
    intros.
    assert (low ℓ_adv Γ Σ2 m2 h2 loc).
    {
      eapply low_in_extended_memory_heap_with_high_implies_low; eauto 2.
    }
    assert (exists loc', left (inverse φ) loc = Some loc') by eauto 2.
    super_destruct; subst.
    assert (left φ loc' = Some loc) by (destruct φ; eauto 2).
    assert (low ℓ_adv Γ Σ1 m1 h1 loc') by eauto 2.
    assert (low ℓ_adv Γ (extend_stenv loc1 τ Σ1)
                (m1 [x → ValLoc loc1])
                (extend_heap v1 loc1 l n1 h1 H1 H2) loc').
    {
      eapply low_extend_memory_heap_with_high; eauto 2.
    }
    assert (exists loc'', left ψ loc' = Some loc'') by eauto 3.
    super_destruct; subst.
    assert (left φ loc' = Some loc'') by eauto 2.
    rewrite_inj.
    exists loc'.
    destruct ψ; eauto.
  }
Qed.

Ltac destruct_LH_join_flowsto :=
  match goal with
    [H: LH.flowsto (LH.join ?a ?b) ?c |- _] =>
    destruct (LHLatProp.join_flowsto_implies_flowsto a b c H); clear H
  end.

Lemma low_update_with_num_implies_low:
  forall ℓ_adv Γ Σ m h loc1 loc2 k n,
    low ℓ_adv Γ Σ m (update_heap loc1 n (ValNum k) h) loc2 ->
    low ℓ_adv Γ Σ m h loc2.
Proof.
  intros.
  destruct_low.
  - assert (low_reach ℓ_adv Γ Σ m h loc) by eauto using low_reach_update_with_num.
    eapply LowReachable; eauto 2.
  - destruct (decide (loc1 = loc)); subst.
    + assert (exists ν, heap_lookup loc h = Some (ℓ, ν) /\
                   μ = update_lookup ν n (ValNum k)) by eauto 2.
      super_destruct; subst.
      eapply LowHeapLevel; eauto 3.
    + rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
      eapply LowHeapLevel; eauto 3.
Qed.

Lemma low_in_updated_heap_high_implies_low:
  forall ℓ_adv Γ Σ m h loc1 v loc2 n σ ℓ ι,
    Σ loc1 = Some (SecType σ (ℓ, ι)) ->
    ~ ℓ ⊑ ℓ_adv ->
    low ℓ_adv Γ Σ m (update_heap loc1 n v h) loc2 ->
    low ℓ_adv Γ Σ m h loc2.
Proof.
  intros.
  destruct_low.
  - eapply LowReachable.
    eauto 3.
  - destruct (decide (loc1 = loc)); subst.
    + assert (exists ν, heap_lookup loc h = Some (ℓ0, ν) /\ μ = update_lookup ν n v) by eauto 2.
      super_destruct; subst.
      eauto 3.
    + rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
      eauto 3.

      Unshelve.
      * repeat constructor; eauto.
      * repeat constructor; eauto.
      * repeat constructor; eauto.
      * repeat constructor; eauto.
Qed.
Hint Resolve low_in_updated_heap_high_implies_low.

Lemma wf_bijection_update_heap1:
  forall ℓ_adv ψ φ Γ Σ1 m1 h1 loc1 n1 v ℓ ι σ,
    Σ1 loc1 = Some (SecType σ (ℓ, ι)) ->
    wf_bijection ℓ_adv φ Γ Σ1 m1 h1 ->
    (forall loc', v = ValLoc loc' -> ℓ ⊑ ℓ_adv ->
             low_reach ℓ_adv Γ Σ1 m1 h1 loc') ->
    filtered (low ℓ_adv Γ Σ1 m1 (update_heap loc1 n1 v h1)) φ ψ ->
    wf_bijection ℓ_adv ψ Γ Σ1 m1 (update_heap loc1 n1 v h1).
Proof.
  intros.
  unfolds.
  intros.
  splits.
  - intros.
    super_destruct; subst.
    assert (left φ loc = Some loc') by eauto 2.
    assert (low ℓ_adv Γ Σ1 m1 h1 loc) by eauto 2.
    eapply filtered_bijection_some_implies_predicate; eauto.
  - intros.
    destruct (flowsto_dec ℓ ℓ_adv).
    + assert (low ℓ_adv Γ Σ1 m1 h1 loc).
      {
        eapply low_update_implies_low_if; eauto 2.
      }
      assert (exists loc', left φ loc = Some loc') by eauto 2.
      super_destruct; subst.
      eauto 3.
    + assert (low ℓ_adv Γ Σ1 m1 h1 loc) by eauto 2.
      assert (exists loc', left φ loc = Some loc') by eauto 2.
      super_destruct; subst.
      eauto 3.
Qed.

Lemma wf_bijection_update_heap2:
  forall ℓ_adv Γ Σ1 Σ2 m1 m2 h1 h2 φ ψ v1 v2 n1 n2 loc1 loc2 ℓ σ ι,
    filtered (low ℓ_adv Γ Σ1 m1 (update_heap loc1 n1 v1 h1)) φ ψ ->
    wf_tenv Γ m1 ->
    wf_tenv Γ m2 ->
    wf_stenv Σ1 h1 ->
    wf_stenv Σ2 h2 ->
    Σ1 loc1 = Some (SecType σ (ℓ, ι)) ->
    Σ2 loc2 = Some (SecType σ (ℓ, ι)) ->
    (ℓ ⊑ ℓ_adv -> left φ loc1 = Some loc2) ->
    wf_bijection ℓ_adv φ Γ Σ1 m1 h1 ->
    wf_bijection ℓ_adv (inverse φ) Γ Σ2 m2 h2 ->
    state_low_eq ℓ_adv φ m1 h1 m2 h2 Γ Σ1 Σ2 ->
    dangling_pointer_free m1 h1 ->
    dangling_pointer_free m2 h2 ->
    heap_level_bound Γ m1 h1 Σ1 ->
    heap_level_bound Γ m2 h2 Σ2 ->
    val_low_eq ℓ_adv (SecType σ (ℓ, ι)) v1 v2 φ ->
    val_low_eq ℓ_adv (SecType Int (ℓ, ι)) (ValNum n1) (ValNum n2) φ ->
    wf_bijection ℓ_adv ψ Γ Σ1 m1 (update_heap loc1 n1 v1 h1) ->
    state_low_eq ℓ_adv ψ m1 (update_heap loc1 n1 v1 h1) m2
                 (update_heap loc2 n2 v2 h2) Γ Σ1 Σ2 ->
    (σ = Int -> exists n, v1 = ValNum n) ->
    (σ = Int -> exists n, v2 = ValNum n) ->
    (forall s ℓ',
        σ = Array s ℓ' ->
        exists loc', v1 = ValLoc loc' /\ (ℓ ⊑ ℓ_adv -> low_reach ℓ_adv Γ Σ1 m1 h1 loc')) ->
    (forall s ℓ',
      σ = Array s ℓ' ->
      exists loc', v2 = ValLoc loc' /\ (ℓ ⊑ ℓ_adv -> low_reach ℓ_adv Γ Σ2 m2 h2 loc')) ->
    wf_bijection ℓ_adv (inverse ψ) Γ Σ2 m2 (update_heap loc2 n2 v2 h2).
Proof.
  intros.
  unfolds.
  intros.
  splits.
  - intros.
    super_destruct; subst.
    assert (left ψ loc' = Some loc) by (destruct ψ; eauto 2).
    assert (low ℓ_adv Γ Σ1 m1 (update_heap loc1 n1 v1 h1) loc') by eauto 2.
    assert (left φ loc' = Some loc) by eauto 2.
    assert (left (inverse φ) loc = Some loc') by (destruct φ; eauto 2).
    eapply low_iff; eauto.
  - intros.
    assert (low ℓ_adv Γ Σ2 m2 h2 loc).
    {
      eapply low_update_implies_low_if; eauto 2.
      intros; subst.
      destruct σ.
      - assert (exists n, ValLoc loc' = ValNum n) by eauto 2.
        super_destruct; discriminate.
      - specialize (H21 s l eq_refl).
        super_destruct; subst.
        injects.
        eauto 2.
    }
    assert (exists loc', left (inverse φ) loc = Some loc') by eauto 2.
    super_destruct; subst.
    assert (left φ loc' = Some loc) by (destruct φ; eauto).
    exists loc'.
    assert (low ℓ_adv Γ Σ1 m1 h1 loc').
    {
      eapply low_iff; eauto.
    }
    assert (low ℓ_adv Γ Σ1 m1 (update_heap loc1 n1 v1 h1) loc').
    {
      assert (exists ℓ μ, heap_lookup loc' h1 = Some (ℓ, μ)) by eauto 2.
      super_destruct; subst.
      assert ((exists ν, heap_lookup loc h2 = Some (ℓ0, ν)) /\ low ℓ_adv Γ Σ2 m2 h2 loc).
      {
        repeat invert_state_low_eq.
        match goal with
          [H: context[low_heap_domain_eq] |- _] =>
          solve[eapply H; eauto]
        end.
      }
      super_destruct; subst.
      destruct (flowsto_dec ℓ0 ℓ_adv).
      - destruct (decide (loc1 = loc')); subst.
        + eapply LowHeapLevel; eauto 3.
        + eapply LowHeapLevel.
          * rewrite -> heap_lookup_update_neq by solve[eauto 2].
            eauto.
          * eauto.
      - match goal with
          [H: low _ _ _ _ (update_heap _ _ _ _) _ |- _] =>
          dependent destruction H
        end.
        + eapply LowReachable.
          destruct (flowsto_dec ℓ ℓ_adv).
          {
            assert (left φ loc1 = Some loc2) by eauto 2.
            assert (low ℓ_adv Γ Σ1 m1 h1 loc1) by eauto 2.
            assert (exists ℓ μ, heap_lookup loc1 h1 = Some (ℓ, μ)) by eauto 2.
            super_destruct; subst.
            assert ((exists ν, heap_lookup loc2 h2 = Some (ℓ1, ν)) /\
                    low ℓ_adv Γ Σ m h2 loc2).
            {
              repeat invert_state_low_eq.
              match goal with
                [H: context[low_heap_domain_eq] |- _] =>
                solve[eapply H; eauto]
              end.
            }
            super_destruct; subst.
            rewrite_inj.
            eapply low_reach_in_updated_heap; try solve[eauto 2 || destruct φ; eauto 2].
            
          }
          { inverts H26.
            - eapply low_reach_update_heap_with_high; eauto 2.
            - congruence. }
        + destruct (decide (loc2 = loc)); subst.
          * assert (exists ν, heap_lookup loc h2 = Some (ℓ0, ν) /\ μ = update_lookup ν n2 v2) by eauto 2.
            super_destruct; subst.
            rewrite_inj.
            contradiction.
          * rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
            rewrite_inj.
            contradiction.
    }
    assert (left ψ loc' = Some loc) by eauto.
    destruct ψ; eauto.
Qed.

Ltac construct_gc_run :=
          match goal with
              [H1: wf_bijection ?ℓ_adv ?φ ?Γ ?Σ1 ?m1 ?h1,
               H2: wf_bijection ?ℓ_adv (inverse ?φ) ?Γ ?Σ2 ?m2 ?h2,
               H3: state_low_eq ?ℓ_adv ?φ ?m1 ?h1 ?m2 ?h2 ?Γ ?Σ1 ?Σ2,
               H4: ?pc ⊑ ?ℓ_adv,
               H5: wf_tenv ?Γ ?m1,
               H6: wf_tenv ?Γ ?m2,
               H7: wf_stenv ?Σ1 ?h1,
               H8: wf_stenv ?Σ2 ?h2,
               H9: heap_level_bound ?Γ ?m1 ?h1 ?Σ1,
               H10: heap_level_bound ?Γ ?m2 ?h2 ?Σ2,
               H14: dangling_pointer_free ?m1 ?h1,
               H15: dangling_pointer_free ?m2 ?h2,
               H16: context[gc_occurred] |- _]
              =>
              apply gc_occurred_implies_gc_occurred_no_ex in H16;
                super_destruct'; subst;
                  remember_simple (gc_noninterference H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H14 H15 H16)
          end.

Lemma about_seq_step_many:
  forall c1 c2 c'' pc''' pc m h t pc'' m'' h'' t'' Γ Σ Σ'',
    wellformed_aux Γ Σ ⟨ c1;; c2, pc, m, h, t ⟩ pc''' ->
    ⟨ c1;; c2, pc, m, h, t ⟩ ⇒ *
    (Γ, Σ, Σ'') ⟨ c'', pc'', m'', h'', t'' ⟩ ->
    (exists d,
        ⟨c1, pc, m, h, t⟩ ⇒ * (Γ, Σ, Σ'') ⟨d, pc'', m'', h'', t''⟩ /\
        c'' = (d ;; c2))
    \/
    (exists pc' m' h' t' Σ',
        (⟨ c1, pc, m, h, t⟩ ⇒ * (Γ, Σ, Σ') ⟨ Stop, pc', m', h', t' ⟩
         /\ ⟨ c2, pc', m', h', t' ⟩ ⇒ *
            (Γ, Σ', Σ'') ⟨ c'', pc'', m'', h'', t'' ⟩)).
Proof.
  intros.
  dependent induction H0.
  - left.
    exists c1.
    splits*.
  - destruct cfg.
    remember_simple (about_seq_step H1).
    super_destruct; subst.
    + super_destruct'; subst.
      right.
      exists pc0 memory heap time Σ'.
      splits*.
    + assert (wellformed_aux Γ Σ' ⟨ c1';; c2, pc0, memory, heap, time ⟩ pc''') by eauto 2 using preservation.
      remember_simple (IHstepmany _ _ _ _ _ _ _ _ _ _ _ H4 eq_refl eq_refl).
      super_destruct; subst.
      * left.
        exists d.
        splits*.
      * right.
        exists pc' m' h' t' Σ'0.
        splits*.
    + unfold gc_occurred in *.
      super_destruct; subst.
      assert (wellformed_aux Γ Σ' ⟨c1;; c2, pc0, memory, [h1_1_pc ⊎ h1_1_not_pc, H10], t + δ⟩ pc''') by eauto 2.
      remember_simple (IHstepmany _ _ _ _ _ _ _ _ _ _ _ H2 eq_refl eq_refl).
      assert (c1 <> Stop).
      {
        intro; subst.
        invert_wf_aux.
        do 2 specialize_gen.
        invert_wt_cmd.
        invert_wt_stop.
      }
      assert (c1 <> TimeOut).
      {
        intro; subst.
        invert_wf_aux.
        do 2 specialize_gen.
        invert_wt_cmd.
        invert_wt_timeout.
      }
      super_destruct; subst.
      * left.
        exists d.
        splits*.
      * right.
        exists pc' m' h' t' Σ'0.
        splits*.
Qed.

Lemma wf_while:
  forall Γ Σ e c pc m h t pc',
    wellformed_aux Γ Σ ⟨WHILE e DO c END, pc, m, h, t ⟩ pc' ->
    wellformed_aux Γ Σ ⟨c, pc, m, h, t ⟩ pc.
Proof.
  intros.
  inverts H.
  do 2 specialize_gen.
  invert_wt_cmd.
  eauto 2.
Qed.
Hint Resolve wf_while.

Lemma while_typing_is_fixpoint:
  forall Γ Σ e c pc m h t pc',
    wellformed_aux Γ Σ ⟨WHILE e DO c END, pc, m, h, t⟩ pc' ->
    pc = pc'.
Proof.
  intros.
  invert_wf_aux.
  do 2 specialize_gen.
  invert_wt_cmd.
  reflexivity.
Qed.
Hint Resolve while_typing_is_fixpoint.

Lemma about_while_step:
  forall e c c' pc pc' m m' h h' t t' Γ Σ Σ',
    ⟨WHILE e DO c END, pc, m, h, t⟩ ⇒ (Γ, Σ, Σ') ⟨c', pc', m', h', t'⟩ ->
    pc = pc' /\ m = m' /\
    ((eval m e = Some (ValNum 0) /\ c' = Stop /\ h = h' /\ t' = S t) \/
     (exists n, n <> 0 /\ eval m e = Some (ValNum n) /\
           c' = (c ;; WHILE e DO c END) /\ h = h' /\ t' = S t) \/
     gc_occurred (WHILE e DO c END) c' pc pc' m m' h h' t t' Σ Σ').
Proof.
  intros.
  invert_step.
  - splits*.
  - splits*.
    right.
    left.
    exists n.
    splits*.
  - splits*.
    right.
    right.
    unfolds.
    splits*.
    do 7 eexists.
    splits; reflexivity || eauto.
Qed.

Lemma gc_noninterference_many:
  forall ℓ_adv φ m1 m1' h1 h1' m2 h2 Γ Σ1 Σ2 c c' pc pc' pc1' pc2' t t' Σ1' n,
    wf_bijection ℓ_adv φ Γ Σ1 m1 h1 ->
    wf_bijection ℓ_adv (inverse φ) Γ Σ2 m2 h2 ->
    state_low_eq ℓ_adv φ m1 h1 m2 h2 Γ Σ1 Σ2 ->
    wellformed_aux Γ Σ1 ⟨c, pc, m1, h1, t⟩ pc1' ->
    wellformed_aux Γ Σ2 ⟨c, pc, m2, h2, t⟩ pc2' ->
    pc ⊑ ℓ_adv ->
    gc_trans Σ1 Σ1' ⟨c, pc, m1, h1, t⟩ ⟨c', pc', m1', h1', t'⟩ n ->
    exists ψ m2' h2' Σ2',
      gc_trans Σ2 Σ2' ⟨c, pc, m2, h2, t⟩ ⟨c', pc', m2', h2', t'⟩ n /\
      wf_bijection ℓ_adv ψ Γ Σ1' m1' h1' /\
      wf_bijection ℓ_adv (inverse ψ) Γ Σ2' m2' h2' /\
      state_low_eq ℓ_adv ψ m1' h1' m2' h2' Γ Σ1' Σ2'.
Proof.
  intros.
  revert φ H H0 H1.
  revert m2 h2 H3.
  dependent induction H5; intros.
  - inverts H2; inverts H3.
    construct_gc_run.
    super_destruct'; subst.
    assert (wellformed_aux Γ Σ' ⟨ c'0, pc'0, m', h', t'0 ⟩ pc1').
    {
      unfold gc_occurred_no_ex in *; super_destruct'; subst.
      eapply gc_preserves_wf; eauto 2.
    }
    assert (wellformed_aux Γ Σ2' ⟨ c'0, pc'0, m2', h2', t2' ⟩ pc2').
    {
      unfold gc_occurred_no_ex in *; super_destruct'; subst.
      eapply gc_preserves_wf; eauto 2.
    }
    unfold gc_occurred_no_ex in *.
    super_destruct'; subst.
    rewrite_inj.
    subst.
    remember_simple (IHgc_trans H17 H4 _ _ H23 _ H9 H10 H15).
    super_destruct'; subst.
    clear IHgc_trans.
    exists ψ0 m2'0 h2' Σ2'0.
    splits~; eauto 3.
    eapply GCTrans.
    + unfolds.
      splits~; eauto 3.
      do 7 eexists.
      splits; reflexivity || eauto.
    + eauto.
  - exists φ m2 h2 Σ2.
    splits~; eauto 3.
Qed.

Ltac construct_many_gc_run :=
  match goal with
    [H1: wf_bijection ?ℓ_adv ?φ ?Γ ?Σ1 ?m1 ?h1,
         H2: wf_bijection ?ℓ_adv (inverse ?φ) ?Γ ?Σ2 ?m2 ?h2,
             H3: state_low_eq ?ℓ_adv ?φ ?m1 ?h1 ?m2 ?h2 ?Γ ?Σ1 ?Σ2,
                 H4: wellformed_aux ?Γ ?Σ1 ⟨?c, ?pc, ?m1, ?h1, ?t1 ⟩ ?pc1_end,
                     H5: wellformed_aux ?Γ ?Σ2 ⟨?c, ?pc, ?s1, ?w1, ?t2⟩ ?pc2_end,
                         H6: ?pc ⊑ ?ℓ_adv,
                             H7: gc_trans ?Σ1 _ ⟨?c, ?pc, ?m1, ?h1, ?t1⟩
                                          ⟨_, _, _, _, _ ⟩ _ |- _] =>
    remember_simple (gc_noninterference_many H1 H2 H3 H4 H5 H6 H7)
  end.

Lemma high_event_low_event_implies_bridge:
  forall ℓ_adv Γ Σ Σ' Σ'' c1 c2 c'' pc pc' pc'' m m' m'' h h' h'' t t' t'' ev ev' n,
    ⟨ c1, pc, m, h, t ⟩ ↷ [ℓ_adv, Γ, Σ, Σ', ev, n] ⟨ Stop, pc', m', h', t' ⟩ ->
    high_event ℓ_adv ev ->
    ⟨c2, pc', m', h', t' ⟩ ⇒ [ev', Γ, Σ', Σ''] ⟨ c'', pc'', m'', h'', t'' ⟩ ->
    low_event ℓ_adv ev' ->
    ⟨ c1;; c2, pc, m, h, t ⟩ ↷ [ℓ_adv, Γ, Σ, Σ'', ev', S n] ⟨ c'', pc'', m'', h'', t'' ⟩.
Proof.
  intros.
  dependent induction H; intros.
  - unfolds in H.
    super_destruct; subst.
    exfalso; eauto.
  - unfold high_event_step in *.
    super_destruct.
    eapply bridge_trans_num with (cfg2 := ⟨c2, pc', m', h', t'⟩) (ev1 := ev).
    + unfolds.
      * splits*.
    + intro.
      unfold is_stop_config, cmd_of in *.
      subst.
      invert_event_step.
      eauto.
    + intro.
      unfold is_timeout_config, cmd_of in *.
      subst.
      invert_event_step.
      eauto.
    + eauto.
  - destruct cfg2 as [c1_ pc_ m_ h_ t_].
    remember_simple (IHbridge_step_num _ _ _ _ _ _ _ _ _ eq_refl eq_refl H3 H4 H5).
    unfold high_event_step in *.
    super_destruct.
    eapply bridge_trans_num with (ev1 := ev1) (cfg2 := ⟨ c1_;; c2, pc_, m_, h_, t_ ⟩).
    + unfolds.
      splits*.                      
    + unfolds.
      intro.
      discriminate.
    + unfolds.
      intro.
      discriminate.
    + eauto.
Qed.
Hint Resolve high_event_low_event_implies_bridge.

Lemma two_high_event_implies_bridge:
  forall ℓ_adv Γ Σ Σ' Σ'' c1 c2 pc pc' pc'' pc''' m m' m'' h h' h'' t t' t'' ev ev' n,
    wellformed_aux Γ Σ ⟨c1;; c2, pc, m, h, t⟩ pc''' ->
    ⟨c1, pc, m, h, t⟩ ↷ [ℓ_adv, Γ, Σ, Σ', ev, n] ⟨Stop, pc', m', h', t'⟩ ->
    high_event ℓ_adv ev ->
    high_event ℓ_adv ev' ->
    ⟨c2, pc', m', h', t'⟩ ⇒ [ev', Γ, Σ', Σ''] ⟨Stop, pc'', m'', h'', t''⟩ ->
    ⟨c1;; c2, pc, m, h, t⟩ ↷ [ℓ_adv, Γ, Σ, Σ'', ev', S n]
                           ⟨Stop, pc'', m'', h'', t''⟩.
Proof.
  intros.
  dependent induction H0.
  - unfold low_event_step in *.
    super_destruct.
    contradiction.
  - unfold high_event_step in *.
    super_destruct.
    assert (c2 <> Stop).
    {
      intro; subst.
      invert_wf_aux.
      do 2 specialize_gen.
      invert_wt_cmd.
      invert_wt_stop.
    }
    assert (c2 <> TimeOut).
    {
      intro; subst.
      invert_wf_aux.
      do 2 specialize_gen.
      invert_wt_cmd.
      invert_wt_timeout.
    }
    eapply bridge_trans_num with (ev1 := ev).
    + splits*.
    + eauto.
    + eauto.
    + eauto.
  - destruct cfg2 as [c1_ pc_ m_ h_ t_].
    unfold high_event_step in *.
    super_destruct.
    assert (wellformed_aux Γ Σ' ⟨c1_ ;; c2, pc_, m_, h_, t_ ⟩ pc''').
    {
      remember_simple (wf_seq _ _ _ _ _ _ _ _ _ H).
      super_destruct.
      assert (wellformed_aux Γ Σ' ⟨c1_, pc_, m_, h_, t_⟩ pc''0).
      {
        eapply preservation_event_step; eauto.
      }
      assert (pc''0 = pc').
      {
        remember_simple (wt_aux_soundness_bridge H10 H2).
        super_destruct; subst.
        reflexivity.
      }
      subst.
      inverts H10.
      constructor; eauto 3.
      intros.
      do 2 specialize_gen.
      inverts H9.
      assert (c2 <> Stop).
      {
        intro; subst.
        invert_wf_aux.
        repeat specialize_gen.
        invert_wt_cmd.
        invert_wt_stop.
      }
      assert (c2 <> TimeOut).
      {
        intro; subst.
        invert_wf_aux.
        repeat specialize_gen.
        invert_wt_cmd.
        invert_wt_timeout.
      }
      eapply wt_aux_seq; eauto.
    }
    remember_simple (IHbridge_step_num _ _ _ _ _ _ _ _ _ H8 eq_refl
                                       eq_refl H4 H5 H6).
    eapply bridge_trans_num with (ev1 := ev1).
    + unfold high_event_step.
      splits*.
    + intro.
      discriminate.
    + intro.
      discriminate.
    + eauto.
Qed.
Hint Resolve two_high_event_implies_bridge.

Lemma iso_events_sym:
  forall φ ev1 ev2,
    iso_events (left φ) ev1 ev2 ->
    iso_events (right φ) ev2 ev1.
Proof.
  intros.
  dependent induction H; eauto using eq_sym.
Qed.
Hint Resolve iso_events_sym.

Lemma event_low_eq_sym:
  forall φ ℓ_adv ev1 ev2,
    event_low_eq ℓ_adv (left φ) ev1 ev2 ->
    event_low_eq ℓ_adv (right φ) ev2 ev1.
Proof.
  intros.
  unfold event_low_eq in *.
  intuition.
Qed.
Hint Resolve event_low_eq_sym.

Lemma concat_bridge_step_seq:
  forall ℓ_adv Γ Σ Σ' Σ'' c1 c2 c'' pc pc' pc'' pc''' m m' m'' h h' h'' t t' t''
    ev ev' n1 n2,
    wellformed_aux Γ Σ ⟨c1;; c2, pc, m, h, t⟩ pc''' ->
    ⟨c1, pc, m, h, t⟩ ↷ [ℓ_adv, Γ, Σ, Σ', ev, n1] ⟨Stop, pc', m', h', t'⟩ ->
    high_event ℓ_adv ev ->
    ⟨c2, pc', m', h', t'⟩ ↷ [ℓ_adv, Γ, Σ', Σ'', ev', n2] ⟨c'', pc'', m'', h'', t''⟩ ->
    ⟨c1 ;; c2, pc, m, h, t⟩ ↷ [ℓ_adv, Γ, Σ, Σ'', ev', (S (n1 + n2))] ⟨c'', pc'', m'', h'', t''⟩.
Proof.
  intros.
  revert c1 c2 c'' pc pc' pc'' m m' m'' h h' h'' t t' t'' ev ev' Σ Σ' Σ'' n1 H H0 H1 H2.
  induction n2.
  - intros.
    replace (S (n1 + 0)) with (S n1) by omega.
    inverts H2.
    + unfold low_event_step in *.
      super_destruct.
      eapply high_event_low_event_implies_bridge; eauto 2.
    + unfold is_stop_config, cmd_of in *; subst.
      replace (n1 + 0) with n1 by omega.
      unfold is_stop_config, cmd_of in *.
      subst.
      unfold high_event_step in *.
      super_destruct.
      eapply two_high_event_implies_bridge; eauto 2.
  - intros.
    inverts H2.
    unfold high_event_step in *.
    super_destruct.
    destruct cfg2 as [c2' pc2 m2 h2 t2].
    revert c1 pc m h t Σ H H0.
    induction n1; intros.
    + replace (S (0 + S n2)) with (S (S n2)) by omega.
      inverts H0.
      * unfold low_event_step in *.
        super_destruct.
        contradiction.
      * unfold high_event_step in *.
        super_destruct.
        assert (c2 <> Stop).
        {
          intro; subst.
          inverts H.
          repeat specialize_gen.
          invert_wt_cmd.
          invert_wt_stop.
        }
        assert (c2 <> TimeOut).
        {
          intro; subst.
          inverts H.
          repeat specialize_gen.
          invert_wt_cmd.
          invert_wt_timeout.
        }
        eapply bridge_trans_num with (ev1 := ev); eauto.
    + invert_bridge_step.
      unfold high_event_step in *.
      super_destruct; subst.
      destruct cfg2 as [c1' pc1 m1 h1 t1].
      assert (wellformed_aux Γ Σ'1 ⟨ c1';; c2, pc1, m1, h1, t1 ⟩ pc''').
      {
        assert (exists pc'' Σ' m' h' t',
                   wellformed_aux Γ Σ ⟨ c1, pc, m, h, t ⟩ pc'' /\
                   wellformed_aux Γ Σ' ⟨ c2, pc'', m', h', t' ⟩ pc''') by eauto 2.
        super_destruct'; subst.
        assert (wellformed_aux Γ Σ'1 ⟨c1', pc1, m1, h1, t1⟩ pc''0).
        {
          eauto 2.          
        }
        repeat invert_wf_aux.
        constructor; eauto 2.
        intros.
        assert (c1 <> Stop).
        {
          intro; subst.
          repeat specialize_gen.
          invert_wt_cmd.
          invert_wt_stop.
        }
        assert (c2 <> Stop).
        {
          intro; subst.
          repeat specialize_gen.
          invert_wt_cmd.
          invert_wt_stop.
        }
        assert (c1 <> TimeOut).
        {
          intro; subst.
          repeat specialize_gen.
          invert_wt_cmd.
          invert_wt_timeout.
        }
        assert (c2 <> TimeOut).
        {
          intro; subst.
          repeat specialize_gen.
          invert_wt_cmd.
          invert_wt_timeout.
        }
        eauto.
      }
      remember_simple (IHn1 c1' pc1 m1 h1 t1 Σ'1 H7 H18).
      eapply bridge_trans_num.
      * eauto.
      * intro; discriminate.
      * intro; discriminate.
      * eauto.
Qed.
Hint Resolve concat_bridge_step_seq.

Lemma while_step_true:
  forall e c pc pc' m m' h h' t t' Γ Σ Σ' n,
    ⟨While e c, pc, m, h, t⟩ ⇒ * (Γ, Σ, Σ') ⟨Stop, pc', m', h', t'⟩ ->
    eval m e = Some (ValNum n) ->
    n <> 0 ->
    ⟨c ;; While e c, pc, m, h, S t⟩ ⇒ * (Γ, Σ, Σ') ⟨Stop, pc', m', h', t'⟩.
Proof.
  intros.
  dependent induction H.
  destruct cfg as [c2 pc2 m2 h2 t2].
  invert_step.
  - congruence.
  - eauto.
  - remember_simple (IHstepmany _ _ _ _ _ _ _ _ _ _ eq_refl eq_refl H1 H2).
    eapply StepManyN.
    + eapply GCStep.
      * eapply step_gc; reflexivity || congruence || eauto.
    + eauto.
Qed.

Lemma eval_low_eq_possibilistic:
  forall ℓ_adv φ m1 m2 h1 h2 Γ Σ1 Σ2 e v σ ℓ ι,
    wf_tenv Γ m1 ->
    wf_tenv Γ m2 ->
    state_low_eq ℓ_adv φ m1 h1 m2 h2 Γ Σ1 Σ2 ->
    eval m1 e = Some v ->
    ℓ ⊑ ℓ_adv ->
    expr_has_type Γ e (SecType σ (ℓ, ι)) ->
    exists u, onvals (left φ) v = Some u /\ eval m2 e = Some u.
Proof.
  intros.
  revert v σ ℓ ι H2 H3 H4.
  induction e; intros.
  - exists (ValNum n).
    eauto.
  - intros.
    invert_var_typing.
    assert (exists u, memory_lookup m2 i = Some u).
    {
      invert_state_low_eq.
      match goal with
        [H: context[low_domain_eq] |- _] =>
        solve[eapply H; eauto]
      end.
    }
    super_destruct; subst.
    exists u.
    splits*.
    unfold eval in *.
    assert (val_low_eq ℓ_adv (SecType σ (ℓ, ι)) v u φ).
    {
      invert_state_low_eq.
      eapply H9; eauto.
    }
    invert_val_low_eq; try contradiction; eauto.

  - match goal with
      [H: expr_has_type _ (BinOp _ _ _) _ |- _] =>
      inverts H
    end.
    destruct l1 as [ℓ1 ι1].
    destruct l2 as [ℓ2 ι2].
    injects H11.
    destruct_join_flowsto.
    rewrite -> about_eval in *.
    
    repeat break_match_hyp; contradiction || congruence || eauto.
    + injects.
      assert (exists u, onvals (left φ) (ValNum n) = Some u /\ eval m2 e1 = Some u) by eauto 2.
      assert (exists u, onvals (left φ) (ValNum n0) = Some u /\ eval m2 e2 = Some u) by eauto 2.
      super_destruct; subst.
      assert (exists n, u0 = ValNum n) by eauto.
      assert (exists n, u = ValNum n) by eauto.
      super_destruct; subst.
      unfold onvals in *.
      repeat injects.                    
      exists (ValNum (n2 + n1)).
      splits*.
      do 2 decide_exist.
      reflexivity.
    + injects.
      assert (exists u, onvals (left φ) (ValNum n) = Some u /\ eval m2 e1 = Some u) by eauto 2.
      assert (exists u, onvals (left φ) (ValNum n0) = Some u /\ eval m2 e2 = Some u) by eauto 2.
      super_destruct; subst.
      assert (exists n, u0 = ValNum n) by eauto.
      assert (exists n, u = ValNum n) by eauto.
      super_destruct; subst.
      unfold onvals in *.
      repeat injects.                    
      exists (ValNum (n2 * n1)).
      splits*.
      do 2 decide_exist.
      reflexivity.
Qed.
Hint Resolve eval_low_eq_possibilistic.

Lemma gc_run_and_stop_implies_bridge:
  forall ℓ_adv Γ Σ Σ' Σ'' c pc pc' pc'' m m' m'' h h' h'' t t' t'' n ev,
    gc_trans Σ Σ' ⟨c, pc, m, h, t⟩ ⟨c, pc', m', h', t'⟩ n ->
    ⟨c, pc', m', h', t'⟩ ⇒ [ev, Γ, Σ', Σ''] ⟨Stop, pc'', m'', h'', t''⟩ ->
    high_event ℓ_adv ev ->
    ⟨c, pc, m, h, t⟩ ↷ [ℓ_adv, Γ, Σ, Σ'', ev, n] ⟨Stop, pc'', m'', h'', t''⟩.
Proof.
  intros.
  revert c pc m h t Σ H H0.
  induction n; intros.
  - inverts H.
    eapply bridge_stop_num.
    + splits*.
    + eauto.
  - inverts H.
    unfold gc_occurred in *.
    super_destruct; subst.
    remember_simple (IHn _ _ _ _ _ _ H16 H0).
    eapply bridge_trans_num with (ev1 := EmptyEvent) (cfg2 := ⟨ c', pc'0, m'0, [h1_1_pc ⊎ h1_1_not_pc, H9], t + δ ⟩) (Σ' := Σ'0).
    + unfolds.
      splits.
      * eapply EventGCStep; eauto.
      * intro; invert_low_event.
    + eauto.
    + eauto.
    + eauto.
Qed.
Hint Resolve gc_run_and_stop_implies_bridge.

Lemma high_pc_does_not_update_low_states_many:
  forall c c' pc pc' pc'' m m' h h' t t' Σ Σ' Γ ℓ,
    ~ pc ⊑ ℓ ->
    ~ contains_low_backat ℓ c ->
    wellformed_aux Γ Σ ⟨c, pc, m, h, t⟩ pc'' ->
    ⟨c, pc, m, h, t⟩ ⇒ * (Γ, Σ, Σ') ⟨c', pc', m', h', t'⟩ ->
    state_low_eq ℓ (identity_bijection loc) m h m' h' Γ Σ Σ'.
Proof.
  intros.
  dependent induction H2.
  - invert_wf_aux.
    eauto.
  - destruct cfg as [c2 pc2 m2 h2 t2].
    assert (state_low_eq ℓ (identity_bijection loc) m h m2 h2 Γ Σ Σ') by eauto 2.
    assert (~ pc2 ⊑ ℓ).
    {
      destruct (eq_cmd_dec c Stop); subst.
      - invert_step.
        eauto.
      - destruct (eq_cmd_dec c TimeOut); subst.
        + invert_step.
          eauto.
        + invert_wf_aux.
          repeat specialize_gen.
          eauto 2 using high_pc_and_no_low_backat_implies_high_pc.
    }
    assert (~ contains_low_backat ℓ c2)
      by eauto 2 using no_spurious_low_backats.
    assert (wellformed_aux Γ Σ' ⟨ c2, pc2, m2, h2, t2 ⟩ pc'').
    {
      eapply preservation; eauto.
    }
    assert (state_low_eq ℓ (identity_bijection loc) m2 h2 m' h' Γ Σ' Σ'') by eauto 2.
    assert (wellformed_aux Γ Σ'' ⟨ c', pc', m', h', t' ⟩ pc'').
    {
      eapply preservation_many_steps; eauto 2.
    }
    rewrite <- (compose_id_left (identity_bijection loc)).
    repeat invert_wf_aux.
    eauto 2 using state_low_eq_trans.
Qed.
Hint Resolve high_pc_does_not_update_low_states_many.

Lemma high_pc_and_no_low_backat_implies_high_pc_many:
  forall ℓ Γ Σ Σ' c c' pc pc' pc'' m m' h h' t t',
    ~ contains_low_backat ℓ c ->
    wellformed_aux Γ Σ ⟨c, pc, m, h, t⟩ pc'' ->
    ~ pc ⊑ ℓ ->
    ⟨c, pc, m, h, t⟩ ⇒ * (Γ, Σ, Σ') ⟨c', pc', m', h', t'⟩ ->
    ~ pc' ⊑ ℓ.
Proof.
  intros.
  dependent induction H2; eauto 2.
  destruct cfg as [c2 pc2 m2 h2 t2].
  assert (c <> Stop).
  {
    intro; subst.
    invert_step.
    eauto.
  }
  assert (c <> TimeOut).
  {
    intro; subst.
    invert_step.
    eauto.
  }
  assert (~ pc2 ⊑ ℓ).
  {
    invert_wf_aux.
    do 2 specialize_gen.
    eauto 2 using high_pc_and_no_low_backat_implies_high_pc.
  }
  assert (wellformed_aux Γ Σ' ⟨c2, pc2, m2, h2, t2⟩ pc'').
  {
    eapply preservation; eauto 2.
  }
  assert (~ contains_low_backat ℓ c2)
    by eauto 2 using no_spurious_low_backats.
  eauto 2.
Qed.
Hint Resolve high_pc_and_no_low_backat_implies_high_pc_many.

Inductive step_many_num: tenv -> stenv -> stenv -> config -> config -> nat ->
                         Prop :=
  StepManyNumRefl:
    forall Γ Σ c pc m h t,
      step_many_num Γ Σ Σ ⟨c, pc, m, h, t⟩ ⟨c, pc, m, h, t⟩ 0
| StepManyNumTrans:
    forall Γ Σ Σ' Σ'' c c' c'' pc pc' pc'' m m' m'' h h' h'' t t' t'' n,
      ⟨c, pc, m, h, t⟩ ⇒ (Γ, Σ, Σ') ⟨c', pc', m', h', t'⟩ ->
      step_many_num Γ Σ' Σ'' ⟨c', pc', m', h', t'⟩ ⟨c'', pc'', m'', h'', t''⟩ n ->
      step_many_num Γ Σ Σ'' ⟨c, pc, m, h, t⟩ ⟨c'', pc'', m'', h'', t''⟩ (S n).
Hint Constructors step_many_num.

Notation "cfg1 '⇒' '(' Γ ',' Σ1 ',' Σ2 ',' n ')' cfg2" :=
  (step_many_num Γ Σ1 Σ2 cfg1 cfg2 n)  (at level 10, no associativity).

Lemma step_many_implies_step_many_num:
  forall c c' pc pc' m m' h h' t t' Γ Σ Σ',
    ⟨c, pc, m, h, t⟩ ⇒ * (Γ, Σ, Σ') ⟨c', pc', m', h', t'⟩ ->
    exists n,
      ⟨c, pc, m, h, t⟩ ⇒ (Γ, Σ, Σ', n) ⟨c', pc', m', h', t'⟩.
Proof.
  intros.
  dependent induction H; eauto 2.
  destruct cfg as [c2 pc2 m2 h2 t2].
  assert (exists n, ⟨ c2, pc2, m2, h2, t2 ⟩
                 ⇒ (Γ, Σ', Σ'', n) ⟨ c', pc', m', h', t' ⟩) by eauto 2.
  super_destruct; subst.
  exists (S n).
  eauto.
Qed.

Lemma stop_takes_no_steps':
  forall c' pc m h t pc' m' h' t' Γ Σ Σ' n,
    ⟨Stop, pc, m, h, t⟩ ⇒ (Γ, Σ, Σ', n) ⟨c', pc', m', h', t'⟩ ->
    n = 0.
Proof.
  intros.
  induction n.
  - reflexivity.
  - inverts H.
    invert_step.
    exfalso; eauto 2.
Qed.
Hint Resolve stop_takes_no_steps'.

Lemma concat_bridge_step_high:
  forall ℓ_adv Γ Σ Σ' Σ'' c1 c2 c'' pc pc' pc'' pc''' m m' m'' h h' h'' t t' t'' ev n1 n2,
    ~ pc ⊑ ℓ_adv ->
    wellformed_aux Γ Σ ⟨c1 ;; c2, pc, m, h, t⟩ pc''' ->
    ~ contains_low_backat ℓ_adv c1 ->
    ⟨c1, pc, m, h, t⟩ ⇒ (Γ, Σ, Σ', n1) ⟨Stop, pc', m', h', t'⟩ ->
    ⟨c2, pc', m', h', t'⟩
      ↷ [ℓ_adv, Γ, Σ', Σ'', ev, n2] ⟨c'', pc'', m'', h'', t''⟩ ->
    ⟨c1;; c2, pc, m, h, t⟩ ↷ [ℓ_adv, Γ, Σ, Σ'', ev,
                              (n1 + n2)] ⟨c'', pc'', m'', h'', t''⟩.
Proof.
  intros.
  revert c1 pc m h t c2 pc' m' h' t' Σ Σ' n2 H H0 H1 H2 H3.
  induction n1; intros.
  - inverts H2.
    invert_wf_aux.
    do 2 specialize_gen.
    invert_wt_cmd.
    invert_wt_stop.
  - match goal with
      [H: step_many_num _ _ _ _ _ (S _) |- _] =>
      inverts H
    end.
    assert (~ pc'0 ⊑ ℓ_adv).
    {
      invert_wf_aux.
      repeat specialize_gen.
      invert_wt_cmd.
      eapply high_pc_and_no_low_backat_implies_high_pc; eauto 2.
    }
    assert (~ contains_low_backat ℓ_adv c').
    {
      eauto 2 using no_spurious_low_backats.
    }
    destruct (eq_cmd_dec c' Stop); subst.
    + assert (n1 = 0) by eauto 2; subst.
      match goal with
        [H: step_many_num _ _ _ _ _ 0 |- _] =>
        inverts H
      end.
      assert (exists pc', wellformed_aux Γ Σ ⟨c1, pc, m, h, t⟩ pc') by eauto 2.
      assert (c1 <> Stop).
      {
        intro; subst.
        repeat invert_wf_aux.
        repeat specialize_gen.
        invert_wt_cmd.
        invert_wt_stop.
      }
      assert (c2 <> TimeOut).
      {
        intro; subst.
        repeat invert_wf_aux.
        repeat specialize_gen.
        invert_wt_cmd.
        invert_wt_timeout.
      }
      super_destruct.
      remember_simple (event_step_adequacy _ _ _ _ _ _ _ _ _ _ _ _ _ _ H5 H9).
      super_destruct.
      assert (high_event ℓ_adv ev0).
      {
        eauto 2 using wt_at_high_implies_high_event.
      }
      eapply bridge_trans_num.
      * unfolds.
        splits.
        {
          eapply EventSemStep.
          eapply event_sem_step_seq_stop; eauto.
        }
        {
          eauto 2.
        }
      * intro.
        unfold is_stop_config, cmd_of in *; subst.
        invert_wf_aux.
        repeat specialize_gen.
        invert_wt_cmd.
        invert_wt_stop.
      * intro.
        unfold is_timeout_config, cmd_of in *; subst.
        invert_wf_aux.
        repeat specialize_gen.
        invert_wt_cmd.
        invert_wt_timeout.
      * eauto.
    + destruct (eq_cmd_dec c' TimeOut); subst.
      * match goal with
          [H: step_many_num _ _ _ _ _ n1 |- _] =>
          inverts H
        end.
        invert_step.
        exfalso; eauto 2.
      * replace (S n1 + n2) with (S (n1 + n2)) by omega.
        assert (wellformed_aux Γ Σ'0 ⟨c' ;; c2, pc'0, m'0, h'0, t'0⟩ pc''').
        {
          assert (⟨c1 ;; c2, pc, m, h, t⟩ ⇒ (Γ, Σ, Σ'0) ⟨c' ;; c2, pc'0, m'0, h'0, t'0⟩).
          {
            eauto.
          }
          eauto 2 using preservation.
        }
        remember_simple (IHn1 _ _ _ _ _ _ _ _ _ _ _ _ _ H2 H5 H4 H19 H3).
        super_destruct.
        assert (exists pc', wellformed_aux Γ Σ ⟨c1, pc, m, h, t⟩ pc') by eauto 2.
        super_destruct.
        remember_simple (event_step_adequacy _ _ _ _ _ _ _ _ _ _ _ _ _ _ H7 H9).
        super_destruct.
        assert (high_event ℓ_adv ev0).
        {
          eauto 3 using wt_at_high_implies_high_event.
        }
        eapply bridge_trans_num.
        { unfolds.
          splits.
          - eapply EventSemStep.
            eapply event_sem_step_seq_nonstop with (c1' := c'); eauto.
          - eauto 2.
        }
        { intro; discriminate. }
        { intro; discriminate. }
        { eauto. }
Qed.

Inductive gc_or_inc: tenv -> stenv -> config -> config -> Prop :=
  Inc:
    forall Γ Σ pc m h t t' ℓ,
      sem_step ⟨BackAt ℓ t', pc, m, h, t⟩ ⟨BackAt ℓ t', pc, m, h, S t⟩ Γ Σ Σ ->
      gc_or_inc Γ Σ ⟨BackAt ℓ t', pc, m, h, t⟩ ⟨BackAt ℓ t', pc, m, h, S t⟩
| GC:
    forall ℓ t' pc m h h' t1 t2 Σ Γ,
      gc_occurred (BackAt ℓ t') (BackAt ℓ t') pc pc m m h h' t1 t2 Σ Σ ->
      gc_or_inc Γ Σ ⟨BackAt ℓ t', pc, m, h, t1⟩ ⟨BackAt ℓ t', pc, m, h', t2⟩.
Hint Constructors gc_or_inc.

Inductive gc_or_inc_many: tenv -> stenv -> config -> config -> nat -> Prop :=
  GCOrIncRefl:
    forall Γ Σ cfg,
      gc_or_inc_many Γ Σ cfg cfg 0
| GCOrIncTrans:
    forall Γ Σ cfg1 cfg2 cfg3 n,
      gc_or_inc Γ Σ cfg1 cfg2 ->
      gc_or_inc_many Γ Σ cfg2 cfg3 n ->
      gc_or_inc_many Γ Σ cfg1 cfg3 (S n).
Hint Constructors gc_or_inc_many.

Lemma construct_gc_or_inc_many:
  forall φ l n pc m h t t' s w Σ1 Σ2 Γ ℓ_adv h' pc1_end pc2_end k,
    state_low_eq ℓ_adv φ m h s w Γ Σ1 Σ2 ->
    gc_or_inc_many Γ Σ1 ⟨BackAt l n, pc, m, h, t⟩
                   ⟨BackAt l n, pc, m, h', t'⟩ k ->
    pc ⊑ ℓ_adv ->
    wellformed_aux Γ Σ1 ⟨BackAt l n, pc, m, h, t⟩ pc1_end ->
    wellformed_aux Γ Σ2 ⟨BackAt l n, pc, s, w, t⟩ pc2_end ->
    wf_bijection ℓ_adv φ Γ Σ1 m h ->
    wf_bijection ℓ_adv (inverse φ) Γ Σ2 s w ->
    exists w' ψ,
      gc_or_inc_many Γ Σ2 ⟨BackAt l n, pc, s, w, t⟩
                     ⟨BackAt l n, pc, s, w', t'⟩ k /\
      wf_bijection ℓ_adv ψ Γ Σ1 m h' /\
      wf_bijection ℓ_adv (inverse ψ) Γ Σ2 s w' /\
      state_low_eq ℓ_adv ψ m h' s w' Γ Σ1 Σ2.
Proof.
  intros.
  revert φ w H H1 H2 H3 H4 H5.
  dependent induction H0; intros.
  - do 2 eexists.
    splits*.
  - inverts H.
    + assert (wellformed_aux Γ Σ ⟨BackAt l n, pc, m, h, S t⟩ pc1_end) by eauto 2.
      assert (wellformed_aux Γ Σ2 ⟨BackAt l n, pc, s, w, S t⟩ pc2_end) by eauto 2.
      remember_simple (IHgc_or_inc_many _ _ _ _ _ _ _ _ eq_refl eq_refl _ _ H1 H2 H H7 H5 H6).
      super_destruct; subst.
      invert_sem_step.
      * exists w' ψ.
        splits*.
    + assert (⟨BackAt l n, pc, m, h, t⟩
                ⇒ (Γ, Σ, Σ) ⟨BackAt l n, pc, m, h'0, t2⟩).
      {
        unfold gc_occurred in *.
        super_destruct; subst.
        rewrite_inj.
        eapply GCStep.
        eapply step_gc; reflexivity || eauto.
      }
      repeat invert_wf_aux.
      construct_gc_run.
      super_destruct; subst.
      unfold gc_occurred_no_ex in *.
      super_destruct; subst.
      assert (wellformed_aux Γ Σ2' ⟨BackAt l n, pc2', m2', [h2_pc ⊎ h2_not_pc, H2'], t + δ⟩ pc2_end).
      {
        eapply gc_preserves_wf; eauto 2.
      }
      assert (wellformed_aux Γ Σ ⟨BackAt l n, pc2', m, [h_pc ⊎ h_not_pc, H4], t + δ ⟩ pc1_end).
      {
        eapply gc_preserves_wf; eauto 2.
      }
      remember_simple (IHgc_or_inc_many _ _ _ _ _ _ _ _ eq_refl eq_refl _ _ H15 H2 H30 H29 H9 H10).
      super_destruct; subst.
      exists w' ψ0.
      splits*.
      eapply GCOrIncTrans.
      * eapply GC.
        { unfolds.
          splits*.
          do 7 eexists.
          splits; reflexivity || eauto. }
      * eauto.
Qed.

Lemma gc_or_inc_many_preserves_wf:
  forall Γ Σ c pc m h t pc' m' h' t' pc_end k,
    gc_or_inc_many Γ Σ ⟨c, pc, m, h, t⟩ ⟨c, pc', m', h', t'⟩ k ->
    wellformed_aux Γ Σ ⟨c, pc, m, h, t⟩ pc_end ->
    wellformed_aux Γ Σ ⟨c, pc', m', h', t'⟩ pc_end.
Proof.
  intros.
  dependent induction H.
  - eauto.
  - inverts H.
    + assert (wellformed_aux Γ Σ ⟨BackAt ℓ t'0, pc, m, h, S t ⟩ pc_end) by eauto 2.
      eapply IHgc_or_inc_many; eauto.
    + unfold gc_occurred in *.
      super_destruct; subst.
      eapply IHgc_or_inc_many; eauto 2.
Qed.
Hint Resolve gc_or_inc_many_preserves_wf.

Lemma high_gc_or_inc_many_preserves_state_low_eq:
  forall Γ Σ pc ℓ_adv l k m h h' t t' n pc'',
    ~ pc ⊑ ℓ_adv ->
    wellformed_aux Γ Σ ⟨BackAt l k, pc, m, h, t⟩ pc'' ->
    gc_or_inc_many Γ Σ
                   ⟨BackAt l k, pc, m, h, t⟩
                   ⟨BackAt l k, pc, m, h', t'⟩ n ->
    state_low_eq ℓ_adv (identity_bijection loc) m h m h' Γ Σ Σ.
Proof.
  intros.
  dependent induction H1.
  - invert_wf_aux.
    eapply state_low_eq_refl; eauto 2.
  - inverts H2.
    + assert (wellformed_aux Γ Σ ⟨BackAt l k, pc, m, h, S t⟩ pc'') by eauto 2.
      eapply IHgc_or_inc_many; eauto 2.
    + unfold gc_occurred in *.
      super_destruct; subst.
      assert (state_low_eq ℓ_adv (identity_bijection loc) m
                           ([[h1_1_pc ⊎ h1_1_not_pc, H10] ⊎ h1_2, H9]) m
                           ([h1_1_pc ⊎ h1_1_not_pc, H10]) Γ Σ
                           Σ)
        by (invert_wf_aux; eauto 2 using high_pc_gc_does_not_update_low_states).
      assert (wellformed_aux Γ Σ ⟨BackAt l k, pc, m, [h1_1_pc ⊎ h1_1_not_pc, H10], t + δ ⟩ pc'') by eauto 2.
      assert (wellformed_aux Γ Σ ⟨BackAt l k, pc, m, h', t' ⟩ pc'') by eauto 2.
      assert (state_low_eq ℓ_adv (identity_bijection loc) m
                           ([h1_1_pc ⊎ h1_1_not_pc, H10]) m h' Γ Σ Σ)
        by eauto 2.
      rewrite <- (compose_id_left (identity_bijection loc)).
      repeat invert_wf_aux.
      eapply state_low_eq_trans with (m2 := m) (Σ2 := Σ) (h2 := ([h1_1_pc ⊎ h1_1_not_pc, H10])); eauto 2.
Qed.

Lemma square_lemma:
  forall φ ψ γ m h s w m' h' s' w' Γ Σ1 Σ2 Σ1' Σ2' ℓ,
    wf_tenv Γ m ->
    wf_tenv Γ m' ->
    wf_tenv Γ s ->
    wf_tenv Γ s' ->
    wf_stenv Σ1 h ->
    wf_stenv Σ1' h' ->
    wf_stenv Σ2 w ->
    wf_stenv Σ2' w' ->
    dangling_pointer_free m h ->
    dangling_pointer_free m' h' ->
    dangling_pointer_free s w ->
    dangling_pointer_free s' w' ->
    heap_level_bound Γ m h Σ1 ->
    heap_level_bound Γ m' h' Σ1' ->
    heap_level_bound Γ s w Σ2 ->
    heap_level_bound Γ s' w' Σ2' ->
    state_low_eq ℓ φ m h s w Γ Σ1 Σ2 ->
    state_low_eq ℓ ψ m h m' h' Γ Σ1 Σ1' ->
    state_low_eq ℓ γ s w s' w' Γ Σ2 Σ2' ->
    state_low_eq ℓ
                 (bijection.bijection_compose (inverse ψ) (bijection.bijection_compose φ γ)) m' h' s' w' Γ Σ1' Σ2'.
Proof.
  intros.
  assert (state_low_eq ℓ (bijection.bijection_compose φ γ) m h s' w' Γ Σ1 Σ2').
  {
    eapply state_low_eq_trans with (m2 := s) (h2 := w) (Σ2 := Σ2); eauto 2.
  }
  assert (state_low_eq ℓ (inverse ψ) m' h' m h Γ Σ1' Σ1).
  {
    eapply state_low_eq_symmetry; eauto 2.
  }
  eapply state_low_eq_trans with (m2 := m) (h2 := h) (Σ2 := Σ1); eauto 2.
Qed.
Hint Resolve square_lemma.

Lemma seq_goes_to_stop_implies:
  forall c1 c2 pc m h t pc' m' h' t' Σ Σ' Γ pc_end,
    wellformed_aux Γ Σ ⟨c1 ;; c2, pc, m, h, t⟩ pc_end ->
    ⟨c1 ;; c2, pc, m, h, t⟩ ⇒ * (Γ, Σ, Σ') ⟨Stop, pc', m', h', t'⟩ ->
    exists pc'' m'' h'' t'' Σ'',
      ⟨c1, pc, m, h, t⟩ ⇒ * (Γ, Σ, Σ'') ⟨Stop, pc'', m'', h'', t''⟩ /\
      ⟨c2, pc'', m'', h'', t''⟩ ⇒ * (Γ, Σ'', Σ') ⟨Stop, pc', m', h', t'⟩.
Proof.
  intros.
  dependent induction H0.
  inverts H1.
  - invert_sem_step.
    + exists pc'0 m'0 h'0 t'0 Σ'.
      splits*.
    + assert (wellformed_aux Γ Σ' ⟨c1' ;; c2, pc'0, m'0, h'0, t'0⟩ pc_end).
      {
        assert (⟨c1 ;; c2, pc, m, h, t⟩ ⇒ (Γ, Σ, Σ') ⟨c1' ;; c2, pc'0, m'0, h'0, t'0⟩).
        {
          constructor.
          constructor; eauto.
        }
        eapply preservation; eauto 2.
      }
      remember_simple (IHstepmany _ _ _ _ _ _ _ _ _ _ H1 eq_refl eq_refl).
      super_destruct; subst.
      exists pc'' m'' h'' t'' Σ''0.
      splits*.
  - invert_gc_step.
    assert (wellformed_aux Γ Σ' ⟨c1;; c2, pc'0, m'0, [h1_pc ⊎ h1_not_pc, H2], t + δ⟩ pc_end).
    {
      eapply gc_preserves_wf; eauto 2.
      erewrite -> disjoint_union_proof_irrelevance.
      eauto.
    }
    remember_simple (IHstepmany _ _ _ _ _ _ _ _ _ _ H4 eq_refl eq_refl).
    super_destruct; subst.
    exists pc'' m'' h'' t'' Σ''0.
    splits*.
    eapply StepManyN.
    + eapply GCStep.
      * eapply step_gc; reflexivity || eauto 2.
        { intro; subst.
          invert_wf_aux.
          do 2 specialize_gen.
          invert_wt_cmd.
          invert_wt_stop. }
        { intro; subst.
          invert_wf_aux.
          do 2 specialize_gen.
          invert_wt_cmd.
          invert_wt_timeout. }
    + eauto.
Qed.

Lemma high_pc_gc_trans_state_low_eq:
  forall c pc m h t pc' m' h' pc'' t' n ℓ Γ Σ,
    ~ pc ⊑ ℓ ->
    wellformed_aux Γ Σ ⟨c, pc, m, h, t⟩ pc'' ->
    gc_trans Σ Σ ⟨c, pc, m, h, t⟩
             ⟨c, pc', m', h', t'⟩ n ->
    state_low_eq ℓ (identity_bijection loc) m h m' h' Γ Σ Σ.
Proof.
  intros.
  dependent induction H1.
  - unfold gc_occurred in *.
    super_destruct; subst.
    invert_wf_aux.
    assert (state_low_eq ℓ (identity_bijection loc) m'0
                         ([[h1_1_pc ⊎ h1_1_not_pc, H10] ⊎ h1_2, H9])
                         m'0 ([h1_1_pc ⊎ h1_1_not_pc, H10])
                         Γ Σ' Σ').
    {
      eapply high_pc_gc_does_not_update_low_states; eauto 2.
    }
    assert (wellformed_aux Γ Σ' ⟨c', pc'0, m'0, [h1_1_pc ⊎ h1_1_not_pc, H10], t + δ⟩ pc'').
    {
      eapply gc_preserves_wf; eauto 2.
    }
    remember_simple (IHgc_trans _ _ _ _ _ _ _ _ _ H H2 eq_refl eq_refl eq_refl).
    rewrite <- (compose_id_left (identity_bijection loc)).
    assert (wellformed_aux Γ Σ' ⟨c', pc', m', h', t'⟩ pc'').
    {
      eauto 2.
    }
    repeat invert_wf_aux.
    eapply state_low_eq_trans; eauto 2.
  - invert_wf_aux; eauto 2.
Qed.

Lemma wf_at_implies:
  forall Γ Σ l e c1 pc m h t pc',
    wellformed_aux Γ Σ ⟨At l e c1, pc, m, h, t⟩ pc' ->
    exists pc'',
      wellformed_aux Γ Σ ⟨c1, l, m, h, t⟩ pc''.
Proof.
  intros.
  inverts H.
  do 2 specialize_gen.
  invert_wt_cmd.
  eauto 3.
Qed.
Hint Resolve wf_at_implies.

Lemma wf_seq_half_step_implies_wf_many:
  forall Γ Σ Σ' c1 c2 pc m h t pc' m' h' t' pc'',
    wellformed_aux Γ Σ ⟨c1;; c2, pc, m, h, t⟩ pc'' ->
    ⟨c1, pc, m, h, t ⟩ ⇒ * (Γ, Σ, Σ') ⟨STOP, pc', m', h', t'⟩ ->
    wellformed_aux Γ Σ' ⟨c2, pc', m', h', t'⟩ pc''.
Proof.
  intros.
  dependent induction H0.
  - invert_wf_aux.
    do 2 specialize_gen.
    invert_wt_cmd.
    invert_wt_stop.
  - assert (exists pc', wellformed_aux Γ Σ ⟨c1, pc, m, h, t⟩ pc') by eauto 2.
    super_destruct; subst.
    assert (c1 <> Stop).
    {
      intro; subst.
      invert_step.
      exfalso; eauto 2.
    }
    assert (c1 <> TimeOut).
    {
      intro; subst.
      invert_step.
      exfalso; eauto 2.
    }
    assert (pc' = pc'0).
    {
      eapply wt_aux_soundness_many; eauto 2.                    
    }
    subst.
    assert (wellformed_aux Γ Σ' cfg pc'0).
    {
      destruct cfg.                    
      super_destruct.
      eauto 2 using preservation.
    }
    destruct cfg as [c' pc' m'' h'' t''].
    destruct (eq_cmd_dec c' Stop).
    {
      subst.
      _apply stop_takes_no_step_many_step in *.
      super_destruct; subst.
      eapply wf_seq_half_step_implies_wf; eauto.
    }
    {
      destruct (eq_cmd_dec c' TimeOut).
      - subst.
        _apply timeout_takes_no_step_many_step in *.
        super_destruct; subst.
        discriminate.
      - assert (⟨c1 ;; c2, pc, m, h, t⟩ ⇒ (Γ, Σ, Σ') ⟨c' ;; c2, pc', m'', h'', t''⟩).
        {
          constructor.
          constructor; eauto 2.
        }
        assert (wellformed_aux Γ Σ' ⟨c' ;; c2, pc', m'', h'', t''⟩ pc'').
        {
          eapply preservation; eauto 2.
        }
        eapply IHstepmany; eauto 2.
    }
Qed.
Hint Resolve wf_seq_half_step_implies_wf_many.

Ltac invert_taint_eq :=
  match goal with
    [H: taint_eq _ _ _ _ _ _ _ _ _ _ _ |- _] =>
    unfolds in H; destructs H
  end.

Ltac invert_taint_eq_cmd :=
  match goal with
    [H: taint_eq_cmd _ _ |- _] =>
    inverts H
  end.

Lemma skip_bridge_properties:
  forall pc pc' c' m m' h h' t t' ℓ Γ Σ Σ' ev n,
    ⟨Skip, pc, m, h, t⟩ ↷ [ℓ, Γ, Σ, Σ', ev, n] ⟨c', pc', m', h', t'⟩ ->
    pc = pc' /\ m = m' /\ Σ = Σ' /\ ev = EmptyEvent /\ c' = Stop /\
    gc_trans Σ Σ' ⟨Skip, pc, m, h, t⟩ ⟨Skip, pc, m, h', t' - 1⟩ n /\
    ⟨Skip, pc, m, h', t' - 1⟩ ⇒ (Γ, Σ, Σ) ⟨Stop, pc, m, h', t'⟩.
Proof.
  intros.
  dependent induction H.
  - invert_low_event_step.
    invert_event_step; invert_low_event.
  - invert_high_event_step.
    unfold is_stop_config, cmd_of in *; subst.
    invert_event_step.
    invert_sem_step.
    replace (S t - 1) with (t + 0) by omega.
    rewrite -> plus_0_r.
    splits*.
  - invert_high_event_step.
    invert_event_step.
    + contradict H0; eauto.
    + specialize (IHbridge_step_num _ _ _ _ _ _ _ _ _ eq_refl eq_refl).
      super_destruct; subst.
      splits*.
      eapply GCTrans.
      * unfolds.
        splits*.
        do 7 eexists.
        splits; reflexivity || eauto 2.
      * eauto.
Qed.

Lemma taint_eq_heap_refl:
  forall ℓ Σ m h,
    wf_stenv Σ h ->
    taint_eq_heap ℓ (identity_bijection loc) Σ Σ m h m h.
Proof.
  intros.
  unfolds.
  intros.
  unfold left, identity_bijection in * |-.
  rewrite_inj.
  splits*.
  intros.
  rewrite_inj.
  destruct τ as [σ ε].
  destruct σ.
  - assert (exists n, v2 = ValNum n) by eauto.
    super_destruct; subst.
    eauto.
  - assert (exists loc, v2 = ValLoc loc) by eauto.
    super_destruct; subst.
    eauto.
Qed.
Hint Resolve taint_eq_heap_refl.

Lemma taint_eq_stenv_refl:
  forall Σ,
    taint_eq_stenv (identity_bijection loc) Σ Σ.
Proof.
  intros.
  unfolds.
  intros.
  unfold left, identity_bijection in *.
  rewrite_inj.
  splits*.
Qed.
Hint Resolve taint_eq_stenv_refl.

Lemma high_supset:
  forall ℓ m h1 h2 loc H,
    high ℓ m h1 loc ->
    high ℓ m ([h1 ⊎ h2, H]) loc.
Proof.
  intros.
  destruct_high.
  - eapply HighReachable; eauto 2.
  - eapply HighHeapLevel; eauto 2.
Qed.
Hint Resolve high_supset.

Lemma low_gc_preserves_taint_eq_heap_domain_eq:
  forall ℓ m m' h h' c c' Σ Σ' t t' pc pc',
    pc ⊑ ℓ ->
    gc_occurred c c' pc pc' m m' h h' t t' Σ Σ' ->
    taint_eq_heap_domain_eq ℓ (identity_bijection loc) m m' h h'.
Proof.
  intros.
  unfold gc_occurred in *; super_destruct'; subst.
  unfolds.
  intros.
  unfold left, identity_bijection in *; rewrite_inj.
  splits; intros.
  - super_destruct'; subst.
    destruct_disjoint_heap_lookup.
    + splits; eauto 2.
      destruct_high.
      * eapply HighReachable.
        eapply reach_supset_if; eauto 2.
      * assert (ℓ0 = ℓ1).
        {
          assert (heap_lookup l2 ([[h1_1_pc ⊎ h1_1_not_pc, H8] ⊎ h1_2, H7]) = Some (ℓ0, μ)).
          {
            eapply disjoint_union_heap_lookup; eauto 2.
          }
          congruence.
        }
        subst.
        eapply HighHeapLevel; eauto 2.
    + assert (~ reach m' ([[h1_1_pc ⊎ h1_1_not_pc, H8] ⊎ h1_2, H7]) l2) by eauto 2.
      destruct_high.
      * contradiction.
      * rewrite_inj.
        assert (pc' = ℓ1) by eauto 2.
        subst.
        contradiction.
  - super_destruct'; subst.
    splits.
    + exists ν.
      eapply disjoint_union_heap_lookup; eauto 2.
    + eauto 2.
Qed.

Lemma taint_eq_heap_domain_eq_refl:
  forall m h ℓ,
    taint_eq_heap_domain_eq ℓ (identity_bijection loc) m m h h.
Proof.
  intros.
  unfolds.
  intros.
  unfold left, identity_bijection in *; rewrite_inj.
  splits*.
Qed.
Hint Resolve taint_eq_heap_domain_eq_refl.

Lemma taint_eq_heap_domain_eq_trans:
  forall ℓ Φ Ψ m1 m2 m3 h1 h2 h3,
    taint_eq_heap_domain_eq ℓ Φ m1 m2 h1 h2 ->
    taint_eq_heap_domain_eq ℓ Ψ m2 m3 h2 h3 ->
    taint_eq_heap_domain_eq ℓ (bijection.bijection_compose Φ Ψ) m1 m3 h1 h3.
Proof.
  intros.
  unfolds.
  intros.
  _apply left_compose in *.
  super_destruct; subst.
  destruct (left Φ l1) eqn:H_l1.
  - specialize (H2 _ eq_refl).
    eapply iff_trans; eauto 2.            
  - repeat specialize_gen.
    congruence.
Qed.

Lemma low_gc_trans_preserves_taint_eq_heap_domain_eq:
  forall ℓ n c c' pc pc' m m' h h' t t' Σ Σ',
    pc ⊑ ℓ ->
    gc_trans Σ Σ' ⟨c, pc, m, h, t⟩ ⟨c', pc', m', h', t'⟩ n ->
    taint_eq_heap_domain_eq ℓ (identity_bijection loc) m m' h h'.
Proof.
  intros.
  dependent induction H0; eauto 2.
  assert (pc = pc'0).
  {
    unfold gc_occurred in *; super_destruct'; congruence.
  }
  subst.
  specialize_gen.
  remember_simple (low_gc_preserves_taint_eq_heap_domain_eq H H1).
  rewrite <- (compose_id_right (identity_bijection loc)).
  eapply taint_eq_heap_domain_eq_trans; eauto 2.
Qed.
Hint Resolve low_gc_trans_preserves_taint_eq_heap_domain_eq.

Lemma low_gc_trans_preserves_taint_eq_heap:
  forall ℓ Γ c c' pc pc' m m' h h' t t' Σ Σ' n pc_end,
    gc_trans Σ Σ' ⟨c, pc, m, h, t⟩ ⟨c', pc', m', h', t'⟩ n ->
    pc ⊑ ℓ ->
    wellformed_aux Γ Σ ⟨c, pc, m, h, t⟩ pc_end ->
    taint_eq_heap ℓ (identity_bijection loc) Σ Σ m h m' h'.
Proof.
  intros.
  dependent induction H.
  - assert (taint_eq_heap ℓ (identity_bijection loc) Σ Σ' m h m'0 h'0).
    {
      invert_wf_aux.
      eapply gc_preserves_taint_eq_heap; eauto.
    }
    assert (pc = pc'0).
    {
      unfold gc_occurred in *; super_destruct'; congruence.
    }
    subst.
    assert (wellformed_aux Γ Σ' ⟨ c'0, pc'0, m'0, h'0, t'0 ⟩ pc_end) by eauto 3.
    assert (taint_eq_heap ℓ (identity_bijection loc) Σ' Σ' m'0 h'0 m' h') by eauto 2.
    clear IHgc_trans.
    unfold gc_occurred in *.
    super_destruct; subst.
    rewrite <- (compose_id_left (identity_bijection loc)).
    eapply taint_eq_heap_trans with (m' := m'0) (h' := [h1_1_pc ⊎ h1_1_not_pc, H13]).
    + unfolds.
      intros.
      unfold left, identity_bijection in * |-.
      rewrite_inj.
      eapply gc_trans_preserves_reach.
      eauto.
    + eauto.
    + invert_wf_aux; eauto 2.
    + eauto 2.
    + eauto 2.
    + eauto 2.
  - invert_wf_aux.
    eapply taint_eq_heap_refl; eauto.
Qed.
Hint Resolve low_gc_trans_preserves_taint_eq_heap.

Lemma assign_bridge_properties:
  forall i e pc pc' m m' h h' t t' Γ Σ Σ' ev n ℓ c',
    ⟨i ::= e, pc, m, h, t⟩ ↷ [ℓ, Γ, Σ, Σ', ev, n] ⟨c', pc', m', h', t'⟩ ->
    pc = pc' /\ Σ = Σ' /\ c' = Stop /\
    gc_trans Σ Σ ⟨i ::= e, pc, m, h, t⟩ ⟨i ::= e, pc, m, h', t' - 1⟩ n /\
    ⟨i ::= e, pc, m, h', t' - 1⟩ ↷ [ℓ, Γ, Σ, Σ, ev, 0] ⟨Stop, pc, m', h', t'⟩.
Proof.
  intros.
  dependent induction H.
  - invert_low_event_step.
    invert_event_step.
    + invert_sem_step.
      replace (S t - 1) with (t + 0) by omega.
      rewrite -> plus_0_r.
      splits*.
      eapply bridge_low_num; eauto 2.
      splits*.
    + invert_low_event.
  - unfold is_stop_config, cmd_of in *; subst.
    invert_high_event_step.
    invert_event_step.
    invert_sem_step.
    replace (S t - 1) with (t + 0) by omega.
    rewrite -> plus_0_r.
    splits*.
  - invert_high_event_step.
    invert_event_step.
    + contradict H0; eauto.
    + specialize (IHbridge_step_num _ _ _ _ _ _ _ _ _ _ _ eq_refl eq_refl).
      super_destruct; subst.
      splits*.
      eapply GCTrans.
      * unfolds.
        splits*.
        do 7 eexists.
        splits; reflexivity || eauto 2.
      * eauto.
Qed.

Lemma bijection_implies_lookup_taint:
  forall ℓ τ m1 m2 h1 h2 n Σ1 Σ2 loc1 loc2 loc1' loc2' Φ l1 l2 μ ν,
    taint_eq_heap ℓ Φ Σ1 Σ2 m1 h1 m2 h2 ->
    Σ1 loc1 = Some τ ->
    Σ2 loc2 = Some τ ->
    wf_stenv Σ1 h1 ->
    reach m1 h1 loc1 ->
    reach m2 h2 loc2 ->
    heap_lookup loc1 h1 = Some (l1, μ) ->
    heap_lookup loc2 h2 = Some (l2, ν) ->
    left Φ loc1 = Some loc2 ->
    lookup μ n = Some (ValLoc loc1') ->
    left Φ loc1' = Some loc2' ->
    lookup ν n = Some (ValLoc loc2').
Proof.
  intros.
  assert (high ℓ m1 h1 loc1) by eauto 2.
  assert (high ℓ m2 h2 loc2) by eauto 2.
  super_destruct; subst.
  remember_simple (H loc1 loc2 _ _ _ _ _ H7 H10 H11 H5 H6 H0 H1).
  super_destruct'; subst.
  assert (exists u, lookup ν n = Some u).
  {
    assert (exists v, lookup μ n = Some v) by eauto.
    eapply_lookup_func_domain_eq; eauto.
  }
  super_destruct; subst.
  destruct τ as [σ [ℓ' ι']].
  assert_wf_type.
  destruct σ.
  - assert (exists n, ValLoc loc1' = ValNum n) by eauto 3.
    super_destruct'; congruence.
  - invert_wf_type.
    assert (val_taint_eq Φ (SecType (Array s l) (ℓ', ∘)) (ValLoc loc1') u) by eauto.
    invert_val_taint_eq; congruence.
Qed.

Lemma taint_reach_in_extended_mem:
  forall Γ Σ1 Σ2 Φ m1 m2 h1 h2 τ ℓ_p ℓ loc1 loc2 loc1' loc2' x ℓ_adv,
    Γ x = Some (SecType (Array τ ℓ_p) (ℓ, ∘)) ->
    wf_tenv Γ m1 ->
    wf_stenv Σ1 h1 ->
    dangling_pointer_free m1 h1 ->
    dangling_pointer_free m2 h2 ->
    wf_taint_bijection ℓ_adv Φ m1 h1 ->
    taint_eq_mem Φ Γ m1 m2 ->
    taint_eq_reach Φ m1 h1 m2 h2 ->
    taint_eq_heap ℓ_adv Φ Σ1 Σ2 m1 h1 m2 h2 ->
    taint_eq_stenv Φ Σ1 Σ2 ->
    left Φ loc1 = Some loc2 ->
    left Φ loc1' = Some loc2' ->
    reach m1 h1 loc1' ->
    reach (m1 [x → ValLoc loc1']) h1 loc1 ->
    reach (m2 [x → ValLoc loc2']) h2 loc2.
Proof.
  intros.
  revert loc2 H9.
  dependent induction H12; intros.
  - assert_wf_type.
    invert_wf_type.
    destruct (decide (x = x0)); subst.
    + rewrite -> extend_memory_lookup_eq in *.
      rewrite_inj.
      eauto 2.
    + rewrite -> extend_memory_lookup_neq in * by solve[eauto 2].
      assert (exists τ', Γ x0 = Some τ') by eauto 2.
      super_destruct; subst.
      destruct τ' as [σ ε].
      destruct σ.
      * assert (exists n, ValLoc loc = ValNum n) by eauto 2.
        super_destruct; discriminate.
      * assert_wf_type.
        invert_wf_type.
        assert (exists v, memory_lookup m2 x0 = Some v).
        {
          eapply H5; eauto.
        }
        super_destruct; subst.
        assert (val_taint_eq Φ (SecType (Array s l) (l_ref, ∘)) (ValLoc loc) v).
        {
          eapply H5; eauto.
        }
        invert_val_taint_eq.
        rewrite_inj.
        eapply reach_mem.
        rewrite -> extend_memory_lookup_neq by solve[eauto 2].
        eauto.
  - assert (high ℓ_adv m1 h loc1').
    {
      eapply H4; eauto.
    }
    assert (reach m1 h loc) by eauto 2.
    assert (high ℓ_adv m1 h loc) by eauto 2.
    assert (exists ℓ μ, heap_lookup loc h = Some (ℓ, μ)) by eauto 2.
    super_destruct'; subst.
    rewrite_inj.
    assert (exists loc'', left Φ loc = Some loc'').
    {
      eapply H4; eauto.
    }
    super_destruct'; subst.
    assert (reach m2 h2 loc'').
    {
      eapply H6; eauto.
    }
    assert (high ℓ_adv m2 h2 loc'') by eauto 2.
    assert (exists ℓ μ, heap_lookup loc'' h2 = Some (ℓ, μ)) by eauto 2.
    super_destruct'; subst.
    assert (exists τ, Σ1 loc = Some τ) by eauto.
    super_destruct'; subst.
    assert (Σ2 loc'' = Some τ0).
    {
      eapply H8; eauto.
    }
    assert (lookup μ n = Some (ValLoc loc2)) by eauto 2 using bijection_implies_lookup_taint.
    eauto 3 using reach_heap, IHreach.
Qed.

Lemma reach_extend_with_num:
  forall m h loc x n Γ ℓ ι,
    reach m h loc ->
    wf_tenv Γ m ->
    Γ x = Some (SecType Int (ℓ, ι)) ->
    reach (extend_memory x (ValNum n)  m) h loc.
Proof.
  intros.
  dependent induction H.
  - destruct (decide (x = x0)); subst.
    + assert (exists n, ValLoc loc = ValNum n) by eauto 2.
      super_destruct; discriminate.
    + eapply reach_mem.
      * rewrite -> extend_memory_lookup_neq by solve[eauto 2].
        eauto.
  - repeat specialize_gen.
    eapply reach_heap; eauto.
Qed.
Hint Resolve reach_extend_with_num.

Lemma val_taint_eq_sym:
  forall τ Φ v1 v2,
    val_taint_eq Φ τ v1 v2 ->
    val_taint_eq (inverse Φ) τ v2 v1.
Proof.
  intros.
  invert_val_taint_eq; destruct Φ; eauto.
Qed.
Hint Resolve val_taint_eq_sym.

Lemma taint_eq_mem_sym:
  forall Φ Γ m1 m2,
    taint_eq_mem Φ Γ m1 m2 ->
    taint_eq_mem (inverse Φ) Γ m2 m1.
Proof.
  intros.
  unfold taint_eq_mem in *.
  super_destruct.
  splits*.
  intros.
  eapply iff_sym; eauto.
Qed.
Hint Resolve taint_eq_mem_sym.

Lemma taint_eq_heap_sym:
  forall ℓ_adv Φ Σ1 Σ2 m1 h1 m2 h2,
    taint_eq_heap ℓ_adv Φ Σ1 Σ2 m1 h1 m2 h2 ->
    taint_eq_heap ℓ_adv (inverse Φ) Σ2 Σ1 m2 h2 m1 h1.
Proof.
  intros.
  unfold taint_eq_heap in *.
  intros.
  assert (left Φ loc' = Some loc) by (destruct Φ; eauto).
  remember_simple (H _ _ _ _ _ _ _ H7 H2 H1 H4 H3 H6 H5).
  super_destruct; subst.
  splits*.
  - intros; eapply iff_sym; eauto.
Qed.
Hint Resolve taint_eq_heap_sym.

Lemma taint_eq_reach_trans:
  forall Φ Ψ m1 m2 m3 h1 h2 h3,
    taint_eq_reach Φ m1 h1 m2 h2 ->
    taint_eq_reach Ψ m2 h2 m3 h3 ->
    taint_eq_reach (bijection.bijection_compose Φ Ψ) m1 h1 m3 h3.
Proof.
  intros.
  unfolds.
  intros.
  _apply left_compose in *.
  super_destruct.
  destruct my.
  - eapply iff_trans; eauto.
  - repeat specialize_gen.
    discriminate.
Qed.

Lemma taint_eq_reach_refl:
  forall m h,
    taint_eq_reach (identity_bijection loc) m h m h.
Proof.
  intros.
  unfolds.
  intros.
  unfold left, identity_bijection in *.
  injects.
  splits*.
Qed.
Hint Resolve taint_eq_reach_refl.

Lemma taint_eq_cmd_contains_backat:
  forall c c',
    taint_eq_cmd c c' ->
    contains_backat c -> contains_backat c'.
Proof.
  intro c.
  induction c; intros; try solve[invert_taint_eq_cmd; eauto].
  - invert_taint_eq_cmd.
    specialize (IHc1 _ H5).
    specialize (IHc2 _ H6).
    inverts H0.
    + assert (contains_backat c1') by firstorder 2.
      eauto.
    + assert (contains_backat c2') by firstorder 2.
      eauto.
  - invert_taint_eq_cmd.
    specialize (IHc _ H4).
    inverts H0.
    assert (contains_backat c'0) by firstorder 2.
    eauto.
  - invert_taint_eq_cmd.
    specialize (IHc1 _ H3).
    specialize (IHc2 _ H5).
    inverts H0.
    + assert (contains_backat c1') by firstorder 2.
      eauto.
    + assert (contains_backat c2') by firstorder 2.
      eauto.
  - invert_taint_eq_cmd.
    specialize (IHc _ H5).
    inverts H0.
    assert (contains_backat c'0) by firstorder 2.
    eauto.
Qed.
Hint Resolve taint_eq_cmd_contains_backat.

Lemma taint_eq_cmd_refl:
  forall c,
    taint_eq_cmd c c.
Proof.
  intros.
  induction c; eauto.
Qed.
Hint Resolve taint_eq_cmd_refl.

Lemma taint_eq_cmd_symmetry:
  forall c1 c2,
    taint_eq_cmd c1 c2 ->
    taint_eq_cmd c2 c1.
Proof.
  intros.
  dependent induction H; eauto.
Qed.
Hint Resolve taint_eq_cmd_symmetry.

Lemma taint_eq_mem_refl:
  forall Γ m,
    wf_tenv Γ m ->
    taint_eq_mem (identity_bijection loc) Γ m m.
Proof.
  intros.
  unfolds.
  splits*.
  intros.
  rewrite_inj.
  destruct τ as [σ ε].
  destruct σ.
  - assert (exists n, v2 = ValNum n) by eauto 2.
    super_destruct; subst.
    eauto.
  - assert (exists loc, v2 = ValLoc loc) by eauto 2.
    super_destruct; subst.
    eauto.
Qed.
Hint Resolve taint_eq_mem_refl.

Lemma taint_eq_cmd_trans:
  forall c c' c'',
    taint_eq_cmd c c' ->
    taint_eq_cmd c' c'' ->
    taint_eq_cmd c c''.
Proof.
  intros.
  revert c'' H0.
  dependent induction H; intros; invert_taint_eq_cmd; eauto.
Qed.

Lemma taint_eq_mem_trans:
  forall Φ Ψ Γ m m' m'',
    taint_eq_mem Φ Γ m m' ->
    taint_eq_mem Ψ Γ m' m'' ->
    taint_eq_mem (bijection.bijection_compose Φ Ψ) Γ m m''.
Proof.
  intros.
  unfold taint_eq_mem in *.
  super_destruct; subst.
  splits.
  - intros.
    eapply iff_trans; eauto 2.
  - intros.
    assert (exists v, memory_lookup m' x = Some v) by firstorder 2.
    super_destruct; subst.
    eapply val_taint_eq_trans; eauto.
Qed.

Lemma taint_eq_heap_size_trans:
  forall ℓ_adv h h' h'',
    taint_eq_heap_size ℓ_adv h h' ->
    taint_eq_heap_size ℓ_adv h' h'' ->
    taint_eq_heap_size ℓ_adv h h''.
Proof.
  firstorder.
Qed.

Lemma taint_eq_stenv_trans:
  forall Φ Ψ Σ1 Σ2 Σ3,
    taint_eq_stenv Φ Σ1 Σ2 ->
    taint_eq_stenv Ψ Σ2 Σ3 ->
    taint_eq_stenv (bijection.bijection_compose Φ Ψ) Σ1 Σ3.
Proof.
  intros.
  unfolds.
  intros.
  _apply left_compose in *; super_destruct; subst.
  destruct (left Φ loc1) eqn:H_loc1.
  - rewrite -> (H _ _ _ H_loc1).
    eauto.
  - repeat specialize_gen.
    congruence.
Qed.

Lemma taint_eq_trans:
  forall Φ Ψ ℓ_adv Γ Σ Σ' Σ'' c c' c'' m h m' h' m'' h'',
    dangling_pointer_free m' h' ->
    taint_eq ℓ_adv Φ Γ Σ Σ' c c' m h m' h' ->
    taint_eq ℓ_adv Ψ Γ Σ' Σ'' c' c'' m' h' m'' h'' ->
    taint_eq ℓ_adv (bijection.bijection_compose Φ Ψ) Γ Σ Σ'' c c'' m h m'' h''.
Proof.
  intros.
  unfold taint_eq in *.
  super_destruct; subst.
  splits.
  - eapply taint_eq_cmd_trans; eauto 2.
  - eapply taint_eq_mem_trans; eauto 2.
  - eapply taint_eq_reach_trans; eauto 2.
  - eapply taint_eq_heap_trans; eauto 2.
  - eapply taint_eq_heap_size_trans; eauto 2.
  - eapply taint_eq_heap_domain_eq_trans; eauto 2.
  - eapply taint_eq_stenv_trans; eauto 2.
Qed.

Lemma taint_eq_heap_size_refl:
  forall ℓ_adv h,
    taint_eq_heap_size ℓ_adv h h.
Proof.
  firstorder.
Qed.
Hint Resolve taint_eq_heap_size_refl.

Lemma taint_eq_refl:
  forall ℓ_adv Γ Σ c m h,
    wf_tenv Γ m ->
    wf_stenv Σ h ->
    taint_eq ℓ_adv (identity_bijection loc) Γ Σ Σ c c m h m h.
Proof.
  intros.
  unfolds.
  splits.
  - eapply taint_eq_cmd_refl.
  - eapply taint_eq_mem_refl; eauto 2.
  - eapply taint_eq_reach_refl.
  - eapply taint_eq_heap_refl; eauto 2.
  - eapply taint_eq_heap_size_refl.
  - eapply taint_eq_heap_domain_eq_refl; eauto 2.
  - eapply taint_eq_stenv_refl.
Qed.
Hint Resolve taint_eq_refl.

Lemma taint_eq_reach_symmetry:
  forall Φ m1 m2 h1 h2,
    taint_eq_reach Φ m1 h1 m2 h2 ->
    taint_eq_reach (inverse Φ) m2 h2 m1 h1.
Proof.
  intros.
  unfold taint_eq_reach in *.
  intros.
  assert (left Φ loc' = Some loc) by (destruct Φ; eauto).
  eapply iff_sym; eauto.
Qed.
Hint Resolve taint_eq_reach_symmetry.

Lemma taint_eq_heap_size_sym:
  forall ℓ_adv h1 h2,
    taint_eq_heap_size ℓ_adv h1 h2 ->
    taint_eq_heap_size ℓ_adv h2 h1.
Proof.
  firstorder.
Qed.

Lemma taint_eq_stenv_sym:
  forall Φ Σ1 Σ2,
    taint_eq_stenv Φ Σ1 Σ2 ->
    taint_eq_stenv (inverse Φ) Σ2 Σ1.
Proof.
  intros.
  unfolds.
  intros.
  assert (left Φ loc2 = Some loc1) by (destruct Φ; eauto).
  eapply iff_sym; eauto.
Qed.
Hint Resolve taint_eq_stenv_sym.

Lemma taint_eq_heap_domain_eq_sym:
  forall ℓ_adv Φ m1 m2 h1 h2,
    taint_eq_heap_domain_eq ℓ_adv Φ m1 m2 h1 h2 ->
    taint_eq_heap_domain_eq ℓ_adv (inverse Φ) m2 m1 h2 h1.
Proof.
  intros.
  unfolds.
  intros.
  assert (left Φ l2 = Some l1) by (destruct Φ; eauto 2).
  eapply iff_sym; eauto.
Qed.
Hint Resolve taint_eq_heap_domain_eq_sym.

Lemma taint_eq_symmetry:
  forall ℓ_adv Γ Φ Σ1 Σ2 c1 c2 m1 m2 h1 h2,
    taint_eq ℓ_adv Φ Γ Σ1 Σ2 c1 c2 m1 h1 m2 h2 ->
    taint_eq ℓ_adv (inverse Φ) Γ Σ2 Σ1 c2 c1 m2 h2 m1 h1.
Proof.
  intros.
  unfold taint_eq in *.
  super_destruct'; subst.
  splits.
  - eapply taint_eq_cmd_symmetry; eauto 2.
  - eapply taint_eq_mem_sym; eauto 2.
  - eapply taint_eq_reach_symmetry; eauto 2.
  - eapply taint_eq_heap_sym; eauto 2.
  - eapply taint_eq_heap_size_sym; eauto 2.
  - eapply taint_eq_heap_domain_eq_sym; eauto 2.
  - eapply taint_eq_stenv_sym; eauto 2.
Qed.

Lemma high_dec:
  forall ℓ_adv m h loc,
    { high ℓ_adv m h loc } + { ~ high ℓ_adv m h loc }.
Proof.
  intros.
  destruct (reach_dec m h loc); eauto.
  destruct (heap_lookup loc h) eqn:H_loc.
  - destruct p.
    destruct (flowsto_dec l ℓ_adv); eauto.
    right.
    intro.
    destruct_high.
    + contradiction.
    + congruence.
  - right.
    intro.
    destruct_high.
    + contradiction.
    + congruence.
Qed.

Lemma taint_eq_reach_extend_mem:
  forall Γ Σ1 Σ2 Φ Ψ m1 m2 h1 h2 τ v1 v2 x ℓ_adv,
    taint_eq_reach Φ m1 h1 m2 h2 ->
    taint_eq_mem Φ Γ m1 m2 ->
    taint_eq_heap ℓ_adv Φ Σ1 Σ2 m1 h1 m2 h2 ->
    taint_eq_stenv Φ Σ1 Σ2 ->
    wf_taint_bijection ℓ_adv Φ m1 h1 ->
    wf_taint_bijection ℓ_adv (inverse Φ) m2 h2 ->
    wf_tenv Γ m1 ->
    wf_tenv Γ m2 ->
    wf_stenv Σ1 h1 ->
    wf_stenv Σ2 h2 ->
    dangling_pointer_free m1 h1 ->
    dangling_pointer_free m2 h2 ->
    val_taint_eq Φ τ v1 v2 ->
    Γ x = Some τ ->
    (forall loc, v1 = ValLoc loc -> reach m1 h1 loc) ->
    (forall loc, v2 = ValLoc loc -> reach m2 h2 loc) ->
    filtered (high ℓ_adv (extend_memory x v1 m1) h1) Φ Ψ ->
    taint_eq_reach Ψ (extend_memory x v1 m1) h1 (extend_memory x v2 m2) h2.
Proof.
  intros.
  unfolds.
  intros.
  assert (left Φ loc = Some loc').
  {
    eapply filtered_bijection_is_subset.
    - eapply high_dec.        
    - eauto.
    - eauto.
  }
  invert_val_taint_eq.
  - splits.
    + intros.
      assert (reach m1 h1 loc) by eauto using Imp.reach_extend_with_num.
      assert (reach m2 h2 loc') by (eapply H; eauto).
      eapply reach_extend_with_num; eauto 2.
    + intros.
      assert (reach m2 h2 loc') by eauto using Imp.reach_extend_with_num.
      assert (reach m1 h1 loc) by (eapply H; eauto).
      eauto 2.
  - splits.
    + intros.
      specialize (H13 loc0 eq_refl).
      specialize (H14 loc'0 eq_refl).
      assert (reach m1 h1 loc) by eauto 2 using reach_extend.
      eapply taint_reach_in_extended_mem with (m1 := m1) (h1 := h1); eauto.
    + intros.
      specialize (H13 loc0 eq_refl).
      specialize (H14 loc'0 eq_refl).
      assert (reach m2 h2 loc') by eauto 2 using reach_extend.
      eapply taint_reach_in_extended_mem with (m1 := m2) (h1 := h2); destruct Φ; eauto 2.
  - splits.
    + intros.
      assert (reach m1 h1 loc) by eauto 2 using Imp.reach_extend_with_num.
      assert (reach m2 h2 loc') by (eapply H; eauto).
      eauto 2.
    + intros.
      assert (reach m2 h2 loc') by eauto 2 using Imp.reach_extend_with_num.
      assert (reach m1 h1 loc) by (eapply H; eauto).
      eauto 2.
  - assert_wf_type.
    invert_wf_type.
Qed.
Hint Resolve taint_eq_reach_extend_mem.

Lemma gc_preserves_taint_eq_reach:
  forall c c' pc pc' m m' h h' t t' Σ Σ',
    gc_occurred c c' pc pc' m m' h h' t t' Σ Σ' ->
    taint_eq_reach (identity_bijection loc) m h m' h'.
Proof.
  intros.
  unfold gc_occurred in *.
  super_destruct; subst.
  unfolds.
  intros.
  unfold left, identity_bijection in *; injects.
  splits.
  - intros.
    eapply reach_supset_if; eauto 2.
  - intros.
    eapply reach_supset; eauto.
Qed.
Hint Resolve gc_preserves_taint_eq_reach.

Lemma gc_trans_preserves_taint_eq_reach:
  forall c c' pc pc' m m' h h' t t' Σ Σ' n,
    gc_trans Σ Σ' ⟨c, pc, m, h, t⟩ ⟨c', pc', m', h', t'⟩ n ->
    taint_eq_reach (identity_bijection loc) m h m' h'.
Proof.
  intros.
  dependent induction H.
  - assert (taint_eq_reach (identity_bijection loc) m h m'0 h'0) by eauto 2.
    rewrite <- (compose_id_left (identity_bijection loc)).
    eapply taint_eq_reach_trans; eauto.
  - eauto.
Qed.
Hint Resolve gc_trans_preserves_taint_eq_reach.

Lemma high_extend_with_num:
  forall ℓ_adv x n m h loc,
    high ℓ_adv (m [x → ValNum n]) h loc -> high ℓ_adv m h loc.
Proof.
  intros.
  destruct_high; eauto 3 using Imp.reach_extend_with_num.
Qed.

Lemma taint_eq_heap_extend_mem:
  forall Γ Φ Ψ m1 m2 h1 h2 Σ1 Σ2 τ v1 v2 x ε ℓ_adv,
    taint_eq_heap ℓ_adv Φ Σ1 Σ2 m1 h1 m2 h2 ->
    Γ x = Some (SecType τ ε) ->
    (τ = Int -> exists n, v1 = ValNum n) ->
    (τ = Int -> exists n, v2 = ValNum n) ->
    (forall τ' ℓ', τ = Array τ' ℓ' -> exists loc, v1 = ValLoc loc /\ reach m1 h1 loc) ->
    (forall τ' ℓ', τ = Array τ' ℓ' -> exists loc, v2 = ValLoc loc /\ reach m2 h2 loc) ->
    wf_taint_bijection ℓ_adv Φ m1 h1 ->
    wf_taint_bijection ℓ_adv (inverse Φ) m2 h2 ->
    filtered (high ℓ_adv (extend_memory x v1  m1) h1) Φ Ψ ->
    taint_eq_heap ℓ_adv Ψ Σ1 Σ2 (extend_memory x v1 m1) h1
                  (extend_memory x v2 m2) h2.
Proof.
  intros.
  unfold taint_eq_heap in *.
  intros.
  assert (left Φ loc = Some loc').
  {
    eapply filtered_bijection_is_subset.
    - eapply high_dec.
    - eauto.
    - eauto.
  }
  assert (high ℓ_adv m1 h1 loc).
  {
    eapply H5; eauto 2.
  }
  assert (high ℓ_adv m2 h2 loc').
  {
    eapply H6; destruct Φ; eauto.
  }
  remember_simple (H _ _ _ _ _ _ _ H15 H16 H17 H11 H12 H13 H14).
  super_destruct'; subst.
  splits*.
  intros.
  assert (reach m1 h1 loc).
  {
    destruct τ.
    - assert (exists n, v1 = ValNum n) by eauto 2.
      super_destruct'; subst.
      eauto 2 using Imp.reach_extend_with_num.
    - specialize (H3 _ _ eq_refl); super_destruct'; subst.
      eapply reach_extend; eauto 2.
  }
  assert (reach m2 h2 loc').
  {
    destruct τ.
    - assert (exists n, v2 = ValNum n) by eauto 2.
      super_destruct'; subst.
      eauto 2 using Imp.reach_extend_with_num.
    - specialize (H4 _ _ eq_refl); super_destruct'; subst.
      eapply reach_extend; eauto 2.
  }
  assert (val_taint_eq Φ τ0 v0 v3) by eauto 2.
  invert_val_taint_eq; eauto 2.
  assert (high ℓ_adv (m1 [x → v1]) h1 loc0).
  {
    eapply HighReachable; eauto 2.
  }
  eauto.
Qed.
Hint Resolve taint_eq_heap_extend_mem.

Lemma gc_trans_same_store_typing:
  forall Σ Σ' cfg cfg' n,
    gc_trans Σ Σ' cfg cfg' n ->
    Σ = Σ'.
Proof.
  intros.
  dependent induction H.
  - subst.
    unfold gc_occurred in *.
    super_destruct; subst.
    reflexivity.
  - reflexivity.
Qed.
Hint Resolve gc_trans_same_store_typing.

Lemma taint_eq_cmd_implies_same_type:
  forall Γ c c' pc pc',
    taint_eq_cmd c c' ->
    wt_aux Γ pc c pc' ->
    wt_aux Γ pc c' pc'.
Proof.
  intros.
  revert c' H.
  dependent induction H0; intros; try solve[invert_taint_eq_cmd; eauto].
  - invert_taint_eq_cmd.
    specialize (IHwt_aux1 _ H8).
    specialize (IHwt_aux2 _ H9).
    assert (~ contains_backat c1').
    {
      intro.
      eapply H0.
      eapply taint_eq_cmd_contains_backat.
      - eapply taint_eq_cmd_symmetry; eauto 2.
      - eauto.
    }
    assert (~ contains_backat c2').
    {
      intro.
      eapply H1.
      eapply taint_eq_cmd_contains_backat.
      - eapply taint_eq_cmd_symmetry; eauto 2.
      - eauto.
    }
    eapply wt_aux_if; eauto 2.
  - invert_taint_eq_cmd.
    specialize (IHwt_aux _ H7).
    assert (~ contains_backat c'0).
    {
      intro.
      eapply H0.
      eapply taint_eq_cmd_contains_backat.
      - eapply taint_eq_cmd_symmetry; eauto 2.
      - eauto.
    }
    eauto.
  - invert_taint_eq_cmd.
    specialize (IHwt_aux _ H9).
    assert (~ contains_backat c'0).
    {
      intro.
      eapply H2.
      eapply taint_eq_cmd_contains_backat.
      - eapply taint_eq_cmd_symmetry; eauto 2.
      - eauto.
    }
    eauto.
Qed.
Hint Resolve taint_eq_cmd_implies_same_type.

Lemma backat_bridge_properties:
  forall l k c' pc pc' pc'' m m' h h' t t' n ℓ Γ Σ Σ' ev,
    wellformed_aux Γ Σ ⟨BackAt l k, pc, m, h, t⟩ pc'' ->
    ⟨BackAt l k, pc, m, h, t⟩
      ↷ [ℓ, Γ, Σ, Σ', ev, n] ⟨c', pc', m', h', t'⟩ ->
    (exists h'' t'',
        k < t'' /\
        gc_or_inc_many Γ Σ ⟨BackAt l k, pc, m, h, t⟩
                       ⟨BackAt l k, pc, m, h'', t''⟩ n /\
        ⟨BackAt l k, pc, m, h'', t''⟩ ⇒ [ev, Γ, Σ, Σ'] ⟨TimeOut, pc', m', h', t'⟩ /\
        c' = TimeOut /\ Σ' = Σ /\ ev = RestoreEvent l t'' /\ pc' = l /\ t' = S t'' /\ m' = m /\ h' = h'')
    \/
    (exists h'' t'',
        gc_or_inc_many Γ Σ ⟨BackAt l k, pc, m, h, t⟩
                       ⟨BackAt l k, pc, m, h'', t''⟩ n /\
        t'' <= k /\ c' = Stop /\ ev = RestoreEvent l t'' /\ pc' = l /\
        m' = m /\ h' = h'' /\ t' = S k /\ Σ' = Σ /\
        ⟨BackAt l k, pc, m, h'', t''⟩ ⇒ (Γ, Σ, Σ) ⟨Stop, l, m, h'', S t''⟩).
Proof.
  intros.
  revert t h H H0.
  induction n; intros.
  - invert_bridge_step.
    + invert_low_event_step.
      invert_event_step.
      * invert_low_event.
      * invert_low_event.
        invert_sem_step.
        { omega. }
        { right.
          exists h' t.
          splits*. }
        { omega. }
      * invert_low_event.
        invert_sem_step.
        { omega. }
        { omega. }
        { left.
          exists h' t.
          splits*. }
      * invert_low_event.          
    + unfold is_stop_config, cmd_of in *; subst.
      invert_high_event_step.
      invert_event_step; invert_sem_step.
      * omega.
      * right.
        exists h' t.
        splits*.
      * omega.
  - invert_bridge_step.
    invert_high_event_step.
    destruct cfg2 as [c2 pc2 m2 h2 t2].
    invert_event_step.
    + invert_sem_step.
      * assert (wellformed_aux Γ Σ'0 ⟨BackAt l k, pc2, m2, h2, S t⟩ pc'') by eauto 2.
        remember_simple (IHn _ _ H0 H12).
        super_destruct; subst.
        {
          clear IHn.
          left.
          exists h'' t''.
          splits*.
        }
        { right.
          exists h'' t''.
          splits*.
        }
      * exfalso; eauto 2.
      * exfalso; eauto 2.
    + assert (wellformed_aux Γ Σ'0 ⟨c2, pc2, m2, h2, t2⟩ pc'').
      {
        eapply preservation; eauto 2.
      }
      invert_sem_step.
      * omega.
      * exfalso; eauto 2.
      * omega.
    + invert_sem_step.
      * omega.
      * exfalso; eauto 2.
      * exfalso; eauto 2.
    + assert (wellformed_aux Γ Σ'0 ⟨BackAt l k, pc2, m2, [h1_pc ⊎ h1_not_pc, H2], t + δ⟩ pc'').
      {
        eapply gc_preserves_wf; eauto 2.
        erewrite -> disjoint_union_proof_irrelevance.
        eauto.
      }
      specialize (IHn _ _ H6 H12).
      destruct IHn.
      * super_destruct'; subst.
        left.
        exists h'' t''.
        splits*.
        eapply GCOrIncTrans.
        { eapply GC.
          unfolds.
          splits; try congruence.
          do 7 eexists.
          splits; reflexivity || eauto 2. }
        { eauto. }
      * super_destruct'; subst.
        right.
        exists h'' t''.
        splits*.
        eapply GCOrIncTrans.
        { eapply GC.
          unfolds.
          splits; try congruence.
          do 7 eexists.
          splits; reflexivity || eauto 2. }
        { eauto. }
Qed.

Lemma low_gc_preserves_taint_eq:
  forall ℓ_adv Γ c c' pc pc' pc'' m m' h h' t t' Σ Σ',
    wellformed_aux Γ Σ ⟨c, pc, m, h, t⟩ pc'' ->
    pc ⊑ ℓ_adv ->
    gc_occurred c c' pc pc' m m' h h' t t' Σ Σ' ->
    taint_eq ℓ_adv (identity_bijection loc) Γ Σ Σ' c c' m h m' h'.
Proof.
  intros.
  unfolds.
  splits.
  - unfold gc_occurred in *; super_destruct; subst.
    eauto.
  - unfold gc_occurred in *; super_destruct; subst.
    invert_wf_aux.
    eauto.
  - eapply gc_preserves_taint_eq_reach; eauto.
  - invert_wf_aux.
    eapply gc_preserves_taint_eq_heap; eauto.
  - unfold gc_occurred in *; super_destruct'; subst.
    unfolds.
    intros.
    rewrite -> size_heap_distr.
    assert (size l h1_2 = 0).
    {
      assert (l <> pc').
      {
        intro; subst.
        contradiction.
      }
      eapply level_neq_size; eauto.
    }
    omega.
  - eapply low_gc_preserves_taint_eq_heap_domain_eq; eauto 2.
  - unfold gc_occurred in *; super_destruct'; subst.
    eauto.
Qed.
Hint Resolve low_gc_preserves_taint_eq.

Lemma taint_eq_event_low_implies_low:
  forall Φ Γ ev1 ev2 ℓ,
    taint_eq_events Γ Φ  ev1 ev2 ->
    low_event ℓ ev1 ->
    low_event ℓ ev2.
Proof.
  intros.
  dependent induction H; invert_low_event; eauto.
Qed.
Hint Resolve taint_eq_event_low_implies_low.

Lemma taint_eq_events_sym:
  forall Φ Γ ev1 ev2,
    taint_eq_events Γ Φ ev1 ev2 ->
    taint_eq_events Γ (inverse Φ) ev2 ev1.
Proof.
  intros.
  dependent induction H; destruct Φ; eauto using val_taint_eq_sym.
Qed.
Hint Immediate taint_eq_events_sym.

Lemma low_gc_trans_preserves_taint_eq:
  forall ℓ_adv Γ c c' pc pc' m m' h h' t t' Σ Σ' n pc_end,
    wellformed_aux Γ Σ ⟨c, pc, m, h, t⟩ pc_end ->
    pc ⊑ ℓ_adv ->
    gc_trans Σ Σ' ⟨c, pc, m, h, t⟩ ⟨c', pc', m', h', t'⟩ n ->
    taint_eq ℓ_adv (identity_bijection loc) Γ Σ Σ' c c' m h m' h'.
Proof.
  intros.
  dependent induction H1.
  - remember_simple (low_gc_preserves_taint_eq H H0 H2).
    assert (wellformed_aux Γ Σ' ⟨ c'0, pc'0, m'0, h'0, t'0 ⟩ pc_end) by eauto 3.
    specialize_gen.
    unfold gc_occurred in *; super_destruct'; subst.
    specialize_gen.
    invert_wf_aux.
    rewrite <- (compose_id_left (identity_bijection loc)).
    eapply taint_eq_trans with (m' := m'0) (h' := ([h1_1_pc ⊎ h1_1_not_pc, H12]));
      eauto.
  - invert_wf_aux.
    eapply taint_eq_refl; eauto.
Qed.
Hint Resolve low_gc_trans_preserves_taint_eq.

Lemma low_gc_or_inc_many_preserves_taint_eq:
  forall ℓ_adv Γ Σ c c' pc pc' m m' h h' t t' pc_end n,
    wellformed_aux Γ Σ ⟨c, pc, m, h, t⟩ pc_end ->
    pc ⊑ ℓ_adv ->
    gc_or_inc_many Γ Σ ⟨c, pc, m, h, t⟩ ⟨c', pc', m', h', t'⟩ n ->
    taint_eq ℓ_adv (identity_bijection loc) Γ Σ Σ c c' m h m' h'.
Proof.
  intros.
  dependent induction H1.
  - splits*.
    + invert_wf_aux.
      eapply taint_eq_mem_refl; eauto 2.
  - inverts H2.
    + assert (wellformed_aux Γ Σ ⟨BackAt ℓ t'0, pc, m, h, S t⟩ pc_end) by eauto 2.
      invert_sem_step.
      eapply IHgc_or_inc_many; eauto 2.
    + assert (wellformed_aux Γ Σ ⟨BackAt ℓ t'0, pc, m, h'0, t2⟩ pc_end).
      {
        unfold gc_occurred in *; super_destruct'; subst.
        eapply gc_preserves_wf; eauto.
      }
      remember_simple (low_gc_preserves_taint_eq H H0 H11).
      remember_simple (IHgc_or_inc_many _ _ _ _ _ _ _ _ _ _ H2 H0 eq_refl eq_refl).
      unfold taint_eq in *; super_destruct'; subst.
      super_destruct'; subst.
      splits; eauto 2.
      * rewrite <- (compose_id_left (identity_bijection loc)).
        eapply taint_eq_reach_trans; eauto.
      * repeat invert_wf_aux.
        rewrite <- (compose_id_left (identity_bijection loc)).
        eapply taint_eq_heap_trans; eauto.
      * eapply taint_eq_heap_size_trans; eauto.
      * rewrite <- (compose_id_left (identity_bijection loc)).
        eapply taint_eq_heap_domain_eq_trans; eauto.
Qed.
Hint Resolve low_gc_or_inc_many_preserves_taint_eq.

Lemma new_bridge_properties:
  forall i e1 e2 pc pc' m m' h h'' t t' Γ Σ Σ' ev n ℓ c' l,
    ⟨NewArr i l e1 e2, pc, m, h, t⟩ ↷ [ℓ, Γ, Σ, Σ', ev, n] ⟨c', pc', m', h'', t'⟩ ->
    exists n_size v h',
      pc = pc' /\ c' = Stop /\
      eval m e1 = Some (ValNum n_size) /\ eval m e2 = Some v /\
      gc_trans Σ Σ
               ⟨NewArr i l e1 e2, pc, m, h, t⟩
               ⟨NewArr i l e1 e2, pc, m, h', t' - 1⟩ n /\
      ⟨NewArr i l e1 e2, pc, m, h', t' - 1⟩ ↷ [ℓ, Γ, Σ, Σ', ev, 0] ⟨Stop, pc, m', h'', t'⟩.
Proof.
  intros.
  dependent induction H.
  - invert_low_event_step.
    invert_event_step.
    + invert_sem_step.
      rewrite_inj.
      assert (l3 = l2) by eauto 2; subst.
      replace (S t - 1) with (t + 0) by omega.
      rewrite -> plus_0_r.
      do 3 eexists.
      splits*.
      eapply bridge_low_num; eauto 2.
      splits*.
    + invert_low_event.
  - unfold is_stop_config, cmd_of in *; subst.
    invert_high_event_step.
    invert_event_step.
    invert_sem_step.
    rewrite_inj.
    assert (l3 = l2) by eauto 2; subst.
    replace (S t - 1) with (t + 0) by omega.
    rewrite -> plus_0_r.
    do 3 eexists.
    splits*.
  - invert_high_event_step.
    invert_event_step.
    + contradict H0; eauto.
    + specialize (IHbridge_step_num _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl eq_refl).
      super_destruct; subst.
      do 3 eexists.
      splits*.
      eapply GCTrans.
      * unfolds.
        splits*.
        do 7 eexists.
        splits; reflexivity || eauto 2.
      * eauto.
Qed.

Lemma taint_eq_mem_extend:
  forall Γ m1 h1 m2 v1 v2 τ Φ Ψ x ℓ_adv,
    Γ x = Some τ ->
    taint_eq_mem Φ Γ m1 m2 ->
    val_taint_eq Φ τ v1 v2 ->
    filtered (high ℓ_adv (extend_memory x v1 m1) h1) Φ Ψ ->
    taint_eq_mem Ψ Γ (extend_memory x v1 m1) (extend_memory x v2 m2).
Proof.
  intros.
  unfolds.
  intros.
  splits*.
  - intros.
    destruct (decide (x = x0)); subst.
    + splits*.
    + do 2 rewrite -> extend_memory_lookup_neq by solve[eauto].
      eapply H0; eauto.
  - intros.
    destruct (decide (x = x0)); subst.
    + rewrite -> extend_memory_lookup_eq in *.
      rewrite_inj.
      invert_val_taint_eq; eauto.
      assert (high ℓ_adv (m1 [x0 → ValLoc loc]) h1 loc).
      {
        eapply HighReachable.
        eauto 2.
      }
      eauto.
    + rewrite -> extend_memory_lookup_neq in * by solve[eauto 2].
      assert (val_taint_eq Φ τ0 v0 v3) by (eapply H0; eauto).
      invert_val_taint_eq; eauto 2.
      assert (high ℓ_adv (m1 [x → v1]) h1 loc).
      {
        eapply HighReachable.
        eapply reach_mem.
        erewrite -> extend_memory_lookup_neq by solve[eauto 2].
        eauto.
      }
      eauto.
Qed.
Hint Resolve taint_eq_mem_extend.

Lemma taint_eq_stenv_extend_mem:
  forall Φ Ψ m1 h1 x v ℓ_adv Σ1 Σ2,
    filtered (high ℓ_adv (extend_memory x v m1) h1) Φ Ψ ->
    taint_eq_stenv Φ Σ1 Σ2 ->
    taint_eq_stenv Ψ Σ1 Σ2.
Proof.
  intros.
  unfolds.
  intros.
  assert (left Φ loc1 = Some loc2).
  {
    eapply filtered_bijection_is_subset.
    - eapply high_dec.
    - eauto.
    - eauto.
  }
  eauto.
Qed.

Lemma wf_taint_bijection_extend_mem1:
  forall ℓ_adv Φ Ψ m1 x v h1,
    wf_taint_bijection ℓ_adv Φ m1 h1 ->
    (forall loc, v = ValLoc loc -> reach m1 h1 loc) ->
    filtered (high ℓ_adv (extend_memory x v m1) h1) Φ Ψ ->
    wf_taint_bijection ℓ_adv Ψ (extend_memory x v m1) h1.
Proof.
  intros.
  unfolds.
  intros.
  splits.
  - intros.
    super_destruct; subst.
    eapply filtered_bijection_some_implies_predicate.
    + eapply high_dec.
    + eauto.
    + eauto.
  - intros.
    destruct v.
    + assert (high ℓ_adv m1 h1 loc) by (eapply high_extend_with_num; eauto 2).
      assert (exists loc', left Φ loc = Some loc') by (eapply H; eauto).
      super_destruct'; subst.
      exists loc'.
      eapply filter_true.
      * eapply H2.
      * eauto.
      * eauto.
    + assert (reach m1 h1 l) by eauto 2.
      assert (high ℓ_adv m1 h1 loc).
      {
        destruct_high.
        - eapply HighReachable; eauto 3.
        - eapply HighHeapLevel; eauto 2.
      }
      assert (exists loc', left Φ loc = Some loc') by (eapply H; eauto).
      super_destruct'; subst.
      exists loc'.
      eapply filter_true.
      * eapply H2.
      * eauto.
      * eauto.
Qed.
Hint Resolve wf_taint_bijection_extend_mem1.

Lemma low_gc_preserves_wf_taint_bijection:
  forall ℓ_adv Φ c c' pc pc' m m' h h' t t' Σ Σ',
    pc ⊑ ℓ_adv ->
    wf_taint_bijection ℓ_adv Φ m h ->
    gc_occurred c c' pc pc' m m' h h' t t' Σ Σ' ->
    wf_taint_bijection ℓ_adv Φ m' h'.
Proof.
  intros.
  unfold gc_occurred in *; super_destruct'; subst.
  unfolds.
  intros.
  splits.
  - intros.
    assert (high ℓ_adv m' ([[h1_1_pc ⊎ h1_1_not_pc, H9] ⊎ h1_2, H8]) loc)
      by (eapply H0; eauto 2).
    destruct_high.
    + eapply HighReachable.
      eapply reach_supset_if; eauto 2.
    + destruct_disjoint_heap_lookup.
      * eapply HighHeapLevel; eauto 2.
      * assert (pc' = ℓ) by eauto 2.
        subst.
        contradiction.
  - intros.
    assert (high ℓ_adv m' ([[h1_1_pc ⊎ h1_1_not_pc, H9] ⊎ h1_2, H8]) loc) by eauto 2.
    eapply H0; eauto 2.
Qed.
Hint Resolve low_gc_preserves_wf_taint_bijection.      

Lemma low_gc_trans_preserves_wf_taint_bijection:
  forall ℓ_adv n Φ c c' pc pc' m m' h h' t t' Σ Σ',
    wf_taint_bijection ℓ_adv Φ m h ->
    pc ⊑ ℓ_adv ->
    gc_trans Σ Σ' ⟨c, pc, m, h, t⟩ ⟨c', pc', m', h', t'⟩ n ->
    wf_taint_bijection ℓ_adv Φ m' h'.
Proof.
  intros.
  dependent induction H1.
  - eapply IHgc_trans; eauto 2.
    cut (pc'0 = pc); intros; subst; eauto 2.
    unfold gc_occurred in *; super_destruct'; subst; eauto 2.
  - eauto.
Qed.

Lemma reach_in_extended_memory:
  forall ℓ_adv Γ Σ1 Σ2 x σ ε Φ v1 v2 m1 m2 h1 h2 loc1 loc2,
    Γ x = Some (SecType σ ε) ->
    taint_eq_mem Φ Γ m1 m2 ->
    taint_eq_heap ℓ_adv Φ Σ1 Σ2 m1 h1 m2 h2 ->
    taint_eq_reach Φ m1 h1 m2 h2 ->
    taint_eq_stenv Φ Σ1 Σ2 ->
    val_taint_eq Φ (SecType σ ε) v1 v2 ->
    wf_taint_bijection ℓ_adv Φ m1 h1 ->
    wf_taint_bijection ℓ_adv (inverse Φ) m2 h2 ->
    reach (m1 [x → v1]) h1 loc1 ->
    dangling_pointer_free m1 h1 ->
    dangling_pointer_free m2 h2 ->
    wf_tenv Γ m1 ->
    wf_tenv Γ m2 ->
    wf_stenv Σ1 h1 ->
    wf_stenv Σ2 h2 ->
    left Φ loc1 = Some loc2 ->
    (forall s ℓ', σ = Array s ℓ' ->
             exists loc', v1 = ValLoc loc' /\
                     reach m1 h1 loc') ->
    (σ = Int -> exists n, v1 = ValNum n) ->
    reach (m2 [x → v2]) h2 loc2.
Proof.
  intros.
  revert dependent loc2.
  dependent induction H7; intros.
  - destruct (decide (x = x0)); subst.
    + rewrite -> extend_memory_lookup_eq in *.
      rewrite_inj.
      invert_val_taint_eq.
      * rewrite_inj.
        eauto 2.
      * assert_wf_type.
        invert_wf_type.
    + rewrite -> extend_memory_lookup_neq in * by solve[eauto].
      assert (memory_lookup m2 x0 = Some (ValLoc loc2)).
      {
        assert (exists u, memory_lookup m2 x0 = Some u).
        {
          eapply H0; eauto.
        }
        super_destruct; subst.
        assert (exists τ, Γ x0 = Some τ) by eauto.
        super_destruct'; subst.
        assert (val_taint_eq Φ τ (ValLoc loc) u).
        {
          eapply H0; eauto.
        }
        invert_val_taint_eq.
        * rewrite_inj.
          eauto.
        * assert_wf_type.
          invert_wf_type.
      }
      eapply reach_mem.
      rewrite -> extend_memory_lookup_neq by solve[eauto 2].
      eauto.
  - assert (reach m1 h loc).
    {
      destruct σ.
      - assert (exists n, v1 = ValNum n) by eauto 2.
        super_destruct; subst.
        eauto 2 using Imp.reach_extend_with_num.
      - specialize (H16 _ _ eq_refl).
        super_destruct'; subst.
        eapply reach_extend; eauto.
    }
    assert (high ℓ_adv m1 h loc) by eauto 2.
    assert (exists loc', left Φ loc = Some loc').
    {
      eapply H5; eauto.
    }
    super_destruct'; subst.
    assert (reach (m2 [x → v2]) h2 loc'0) by eauto 2.
    assert (reach m2 h2 loc'0).
    {
      apply_taint_eq_reach.
    }
    assert (high ℓ_adv m2 h2 loc'0) by eauto 2.
    assert (exists ℓ μ, heap_lookup loc'0 h2 = Some (ℓ, μ)) by eauto 2.
    super_destruct'; subst.
    assert (exists τ, Σ1 loc = Some τ) by eauto 2.
    super_destruct'; subst.
    assert (Σ2 loc'0 = Some τ).
    {
      eapply H3; eauto.
    }
    remember_simple (H1 loc loc'0 _ _ _ _ _ H21 H20 H24 H8 H25 H26 H27).
    super_destruct'; subst.
    assert (exists v, lookup μ0 n = Some v) by firstorder 2.
    super_destruct'; subst.
    assert (val_taint_eq Φ τ (ValLoc loc') v) by eauto 2.
    invert_val_taint_eq.
    + rewrite_inj.
      eauto 2.
    + assert_wf_type.
      invert_wf_type.
Qed.

Lemma high_extend_with_num2:
  forall Γ ℓ_adv x n m h loc ℓ ι,
    wf_tenv Γ m ->
    Γ x = Some (SecType Int (ℓ, ι)) ->
    high ℓ_adv m h loc -> high ℓ_adv (m [x → ValNum n]) h loc.
Proof.
  intros.
  destruct_high; eauto 2.
  eapply HighReachable.
  eapply reach_extend_with_num; eauto 2.
Qed.

Lemma wf_taint_bijection_extend_mem2:
  forall Γ Φ Ψ Σ1 Σ2 s w m h τ ℓ ι x v1 v2 ℓ_adv,
    taint_eq_reach Φ m h s w ->
    taint_eq_mem Φ Γ m s ->
    taint_eq_heap ℓ_adv Φ Σ1 Σ2 m h s w ->
    taint_eq_heap_domain_eq ℓ_adv Φ m s h w ->
    taint_eq_stenv Φ Σ1 Σ2 ->
    Γ x = Some (SecType τ (ℓ, ι)) ->
    taint_eq_heap_domain_eq ℓ_adv Ψ (m [x → v1]) (s [x → v2]) h w ->
    taint_eq_reach Ψ (m [x → v1]) h (s [x → v2]) w ->
    wf_taint_bijection ℓ_adv Φ m h ->
    wf_taint_bijection ℓ_adv (inverse Φ) s w ->
    filtered (high ℓ_adv (m [x → v1]) h) Φ Ψ ->
    (τ = Int -> exists n, v1 = ValNum n) ->
    (τ = Int -> exists n, v2 = ValNum n) ->
    val_taint_eq Φ (SecType τ (ℓ, ι)) v1 v2 ->
    dangling_pointer_free s w ->
    dangling_pointer_free m h ->
    wf_tenv Γ m ->
    wf_tenv Γ s ->
    wf_stenv Σ1 h ->
    wf_stenv Σ2 w ->
    (forall τ' ℓ', τ = Array τ' ℓ' ->
              exists loc, v2 = ValLoc loc /\ reach s w loc) ->
    wf_taint_bijection ℓ_adv (inverse Ψ) (s [x → v2]) w.
Proof.
  intros.
  unfolds.
  intros.
  splits.
  - intros.
    super_destruct'; subst.
    assert (left Ψ loc' = Some loc) by (destruct Ψ; eauto 2).
    assert (high ℓ_adv (m [x → v1]) h loc').
    {
      eapply filtered_bijection_some_implies_predicate; eauto 2.
      eapply high_dec.
    }
    rewrite <- high_iff; eauto 2.
  - intros.
    assert (high ℓ_adv s w loc).
    {
      destruct τ.
      - assert (exists n, v2 = ValNum n) by eauto 2.
        super_destruct'; subst.
        eapply high_extend_with_num; eauto 2.
      - specialize (H19 _ _ eq_refl).
        super_destruct'; subst.
        destruct_high; eauto 3.
    }
    assert (exists loc', left (inverse Φ) loc = Some loc').
    {
      match goal with
        [H: wf_taint_bijection _ _ _ _ |- _] =>
        solve[eapply H; eauto]
      end.
    }
    super_destruct'; subst.
    assert (left Φ loc' = Some loc) by (destruct Φ; eauto 2).
    exists loc'.
    assert (high ℓ_adv m h loc').
    {
      rewrite <- high_iff; eauto 2.      
    }
    assert (high ℓ_adv (m [x → v1]) h loc').
    {
      destruct τ.
      - assert (exists n, v1 = ValNum n) by eauto.
        super_destruct'; subst.
        eapply high_extend_with_num2; eauto 2.        
      - destruct_high.
        + inverts H20.
          * eapply HighReachable.
            eapply reach_in_extended_memory with (Φ := inverse Φ) (m1 := s); eauto 2.
            rewrite <- inverse_is_involutive; eauto.
          * assert ((exists μ, heap_lookup loc' h = Some (ℓ0, μ)) /\ high ℓ_adv m h loc').
            {
              eapply H2; eauto.
            }
            super_destruct'; subst.
            eauto 2.
        + eapply HighHeapLevel; eauto 2.
    }
    assert (left Ψ loc' = Some loc) by eauto 2.
    destruct Ψ; eauto.
Qed.

Lemma gc_or_inc_many_preserves_wf_taint_eq:
  forall ℓ_adv Γ Σ c c' pc pc' m m' h h' t t' Φ n,
    pc ⊑ ℓ_adv ->
    gc_or_inc_many Γ Σ ⟨c, pc, m, h, t⟩ ⟨c', pc', m', h', t'⟩ n ->
    wf_taint_bijection ℓ_adv Φ m h ->
    wf_taint_bijection ℓ_adv Φ m' h'.
Proof.
  intros.
  dependent induction H0.
  - eauto.
  - inverts H1; eauto.
Qed.
Hint Resolve gc_or_inc_many_preserves_wf_taint_eq.

Lemma wf_taint_bijection_extend_mem_and_heap1:
  forall ℓ_adv ψ φ loc1 loc2 m τ l ℓ n v h H1 H2 Γ x H3 H4,
    Γ x = Some (SecType (Array τ l) (ℓ, ∘)) ->
    wf_tenv Γ m ->
    (forall loc', v = ValLoc loc' -> reach m h loc') ->
    filtered
      (high ℓ_adv (m [x → ValLoc loc1])
             (extend_heap v loc1 l n h H3 H4)) φ ψ ->
    wf_taint_bijection ℓ_adv φ m h ->
    wf_taint_bijection ℓ_adv (extend_bijection ψ loc1 loc2 H1 H2)
                       (m [x → ValLoc loc1]) 
                       (extend_heap v loc1 l n h H3 H4).
Proof.
  intros.
  unfolds.
  intros.
  splits.
  - intros.
    super_destruct; subst.
    destruct (decide (loc = loc1)); subst.
    + _rewrite -> left_extend_bijection_eq in *.
      rewrite_inj.
      eauto 3.
    + _rewrite -> left_extend_bijection_neq in * by solve[eauto].
      eapply filtered_bijection_some_implies_predicate; eauto 2.
      eapply high_dec.
  - intros.
    destruct (decide (loc = loc1)); subst.
    + eauto.
    + rewrite -> left_extend_bijection_neq by solve[eauto].
      assert (high ℓ_adv m h loc).
      {
        destruct_high.
        - eapply HighReachable.
          eapply reach_extend_implies_reach_if; eauto.
        - rewrite -> heap_lookup_extend_neq in * by solve[eauto 2].
          eauto 2.
      }
      assert (exists loc', left φ loc = Some loc').
      {
        eapply H7; eauto.
      }
      super_destruct; subst.
      eauto 3.
Qed.
Hint Resolve wf_taint_bijection_extend_mem_and_heap1.

Lemma wf_taint_bijection_extend_mem_and_heap2:
  forall ℓ_adv Ψ Φ loc1 loc2 Γ Σ1 Σ2 ℓ ℓ' ι' τ l n v1 v2 m1 m2 h1 h2 x H1 H2 H3 H4 H5 H6,
    Γ x = Some (SecType (Array (SecType τ (ℓ', ι')) l) (ℓ, ∘)) ->
    taint_eq_reach Φ m1 h1 m2 h2 ->
    taint_eq_mem Φ Γ m1 m2 ->
    taint_eq_heap ℓ_adv Φ Σ1 Σ2 m1 h1 m2 h2 ->
    taint_eq_heap_domain_eq ℓ_adv Φ m1 m2 h1 h2 ->
    taint_eq_stenv Φ Σ1 Σ2 ->
    wf_taint_bijection ℓ_adv Φ m1 h1 ->
    wf_taint_bijection ℓ_adv (inverse Φ) m2 h2 ->
    dangling_pointer_free m1 h1 ->
    dangling_pointer_free m2 h2 ->
    wf_tenv Γ m1 ->
    wf_tenv Γ m2 ->
    wf_stenv Σ1 h1 ->
    wf_stenv Σ2 h2 ->
    (τ = Int -> exists n, v1 = ValNum n) ->
    (τ = Int -> exists n, v2 = ValNum n) ->
    (forall s ℓ, τ = Array s ℓ ->
            exists loc, v1 = ValLoc loc /\ reach m1 h1 loc) ->
    (forall s ℓ, τ = Array s ℓ ->
            exists loc, v2 = ValLoc loc /\ reach m2 h2 loc) ->
    val_taint_eq Φ (SecType τ (ℓ', ι')) v1 v2 ->
    filtered
      (high ℓ_adv
         (m1 [x → ValLoc loc1])
         (extend_heap v1 loc1 l n h1 H3 H4)) Φ Ψ ->
    wf_taint_bijection ℓ_adv (extend_bijection Ψ loc1 loc2 H1 H2)
                       (m1 [x → ValLoc loc1])
                       (extend_heap v1 loc1 l n h1 H3 H4) ->
    wf_taint_bijection ℓ_adv (inverse (extend_bijection Ψ loc1 loc2 H1 H2))
                       (m2 [x → ValLoc loc2])
                       (extend_heap v2 loc2 l n h2 H5 H6).
Proof.
  intros.
  unfolds.
  intros.
  splits.
  intros.
  - intros.
    super_destruct; subst.
    _rewrite -> left_inverse_is_right in *.
    destruct (decide (loc2 = loc)); subst.
    + _rewrite -> right_extend_bijection_eq in *.
      rewrite_inj.
      eauto.
    + assert (left (extend_bijection Ψ loc1 loc2 H1 H2) loc' = Some loc).
      {
        destruct (extend_bijection Ψ loc1 loc2 H1 H2); eauto.
      }
      _rewrite -> right_extend_bijection_neq in * by solve[eauto].
      assert (left Ψ loc' = Some loc) by (destruct Ψ; eauto).
      assert (left Φ loc' = Some loc).
      {
        eapply filtered_bijection_is_subset.
        - eapply high_dec.
        - eauto.
        - eauto.
      }
      assert (high ℓ_adv m1 h1 loc').
      {
        eapply H11; eauto 2.
      }
      assert (high ℓ_adv m2 h2 loc).
      {
        rewrite <- high_iff; eauto 2.
      }
      assert (high ℓ_adv
                (m1 [x → ValLoc loc1]) 
                (extend_heap v1 loc1 l n h1 H3 H4) loc').
      {
        eapply H25; eauto.
      }
      destruct_high.
      * eapply HighReachable.
        eapply reach_in_extended_memory_and_heap with (Φ := Φ); eauto 2.
      * assert (loc' <> loc1).
        {
          intro; subst.
          _rewrite -> left_extend_bijection_eq in *.
          congruence.
        }
        rewrite -> heap_lookup_extend_neq in * by solve[eauto 2].
        rewrite_inj.
        assert ((exists ν, heap_lookup loc h2 = Some (ℓ0, ν)) /\ high ℓ_adv m2 h2 loc).
        {
          eapply H9; eauto.
        }
        super_destruct'; subst.
        eapply HighHeapLevel.
        { rewrite -> heap_lookup_extend_neq by solve[eauto 2].
          eauto. }
        { eauto 2. }
  - intros.
    rewrite -> left_inverse_is_right.
    destruct (decide (loc = loc2)); subst.
    {
      rewrite -> right_extend_bijection_eq.
      eauto.
    }
    assert (high ℓ_adv m2 h2 loc).
    {
      destruct_high.
      - eapply HighReachable.
        eapply reach_extend_implies_reach_if; eauto 2.
        intros; subst.
        destruct τ.
        + assert (exists n, ValLoc loc' = ValNum n) by eauto 2.
          super_destruct; congruence.
        + specialize (H22 _ _ eq_refl).
          super_destruct; subst.
          injects.
          eauto.
      - rewrite -> heap_lookup_extend_neq in * by solve[eauto 2].
        eauto 2.
    }
    assert (exists loc', left (inverse Φ) loc = Some loc').
    {
      eapply H12; eauto.
    }
    super_destruct; subst.
    assert (high ℓ_adv (m1 [x → ValLoc loc1])
                  (extend_heap v1 loc1 l n h1 H3 H4) loc').
    {
      inverts H26.
      - eapply HighReachable.
        eapply reach_in_extended_memory_and_heap with (Φ := inverse Φ); eauto 2.
      - rewrite -> heap_lookup_extend_neq in * by solve[eauto 2].
        assert (left Φ loc' = Some loc) by (destruct Φ; eauto 2).
        assert ((exists μ, heap_lookup loc' h1 = Some (ℓ0, μ)) /\ high ℓ_adv m1 h1 loc').
        {
          eapply H9; eauto.
        }
        super_destruct'.
        assert (loc1 <> loc').
        {
          intro; subst.
          congruence.
        }
        eapply HighHeapLevel.
        + rewrite -> heap_lookup_extend_neq by solve[eauto 2].
          eauto.
        + eauto 2.
    }
    assert (exists loc'', left (extend_bijection Ψ loc1 loc2 H1 H2)
                          loc' = Some loc'').
    {
      eapply H25; eauto.
    }
    super_destruct; subst.

    assert (loc1 <> loc').
    {
      intro; subst.
      _rewrite -> left_extend_bijection_eq in *.
      rewrite_inj.
      assert (left Φ loc' = Some loc) by (destruct Φ; eauto).
      assert (high ℓ_adv m1 h1 loc').
      {
        eapply H11; eauto.
      }
      destruct_high.
      - assert (exists ℓ μ, heap_lookup loc' h1 = Some (ℓ, μ)) by eauto 2.
        super_destruct; congruence.
      - congruence.
    }
    
    assert (left Φ loc' = Some loc) by (destruct Φ; eauto 2).
    assert (loc = loc'').
    {
      _rewrite -> left_extend_bijection_neq in * by solve[eauto 2].
      assert (left Φ loc' = Some loc'').
      {
        eapply filtered_bijection_is_subset.
        - eapply high_dec.
        - eauto.
        - eauto.
      }
      congruence.
    }
    subst.
    assert (right (extend_bijection Ψ loc1 loc2 H1 H2) loc'' = Some loc').
    {
      destruct (extend_bijection Ψ loc1 loc2 H1 H2); eauto 2.
    }
    eauto 3.
Qed.

Lemma taint_eq_mem_extend_mem_and_bijection:
  forall ℓ_adv Ψ Φ loc1 loc2 Γ τ ℓ ε m1 m2 x n1 v1 h1 H1 H2 H3 H4,
    taint_eq_mem Φ Γ m1 m2 ->
    Γ x = Some (SecType (Array τ ℓ) ε) ->
    filtered (high ℓ_adv 
                (extend_memory x (ValLoc loc1) m1)
                (extend_heap v1 loc1 ℓ n1 h1 H3 H4)) Φ Ψ ->
    taint_eq_mem (extend_bijection Ψ loc1 loc2 H1 H2) Γ
                 (extend_memory x (ValLoc loc1) m1)
                 (extend_memory x (ValLoc loc2) m2).
Proof.
  intros.
  unfold taint_eq_mem in *; super_destruct; subst.
  splits.
  - intros.
    destruct (decide (x = x0)); subst.
    * do 2 rewrite -> extend_memory_lookup_eq.
      splits*.
    * do 2 rewrite -> extend_memory_lookup_neq by solve[eauto 2].
      eauto.
  - intros.
    destruct (decide (x = x0)); subst.
    + rewrite -> extend_memory_lookup_eq in *.
      repeat injects.
      rewrite_inj.
      destruct ε as [ℓ' ι].
      destruct ι; eauto.
    + rewrite -> extend_memory_lookup_neq in * by solve[eauto 2].
      assert (val_taint_eq Φ τ0 v0 v2) by eauto 2.
      invert_val_taint_eq; eauto 3.
      assert (high ℓ_adv (m1 [x → ValLoc loc1])
                    (extend_heap v1 loc1 ℓ n1 h1 H3 H4) loc).
      {
        eapply HighReachable.
        eapply reach_mem.
        rewrite -> extend_memory_lookup_neq by solve[eauto 2].
        eauto.
      }
      assert (left Ψ loc = Some loc').
      {
        eapply filter_true; eauto 2.
      }
      assert (loc1 <> loc) by congruence.
      constructor.
      rewrite -> left_extend_bijection_neq by solve[eauto 2].
      eauto.
Qed.
Hint Resolve taint_eq_mem_extend_mem_and_bijection.

Lemma taint_eq_reach_extend_mem_and_heap:
  forall ℓ_adv Γ Ψ Φ loc1 loc2 ℓ ℓ_p x ε σ m1 m2 h1 h2 v1 v2 n1 n2 Σ1 Σ2 H1 H2 H3 H4 H5 H6,
    taint_eq_reach Φ m1 h1 m2 h2 ->
    wf_taint_bijection ℓ_adv Φ m1 h1 ->
    wf_taint_bijection ℓ_adv (inverse Φ) m2 h2 ->
    taint_eq_mem Φ Γ m1 m2 ->
    taint_eq_heap ℓ_adv Φ Σ1 Σ2 m1 h1 m2 h2 ->
    taint_eq_stenv Φ Σ1 Σ2 ->
    dangling_pointer_free m1 h1 ->
    dangling_pointer_free m2 h2 ->
    wf_tenv Γ m1 ->
    wf_tenv Γ m2 ->
    wf_stenv Σ1 h1 ->
    wf_stenv Σ2 h2 ->
    (forall s ℓ,
        σ = Array s ℓ -> exists loc, v1 = ValLoc loc /\ reach m1 h1 loc) ->
    (forall s ℓ,
        σ = Array s ℓ -> exists loc, v2 = ValLoc loc /\ reach m2 h2 loc) ->
    (σ = Int -> exists n, v1 = ValNum n) ->
    (σ = Int -> exists n, v2 = ValNum n) ->
    val_taint_eq Φ (SecType σ ε) v1 v2 ->
    Γ x = Some (SecType (Array (SecType σ ε) ℓ_p) (ℓ, ∘)) ->
    filtered (high ℓ_adv (extend_memory x (ValLoc loc1) m1)
                    (extend_heap v1 loc1 ℓ_p n1 h1 H3 H4)) Φ Ψ ->
    taint_eq_reach (extend_bijection Ψ loc1 loc2 H1 H2)
                   (extend_memory x (ValLoc loc1)  m1)
                   (extend_heap v1 loc1 ℓ_p n1 h1 H3 H4)
                   (extend_memory x (ValLoc loc2) m2)
                   (extend_heap v2 loc2 ℓ_p n2 h2 H5 H6).
Proof.
  intros.
  unfolds.
  intros.
  destruct (decide (loc = loc1)); subst.
  - _rewrite -> left_extend_bijection_eq in *.
    rewrite_inj.
    splits*.
  - _rewrite -> left_extend_bijection_neq in * by solve[eauto 2].
    destruct ε as [ℓ' ι'].
    splits.
    + intros.
      eapply reach_in_extended_memory_and_heap with (Φ := Φ);
        try solve[intros; subst; eauto 3].
      eapply filtered_bijection_is_subset.
      * eapply high_dec.
      * eauto.
      * eauto.
    + intros.
      eapply reach_in_extended_memory_and_heap with (Φ := (inverse Φ)) (m1 := m2) (h1 := h2); try solve[intros; subst; eauto 3].
      assert (left Φ loc = Some loc').
      {
        eapply filtered_bijection_is_subset.
        - eapply high_dec.
        - eauto.
        - eauto.
      }
      destruct Φ; eauto.
Qed.

Lemma taint_eq_heap_extend_mem_and_heap:
  forall ℓ_adv Ψ Φ loc1 loc2 τ Σ1 Σ2 ℓ m1 m2 n h1 h2 x v1 v2 H1 H2 H3 H4 H5 H6,
    taint_eq_heap ℓ_adv Φ Σ1 Σ2 m1 h1 m2 h2 ->
    val_taint_eq Φ τ v1 v2 ->
    (forall loc, v1 = ValLoc loc -> reach m1 h1 loc) ->
    (forall loc, v2 = ValLoc loc -> reach m2 h2 loc) ->
    filtered (high ℓ_adv
                (extend_memory x (ValLoc loc1) m1)
                (extend_heap v1 loc1 ℓ n h1 H3 H4)) Φ Ψ ->
    taint_eq_heap ℓ_adv
                  (extend_bijection Ψ loc1 loc2 H1 H2)
                  (extend_stenv loc1 τ Σ1) (extend_stenv loc2 τ Σ2)
                  (extend_memory x (ValLoc loc1) m1)
                  (extend_heap v1 loc1 ℓ n h1 H3 H4)
                  (extend_memory x (ValLoc loc2) m2)
                  (extend_heap v2 loc2 ℓ n h2 H5 H6).
Proof.
  intros.
  unfolds.
  intros.
  destruct (decide (loc1 = loc)); subst.
  - _rewrite -> left_extend_bijection_eq in *.
    rewrite_inj.
    rewrite -> extend_stenv_lookup_eq in *.
    rewrite_inj.
    apply_heap_lookup_extend_eq.
    rewrite_inj.
    revert H13; intros.
    apply_heap_lookup_extend_eq.
    rewrite_inj.
    splits*.
    + do 2 rewrite -> length_of_extend_eq.
      reflexivity.
    + intros.
      assert (v0 = v1) by congruence.
      assert (v2 = v3) by congruence.
      subst.
      invert_val_taint_eq; eauto 2.
      assert (high ℓ_adv
                   (m1 [x → ValLoc loc])
                   (extend_heap (ValLoc loc0) loc ℓ n h1 H3 H4) loc0).
      {
        eapply HighReachable.
        eauto 2.
      }
      assert (left Ψ loc0 = Some loc'0) by eauto.
      assert (loc0 <> loc) by congruence.
      constructor.
      rewrite -> left_extend_bijection_neq by solve[eauto 2].
      eauto.
  - _rewrite -> left_extend_bijection_neq in * by solve[eauto 2].
    assert (loc2 <> loc').
    {
      intro; subst.
      assert (right Ψ loc' = Some loc) by (destruct Ψ; eauto 2).
      congruence.
    }
    rewrite -> extend_stenv_lookup_neq in * by solve[eauto 2].
    rewrite -> heap_lookup_extend_neq in * by solve[eauto 2].
    assert (high ℓ_adv m1 h1 loc).
    {
      inverts H11.
      - eapply HighReachable.
        eapply reach_extend_implies_reach_if; eauto 2.
      - rewrite -> heap_lookup_extend_neq in * by solve[eauto 2].
        eauto 2.
    }
    assert (high ℓ_adv m2 h2 loc').
    {
      inverts H12.
      - eapply HighReachable.
        eapply reach_extend_implies_reach_if; eauto 2.
      - rewrite -> heap_lookup_extend_neq in * by solve[eauto 2].
        eauto 2.
    }
    assert (left Φ loc = Some loc').
    {
      eapply filtered_bijection_is_subset.
      - eapply high_dec.
      - eauto.
      - eauto.
    }
    remember_simple (H loc loc' _ _ _ _ _ H20 H18 H19 H13 H14 H15 H16).
    super_destruct'; subst.
    splits*.
    + do 2 rewrite -> length_of_extend_neq by solve[eauto 2].
      eauto.
    + intros.
      assert (reach m1 h1 loc) by eauto 2.
      assert (reach m2 h2 loc') by eauto 2.
      assert (val_taint_eq Φ τ0 v0 v3) by eauto 2.
      invert_val_taint_eq; eauto 2.
      assert (high ℓ_adv (m1 [x → ValLoc loc1])
                   (extend_heap v1 loc1 ℓ n h1 H3 H4) loc0).
      {
        eapply HighReachable.
        eapply reach_heap.
        - eauto.
        - rewrite -> heap_lookup_extend_neq by solve[eauto 2].
          eauto.
        - eauto.
      }
      assert (left Ψ loc0 = Some loc'0) by eauto 2.
      assert (loc0 <> loc1) by congruence.
      constructor.
      rewrite -> left_extend_bijection_neq by solve[eauto 2].
      eauto.
Qed.

Lemma high_update_implies_high_if:
  forall ℓ_adv m h loc1 loc2 n v,
    high ℓ_adv m (update_heap loc1 n v h) loc2 ->
    (forall loc', v = ValLoc loc' -> reach m h loc') ->
    high ℓ_adv m h loc2.
Proof.
  intros.
  destruct_high; eauto 3.
  destruct (decide (loc2 = loc1)); subst.
  - _apply heap_lookup_update_eq2 in *.
    super_destruct'; eauto 3.
  - rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
    eauto 2.
Qed.
Hint Resolve high_update_implies_high_if.

 Lemma taint_eq_update_bijection1:
    forall ℓ_adv Φ Ψ m1 h1 loc n v,
      wf_taint_bijection ℓ_adv Φ m1 h1 ->
      filtered (high ℓ_adv m1 (update_heap loc n v h1)) Φ Ψ ->
      (forall loc, v = ValLoc loc -> reach m1 h1 loc) ->
      wf_taint_bijection ℓ_adv Ψ m1 (update_heap loc n v h1).
  Proof.
    intros.
    unfolds.
    intros.
    splits; intros.
    - super_destruct'; subst.
      eapply filtered_bijection_some_implies_predicate; eauto 2.
      eapply high_dec.
    - assert (high ℓ_adv m1 h1 loc0) by eauto 2.
      assert (exists loc', left Φ loc0 = Some loc').
      {
        eapply H; eauto.
      }
      super_destruct'; subst.
      exists loc'.
      eapply filter_true.
      + eapply H2.
      + eauto.
      + eauto.
  Qed.

  Lemma reach_in_updated_heap:
    forall ℓ_adv Γ Σ1 Σ2 m1 h1 m2 h2 n v1 v2 l1 l2 loc1 loc2 Φ ε τ,
      wf_tenv Γ m1 ->
      wf_tenv Γ m2 ->
      wf_stenv Σ1 h1 ->
      wf_stenv Σ2 h2 ->
      taint_eq_mem Φ Γ m1 m2 ->
      taint_eq_heap ℓ_adv Φ Σ1 Σ2 m1 h1 m2 h2 ->
      taint_eq_heap_domain_eq ℓ_adv Φ m1 m2 h1 h2 -> 
      taint_eq_reach Φ m1 h1 m2 h2 ->
      taint_eq_stenv Φ Σ1 Σ2 ->
      Σ1 l1 = Some (SecType τ ε) ->
      Σ2 l2 = Some (SecType τ ε) ->
      left Φ l1 = Some l2 ->
      reach m1 (update_heap l1 n v1 h1) loc1 ->
      left Φ loc1 = Some loc2 ->
      val_taint_eq Φ (SecType τ ε) v1 v2 ->
      (forall s ℓ', τ = Array s ℓ' -> exists loc', v1 = ValLoc loc' /\
                                        reach m1 h1 loc') ->
      (forall s ℓ', τ = Array s ℓ' -> exists loc', v2 = ValLoc loc' /\
                                        reach m2 h2 loc') ->
      (τ = Int -> exists n, v1 = ValNum n) ->
      (τ = Int -> exists n, v2 = ValNum n) ->
      dangling_pointer_free m1 h1 ->
      dangling_pointer_free m2 h2 ->
      heap_level_bound Γ m1 h1 Σ1 ->
      heap_level_bound Γ m2 h2 Σ2 ->
      wf_taint_bijection ℓ_adv Φ m1 h1 ->
      reach m2 (update_heap l2 n v2 h2) loc2.
  Proof.
    intros.
    revert dependent loc2.
    match goal with
      [H: reach _ _ _ |- _] =>
      dependent induction H; intros
    end.
    - assert (memory_lookup m2 x = Some (ValLoc loc2)).
      {
        assert (exists v, memory_lookup m2 x = Some v).
        {
          eapply H3; eauto.
        }
        super_destruct; eauto.
        assert (exists τ, Γ x = Some τ) by eauto 2.
        super_destruct'; subst.
        assert (val_taint_eq Φ τ0 (ValLoc loc) v).
        {
          eapply H3; eauto 2.
        }
        invert_val_taint_eq.
        + rewrite_inj.
          eauto.
        + assert_wf_type.
          invert_wf_type.
      }
      eauto 2.
    - destruct (decide (loc = l1)); subst.
      + rewrite_inj.
        _apply heap_lookup_update_eq2 in *.
        super_destruct'; subst.
        rewrite_inj.
        destruct (decide (n = n0)); subst.
        * rewrite -> lookup_update_eq in *.
          rewrite_inj.
          invert_val_taint_eq.
          {
            rewrite_inj.
            assert (reach m2 (update_heap l2 n0 (ValLoc loc'0) h2) l2).
            {
              eapply IHreach; eauto 2.
            }
            assert (exists ℓ μ, heap_lookup l2 h2 = Some (ℓ, μ)).
            {
              assert (high ℓ_adv m h1 l1).
              {
                eapply H23; eauto.
              }
              assert (high ℓ_adv m2 h2 l2).
              {
                rewrite <- high_iff; eauto 2.
              }
              destruct_high; eauto 3.
            }
            super_destruct'; subst.
            eapply reach_heap.
            { eauto. }
            { eapply heap_lookup_update_eq; eauto. }
            { eauto. }
          }
          {
            assert_wf_type.
            invert_wf_type.
          }
        * rewrite -> lookup_update_neq in * by solve[eauto].
          assert (reach m2 (update_heap l2 n v2 h2) l2) by eauto 2.
          clear IHreach.
          assert (reach m h1 l1).
          {
            eapply reach_update_implies_reach_if; eauto 2.
            intros; subst.
            destruct τ.
            - repeat specialize_gen; super_destruct'; congruence.
            - specialize (H15 _ _ eq_refl).
              super_destruct; injects; eauto 2.
          }
          assert (reach m2 h2 l2).
          {
            eapply reach_update_implies_reach_if; eauto 2.
            intros; subst.
            destruct τ.
            - repeat specialize_gen; super_destruct'; congruence.
            - specialize (H16 _ _ eq_refl).
              super_destruct; injects; eauto 2.
          }
          assert (exists ℓ μ, heap_lookup l2 h2 = Some (ℓ, μ)).
          {
            eauto 2.
          }
          super_destruct'; subst.
          assert (lookup μ n0 = Some (ValLoc loc2)) by eauto 2 using taint_bijection_implies_lookup.
          eapply reach_heap.
          { eauto. }
          { eauto. }
          { rewrite -> lookup_update_neq by solve[eauto 2].
            eauto. }
      + rewrite -> heap_lookup_update_neq in * by solve[eauto].
        assert (reach m h1 loc).
        {
          eapply reach_update_implies_reach_if.
          - eauto.
          - intros; subst.
            destruct τ.
            + assert (exists n, ValLoc loc'0 = ValNum n) by eauto 2.
              super_destruct'; discriminate.
            + specialize (H15 _ _ eq_refl).
              super_destruct'; subst.
              injects.
              eauto.
        }
        assert (reach m h1 loc') by eauto 2.
        assert (reach m2 h2 loc2).
        {
          apply_taint_eq_reach.
        }
        assert (exists loc', left Φ loc = Some loc').
        {
          eapply H23; eauto.
        }
        super_destruct'; subst.
        assert (reach m2 h2 loc'0).
        {
          apply_taint_eq_reach.
        }
        assert (exists ℓ μ, heap_lookup loc'0 h2 = Some (ℓ, μ)) by eauto 3.
        super_destruct'; subst.
        assert (exists τ, Σ1 loc = Some τ) by eauto 2.
        super_destruct'; subst.
        assert (Σ2 loc'0 = Some τ0).
        {
          eapply H7; eauto.
        }
        
        assert (lookup μ0 n0 = Some (ValLoc loc2)).
        {
          eapply taint_bijection_implies_lookup
          with (h1 := h1) (h2 := h2) (loc2 := loc'0) (loc1 := loc); eauto.
        }
        assert (reach m2 (update_heap l2 n v2 h2) loc'0).
        {
          eapply IHreach; eauto 2.
        }
        assert (loc'0 <> l2).
        {
          assert (Some loc'0 <> left Φ l1) by eauto 2 using bijection_is_injective_left.
          intro; subst.
          eauto.
        }
        eapply reach_heap.
        * eauto.
        * rewrite -> heap_lookup_update_neq by solve[eauto 2].
          eauto.
        * eauto.
  Qed.

  Lemma wf_taint_bijection_update_heap2:
    forall ℓ_adv Φ Ψ m1 m2 h1 h2 loc1 loc2 n v1 v2 Γ σ ε Σ1 Σ2,
      wf_taint_bijection ℓ_adv Φ m1 h1 ->
      wf_taint_bijection ℓ_adv (inverse Φ) m2 h2 ->
      filtered (high ℓ_adv m1 (update_heap loc1 n v1 h1)) Φ Ψ ->
      wf_taint_bijection ℓ_adv Ψ m1 (update_heap loc1 n v1 h1) ->
      wf_tenv Γ m1 ->
      wf_tenv Γ m2 ->
      wf_stenv Σ1 h1 ->
      wf_stenv Σ2 h2 ->
      dangling_pointer_free m1 h1 ->
      dangling_pointer_free m2 h2 ->
      heap_level_bound Γ m1 h1 Σ1 ->
      heap_level_bound Γ m2 h2 Σ2 ->
      taint_eq_mem Φ Γ m1 m2 ->
      taint_eq_heap ℓ_adv Φ Σ1 Σ2 m1 h1 m2 h2 ->
      taint_eq_heap_domain_eq ℓ_adv Φ m1 m2 h1 h2 ->
      taint_eq_reach Φ m1 h1 m2 h2 ->
      taint_eq_stenv Φ Σ1 Σ2 ->
      left Φ loc1 = Some loc2 ->
      Σ1 loc1 = Some (SecType σ ε) ->
      Σ2 loc2 = Some (SecType σ ε) ->
      val_taint_eq Φ (SecType σ ε) v1 v2 ->
      (forall s ℓ, σ = Array s ℓ -> exists loc, v1 = ValLoc loc /\ reach m1 h1 loc) ->
      (forall s ℓ, σ = Array s ℓ -> exists loc, v2 = ValLoc loc /\ reach m2 h2 loc) ->
      (σ = Int -> exists n, v1 = ValNum n) ->
      (σ = Int -> exists n, v2 = ValNum n) ->
      wf_taint_bijection ℓ_adv (inverse Ψ) m2 (update_heap loc2 n v2 h2).
  Proof.
    intros.
    unfolds.
    intros.
    splits; intros.
    - super_destruct'; subst.
      assert (left Ψ loc' = Some loc) by (destruct Ψ; eauto 2).
      assert (left Φ loc' = Some loc).
      {
        eapply filtered_bijection_is_subset.
        - eapply high_dec.
        - eauto 2.
        - eauto 2.
      }
      assert (high ℓ_adv m1 (update_heap loc1 n v1 h1) loc').
      {
        eapply H2; eauto 2.
      }
      destruct_high.
      + assert (reach m1 h1 loc').
        {
          eapply reach_update_implies_reach_if; eauto 2.
          intros; subst.
          destruct σ.
          - repeat specialize_gen.
            super_destruct'; discriminate.
          - specialize (H20 _ _ eq_refl).
            super_destruct'; subst.
            injects.
            eauto 2.
        }
        eapply HighReachable.
        eapply reach_in_updated_heap with (m1 := m1) (m2 := m2) (h1 := h1) (h2 := h2); eauto.
      + assert ((exists μ, heap_lookup loc h2 = Some (ℓ, μ)) /\ high ℓ_adv m2 h2 loc).
        {
          destruct (decide (loc' = loc1)); subst.
          - _apply heap_lookup_update_eq2 in *.
            super_destruct'; subst.
            eapply H13; eauto.
          - rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
            eapply H13; eauto.
            
        }
        super_destruct'; subst.
        destruct (decide (loc2 = loc)); subst.
        * eapply HighHeapLevel; eauto.
        * eapply HighHeapLevel.
          {
            rewrite -> heap_lookup_update_neq by solve[eauto 2].
            eauto.
          }
          {
            eauto 2.
          }
    - assert (high ℓ_adv m2 h2 loc).
      {
        eapply high_update_implies_high_if; eauto 2.
        intros; subst.
        destruct σ.
        - assert (exists n, ValLoc loc' = ValNum n) by eauto 2.
          super_destruct'; discriminate.
        - specialize (H21 _ _ eq_refl).
          super_destruct'; subst.
          injects.
          eauto.
      }
      assert (exists loc', left (inverse Φ) loc = Some loc').
      {
        eapply H0; eauto.
      }
      super_destruct'; subst.
      exists loc'.
      assert (left Φ loc' = Some loc) by (destruct Φ; eauto 2).
      assert (left Ψ loc' = Some loc).
      {
        assert (high ℓ_adv m1 (update_heap loc1 n v1 h1) loc').
        {
          inverts H24.
          - eapply HighReachable.
            eapply reach_in_updated_heap with (m1 := m2) (m2 := m1)
                                                         (h1 := h2) (h2 := h1); eauto 3.
            destruct Φ; eauto 2.
          - assert ((exists μ, heap_lookup loc' h1 = Some (ℓ, μ)) /\ high ℓ_adv m1 h1 loc').
            {
              destruct (decide (loc = loc2)); subst.
              - _apply heap_lookup_update_eq2 in *.
                super_destruct'; subst.
                eapply H13; eauto.
              - rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
                eapply H13; eauto.
            }
            super_destruct'.
            destruct (decide (loc1 = loc')); subst.
            + eapply HighHeapLevel; eauto.
            + eapply HighHeapLevel.
              * rewrite -> heap_lookup_update_neq by solve[eauto 2].
                eauto.
              * eauto.
        }
        eauto 2.
      }
      destruct Ψ; eauto.
  Qed.

  Lemma taint_eq_mem_update_heap:
    forall ℓ_adv Φ Ψ Γ m1 m2 h1 v1 n loc1,
      taint_eq_mem Φ Γ m1 m2 ->
      filtered (high ℓ_adv m1 (update_heap loc1 n v1 h1)) Φ Ψ ->
      taint_eq_mem Ψ Γ m1 m2.
  Proof.
    intros.
    unfolds.
    splits.
    - eapply H; eauto.
    - intros.
      assert (val_taint_eq Φ τ v0 v2) by (eapply H; eauto 2).
      invert_val_taint_eq; eauto 2.
      assert (high ℓ_adv m1 (update_heap loc1 n v1 h1) loc) by eauto.
      assert (left Φ loc = Some loc') by eauto 2.
      eauto.
  Qed.

  Lemma taint_eq_reach_update_heap:
    forall ℓ_adv Φ Ψ m1 m2 h1 h2 v1 v2 n loc1 loc2 σ ε Γ Σ1 Σ2,
      taint_eq_reach Φ m1 h1 m2 h2 ->
      taint_eq_heap_domain_eq ℓ_adv Φ m1 m2 h1 h2 ->
      (forall s ℓ, σ = Array s ℓ -> exists loc, v1 = ValLoc loc /\ reach m1 h1 loc) ->
      (forall s ℓ, σ = Array s ℓ -> exists loc, v2 = ValLoc loc /\ reach m2 h2 loc) ->
      (σ = Int -> exists n, v1 = ValNum n) ->
      (σ = Int -> exists n, v2 = ValNum n) ->
      wf_taint_bijection ℓ_adv Φ m1 h1 ->
      wf_taint_bijection ℓ_adv (inverse Φ) m2 h2 ->
      wf_tenv Γ m1 ->
      wf_tenv Γ m2 ->
      wf_stenv Σ1 h1 ->
      wf_stenv Σ2 h2 ->
      dangling_pointer_free m1 h1 ->
      dangling_pointer_free m2 h2 ->
      heap_level_bound Γ m1 h1 Σ1 ->
      heap_level_bound Γ m2 h2 Σ2 ->
      taint_eq_mem Φ Γ m1 m2 ->
      taint_eq_heap ℓ_adv Φ Σ1 Σ2 m1 h1 m2 h2 ->
      taint_eq_reach Φ m1 h1 m2 h2 ->
      taint_eq_stenv Φ Σ1 Σ2 ->
      left Φ loc1 = Some loc2 ->
      Σ1 loc1 = Some (SecType σ ε) ->
      Σ2 loc2 = Some (SecType σ ε) ->
      val_taint_eq Φ (SecType σ ε) v1 v2 ->
      filtered (high ℓ_adv m1 (update_heap loc1 n v1 h1)) Φ Ψ ->
      taint_eq_reach Ψ
                     m1 (update_heap loc1 n v1 h1)
                     m2 (update_heap loc2 n v2 h2).
  Proof.
    intros.
    unfolds.
    intros.
    assert (left Φ loc = Some loc').
    {
      eapply filtered_bijection_is_subset.
      - eapply high_dec.
      - eauto.
      - eauto.
    }
    splits; intros.
    - assert (reach m1 h1 loc).
      {
        eapply reach_update_implies_reach_if.
        - eauto 2.
        - intros; subst.
          destruct σ.
          + assert (exists n, ValLoc loc'0 = ValNum n) by eauto 2.
            super_destruct'; discriminate.
          + specialize (H1 _ _ eq_refl).
            super_destruct'; injects.
            eauto.
      }
      assert (reach m2 h2 loc') by (eapply H; eauto 2).
      eapply reach_in_updated_heap with (m1 := m1) (m2 := m2) (h1 := h1) (h2 := h2); eauto 2.
    - assert (reach m2 h2 loc').
      {
        eapply reach_update_implies_reach_if.
        - eauto 2.
        - intros; subst.
          destruct σ.
          + assert (exists n, ValLoc loc'0 = ValNum n) by eauto 2.
            super_destruct'; discriminate.
          + specialize (H2 _ _ eq_refl).
            super_destruct'; injects.
            eauto.
      }
      assert (reach m1 h1 loc) by (eapply H; eauto 2).
      eapply reach_in_updated_heap with (m1 := m2) (m2 := m1) (h1 := h2) (h2 := h1); eauto 2 || (destruct Φ; eauto 2).
  Qed.

  Lemma taint_eq_heap_update_heap:
    forall Φ Ψ Σ1 Σ2 m1 h1 m2 h2 loc1 loc2 v1 v2 ℓ_adv τ n,
      taint_eq_heap ℓ_adv Φ Σ1 Σ2 m1 h1 m2 h2 ->
      left Φ loc1 = Some loc2 ->
      Σ1 loc1 = Some τ ->
      Σ2 loc2 = Some τ ->
      (forall loc, v1 = ValLoc loc -> reach m1 h1 loc) ->
      (forall loc, v2 = ValLoc loc -> reach m2 h2 loc) ->
      val_taint_eq Φ τ v1 v2 ->
      filtered (high ℓ_adv m1 (update_heap loc1 n v1 h1)) Φ Ψ ->
      taint_eq_heap ℓ_adv Ψ Σ1 Σ2 m1 (update_heap loc1 n v1 h1) m2 (update_heap loc2 n v2 h2).
  Proof.
    intros.
    unfolds.
    intros.
    assert (left Φ loc = Some loc').
    {
      eapply filtered_bijection_is_subset.
      - eapply high_dec.
      - eauto.
      - eauto.
    }
    destruct (decide (loc = loc1)); subst.
    - rewrite_inj.
      _apply heap_lookup_update_eq2 in *.
      super_destruct'; subst.
      assert (high ℓ_adv m1 h1 loc1) by eauto 2.
      assert (high ℓ_adv m2 h2 loc') by eauto 2.
      remember_simple (H loc1 loc' _ _ _ _ _ H0 H11 H12 H10 H2 H1 H13).
      super_destruct'; subst.
      splits*.
      + repeat rewrite -> length_of_update.
        eauto.
      + intros.
        splits; intros.
        * super_destruct'; subst.
          destruct (decide (n = n0)); subst.
          { rewrite -> lookup_update_eq in *.
            eauto. }
          { rewrite -> lookup_update_neq in * by solve[eauto 2].
            firstorder 2. }
        * super_destruct'; subst.
          destruct (decide (n = n0)); subst.
          { rewrite -> lookup_update_eq in *.
            eauto. }
          { rewrite -> lookup_update_neq in * by solve[eauto 2].
            firstorder 2. }
      + intros.
        destruct (decide (n = n0)); subst.
        * rewrite -> lookup_update_eq in *.
          rewrite_inj.
          invert_val_taint_eq; eauto 2.
          assert (high ℓ_adv m1 (update_heap loc1 n0 (ValLoc loc) h1) loc).
          {
            eapply HighReachable.
            eapply reach_heap; eauto.
          }
          assert (left Ψ loc = Some loc'0) by eauto 2.
          eauto 2.
        * rewrite -> lookup_update_neq in * by solve[eauto 2].
          assert (reach m1 h1 loc1) by eauto 2.
          assert (reach m2 h2 loc') by eauto 2.
          assert (val_taint_eq Φ τ v0 v3) by eauto 2.
          invert_val_taint_eq; eauto 2.
          assert (left Ψ loc = Some loc'0).
          {
            assert (high ℓ_adv m1 (update_heap loc1 n v1 h1) loc).
            {
              eapply HighReachable.
              eapply reach_heap.
              - eauto.
              - eauto.
              - rewrite -> lookup_update_neq by solve[eauto 2].
                eauto.
            }
            eauto 2.
          }
          eauto 2.
    - repeat rewrite -> length_of_update.
      assert (loc' <> loc2).
      {
        intro; subst.
        assert (Some loc2 <> left Φ loc1) by eauto 2 using bijection_is_injective_left.
        eauto.
      }
      repeat rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
      assert (high ℓ_adv m1 h1 loc) by eauto 2.
      assert (high ℓ_adv m2 h2 loc') by eauto 2.
      remember_simple (H loc loc' _ _ _ _ _ H14 H16 H17 H10 H11 H12 H13).
      super_destruct'; subst.
      splits*.
      intros.
      assert (reach m1 h1 loc) by eauto 2.
      assert (reach m2 h2 loc') by eauto 2.
      assert (val_taint_eq Φ τ0 v0 v3) by eauto 2.
      invert_val_taint_eq; eauto 2.
      assert (left Ψ loc0 = Some loc'0).
      {
        assert (high ℓ_adv m1 (update_heap loc1 n v1 h1) loc0).
        {
          eapply HighReachable.
          eapply reach_heap.
          - eauto.
          - rewrite -> heap_lookup_update_neq by solve[eauto 2].
            eauto.
          - eauto 2.
        }
        eauto 2.
      }
      eauto.
  Qed.

  Lemma set_bridge_properties:
    forall x e e0 pc pc' m m' h h'' t t' Γ Σ Σ' ev n ℓ c',
      ⟨SetArr x e e0, pc, m, h, t⟩ ↷ [ℓ, Γ, Σ, Σ', ev, n] ⟨c', pc', m', h'', t'⟩ ->
      exists h',
        c' = Stop /\
        gc_trans Σ Σ ⟨SetArr x e e0, pc, m, h, t⟩ ⟨SetArr x e e0, pc, m, h', t' - 1⟩ n /\
        ⟨SetArr x e e0, pc, m, h', t' - 1⟩ ↷ [ℓ, Γ, Σ, Σ', ev, 0] ⟨Stop, pc', m', h'', t'⟩.
  Proof.
    intros.
    dependent induction H.
    - invert_low_event_step.
      invert_event_step.
      + invert_sem_step.
        replace (S t - 1) with (t + 0) by omega.
        rewrite -> plus_0_r.
        exists h.
        splits*.
        constructor.
        constructor; eauto 2.
        constructor.
        eapply event_sem_step_set; eauto 2.
      + invert_low_event.
    - unfold is_stop_config, cmd_of in *; subst.
      invert_high_event_step.
      invert_event_step.
      invert_sem_step.
      replace (S t - 1) with (t + 0) by omega.
      rewrite -> plus_0_r.
      exists h.
      splits*.
    - invert_high_event_step.
      invert_event_step.
      + exfalso; eauto 2.
      + remember_simple (IHbridge_step_num _ _ _ _ _ _ _ _ _ _ _ _ eq_refl eq_refl).
        super_destruct'; subst.
        exists h'.
        splits*.
        eapply GCTrans.
        * unfolds.
          splits; reflexivity || eauto 2.
          do 7 eexists.
          splits; reflexivity || eauto 2.
        * eauto.
  Qed.

  Lemma get_bridge_properties:
    forall x y e pc pc' m m' h h'' t t' Γ Σ Σ' ev n ℓ c',
      ⟨GetArr x y e, pc, m, h, t⟩ ↷ [ℓ, Γ, Σ, Σ', ev, n] ⟨c', pc', m', h'', t'⟩ ->
      exists h', c' = Stop /\
        gc_trans Σ Σ ⟨GetArr x y e, pc, m, h, t⟩ ⟨GetArr x y e, pc, m, h', t' - 1⟩ n /\
        ⟨GetArr x y e, pc, m, h', t' - 1⟩ ↷ [ℓ, Γ, Σ, Σ', ev, 0] ⟨Stop, pc', m', h'', t'⟩.
  Proof.
    intros.
    dependent induction H.
    - invert_low_event_step.
      invert_event_step.
      + invert_sem_step.
        replace (S t - 1) with (t + 0) by omega.
        rewrite -> plus_0_r.
        exists h''.
        splits*.
        constructor.
        constructor; eauto 2.
        constructor.
        rewrite_inj.
        eapply event_sem_step_get; eauto 2.
      + invert_low_event.
    - unfold is_stop_config, cmd_of in *; subst.
      invert_high_event_step.
      invert_event_step.
      invert_sem_step.
      replace (S t - 1) with (t + 0) by omega.
      rewrite -> plus_0_r.
      exists h''.
      rewrite_inj.
      splits*.
    - invert_high_event_step.
      invert_event_step.
      + exfalso; eauto 2.
      + remember_simple (IHbridge_step_num _ _ _ _ _ _ _ _ _ _ _ _ eq_refl eq_refl).
        super_destruct'; subst.
        exists h'.
        splits*.
        eapply GCTrans.
        * unfolds.
          splits; reflexivity || eauto 2.
          do 7 eexists.
          splits; reflexivity || eauto 2.
        * eauto.
  Qed.

  Lemma time_bridge_properties:
    forall x pc pc' m m' h h'' t t' Γ Σ Σ' ev n ℓ c',
      ⟨Time x, pc, m, h, t⟩ ↷ [ℓ, Γ, Σ, Σ', ev, n] ⟨c', pc', m', h'', t'⟩ ->
      exists h', c' = Stop /\
        gc_trans Σ Σ ⟨Time x, pc, m, h, t⟩ ⟨Time x, pc, m, h', t' - 1⟩ n /\
        ⟨Time x, pc, m, h', t' - 1⟩ ↷ [ℓ, Γ, Σ, Σ', ev, 0] ⟨Stop, pc', m', h'', t'⟩.
  Proof.
    intros.
    dependent induction H.
    - invert_low_event_step.
      invert_event_step.
      + invert_sem_step.
        replace (S t - 1) with (t + 0) by omega.
        rewrite -> plus_0_r.
        exists h''.
        splits*.
        constructor.
        constructor; eauto 2.
        constructor.
        rewrite_inj.
        eapply event_sem_step_time; eauto 2.
      + invert_low_event.
    - unfold is_stop_config, cmd_of in *; subst.
      invert_high_event_step.
      invert_event_step.
      invert_sem_step.
      replace (S t - 1) with (t + 0) by omega.
      rewrite -> plus_0_r.
      exists h''.
      rewrite_inj.
      splits*.
    - invert_high_event_step.
      invert_event_step.
      + exfalso; eauto 2.
      + remember_simple (IHbridge_step_num _ _ _ _ _ _ _ _ _ _ eq_refl eq_refl).
        super_destruct'; subst.
        exists h'.
        splits*.
        eapply GCTrans.
        * unfolds.
          splits; reflexivity || eauto 2.
          do 7 eexists.
          splits; reflexivity || eauto 2.
        * eauto.
  Qed.

  Ltac apply_IH :=
    match goal with
      [H: forall m, m <= ?n -> ni_bridge m ?ℓ,
         H1: ?k <= ?n,
         H2: wf_bijection ?ℓ ?ψ ?Γ ?Σ' ?m' ?h,
         H3: wf_bijection ?ℓ (inverse ?ψ) ?Γ ?Σ2' ?m2' ?h2,
         H4: wf_taint_bijection ?ℓ ?Φ ?m2' ?h2,
         H5: wf_taint_bijection ?ℓ (inverse ?Φ) ?s1' ?w1',
         H6: wellformed_aux ?Γ ?Σ' ⟨?c, ?pc2', ?m', ?h, ?t ⟩ ?pc_end,
         H7: wellformed_aux ?Γ ?Σ2' ⟨?c, ?pc2', ?m2', ?h2, ?t⟩ ?pc_end,
         H8: wellformed_aux ?Γ ?Σ3 ⟨?c', ?pc2', ?s1', ?w1', ?t' ⟩ ?pc_end',
         H9: state_low_eq ?ℓ ?ψ ?m' ?h ?m2' ?h2 ?Γ ?Σ' ?Σ2',
         H10: ?pc2' ⊑ ?ℓ,
         H11: taint_eq ?ℓ ?Φ ?Γ ?Σ2' ?Σ3 ?c ?c' ?m2' ?h2 ?s1' ?w1',
         H12: ⟨?c, ?pc2', ?m', ?h, ?t ⟩ ↷ [?ℓ, ?Γ, ?Σ', ?Σ1', ?ev1, ?k] ⟨?c2, ?pc1', ?m2, ?h3, ?t2 ⟩,
         H13: ⟨?c', ?pc2', ?s1', ?w1', ?t'⟩ ↷ [?ℓ, ?Γ, ?Σ3, ?Σ3', ?ev2, ?n2] ⟨?c2', ?pc2'', ?s2'', ?w2'', ?g2''⟩,
         H14: ?c2 <> TimeOut,
         H15: ?c2' <> TimeOut |- _] =>
      remember_simple (H _ H1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)
    end.

  Lemma gc_trans_preserves_eval2:
    forall Σ Σ' c c' pc pc' m m' h h' t t' e v n,
      gc_trans Σ Σ' ⟨ c, pc, m, h, t⟩ ⟨ c', pc', m', h', t' ⟩ n ->
      eval m e = Some v ->
      eval m' e = Some v.
  Proof.
    intros.
    dependent induction H; eauto.
    unfold gc_occurred in *; super_destruct; subst.
    eapply IHgc_trans; eauto.
  Qed.
  Hint Resolve gc_trans_preserves_eval2.

Lemma at_bridge_properties:
    forall n Γ ℓ Σ Σ' l e c c' pc pc' m m' h h' t t' ev,
      ⟨At l e c, pc, m, h, t⟩ ↷ [ℓ, Γ, Σ, Σ', ev, n] ⟨c', pc', m', h', t'⟩ ->
      exists k1 h1 t1 v,
        gc_trans Σ Σ ⟨At l e c, pc, m, h, t⟩ ⟨At l e c, pc, m, h1, t1⟩ k1 /\
        eval m e = Some (ValNum v) /\
        ⟨At l e c, pc, m, h1, t1⟩ ⇒ (Γ, Σ, Σ) ⟨c;; BackAt pc (v + t1), l, m, h1, S t1⟩ /\
        ⟨c;; BackAt pc (v + t1), l, m, h1, S t1⟩ ↷ [ℓ, Γ, Σ, Σ', ev, n - k1 - 1] ⟨c', pc', m', h', t'⟩.
  Proof.
    intros n Γ ℓ.        
    induction n; intros.
    - invert_bridge_step.
      + invert_low_event_step.
        invert_event_step; invert_low_event.
      + unfold is_stop_config, cmd_of in *; subst.
        invert_high_event_step.
        invert_event_step.
        invert_sem_step.
    - invert_bridge_step.
      invert_high_event_step.
      invert_event_step.
      + invert_sem_step.
        exists 0 h'0 t n0.
        replace (S n - 0 - 1) with n by omega.
        splits*.
      + remember_simple (IHn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H11).
        super_destruct'; subst.
        exists (S k1) h1 t1 v.
        splits*.
        * eapply GCTrans.
          {
            unfolds.
            splits; reflexivity || eauto 2.
            do 7 eexists.
            splits; reflexivity || eauto 2.
          }
          { eauto. }
  Qed. 

  Lemma no_backat_and_taint_eq_implies_eq:
    forall c c',
      ~ contains_backat c ->
      taint_eq_cmd c c' ->
      c = c'.
  Proof.
    intros.
    dependent induction H0; eauto 2.
    - assert (~ contains_backat c1) by eauto.
      assert (~ contains_backat c2) by eauto.
      repeat specialize_gen.
      congruence.
    - assert (~ contains_backat c) by eauto.
      specialize_gen.
      congruence.
    - assert (~ contains_backat c1) by eauto.
      assert (~ contains_backat c2) by eauto.
      repeat specialize_gen.
      congruence.
    - assert (~ contains_backat c) by eauto.
      specialize_gen.
      congruence.
    - exfalso; eauto 2.
  Qed.
  Hint Resolve no_backat_and_taint_eq_implies_eq.

  Lemma gc_trans_high_event_bridge_implies_bridge:
    forall ℓ Γ n k Σ Σ' Σ'' Σ''' c c' c'' pc pc' pc'' pc''' m m' m'' m''' h h' h'' h''' t t' t'' t''' ev ev',
      gc_trans Σ Σ' ⟨c, pc, m, h, t⟩ ⟨c, pc', m', h', t'⟩ k ->
      ⟨c, pc, m', h', t'⟩ ⇒ [ev, Γ, Σ', Σ''] ⟨c', pc'', m'', h'', t''⟩ ->
      high_event ℓ ev ->
      ⟨c', pc'', m'', h'', t''⟩ ↷ [ℓ, Γ, Σ'', Σ''', ev', n] ⟨c'', pc''', m''', h''', t'''⟩ ->
      ⟨c, pc, m, h, t⟩ ↷ [ℓ, Γ, Σ, Σ''', ev', k + n + 1] ⟨c'', pc''', m''', h''', t'''⟩.
  Proof.
    intros.
    dependent induction H.
    - unfold gc_occurred in *; super_destruct'; subst.
      remember_simple (IHgc_trans _ _ _ _ eq_refl H1 H2 H3).
      replace (S n0 + n + 1) with (S (n0 + n + 1)) by omega.
      eapply bridge_trans_num.
      + splits*.
      + eauto.
      + eauto.
      + eauto.
    - replace (0 + n + 1) with (n + 1) by omega.
      revert c pc' m' h' t' Σ Σ''' ev' c'' pc''' m''' h''' t''' H0 H2.
      revert Σ'' c' pc'' m'' h'' t'' ev H1.
      induction n; intros.
      + replace (0 + 1) with 1 by omega.
        invert_bridge_step.
        * invert_low_event_step.
          eapply bridge_trans_num.
          {
            splits*.
          }
          {
            intro; unfold is_stop_config, cmd_of in *; subst.
            invert_event_step; exfalso; eauto 2.
          }
          {
            intro; unfold is_timeout_config, cmd_of in *; subst.
            invert_event_step; exfalso; eauto 2.
          }
          { eauto. }
        * unfold is_stop_config, cmd_of in *; subst.
          invert_high_event_step.
          eapply bridge_trans_num.
          {
            eauto.
          }
          { unfold is_stop_config, cmd_of; intro; subst.
            invert_event_step; exfalso; eauto 2. }
          { unfold is_timeout_config, cmd_of; intro; subst.
            invert_event_step; exfalso; eauto 2. }
          { eauto. }
      + invert_bridge_step.
        invert_high_event_step.
        destruct cfg2 as [c2 pc2 m2 h2 t2].
        remember_simple (IHn _ _ _ _ _ _ _ H2 _ _ _ _ _ _ _ _ _ _ _ _ _ H H13).
        replace (S n + 1) with (S (n + 1)) by omega.
        eapply bridge_trans_num.
        * splits*.
        * unfold is_stop_config, cmd_of; intro; subst.
          invert_event_step; exfalso; eauto 2.
        * unfold is_timeout_config, cmd_of; intro; subst.
          invert_event_step; exfalso; eauto 2.
        * eauto.
  Qed.

  Inductive lack_behind: nat -> cmd -> cmd -> Prop :=
  | LackBehindSkip: forall δ,
      lack_behind δ Skip Skip
  | LackBehindStop: forall δ,
      lack_behind δ Stop Stop
  | LackBehindAssign: forall δ x e,
      lack_behind δ (Assign x e) (Assign x e)
  | LackBehindIf: forall δ e c1 c2 c1' c2',
      lack_behind δ c1 c1' ->
      lack_behind δ c2 c2' ->
      lack_behind δ (If e c1 c2) (If e c1' c2')
  | LackBehindWhile: forall δ e c c',
      lack_behind δ c c' ->
      lack_behind δ (While e c) (While e c')
  | LackBehindSeq: forall δ c1 c2 c1' c2',
      lack_behind δ c1 c1' ->
      lack_behind δ c2 c2' ->
      lack_behind δ (c1 ;; c2) (c1' ;; c2')
  | LackBehindAt: forall δ ℓ e c c',
      lack_behind δ c c' ->
      lack_behind δ (At ℓ e c) (At ℓ e c')
  | LackBehindBackAt: forall δ ℓ n1 n2,
      n1 + δ = n2 ->
      lack_behind δ (BackAt ℓ n1) (BackAt ℓ n2)
  | LackBehindNew: forall δ x ℓ e1 e2,
      lack_behind δ (NewArr x ℓ e1 e2) (NewArr x ℓ e1 e2)
  | LackBehindSet: forall δ x e1 e2,
      lack_behind δ (SetArr x e1 e2) (SetArr x e1 e2)
  | LackBehindGet: forall δ x y e,
      lack_behind δ (GetArr x y e) (GetArr x y e)
  | LackBehindTime: forall δ x,
      lack_behind δ (Time x) (Time x)
  | LackBehindTimeOut: forall δ,
      lack_behind δ TimeOut TimeOut.
  Hint Constructors lack_behind.

  Notation "c1 '≲' '[' δ ']' c2" := (lack_behind δ c1 c2)  (at level 20).

  Ltac invert_lack_behind :=
    match goal with
      [H: lack_behind _ _ _ |- _] => inverts H
    end.
  
  Lemma lack_behind_refl:
    forall c,
      c ≲ [0] c.
  Proof.
    intros.
    induction c; eauto.
  Qed.

  Lemma lack_behind_trans:
    forall δ δ' c c' c'',
      c ≲ [δ] c' ->
      c' ≲ [δ'] c'' ->
      c ≲ [δ + δ'] c''.
  Proof.
    intros.
    revert c'' δ' H0.
    dependent induction H; intros; try solve[inverts H0; eauto].
    - inverts H1.
      eauto.
    - inverts H1.
      eauto.
    - inverts H0.
      constructor.
      omega.
  Qed.

  
  Lemma taint_eq_heap_domain_eq_extend_mem:
    forall Γ ℓ_adv Φ Ψ m s h w l σ x v1 v2 Σ1 Σ2,
      taint_eq_heap_domain_eq ℓ_adv Φ m s h w ->
      wf_taint_bijection ℓ_adv Φ m h ->
      wf_taint_bijection ℓ_adv (inverse Φ) s w ->
      Γ x = Some (SecType σ l) ->
      taint_eq_mem Φ Γ m s ->
      taint_eq_heap ℓ_adv Φ Σ1 Σ2 m h s w ->
      taint_eq_reach Φ m h s w ->
      taint_eq_stenv Φ Σ1 Σ2 ->
      val_taint_eq Φ (SecType σ l) v1 v2 ->
      wf_taint_bijection ℓ_adv Φ m h ->
      wf_taint_bijection ℓ_adv (inverse Φ) s w ->
      dangling_pointer_free m h ->
      dangling_pointer_free s w ->
      wf_tenv Γ m ->
      wf_tenv Γ s ->
      wf_stenv Σ1 h ->
      wf_stenv Σ2 w ->
      (forall t ℓ, σ = Array t ℓ -> exists loc', v1 = ValLoc loc' /\ reach m h loc') ->
      (σ = Int -> exists n, v1 = ValNum n) ->
      (forall t ℓ, σ = Array t ℓ -> exists loc', v2 = ValLoc loc' /\ reach s w loc') ->
      (σ = Int -> exists n, v2 = ValNum n) ->
      filtered (high ℓ_adv (extend_memory x v1 m) h) Φ Ψ ->
      taint_eq_heap_domain_eq ℓ_adv Ψ
                              (extend_memory x v1 m)
                              (extend_memory x v2 s) h w.
  Proof.
    intros.
    unfolds.
    intros.
    assert (left Φ l1 = Some l2).
    {
      eapply filtered_bijection_is_subset.
      - eapply high_dec.
      - eauto.
      - eauto.
    }
    assert (high ℓ_adv m h l1).
    {
      eapply H0; eauto 2.
    }
    assert (high ℓ_adv s w l2).
    {
      eapply H1.
      destruct Φ; eauto.
    }
    splits; intros.
    - super_destruct'; subst.
      splits.
      + eapply H; eauto.
      + destruct_high.
        * eapply HighReachable.
          eapply reach_in_extended_memory; eauto 2.
        * rewrite_inj.
          assert ((exists μ, heap_lookup l2 w = Some (ℓ0, μ)) /\ high ℓ_adv s w l2).
          {
            eapply H; eauto.
          }
          super_destruct'; subst.
          eapply HighHeapLevel; eauto 2.
    - super_destruct'; subst.
      splits.
      + eapply H; eauto.
      + destruct_high.
        * eapply HighReachable.
          eapply reach_in_extended_memory with (Φ := inverse Φ); eauto 3.
          { rewrite <- inverse_is_involutive; eauto 2. }
          { destruct Φ; eauto 2. }
        * rewrite_inj.
          assert ((exists μ, heap_lookup l1 h = Some (ℓ0, μ)) /\ high ℓ_adv m h l1).
          {
            eapply H; eauto.
          }
          super_destruct'; subst.
          eapply HighHeapLevel; eauto 2.
  Qed.

  Lemma taint_eq_heap_domain_eq_extend_mem_and_heap:
    forall Γ ℓ_adv Φ m s h w loc1 loc2 x n v1 v2 ℓ ℓ_x σ ε Ψ Σ1 Σ2 H1 H2 H3 H4 H5 H6,
      wf_taint_bijection ℓ_adv Φ m h ->
      wf_taint_bijection ℓ_adv (inverse Φ) s w ->
      (forall t ℓ, σ = Array t ℓ -> exists loc, v1 = ValLoc loc /\ reach m h loc) ->
      (forall t ℓ, σ = Array t ℓ -> exists loc, v2 = ValLoc loc /\ reach s w loc) ->
      filtered (high ℓ_adv (extend_memory x (ValLoc loc1)  m)
                     (extend_heap v1 loc1 ℓ n h H3 H4)) Φ Ψ ->
      Γ x = Some (SecType (Array (SecType σ ε) ℓ) (ℓ_x, ∘)) ->
      taint_eq_reach Φ m h s w ->
      taint_eq_mem Φ Γ m s ->
      taint_eq_heap ℓ_adv Φ Σ1 Σ2 m h s w ->
      taint_eq_heap_domain_eq ℓ_adv Φ m s h w ->
      taint_eq_stenv Φ Σ1 Σ2 ->
      dangling_pointer_free m h ->
      dangling_pointer_free s w ->
      wf_tenv Γ m ->
      wf_tenv Γ s ->
      wf_stenv Σ1 h ->
      wf_stenv Σ2 w ->
      (σ = Int -> exists n, v1 = ValNum n) ->
      (σ = Int -> exists n, v2 = ValNum n) ->
      val_taint_eq Φ (SecType σ ε) v1 v2 ->
      taint_eq_heap_domain_eq ℓ_adv
                              (extend_bijection Ψ loc1 loc2 H1 H2)
                              (extend_memory x (ValLoc loc1) m)
                              (extend_memory x (ValLoc loc2) s)
                              (extend_heap v1 loc1 ℓ n h H3 H4)
                              (extend_heap v2 loc2 ℓ n w H5 H6).
  Proof.
    intros.
    unfolds.
    intros.
    remember_simple (heap_lookup_extend_eq loc1 ℓ n v1 h H3 H4).
    remember_simple (heap_lookup_extend_eq loc2 ℓ n v2 w H5 H6).
    super_destruct; subst.
    destruct (decide (l1 = loc1)); subst.
    - _rewrite -> left_extend_bijection_eq in *.
      injects.                
      splits; intros.
      + super_destruct'; subst.
        rewrite_inj.
        splits; eauto 4.        
      + super_destruct'; subst.
        rewrite_inj.
        splits; eauto 4.
    - _rewrite -> left_extend_bijection_neq in * by solve[eauto 2].
      splits; intros.
      + super_destruct'; subst.
        rewrite -> heap_lookup_extend_neq in * by solve[eauto 2].
        assert (l2 <> loc2).
        {
          intro; subst.
          assert (right Ψ loc2 = Some l1) by (destruct Ψ; eauto 2).
          congruence.
        }
        rewrite -> heap_lookup_extend_neq by solve[eauto 2].
        assert (high ℓ_adv m h l1).
        {
          destruct_high.
          - eapply HighReachable.
            eapply reach_extend_implies_reach_if; eauto 2.
            intros; subst.
            destruct σ.
            + assert (exists n, ValLoc loc' = ValNum n) by eauto 2.
              super_destruct; discriminate.
            + specialize (H7 _ _ eq_refl); super_destruct; subst.
              injects.
              eauto.
          - rewrite -> heap_lookup_extend_neq in * by solve[eauto 2].
            eapply HighHeapLevel; eauto 2.
        }
        assert (left Φ l1 = Some l2).
        {
          eapply filtered_bijection_is_subset.
          - eapply high_dec.
          - eauto 2.
          - eauto 2.
        }
        assert ((exists ν, heap_lookup l2 w = Some (ℓ0, ν)) /\ high ℓ_adv s w l2).
        {
          eapply H14; eauto.
        }
        super_destruct'; subst.
        splits; eauto 2.
        inverts H31.
        * eapply HighReachable.
          destruct ε as [ℓ' ι'].                    
          eapply reach_in_extended_memory_and_heap with (Φ := Φ); eauto 2.
        * rewrite -> heap_lookup_extend_neq in * by solve[eauto 2].
          rewrite_inj.
          eapply HighHeapLevel.
          { rewrite -> heap_lookup_extend_neq by solve[eauto 2].
            eauto 2. }
          { eauto 2. }
      + super_destruct'; subst.
        rewrite -> heap_lookup_extend_neq by solve[eauto 2].
        assert (l2 <> loc2).
        {
          intro; subst.
          assert (right Ψ loc2 = Some l1) by (destruct Ψ; eauto 2).
          congruence.
        }
        rewrite -> heap_lookup_extend_neq in * by solve[eauto 2].
        assert (high ℓ_adv s w l2).
        {
          destruct_high.
          - eapply HighReachable.
            eapply reach_extend_implies_reach_if; eauto 2.
            intros; subst.
            destruct σ.
            + assert (exists n, ValLoc loc' = ValNum n) by eauto 2.
              super_destruct; discriminate.
            + specialize (H8 _ _ eq_refl); super_destruct; subst.
              injects.
              eauto.
          - rewrite -> heap_lookup_extend_neq in * by solve[eauto 2].
            eapply HighHeapLevel; eauto 2.
        }
        assert (left Φ l1 = Some l2).
        {
          eapply filtered_bijection_is_subset.
          - eapply high_dec.
          - eauto 2.
          - eauto 2.
        }
        assert ((exists ν, heap_lookup l1 h = Some (ℓ0, ν)) /\ high ℓ_adv m h l1).
        {
          eapply H14; eauto.
        }
        super_destruct'; subst.
        splits; eauto 2.
        inverts H31.
        * eapply HighReachable.
          destruct ε as [ℓ' ι'].                    
          eapply reach_in_extended_memory_and_heap with (Φ := inverse Φ); destruct Φ; eauto 2.
        * rewrite -> heap_lookup_extend_neq in * by solve[eauto 2].
          rewrite_inj.
          eapply HighHeapLevel.
          { rewrite -> heap_lookup_extend_neq by solve[eauto 2].
            eauto 2. }
          { eauto 2. }
  Qed.

  Lemma taint_eq_heap_update_domain_eq_update_heap:
    forall ℓ_adv Φ Ψ m s h w n loc1 loc2 τ ε v u Σ1 Σ2 Γ,
      taint_eq_heap_domain_eq ℓ_adv Φ m s h w ->
      wf_taint_bijection ℓ_adv Φ m h ->
      wf_taint_bijection ℓ_adv (inverse Φ) s w ->
      filtered (high ℓ_adv m (update_heap loc1 n v h)) Φ Ψ ->
      left Φ loc1 = Some loc2 ->
      Σ1 loc1 = Some (SecType τ ε) ->
      Σ2 loc2 = Some (SecType τ ε) ->
      val_taint_eq Φ (SecType τ ε) v u ->
      wf_tenv Γ m ->
      wf_tenv Γ s ->
      wf_stenv Σ1 h ->
      wf_stenv Σ2 w ->
      taint_eq_mem Φ Γ m s ->
      taint_eq_heap ℓ_adv Φ Σ1 Σ2 m h s w ->
      taint_eq_heap_domain_eq ℓ_adv Φ m s h w ->
      taint_eq_reach Φ m h s w ->
      taint_eq_stenv Φ Σ1 Σ2 ->
      val_taint_eq Φ (SecType τ ε) v u ->
      (forall t ℓ, τ = Array t ℓ -> exists loc, v = ValLoc loc /\ reach m h loc) ->
      (forall t ℓ, τ = Array t ℓ -> exists loc, u = ValLoc loc /\ reach s w loc) ->
      (τ = Int -> exists n0, v = ValNum n0) ->
      (τ = Int -> exists n0, u = ValNum n0) ->
      dangling_pointer_free m h ->
      dangling_pointer_free s w ->
      heap_level_bound Γ m h Σ1 ->
      heap_level_bound Γ s w Σ2 ->
      taint_eq_heap_domain_eq ℓ_adv Ψ m s (update_heap loc1 n v h) (update_heap loc2 n u w).
  Proof.
    intros.
    unfolds.
    intros.
    assert (left Φ l1 = Some l2).
    {
      eapply filtered_bijection_is_subset.
      - eapply high_dec.
      - eauto.
      - eauto.
    }
    assert (high ℓ_adv m h l1).
    {
      eapply H0; eauto 2.
    }
    assert (exists ℓ μ, heap_lookup l1 h = Some (ℓ, μ)).
    {
      destruct_high; eauto 3.
    }
    super_destruct'; subst.
    assert ((exists ν, heap_lookup l2 w = Some (ℓ0, ν)) /\ high ℓ_adv s w l2).
    {
      eapply H; eauto.
    }
    super_destruct'; subst.
    splits; intros.
    - super_destruct'; subst.
      destruct (decide (l1 = loc1)); subst.
      + rewrite_inj.
        _apply heap_lookup_update_eq2 in *.
        super_destruct'; subst.
        rewrite_inj.
        splits; eauto 3.
        destruct_high.
        * eapply HighReachable.
          eapply reach_in_updated_heap with (m1 := m) (Φ := Φ) (h1 := h); eauto 2.
        * _apply heap_lookup_update_eq2 in *.
          super_destruct'; subst.
          rewrite_inj.
          eapply HighHeapLevel; eauto 2.
      + assert (l2 <> loc2).
        {
          intro; subst.
          assert (Some loc2 <> left Φ loc1) by eauto 2 using bijection_is_injective_left.
          congruence.
        }
        rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
        rewrite_inj.
        splits; eauto 4.
        destruct_high.
        * eapply HighReachable.
          eapply reach_in_updated_heap with (m1 := m) (Φ := Φ) (h1 := h); eauto 2.
        * rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
          rewrite_inj.
          eapply HighHeapLevel.
          { rewrite -> heap_lookup_update_neq by solve[eauto 2].
            eauto. }
          { eauto 2. }
    - super_destruct'; subst.
      destruct (decide (l1 = loc1)); subst.
      + rewrite_inj.
        _apply heap_lookup_update_eq2 in *.
        super_destruct'; subst.
        rewrite_inj.
        splits; eauto 3.
        destruct_high.
        * eapply HighReachable.
          eapply reach_in_updated_heap with (m2 := m) (Φ := inverse Φ) (h2 := h); destruct Φ; eauto 2.
        * _apply heap_lookup_update_eq2 in *.
          super_destruct'; subst.
          rewrite_inj.
          eapply HighHeapLevel; eauto 2.
      + assert (l2 <> loc2).
        {
          intro; subst.
          assert (Some loc2 <> left Φ loc1) by eauto 2 using bijection_is_injective_left.
          congruence.
        }
        rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
        rewrite_inj.
        splits; eauto 4.
        destruct_high.
        * eapply HighReachable.
          eapply reach_in_updated_heap with (m2 := m) (Φ := inverse Φ) (h2 := h); destruct Φ; eauto 2.
        * rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
          rewrite_inj.
          eapply HighHeapLevel.
          { rewrite -> heap_lookup_update_neq by solve[eauto 2].
            eauto. }
          { eauto 2. }
  Qed.

  
  Lemma low_gc_preserves_high:
    forall c c' ℓ_adv pc pc' m m' h h' t t' Σ Σ' loc,
      gc_occurred c c' pc pc' m m' h h' t t' Σ Σ' ->
      pc ⊑ ℓ_adv ->
      high ℓ_adv m h loc ->
      high ℓ_adv m' h' loc.
  Proof.
    intros.
    unfold gc_occurred in *; super_destruct'; subst.
    destruct_high.
    - eapply HighReachable.
      eapply reach_supset_if; eauto 2.
    - destruct_disjoint_heap_lookup.
      + eauto 2.
      + assert (pc' = ℓ) by eauto 2.
        subst.
        contradiction.
  Qed.
  Hint Resolve low_gc_preserves_high.

   Lemma low_gc_preserves_high2:
    forall c c' ℓ_adv pc pc' m m' h h' t t' Σ Σ' loc,
      gc_occurred c c' pc pc' m m' h h' t t' Σ Σ' ->
      pc ⊑ ℓ_adv ->
      high ℓ_adv m' h' loc ->
      high ℓ_adv m h loc.
  Proof.
    intros.
    unfold gc_occurred in *; super_destruct'; subst.
    destruct_high; eauto 3.
  Qed.
  Hint Resolve low_gc_preserves_high2.

  Lemma low_gc_trans_preserves_high:
    forall n c c' ℓ_adv pc pc' m m' h h' t t' Σ Σ' loc,
      gc_trans Σ Σ' ⟨c, pc, m, h, t⟩ ⟨c', pc', m', h', t'⟩ n ->
      pc ⊑ ℓ_adv ->
      high ℓ_adv m h loc ->
      high ℓ_adv m' h' loc.
  Proof.
    intros.
    dependent induction H; eauto 2.
    assert (pc = pc'0).
    {
      unfold gc_occurred in *; super_destruct'; congruence.
    }
    subst.
    eauto 3.
  Qed.
  Hint Resolve low_gc_trans_preserves_high.

  Lemma low_gc_trans_preserves_high2:
    forall Σ Σ' c c' pc pc' m m' h h' t t' n ℓ_adv loc,
      gc_trans Σ Σ' ⟨c, pc, m, h, t⟩ ⟨c', pc', m', h', t'⟩ n ->
      pc ⊑ ℓ_adv ->
      high ℓ_adv m' h' loc ->
      high ℓ_adv m h loc.
  Proof.
    intros.
    dependent induction H; eauto 2.
    assert (pc = pc'0).
    {
      unfold gc_occurred in *; super_destruct'; congruence.
    }
    subst.
    eauto 3.
  Qed.
  Hint Resolve low_gc_trans_preserves_high2.

  Lemma taint_eq_gc_noninterference:
    forall ℓ Φ Γ Σ1 Σ1' Σ2 c c' d m m' h h' s w pc pc' t t' g pc_end h1 h2 h3 H1 H2 H3 δ,
      taint_eq ℓ Φ Γ Σ1 Σ2 c d m h s w ->
      wf_taint_bijection ℓ Φ m h ->
      wf_taint_bijection ℓ (inverse Φ) s w ->
      ~ pc ⊑ ℓ ->
      wellformed_aux Γ Σ1 ⟨c, pc, m, h, t⟩ pc_end ->
      wellformed_aux Γ Σ2 ⟨d, pc, s, w, g⟩ pc_end ->
      @gc_occurred_no_ex c c' pc pc' m m' h h' t t' Σ1 Σ1' h1 h2 h3 δ H1 H2 H3 ->
      exists w1 w2 w3 w' g' H4 H5 H6 Ψ,
        @gc_occurred_no_ex d d pc pc' s s w w' g g' Σ2 Σ2 w1 w2 w3 δ H4 H5 H6 /\
        taint_eq ℓ Ψ Γ Σ1 Σ2 c d m' h' s w' /\
        wf_taint_bijection ℓ Ψ m' h' /\
        wf_taint_bijection ℓ (inverse Ψ) s w'.
  Proof.
    intros.
    unfold gc_occurred_no_ex in *; super_destruct'; subst.
    rename h2 into h_pc.
    rename h1 into h_gc.
    rename h3 into h_not_pc.
    assert (loc -> forall ℓ : T, {ℓ = pc'} + {ℓ <> pc'}) as H'.
    {
      intros.
      eapply T_dec; eauto 2.
    }
    remember_simple (filter_heap (fun _ ℓ => ℓ = pc') H' w).
    clear H'.
    super_destruct'; subst.
    rename h' into w_pc_gc.
    assert ((forall loc0 : loc,
                {(exists loc' ℓ μ,
                     left Φ loc' = Some loc0 /\ heap_lookup loc' h_pc = Some (ℓ, μ))} +
                {~
                   (exists loc' ℓ μ,
                       left Φ loc' = Some loc0 /\ heap_lookup loc' h_pc = Some (ℓ, μ))}))
      as H'.
    {
      intros.
      destruct (right Φ loc0) eqn:H_loc0.
      - assert (left Φ l = Some loc0) by (destruct Φ; eauto 2).
        destruct (heap_lookup l h_pc) eqn:H_l.
        + destruct p.
          left; eauto.
        + right.
          intro.
          super_destruct; subst.
          assert (right Φ loc0 = Some loc') by (destruct Φ; eauto 2).
          congruence.
      - right.
        intro.
        super_destruct; subst.
        assert (right Φ loc0 = Some loc') by (destruct Φ; eauto 2).
        congruence.        
    }            
    remember_simple (partition_heap (fun loc =>
                                       exists loc' ℓ μ, left Φ loc' = Some loc /\
                                                   heap_lookup loc' h_pc = Some (ℓ, μ))
                                    H' w_pc_gc).
    super_destruct; subst.
    rename x0 into w_pc.
    rename x1 into w_gc.

    assert (forall loc1 loc2 ℓ μ,
               left Φ loc1 = Some loc2 ->
               heap_lookup loc1 h_gc = Some (ℓ, μ) ->
               exists ν, heap_lookup loc2 w_gc = Some (ℓ, ν)).
    {
      intros.
      assert (pc' = ℓ0) by eauto 2.
      subst.

      assert (heap_lookup loc1 ([[h_pc ⊎ h_not_pc, H2] ⊎ h_gc, H1]) = Some (ℓ0, μ)).
      {
        rewrite -> disjoint_union_sym; eauto 2.
      }
      assert (exists ν, heap_lookup loc2 w = Some (ℓ0, ν)).
      {
        invert_taint_eq.
        match goal with
          [H: context[taint_eq_heap_domain_eq] |- _] =>
          solve[eapply H; eauto]
        end.

      }
      super_destruct'; subst.
      assert (heap_lookup loc2 w_pc_gc = Some (ℓ0, ν)) by eauto 2.
      remember_simple (H23 _ _ _ H30).
      destruct H31; try eauto 2.
      remember_simple (H24 _ _ _ H31).
      super_destruct; subst.
      assert (loc' = loc1).
      {
        assert (right Φ loc2 = Some loc') by (destruct Φ; eauto 2).
        assert (right Φ loc2 = Some loc1) by (destruct Φ; eauto 2).
        congruence.
      }
      subst.
      assert (heap_lookup loc1 h_pc = None).
      {
        eapply H3; eauto.
      }
      congruence.
    }

    assert (forall loc1 loc2 ℓ μ,
               left Φ loc1 = Some loc2 ->
               heap_lookup loc1 h_pc = Some (ℓ, μ) ->
               exists ν, heap_lookup loc2 w_pc = Some (ℓ, ν)).
    {
      intros.
      assert (pc' = ℓ0) by eauto 2.
      subst.
      assert (heap_lookup loc1 ([[h_pc ⊎ h_not_pc, H2] ⊎ h_gc, H1]) = Some (ℓ0, μ))
        by eauto 3.
      assert (exists ν, heap_lookup loc2 w = Some (ℓ0, ν)).
      {
        invert_taint_eq.
        match goal with
          [H: context[taint_eq_heap_domain_eq] |- _] =>
          solve[eapply H; eauto]
        end.
      }
      super_destruct'; subst.
      assert (heap_lookup loc2 w_pc_gc = Some (ℓ0, ν)) by eauto 2.
      remember_simple (H23 _ _ _ H31).
      destruct H32; try eauto 2.
      remember_simple (H25 _ _ _ H32).
      match goal with
        [H: ~ (exists _ _ _, _ /\ _) |- _] =>
        contradict H
      end.
      exists loc1 ℓ0 μ.
      splits*.
    }

    exists w_gc w_pc.

    assert (forall l : level_proj1, {compose not (eq pc') l} + {~ compose not (eq pc') l})
      as H''.
    {
      intros; destruct (T_dec pc' l); subst; eauto 4.
    }
    remember_simple (levels_satisfy_exists (compose not (eq pc')) H'' w).
    clear H''.
    super_destruct; subst.
    rename h' into w_not_pc.
    
    exists w_not_pc.

    unfold compose in *.
    
    assert (disjoint w_pc w_not_pc).
    {
      unfolds.
      intros.
      splits; intros.
      - destruct (heap_lookup loc w_not_pc) eqn:H_loc; try reflexivity.
        destruct p.
        assert (heap_lookup loc w = Some (ℓ0, μ)) by eauto 3.
        assert (heap_lookup loc w = Some (l, l0)) by eauto 3.
        rewrite_inj.
        assert (pc' <> l) by eauto 2.
        remember_simple (H24 _ _ _ H32).
        super_destruct; subst.
        assert (pc' = ℓ0) by eauto 2.
        subst.
        assert (heap_lookup loc' ([[h_pc ⊎ h_not_pc, H2] ⊎ h_gc, H1]) = Some (ℓ0, μ)).
        {
          eauto 3.
        }
        assert (exists ν, heap_lookup loc w = Some (ℓ0, ν)).
        {
          invert_taint_eq.
          match goal with
            [H: context[taint_eq_heap_domain_eq] |- _] =>
            solve[eapply H; eauto]
          end.
        }
        super_destruct; subst.
        congruence.
    - destruct (heap_lookup loc w_pc) eqn:H_loc; try reflexivity.
      destruct p.
      assert (heap_lookup loc w = Some (ℓ0, μ)) by eauto 2.
      assert (heap_lookup loc w = Some (l, l0)) by eauto 3.
      rewrite_inj.
      assert (pc' <> l) by eauto 2.
      remember_simple (H24 _ _ _ H_loc).
      super_destruct; subst.
      assert (heap_lookup loc' ([[h_pc ⊎ h_not_pc, H2] ⊎ h_gc, H1]) = Some (ℓ0, μ))
        by eauto 3.
      assert (high ℓ m' ([[h_pc ⊎ h_not_pc, H2] ⊎ h_gc, H1]) loc').
      {
        eapply H0; eauto 2.
      }
      assert (exists ν, heap_lookup loc w = Some (ℓ0, ν)).
      {
        invert_taint_eq.
        match goal with
          [H: context[taint_eq_heap_domain_eq] |- _] =>
          solve[eapply H; eauto 3]
        end.
      }
      super_destruct; subst.
      assert (pc' = ℓ0) by eauto 2.
      congruence.
    }
    exists ([w_pc ⊎ w_not_pc, H32]).
    exists (g + δ).

    assert (disjoint w_not_pc w_gc).
    {
      unfolds.
      intros.
      splits; intros.
      - destruct (heap_lookup loc w_gc) eqn:H_loc; try reflexivity.
        destruct p.
        assert (heap_lookup loc w_pc_gc = Some (l, l0)) by eauto 2.
        assert (l = pc') by eauto 2.
        subst.
        assert (heap_lookup loc w = Some (ℓ0, μ)) by eauto 3.
        assert (heap_lookup loc w = Some (pc', l0)) by eauto 3.
        rewrite_inj.
        assert (pc' <> pc') by eauto 2.
        congruence.
      - destruct (heap_lookup loc w_not_pc) eqn:H_loc; try reflexivity.
        destruct p.
        assert (heap_lookup loc w = Some (ℓ0, μ)) by eauto 3.
        assert (heap_lookup loc w = Some (l, l0)) by eauto 3.
        rewrite_inj.
        assert (pc' <> l) by eauto 2.
        assert (l = pc') by eauto.
        subst.
        congruence.
    }
    assert (disjoint ([w_pc ⊎ w_not_pc, H32]) w_gc).
    {
      eapply disjoint_sym.
      eauto 4.
    }
    exists H34.
    exists H32.
    exists x2.

    remember_simple (remove_gc'd_locations w_gc Φ).
    super_destruct; subst.
    rename ψ into Ψ.
    exists Ψ.

    assert (w = [[w_pc ⊎ w_not_pc, H32] ⊎ w_gc, H34]).
    {
      eapply heap_extensionality.
      intros.
      destruct (heap_lookup loc ([[w_pc ⊎ w_not_pc, H32] ⊎ w_gc, H34])) eqn:H_loc.
      - destruct p.
        destruct_disjoint_heap_lookup.
        + destruct_disjoint_heap_lookup; eauto 3.
        + eauto 3.
      - destruct (heap_lookup loc w) eqn:Hloc'; try reflexivity.
        destruct p.
        assert (heap_lookup loc w_pc = None).
        {
          destruct (heap_lookup loc w_pc) eqn:H_loc''; try reflexivity.
          destruct p.
          assert (heap_lookup loc ([[w_pc ⊎ w_not_pc, H32] ⊎ w_gc, H34]) = Some (l1, l2)) by eauto 3.
          congruence.
        }
        assert (heap_lookup loc w_gc = None).
        {
          destruct (heap_lookup loc w_gc) eqn:H_loc''; try reflexivity.
          destruct p.
          assert (heap_lookup loc ([[w_pc ⊎ w_not_pc, H32] ⊎ w_gc, H34]) = Some (l1, l2)).
          {
            rewrite -> disjoint_union_sym; eauto 3.
          }
          congruence.
        }
        assert (heap_lookup loc w_not_pc = None).
        {
          destruct (heap_lookup loc w_not_pc) eqn:H_loc''; try reflexivity.
          destruct p.
          assert (heap_lookup loc ([[w_pc ⊎ w_not_pc, H32] ⊎ w_gc, H34]) = Some (l1, l2)).
          {
            eapply disjoint_union_heap_lookup.
            rewrite -> disjoint_union_sym; eauto 3.
          }
          congruence.
        }
        destruct (T_dec l pc').
        + subst.
          assert (heap_lookup loc w_pc_gc = Some (pc', l0)) by eauto 2.
          remember_simple (H23 _ _ _ H42).
          destruct H43; congruence.
        + assert (pc' <> l) by eauto 2.
          assert (heap_lookup loc w_not_pc = Some (l, l0)) by eauto 2.
          congruence.
    }
    subst.

    assert (levels_satisfy w_gc (eq pc')).
    {
      unfolds.
      intros.
      assert (heap_lookup loc w_pc_gc = Some (ℓ0, μ)) by eauto 2.
      symmetry; eauto 2.
    }

    assert (levels_satisfy w_pc (eq pc')).
    {
      unfolds.
      intros.
      assert (heap_lookup loc w_pc_gc = Some (ℓ0, μ)) by eauto 2.
      symmetry; eauto 2.
    }

    unfold compose in *.
    
    assert (forall loc loc' ℓ,
               left Φ loc = Some loc' ->
               (exists μ, heap_lookup loc h_gc = Some (ℓ, μ)) <->
               (exists ν, heap_lookup loc' w_gc = Some (ℓ, ν))).
    {
      intros.
      splits; intros.
      - super_destruct; subst.
        eauto 2.
      - super_destruct; subst.
        assert (pc' = ℓ0) by eauto 2.
        subst.
        remember_simple (H25 _ _ _ H42).
        assert (heap_lookup loc h_pc = None).
        {
          destruct (heap_lookup loc h_pc) eqn:H_loc.
          - destruct p.
            match goal with
              [H: ~ (exists _ _ _, _ /\ _) |- _] =>
              solve[contradict H; eauto]
            end.
          - reflexivity.
        }
        
        destruct (heap_lookup loc h_gc) eqn:H_loc.
        + destruct p as [ℓ' μ'].
          assert (ℓ0 = ℓ') by eauto 2.
          subst.
          eauto 2.
        + assert (heap_lookup loc' w_pc_gc = Some (ℓ0, ν)) by eauto 2.
          assert (heap_lookup loc' ([[w_pc ⊎ w_not_pc, H32] ⊎ w_gc, H34]) = Some (ℓ0, ν)) by eauto 2.
          assert (exists μ, heap_lookup loc ([[h_pc ⊎ h_not_pc, H2] ⊎ h_gc, H1]) = Some (ℓ0, μ)).
          {
            invert_taint_eq.
            match goal with
              [H: context[taint_eq_heap_domain_eq] |- _] =>
              solve[eapply H; eauto]
            end.
          }
          super_destruct'; subst.
          destruct_disjoint_heap_lookup; try congruence.
          destruct_disjoint_heap_lookup; try congruence.
          assert (ℓ0 <> ℓ0) by eauto 2.
          congruence.
    }

    assert (forall loc loc' ℓ,
               left Φ loc = Some loc' ->
               (exists μ, heap_lookup loc h_pc = Some (ℓ, μ)) <->
               (exists ν, heap_lookup loc' w_pc = Some (ℓ, ν))).
    {
      intros.
      splits; intros.
      - super_destruct'; subst.
        eauto 3.
      - super_destruct'; subst.
        remember_simple (H24 _ _ _ H43).
        super_destruct; subst.
        assert (loc = loc'0).
        {
          assert (right Φ loc' = Some loc'0) by (destruct Φ; eauto 2).
          assert (right Φ loc' = Some loc) by (destruct Φ; eauto 2).
          congruence.
        }
        subst.
        exists μ.
        assert (pc' = ℓ0) by eauto 2.
        subst.
        assert (exists ν, heap_lookup loc' w_pc = Some (ℓ0, ν)) by eauto 2.
        super_destruct; subst.
        assert (ℓ0 = ℓ1) by eauto 2.
        subst.
        congruence.
    }

    assert (forall loc ℓ μ,
               heap_lookup loc w_gc = Some (ℓ, μ) ->
               ~ reach s ([[w_pc ⊎ w_not_pc, H32] ⊎ w_gc, H34]) loc).
    {
      intros.
      invert_taint_eq.
      intro.
      assert (pc' = ℓ0) by eauto 2.
      subst.
      assert (high ℓ s ([[w_pc ⊎ w_not_pc, H32] ⊎ w_gc, H34]) loc) by eauto 2.
      assert (exists loc', left Φ loc' = Some loc).
      {
        assert (exists loc', left (inverse Φ) loc = Some loc').
        {
          eapply H4; eauto.
        }
        super_destruct; subst.
        destruct Φ; eauto.
      }
      super_destruct; subst.
      
      assert (reach m' ([[h_pc ⊎ h_not_pc, H2] ⊎ h_gc, H1]) loc').
      {
        eapply H45; eauto.
      }
      assert (exists ν, heap_lookup loc' h_gc = Some (ℓ0, ν)).
      {
        eapply H41; eauto.
      }
      super_destruct'; subst.
      assert (~ reach m' ([[h_pc ⊎ h_not_pc, H2] ⊎ h_gc, H1]) loc') by eauto 2.
      contradiction.
    }

    assert (([w_pc ⊎ w_gc, x2]) ⇝ (s, δ) w_pc).
    {
      eapply gc_axiom with (φ := Φ) (m1 := m'); eauto 2.
      - intros.
        splits; intros.
        + super_destruct'; subst.
          destruct_disjoint_heap_lookup.
          * assert (exists ν, heap_lookup loc2 w_pc = Some (ℓ0, ν)) by eauto 2.
            super_destruct; eauto.
          * assert (exists ν, heap_lookup loc2 w_gc = Some (ℓ0, ν)) by eauto 2.
            rewrite -> disjoint_union_sym.
            super_destruct; eauto.
        + super_destruct'; subst.
          destruct_disjoint_heap_lookup.
          * assert (exists ν, heap_lookup loc1 h_pc = Some (ℓ0, ν)).
            {
              eapply H42; eauto 2.
            }
            super_destruct; eauto.
          * assert (exists ν, heap_lookup loc1 h_gc = Some (ℓ0, ν)).
            {
              eapply H41; eauto 2.
            }
            rewrite -> disjoint_union_sym.
            super_destruct; eauto.
      - intros.
        assert (pc' = ℓ0).
        {
          destruct_disjoint_heap_lookup; eauto 2.
        }
        subst.
        assert (high ℓ m' ([[h_pc ⊎ h_not_pc, H2] ⊎ h_gc, H1]) loc).
        {
          destruct_disjoint_heap_lookup.
          - eapply HighHeapLevel with (ℓ := ℓ0) (μ := μ); eauto 2.
            do 2 eapply disjoint_union_heap_lookup.
            eauto 2.
          - eapply HighHeapLevel with (ℓ := ℓ0) (μ := μ); eauto 2.
            rewrite -> disjoint_union_sym.
            eauto 2.
        }
        eapply H0; eauto 2.
      - intros.
        assert (pc' = ℓ0).
        {
          destruct_disjoint_heap_lookup; eauto 2.
        }
        subst.
        assert (high ℓ s ([[w_pc ⊎ w_not_pc, H32] ⊎ w_gc, H34]) loc).
        {
          destruct_disjoint_heap_lookup.
          - eapply HighHeapLevel with (ℓ := ℓ0) (μ := μ); eauto 2.
            do 2 eapply disjoint_union_heap_lookup.
            eauto 2.
          - eapply HighHeapLevel with (ℓ := ℓ0) (μ := μ); eauto 2.
            rewrite -> disjoint_union_sym.
            eauto 2.
        }
        cut (exists loc', left (inverse Φ) loc = Some loc').
        {
          intros.
          super_destruct.
          destruct Φ; eauto. 
        }
        {
          eapply H4; eauto 2.
        }
    }
    
    assert (taint_eq ℓ Ψ Γ Σ1' Σ2 c' d m' ([h_pc ⊎ h_not_pc, H2]) s ([w_pc ⊎ w_not_pc, H32])).
    {
      unfold taint_eq in *; super_destruct.
      splits; eauto 2.
      - unfold taint_eq_mem in *.
        splits*.
        intros.
        assert (val_taint_eq Φ τ v1 v2).
        {
          eapply H45; eauto.
        }
        invert_val_taint_eq; eauto 3.
        assert (left Ψ loc = Some loc').
        {
          assert (heap_lookup loc' w_gc = None).
          {
            destruct (heap_lookup loc' w_gc) eqn:H_loc'; try reflexivity.
            destruct p.
            assert (~ reach s ([[w_pc ⊎ w_not_pc, H32] ⊎ w_gc, H34]) loc') by eauto 2.
            contradict H54; eauto.
          }
          assert (right Φ loc' = right Ψ loc') by eauto 2.
          assert (right Φ loc' = Some loc) by (destruct Φ; eauto 2).
          cut (right Ψ loc' = Some loc).
          {
            destruct Ψ; eauto 2.
          }
          { congruence. }
        }
        eauto 2.
      - unfolds.
        intros.
        assert (left Φ loc = Some loc') by eauto 3.
        splits; intros.
        + assert (reach m' ([[h_pc ⊎ h_not_pc, H2] ⊎ h_gc, H1]) loc) by eauto 2.
          eapply reach_supset_if.
          * eapply H46; eauto.
          * eauto.
        + assert (reach s ([[w_pc ⊎ w_not_pc, H32] ⊎ w_gc, H34]) loc') by eauto 2.
          eapply reach_supset_if.
          * eapply H46; eauto.
          * eauto.
      - unfolds.
        intros.
        assert (left Φ loc = Some loc') by eauto 2.
        assert (high ℓ m' ([[h_pc ⊎ h_not_pc, H2] ⊎ h_gc, H1]) loc) by eauto 2.
        assert (high ℓ s ([[w_pc ⊎ w_not_pc, H32] ⊎ w_gc, H34]) loc') by eauto 2.
        assert (heap_lookup loc ([[h_pc ⊎ h_not_pc, H2] ⊎ h_gc, H1]) = Some (ℓ1, μ1))
          by eauto 2.
        assert (heap_lookup loc' ([[w_pc ⊎ w_not_pc, H32] ⊎ w_gc, H34]) = Some (ℓ2, μ2))
          by eauto 2.
        remember_simple (H47 loc loc' _ _ _ _ _ H58 H59 H60 H61 H62 H56 H57).
        super_destruct; subst.
        splits*.
        + assert (exists length, length_of loc ([h_pc ⊎ h_not_pc, H2]) = Some length).
          {
            eapply length_of_lookup_correspondance; eauto 3.
          }
          super_destruct; subst.
          assert (length_of loc ([[h_pc ⊎ h_not_pc, H2] ⊎ h_gc, H1]) = Some length).
          {
            eapply disjoint_union_length_of; eauto 2.
          }
          assert (exists length', length_of loc' ([w_pc ⊎ w_not_pc, H32]) = Some length').
          {
            eapply length_of_lookup_correspondance; eauto 3.
          }
          super_destruct; subst.
          assert (length_of loc' ([[w_pc ⊎ w_not_pc, H32] ⊎ w_gc, H34]) = Some length').
          {
            eapply disjoint_union_length_of; eauto 2.
          }
          congruence.
        + intros.
          assert (reach m' ([[h_pc ⊎ h_not_pc, H2] ⊎ h_gc, H1]) loc) by eauto 2.
          assert (reach s ([[w_pc ⊎ w_not_pc, H32] ⊎ w_gc, H34]) loc') by eauto 2.
          assert (val_taint_eq Φ τ v1 v2) by eauto 2.
          invert_val_taint_eq; eauto 2.
          assert (left Ψ loc0 = Some loc'0).
          {
            assert (heap_lookup loc0 h_gc = None).
            {
              destruct (heap_lookup loc0 h_gc) eqn:H_loc0; try reflexivity.
              destruct p.
              assert (~ reach m' ([[h_pc ⊎ h_not_pc, H2] ⊎ h_gc, H1]) loc0) by eauto 2.
              contradict H72; eauto 2.
            }
            assert (heap_lookup loc'0 w_gc = None).
            {
              destruct (heap_lookup loc'0 w_gc) eqn:H_loc'0; try reflexivity.
              destruct p.
              assert (~ reach s ([[w_pc ⊎ w_not_pc, H32] ⊎ w_gc, H34]) loc'0) by eauto 2.
              contradict H74; eauto 2.
            }
            assert (right Φ loc'0 = right Ψ loc'0) by eauto 2.
            revert H51; intros.
            revert H58; intros.
            revert H73; intros.
            assert (left Φ loc0 = left Ψ loc0).
            {
              destruct (left Ψ loc0) eqn:H_loc0.
              - assert (left Φ loc0 = Some l) by eauto 2.
                rewrite_inj.
                assert (right Φ l = Some loc0) by (destruct Φ; eauto 2).
                congruence.
              - destruct (left Φ loc0) eqn:H_loc'; try reflexivity.
                injects.
                assert (right Φ loc'0 = Some loc0) by (destruct Φ; eauto 2).
                assert (right Ψ loc'0 = Some loc0) by congruence.
                assert (left Ψ loc0 = Some loc'0) by (destruct Ψ; eauto 2).
                congruence.
            }
            congruence.
          }
          eauto 2.
      - unfolds.
        intros.
        remember_simple (H48 l H51).
        repeat rewrite -> size_heap_distr in *.
        cut (size l h_gc = size l w_gc).
        {
          intros; omega.
        }
        {
          eapply implies_same_size with (φ := Φ).
          intros.
          super_destruct; subst.
          assert (high ℓ m' ([[h_pc ⊎ h_not_pc, H2] ⊎ h_gc, H1]) loc1).
          {
            eapply H0; eauto.
          }
          assert (exists ℓ μ, heap_lookup loc1 ([[h_pc ⊎ h_not_pc, H2] ⊎ h_gc, H1]) = Some (ℓ, μ)).
          {
            repeat invert_wf_aux.
            destruct_high; eauto 3.
          }
          assert (high ℓ s ([[w_pc ⊎ w_not_pc, H32] ⊎ w_gc, H34]) loc2).
          {
            eapply H4; eauto 2.
            destruct Φ; eauto.
          }
          assert (exists ℓ μ, heap_lookup loc2 ([[w_pc ⊎ w_not_pc, H32] ⊎ w_gc, H34]) = Some (ℓ, μ)).
          {
            repeat invert_wf_aux.
            destruct_high; eauto 3.
          }
          super_destruct; subst.
          assert (exists τ, Σ1' loc1 = Some τ).
          {
            repeat invert_wf_aux; eauto 2.
          }
          super_destruct; subst.
          assert (Σ2 loc2 = Some τ).
          {
            eapply H50; eauto.
          }
          remember_simple (H47 loc1 loc2 _ _ _ _ _ H53 H54 H56 H55 H57 H58 H59).
          super_destruct; subst.
          destruct (length_of loc2 w_gc) eqn:H_loc2.
          + assert (length_of loc2 ([[w_pc ⊎ w_not_pc, H32] ⊎ w_gc, H34]) = Some n).
            {
              rewrite -> disjoint_union_sym.
              eauto 2.
            }
            rewrite -> H60 in *.
            destruct (length_of loc1 h_gc) eqn:H_loc1.
            * cut (length_of loc1 ([[h_pc ⊎ h_not_pc, H2] ⊎ h_gc, H1]) = Some n0).
              {
                intros; congruence.
              }
              {
                rewrite -> disjoint_union_sym.
                eauto 2.
              }
            * assert (exists ℓ μ, heap_lookup loc2 w_gc = Some (ℓ, μ)).
              {
                eapply length_of_lookup_correspondance; eauto 2.
              }
              assert (heap_lookup loc1 h_gc = None).
              {
                destruct (heap_lookup loc1 h_gc) eqn:H_loc1'; try reflexivity.
                destruct p.
                assert (exists n, length_of loc1 h_gc = Some n).
                {
                  eapply length_of_lookup_correspondance; eauto 3.
                }
                super_destruct; congruence.
              }
              super_destruct; subst.
              assert (exists ν, heap_lookup loc1 h_gc = Some (ℓ1, ν)).
              {
                eapply H41; eauto.
              }
              super_destruct; congruence.
          + destruct (length_of loc1 h_gc) eqn:H_loc1; try reflexivity.
            assert (exists ℓ μ, heap_lookup loc1 h_gc = Some (ℓ, μ)).
            {
              eapply length_of_lookup_correspondance; eauto 2.
            }
            assert (heap_lookup loc2 w_gc = None).
            {
              destruct (heap_lookup loc2 w_gc) eqn:H_loc2'; try reflexivity.
              destruct p.
              assert (exists n, length_of loc2 w_gc = Some n).
              {
                eapply length_of_lookup_correspondance; eauto 3.
              }
              super_destruct; congruence.
            }
            super_destruct; subst.
            assert (exists ν, heap_lookup loc2 w_gc = Some (ℓ1, ν)).
            {
              eapply H41; eauto.
            }
            super_destruct; congruence.
          + intros.
            assert (exists ℓ μ, heap_lookup loc h_gc = Some (ℓ, μ)).
            {
              eapply length_of_lookup_correspondance; eauto 2.
            }
            super_destruct'; subst.
            assert (pc' = ℓ0) by eauto 2.
            subst.
            eapply H0; eauto 2.
            eapply HighHeapLevel with (μ := μ) (ℓ := ℓ0); eauto 2.
            rewrite -> disjoint_union_sym; eauto 2.
          + intros.
            assert (exists ℓ μ, heap_lookup loc w_gc = Some (ℓ, μ)).
            {
              eapply length_of_lookup_correspondance; eauto 2.
            }
            super_destruct'; subst.
            assert (pc' = ℓ0) by eauto 2.
            subst.

            cut (exists loc', left (inverse Φ) loc = Some loc').
            {
              intros.
              super_destruct.
              destruct Φ; eauto.
            }
            {
              eapply H4; eauto 2.
              eapply HighHeapLevel with (μ := μ) (ℓ := ℓ0); eauto 2.
              rewrite -> disjoint_union_sym; eauto 2.
            }
        }
      - unfolds.
        intros.
        assert (left Φ l1 = Some l2) by eauto 2.
        splits; intros.
        + super_destruct.
          assert (heap_lookup l1 ([[h_pc ⊎ h_not_pc, H2] ⊎ h_gc, H1]) = Some (ℓ0, μ))
            by eauto 2.
          assert (high ℓ m' ([[h_pc ⊎ h_not_pc, H2] ⊎ h_gc, H1]) l1) by eauto 2.
          assert ((exists ν, heap_lookup l2 ([[w_pc ⊎ w_not_pc, H32] ⊎ w_gc, H34]) = Some (ℓ0, ν)) /\ high ℓ s ([[w_pc ⊎ w_not_pc, H32] ⊎ w_gc, H34]) l2).
          {
            eapply H49; eauto.
          }
          super_destruct.
          splits.
          * destruct_disjoint_heap_lookup; eauto 2.
            assert (right Ψ l2 = None) by eauto 2.
            assert (right Ψ l2 = Some l1) by (destruct Ψ; eauto 2).
            congruence.
          * destruct_high.
            { eapply HighReachable.
              eapply reach_supset_if; eauto 2. }
            { rewrite_inj.
              destruct_disjoint_heap_lookup; eauto 2.
              assert (pc' = ℓ1) by eauto 2.
              subst.
              assert (exists μ, heap_lookup l1 h_gc = Some (ℓ1, μ)).
              {
                eapply H41; eauto 3.
              }
              super_destruct; subst.
              assert (exists ℓ μ, heap_lookup l1 ([h_pc ⊎ h_not_pc, H2]) = Some (ℓ, μ)).
              {
                repeat invert_wf_aux.
                inverts H54; eauto.
              }
              super_destruct; subst.
              assert (heap_lookup l1 h_gc = None).
              {
                eapply H1; eauto.
              }
              congruence.
            }
        + super_destruct.
          assert (heap_lookup l2 ([[w_pc ⊎ w_not_pc, H32] ⊎ w_gc, H34]) = Some (ℓ0, ν))
            by eauto 2.
          assert (high ℓ s ([[w_pc ⊎ w_not_pc, H32] ⊎ w_gc, H34]) l2) by eauto 2.
          assert ((exists ν, heap_lookup l1 ([[h_pc ⊎ h_not_pc, H2] ⊎ h_gc, H1]) = Some (ℓ0, ν)) /\ high ℓ m' ([[h_pc ⊎ h_not_pc, H2] ⊎ h_gc, H1]) l1).
          {
            eapply H49; eauto.
          }
          super_destruct.
          splits.
          * destruct_disjoint_heap_lookup; eauto 2.
            assert (exists μ, heap_lookup l2 w_gc = Some (ℓ0, μ)).
            {
              eapply H41; eauto 2.
            }
            super_destruct; subst.
            assert (right Ψ l2 = None) by eauto 2.
            assert (right Ψ l2 = Some l1) by (destruct Ψ; eauto 2).
            congruence.
          * destruct_high.
            { eapply HighReachable.
              eapply reach_supset_if; eauto 2. }
            { rewrite_inj.
              destruct_disjoint_heap_lookup; eauto 2.
              assert (pc' = ℓ1) by eauto 2.
              subst.
              assert (exists μ, heap_lookup l2 w_gc = Some (ℓ1, μ)).
              {
                eapply H41; eauto 3.
              }
              super_destruct; subst.
              
              assert (exists ℓ μ, heap_lookup l2 ([w_pc ⊎ w_not_pc, H32]) = Some (ℓ, μ)).
              {
                repeat invert_wf_aux.
                inverts H54; eauto.
              }
              super_destruct; subst.
              assert (heap_lookup l2 w_gc = None).
              {
                eapply H34; eauto 2.
              }
              congruence.
            }
      - unfolds.
        intros.
        assert (left Φ loc1 = Some loc2) by eauto 2.
        eauto.
    }
    splits; eauto 2.
    - unfold taint_eq in *; super_destruct'; subst; splits; eauto 2.
      + intro; subst.
        invert_taint_eq_cmd; eauto 2.
      + intro; subst.
        invert_taint_eq_cmd; eauto 2.
      + splits*.
    - unfolds.
      intros.
      splits; intros.
      + super_destruct'; subst.
        assert (left Φ loc = Some loc') by eauto 2.
        assert (high ℓ m' ([[h_pc ⊎ h_not_pc, H2] ⊎ h_gc, H1]) loc).
        {
          eapply H0; eauto 2.
        }
        destruct_high.
        * eapply HighReachable.
          eapply reach_supset_if; eauto 2.
        * destruct_disjoint_heap_lookup; eauto 2.
          assert (pc' = ℓ0) by eauto 2.
          subst.
          assert (exists ν, heap_lookup loc' w_gc = Some (ℓ0, ν)).
          {
            eapply H41; eauto.
          }
          super_destruct; subst.
          assert (right Ψ loc' = None) by eauto 2.
          assert (right Ψ loc' = Some loc) by (destruct Ψ; eauto 2).
          congruence.
      + assert (high ℓ m' ([[h_pc ⊎ h_not_pc, H2] ⊎ h_gc, H1]) loc) by eauto 2.
        assert (exists loc', left Φ loc = Some loc').
        {
          eapply H0; eauto 2.
        }
        super_destruct; subst.
        exists loc'.
        assert (heap_lookup loc h_gc = None).
        {
          destruct (heap_lookup loc h_gc) eqn:H_loc; try reflexivity.
          destruct p.
          assert (pc' = l) by eauto 2.
          subst.
          assert (exists ℓ μ, heap_lookup loc ([h_pc ⊎ h_not_pc, H2]) = Some (ℓ, μ)).
          {
            repeat invert_wf_aux.
            inverts H46; eauto 3.
            assert (dangling_pointer_free m' ([h_pc ⊎ h_not_pc, H2])).
            {
              eapply dangling_pointer_free_subset; eauto 2.
            }
            eauto 3.
          }
          super_destruct; subst.
          assert (heap_lookup loc h_gc = None).
          {
            eapply H1; eauto 2.
          }
          congruence.
        }
        assert (heap_lookup loc' w_gc = None).
        {
          destruct (heap_lookup loc' w_gc) eqn:H_loc; try reflexivity.
          destruct p.
          assert (exists ν, heap_lookup loc h_gc = Some (l, ν)).
          {
            eapply H41; eauto 2.
          }
          super_destruct; subst.
          congruence.
        }
        assert (right Φ loc' = right Ψ loc') by eauto 2.
        assert (left Φ loc = left Ψ loc).
        {
          destruct (left Ψ loc) eqn:H_loc.
          - assert (left Φ loc = Some l) by eauto 2.
            rewrite_inj.
            assert (right Φ l = Some loc) by (destruct Φ; eauto 2).
            congruence.
          - destruct (left Φ loc) eqn:H_loc'; try reflexivity.
            injects.
            assert (right Φ loc' = Some loc) by (destruct Φ; eauto 2).
            assert (right Ψ loc' = Some loc) by congruence.
            assert (left Ψ loc = Some loc') by (destruct Ψ; eauto 2).
            congruence.
        }
        congruence.
    - unfolds.
      intros.
      splits; intros.
      + super_destruct'; subst.
        assert (left (inverse Φ) loc = Some loc').
        {
          assert (left Φ loc' = Some loc).
          {
            assert (left Ψ loc' = Some loc) by (destruct Ψ; eauto 2).
            eauto 2.
          }
          destruct Φ; eauto 2.
        }
        assert (high ℓ s ([[w_pc ⊎ w_not_pc, H32] ⊎ w_gc, H34]) loc).
        {
          eapply H4; eauto 2. 
        }
        destruct_high.
        * eapply HighReachable.
          eapply reach_supset_if; eauto 2.
        * destruct_disjoint_heap_lookup; eauto 2.
          assert (pc' = ℓ0) by eauto 2.
          subst.
          assert (right Ψ loc = None) by eauto 2.
          repeat _rewrite -> left_inverse_is_right in *.
          congruence.
      + assert (high ℓ s ([[w_pc ⊎ w_not_pc, H32] ⊎ w_gc, H34]) loc) by eauto 2.
        assert (exists loc', left (inverse Φ) loc = Some loc').
        {
          eapply H4; eauto 3.
        }
        super_destruct; subst.
        exists loc'.
        assert (left Φ loc' = Some loc) by (destruct Φ; eauto 2).
        cut (left Ψ loc' = Some loc).
        {
          destruct Ψ; eauto 2.
        }
        {
         assert (heap_lookup loc w_gc = None).
         {
           destruct (heap_lookup loc w_gc) eqn:H_loc; try reflexivity.
           destruct p.
           assert (pc' = l) by eauto 2.
           subst.
           assert (exists ℓ μ, heap_lookup loc ([w_pc ⊎ w_not_pc, H32]) = Some (ℓ, μ)).
           {
             repeat invert_wf_aux.
             inverts H46; eauto 3.
             assert (dangling_pointer_free s ([w_pc ⊎ w_not_pc, H32])).
             {               
               eapply dangling_pointer_free_subset; eauto 2.
             }
             eauto 3.
           }
           super_destruct; subst.
           assert (heap_lookup loc w_gc = None).
           {
             eapply H34; eauto 2.
           }
           congruence.
        }
        assert (heap_lookup loc' h_gc = None).
        {
          destruct (heap_lookup loc' h_gc) eqn:H_loc; try reflexivity.
          destruct p.
          assert (exists ν, heap_lookup loc w_gc = Some (l, ν)).
          {
            eapply H41; eauto 2.
          }
          super_destruct; subst.
          congruence.
        }
        assert (right Φ loc = right Ψ loc) by eauto 2.
        assert (left Φ loc' = left Ψ loc').
        {
          destruct (left Ψ loc') eqn:H_loc'.
          - assert (left Φ loc' = Some l) by eauto 2.
            rewrite_inj.
            assert (right Φ l = Some loc') by (destruct Φ; eauto 2).
            congruence.
          - destruct (left Φ loc') eqn:H_loc''; try reflexivity.
            injects.
            assert (right Φ loc = Some loc') by (destruct Φ; eauto 2).
            assert (right Ψ loc = Some loc') by congruence.
            assert (left Ψ loc' = Some loc) by (destruct Ψ; eauto 2).
            congruence.
        }
        congruence.
        }
  Qed.
  
  Lemma offset_config_gives_taint_eq_event:
    forall c ℓ_adv Γ d pc_end c' pc pc' m m' h h' t t' Σ1 Σ2 Σ1' Φ δ s w ev,
      wellformed_aux Γ Σ1 ⟨c, pc, m, h, t⟩ pc_end ->
      wellformed_aux Γ Σ2 ⟨d, pc, s, w, t + δ⟩ pc_end ->
      wf_taint_bijection ℓ_adv Φ m h ->
      wf_taint_bijection ℓ_adv (inverse Φ) s w ->
      ~ pc ⊑ ℓ_adv ->
      ⟨c, pc, m, h, t⟩ ⇒ [ev, Γ, Σ1, Σ1'] ⟨c', pc', m', h', t'⟩ ->
      c ≲ [δ] d ->
      taint_eq ℓ_adv Φ Γ Σ1 Σ2 c d m h s w ->
      exists d' s' w' Σ2' Ψ ev',
        ⟨d, pc, s, w, t + δ⟩ ⇒ [ev', Γ, Σ2, Σ2'] ⟨d', pc', s', w', t' + δ⟩
        /\ taint_eq ℓ_adv Ψ Γ Σ1' Σ2' c' d' m' h' s' w'
        /\ c' ≲ [δ] d'
        /\ wf_taint_bijection ℓ_adv Ψ m' h'
        /\ wf_taint_bijection ℓ_adv (inverse Ψ) s' w'
        /\ taint_eq_events Γ Ψ ev ev'.
  Proof.
    intros c ℓ Γ.
    induction c; intros.
    - invert_lack_behind.
      invert_event_step.
      + invert_sem_step.
        exists Stop s w Σ2 Φ EmptyEvent.
        replace (S t + δ) with (S (t + δ)) by omega.
        splits*.
        unfold taint_eq in *; super_destruct.
        splits*.
      + assert (gc_occurred_no_ex Skip Skip pc' pc' m' m'
                                  ([[h1_pc ⊎ h1_not_pc, H5] ⊎ h2, H4])
                                  t (t + δ0) Σ1' Σ1' δ0 H4 H5 H7) as H'.
        {
          unfold gc_occurred_no_ex.
          splits; reflexivity || eauto 2.
          splits; eauto 2.
          erewrite -> disjoint_union_proof_irrelevance; eauto 2.
        }
        remember_simple (taint_eq_gc_noninterference H6 H1 H2 H3 H H0 H').
        clear H'.
        super_destruct'; subst.
        unfold gc_occurred_no_ex in *; super_destruct'; subst.
        exists Skip s ([w2 ⊎ w3, H10]) Σ2 Ψ EmptyEvent.
        splits*.
        * replace (t + δ0 + δ) with ((t + δ) + δ0) by omega.
          eapply EventGCStep.
          eapply step_gc; reflexivity || eauto 2.
    - invert_event_step; exfalso; eauto 2.
    - invert_lack_behind.
      invert_event_step.
      + invert_sem_step.
        repeat invert_wf_aux.
        repeat specialize_gen.
        invert_wt_cmd.
        invert_lifted.
        rewrite_inj.
        destruct ε as [ℓ' ι'].
        invert_taint_eq.
        remember_simple (eval_taint_eq_possibilistic H8 H10 H9 H0 H21).
        super_destruct'; subst.
        
        remember_simple (filter_bijection
                           (high ℓ (extend_memory i v0 m) h')
                           (high_dec ℓ (extend_memory i v0 m) h') Φ).
        super_destruct'; subst.
        rename ψ into Ψ.
        exists Stop (extend_memory i v2 s) w Σ2 Ψ.
        replace (S t + δ) with (S (t + δ)) by omega.
        assert (val_taint_eq Φ (SecType σ (ℓ0, ι)) v0 v2).
        {
          destruct_prod_join_flowsto.
          eapply val_taint_eq_mon.
          + eapply eval_taint_eq with (m1 := m) (m2 := s); eauto 2.
          + eauto 2.
        }
        assert (taint_eq_heap_domain_eq ℓ Ψ (m [i → v0]) (s [i → v2]) h' w).
        {
          eapply taint_eq_heap_domain_eq_extend_mem; eauto 2.
          - intros; subst.
            assert (exists loc, v0 = ValLoc loc) by eauto 2.
            super_destruct'; subst.
            eauto.
          - intros; subst; eauto 2.
          - intros; subst.
            assert (exists loc, v2 = ValLoc loc) by eauto 2.
            super_destruct'; subst.
            eauto.
          - intros; subst; eauto 2.
        }
        assert (taint_eq_reach Ψ (m [i → v0]) h' (s [i → v2]) w).
        {
          eapply taint_eq_reach_extend_mem; intros; subst; eauto 2.
        }
        exists (AssignEvent ℓ0 i v2).
        splits; eauto 3.
        * constructor.
          constructors; eauto 2.
        * unfold taint_eq in *; super_destruct.
          splits; eauto 3.
          {
            eapply taint_eq_heap_extend_mem; eauto 2.
            - intros; subst; eauto.
            - intros; subst; eauto.
            - intros; subst.
              assert (exists loc, v0 = ValLoc loc) by eauto 2.
              super_destruct'; subst.
              eauto.
            - intros; subst.
              assert (exists loc, v2 = ValLoc loc) by eauto 2.
              super_destruct'; subst.
              eauto.
          }
          {
            eapply taint_eq_stenv_extend_mem; eauto 2.
          }
        * eapply wf_taint_bijection_extend_mem1; eauto 2.
          intros; subst; eauto 2.
        * eapply wf_taint_bijection_extend_mem2; eauto 2.
          { intros; subst; eauto 2. }
          { intros; subst; eauto 2. }
          { intros; subst.
            assert (exists loc, v2 = ValLoc loc) by eauto 2.
            super_destruct'; subst; eauto. }
        * assert (val_taint_eq Ψ (SecType σ (ℓ0, ι)) v0 v2).
          {
            invert_val_taint_eq; eauto 3.
            assert (high ℓ (m [i → ValLoc loc]) h' loc).
            {
              eauto.
            }
            eauto.
          }
          constructors; eauto 2.
      + assert (gc_occurred_no_ex (i ::= e) (i ::= e) pc' pc' m' m'
                                  ([[h1_pc ⊎ h1_not_pc, H5] ⊎ h2, H4])
                                  t (t + δ0) Σ1' Σ1' δ0 H4 H5 H7) as H'.
        {
          unfold gc_occurred_no_ex.
          splits; reflexivity || eauto 2.
          splits; eauto 2.
          erewrite -> disjoint_union_proof_irrelevance; eauto 2.
        }
        remember_simple (taint_eq_gc_noninterference H6 H1 H2 H3 H H0 H').
        clear H'.
        super_destruct'; subst.
        unfold gc_occurred_no_ex in *; super_destruct'; subst.
        exists (i ::= e) s ([w2 ⊎ w3, H10]) Σ2 Ψ EmptyEvent.
        splits*.
        * replace (t + δ0 + δ) with ((t + δ) + δ0) by omega.
          eapply EventGCStep.
          eapply step_gc; reflexivity || eauto 2.
    - assert (H6' := H6).
      invert_taint_eq; invert_taint_eq_cmd.
      invert_lack_behind.
      invert_event_step.
      + invert_sem_step.
        * exists c2' s w Σ2 Φ EmptyEvent.
          splits*.
          { replace (S t + δ) with (S (t + δ)) by omega.
            assert (eval s e = Some (ValNum 0)).
            {
              repeat invert_wf_aux.
              repeat specialize_gen.
              invert_wt_cmd.
              remember_simple (eval_taint_eq_possibilistic H5 H17 H15 H8 H27).
              super_destruct'; subst.
              invert_val_taint_eq; eauto 2.
            }
            eauto. }
          { unfolds.
            splits*. }
        * exists c1' s w Σ2 Φ EmptyEvent.
          splits*.
          { replace (S t + δ) with (S (t + δ)) by omega.
            assert (eval s e = Some (ValNum n)).
            {
              repeat invert_wf_aux.
              repeat specialize_gen.
              invert_wt_cmd.
              remember_simple (eval_taint_eq_possibilistic H5 H17 H15 H8 H27).
              super_destruct'; subst.
              invert_val_taint_eq; eauto 2.
            }
            eauto. }
          { unfolds.
            splits*. }
      + assert (gc_occurred_no_ex (If e c1 c2) (If e c1 c2) pc' pc' m' m'
                                  ([[h1_pc ⊎ h1_not_pc, H5] ⊎ h2, H4])
                                  t (t + δ0) Σ1' Σ1' δ0 H4 H5 H7) as H'.
        {
          unfold gc_occurred_no_ex.
          splits; reflexivity || eauto 2.
          splits; eauto 2.
          erewrite -> disjoint_union_proof_irrelevance; eauto 2.
        }
        remember_simple (taint_eq_gc_noninterference H6 H1 H2 H3 H H0 H').
        clear H'.
        super_destruct'; subst.
        unfold gc_occurred_no_ex in *; super_destruct'; subst.
        exists (If e c1' c2') s ([w2 ⊎ w3, H17]) Σ2 Ψ EmptyEvent.
        splits*.
        * replace (t + δ0 + δ) with ((t + δ) + δ0) by omega.
          eapply EventGCStep.
          eapply step_gc; reflexivity || eauto 2.
    - assert (H6' := H6).
      invert_taint_eq; invert_taint_eq_cmd.
      invert_event_step.
      + invert_sem_step.
        * exists Stop s w Σ2 Φ EmptyEvent.
          splits*.
          { replace (S t + δ) with (S (t + δ)) by omega.
            assert (eval s e = Some (ValNum 0)).
            {
              repeat invert_wf_aux.
              repeat specialize_gen.
              invert_wt_cmd.
              remember_simple (eval_taint_eq_possibilistic H4 H18 H16 H8 H24).
              super_destruct'; subst.
              invert_val_taint_eq; eauto 2.
            }
            eauto. }
          { unfolds.
            splits*. }
        * exists (c'0 ;; While e c'0) s w Σ2 Φ EmptyEvent.
          invert_lack_behind.
          splits*.
          { replace (S t + δ) with (S (t + δ)) by omega.
            assert (eval s e = Some (ValNum n)).
            {
              repeat invert_wf_aux.
              repeat specialize_gen.
              invert_wt_cmd.
              remember_simple (eval_taint_eq_possibilistic H4 H18 H16 H8 H24).
              super_destruct'; subst.
              invert_val_taint_eq; eauto 2.
            }
            eauto. }
          { unfolds.
            splits*. }
      + assert (gc_occurred_no_ex (While e c) (While e c) pc' pc' m' m'
                                  ([[h1_pc ⊎ h1_not_pc, H7] ⊎ h2, H4])
                                  t (t + δ0) Σ1' Σ1' δ0 H4 H7 H14) as H'.
        {
          unfold gc_occurred_no_ex.
          splits; reflexivity || eauto 2.
          splits; eauto 2.
          erewrite -> disjoint_union_proof_irrelevance; eauto 2.
        }
        remember_simple (taint_eq_gc_noninterference H6 H1 H2 H3 H H0 H').
        clear H'.
        super_destruct'; subst.
        unfold gc_occurred_no_ex in *; super_destruct'; subst.
        exists (While e c'0) s ([w2 ⊎ w3, H18]) Σ2 Ψ EmptyEvent.
        splits*.
        * replace (t + δ0 + δ) with ((t + δ) + δ0) by omega.
          eapply EventGCStep.
          eapply step_gc; reflexivity || eauto 2.
    - assert (H6' := H6).
      invert_taint_eq; invert_taint_eq_cmd.
      invert_lack_behind.
      invert_event_step.
      + _apply wf_seq1 in *.
        super_destruct'; subst.
        assert (c1 <> Stop).
        {
          intro; subst.
          invert_event_step; exfalso; eauto 2.
        }
        assert (c1 <> TimeOut).
        {
          intro; subst.
          invert_event_step; exfalso; eauto 2.
        }
        assert (c1' <> Stop).
        {
          intro; subst.
          invert_lack_behind.
          invert_event_step; exfalso; eauto 2.
        }
        assert (c1' <> TimeOut).
        {
          intro; subst.
          invert_lack_behind.
          invert_event_step; exfalso; eauto 2.
        }
        assert (pc''0 = pc'').
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          eauto.
        }
        subst.
        assert (taint_eq ℓ Φ Γ Σ1 Σ2 c1 c1' m h s w).
        {
          unfolds.
          splits*.
        }
        remember_simple (IHc1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H H0 H1 H2 H3 H31 H19 H15).
        super_destruct'; subst.
        exists (d' ;; c2') s' w' Σ2' Ψ ev'.
        assert (d' <> Stop).
        {
          intro; subst.
          invert_lack_behind.
          eauto.
        }
        assert (d' <> TimeOut).
        {
          intro; subst.
          invert_lack_behind.
          eauto.
        }
        splits*.
        unfold taint_eq in *; super_destruct'; splits*.
      + _apply wf_seq1 in *.
        super_destruct'; subst.
        assert (c1 <> Stop).
        {
          intro; subst.
          invert_event_step; exfalso; eauto 2.
        }
        assert (c1 <> TimeOut).
        {
          intro; subst.
          invert_event_step; exfalso; eauto 2.
        }
        assert (c1' <> Stop).
        {
          intro; subst.
          invert_lack_behind.
          invert_event_step; exfalso; eauto 2.
        }
        assert (c1' <> TimeOut).
        {
          intro; subst.
          invert_lack_behind.
          invert_event_step; exfalso; eauto 2.
        }
        assert (pc''0 = pc'').
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          eauto.
        }
        subst.
        assert (taint_eq ℓ Φ Γ Σ1 Σ2 c1 c1' m h s w).
        {
          unfolds.
          splits*.
        }
        remember_simple (IHc1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H H0 H1 H2 H3 H31 H19 H15).
        super_destruct'; subst.
        exists c2' s' w' Σ2' Ψ ev'.
        invert_lack_behind.
        splits*.
        unfold taint_eq in *; super_destruct'; splits*.
      + assert (gc_occurred_no_ex (c1 ;; c2) (c1 ;; c2) pc' pc' m' m'
                                  ([[h1_pc ⊎ h1_not_pc, H5] ⊎ h2, H4])
                                  t (t + δ0) Σ1' Σ1' δ0 H4 H5 H7) as H'.
        {
          unfold gc_occurred_no_ex.
          splits; reflexivity || eauto 2.
          splits; eauto 2.
          erewrite -> disjoint_union_proof_irrelevance; eauto 2.
        }
        remember_simple (taint_eq_gc_noninterference H6 H1 H2 H3 H H0 H').
        clear H'.
        super_destruct'; subst.
        unfold gc_occurred_no_ex in *; super_destruct'; subst.
        exists (c1' ;; c2') s ([w2 ⊎ w3, H17]) Σ2 Ψ EmptyEvent.
        splits*.
        * replace (t + δ0 + δ) with ((t + δ) + δ0) by omega.
          eapply EventGCStep.
          eapply step_gc; reflexivity || eauto 2.
    - assert (H6' := H6).
      invert_taint_eq; invert_taint_eq_cmd.
      invert_lack_behind.
      invert_event_step.
      + invert_sem_step.
        assert (eval s e = Some (ValNum n)).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          invert_wt_cmd.
          remember_simple (eval_taint_eq_possibilistic H23 H17 H16 H8 H25).
          super_destruct'; subst.
          invert_val_taint_eq; eauto 2.
        }
        exists (c'0 ;; BackAt pc (n + (t + δ))) s w Σ2 Φ EmptyEvent.
        replace (S t + δ) with (S (t + δ)) by omega.
        splits*.
        * unfold taint_eq in *; super_destruct'; splits*.
        * constructor; eauto 2.
          constructor; omega.
      + assert (gc_occurred_no_ex (At l e c) (At l e c) pc' pc' m' m'
                                  ([[h1_pc ⊎ h1_not_pc, H5] ⊎ h2, H4])
                                  t (t + δ0) Σ1' Σ1' δ0 H4 H5 H7) as H'.
        {
          unfold gc_occurred_no_ex.
          splits; reflexivity || eauto 2.
          splits; eauto 2.
          erewrite -> disjoint_union_proof_irrelevance; eauto 2.
        }
        remember_simple (taint_eq_gc_noninterference H6 H1 H2 H3 H H0 H').
        clear H'.
        super_destruct'; subst.
        unfold gc_occurred_no_ex in *; super_destruct'; subst.
        exists (At l e c'0) s ([w2 ⊎ w3, H17]) Σ2 Ψ EmptyEvent.
        splits*.
        * replace (t + δ0 + δ) with ((t + δ) + δ0) by omega.
          eapply EventGCStep.
          eapply step_gc; reflexivity || eauto 2.
    - assert (H6' := H6).
      invert_taint_eq; invert_taint_eq_cmd.
      invert_lack_behind.
      invert_event_step.
      + invert_sem_step; try omega.
        exists (BackAt l (n + δ)) s w Σ2 Φ EmptyEvent.
        replace (S t + δ) with (S (t + δ)) by omega.
        splits*.
        constructor.
        constructor.
        * omega.
        * constructor; eauto 2.
          omega.
      + invert_sem_step; try omega.
        exists Stop s w Σ2 Φ (RestoreEvent pc' (t + δ)).
        replace (S t + δ) with (S (t + δ)) by omega.
        splits*.
        unfold taint_eq in *; super_destruct'; splits*.
      + invert_sem_step; try omega.
        exists TimeOut s w Σ2 Φ (RestoreEvent pc' (t + δ)).
        replace (S t + δ) with (S (t + δ)) by omega.
        splits*.
        * constructor.
          constructor; omega || eauto 2.
          constructor; omega.
        * unfold taint_eq in *; super_destruct'; splits*.
      + assert (gc_occurred_no_ex (BackAt l n) (BackAt l n) pc' pc' m' m'
                                  ([[h1_pc ⊎ h1_not_pc, H5] ⊎ h2, H4])
                                  t (t + δ0) Σ1' Σ1' δ0 H4 H5 H7) as H'.
        {
          unfold gc_occurred_no_ex.
          splits; reflexivity || eauto 2.
          splits; eauto 2.
          erewrite -> disjoint_union_proof_irrelevance; eauto 2.
        }
        remember_simple (taint_eq_gc_noninterference H6 H1 H2 H3 H H0 H').
        clear H'.
        super_destruct'; subst.
        unfold gc_occurred_no_ex in *; super_destruct'; subst.
        exists (BackAt l (n + δ)) s ([w2 ⊎ w3, H16]) Σ2 Ψ EmptyEvent.
        splits*.
        * replace (t + δ0 + δ) with ((t + δ) + δ0) by omega.
          eapply EventGCStep.
          eapply step_gc; reflexivity || eauto 2.
    - assert (H6' := H6).
      invert_taint_eq; invert_taint_eq_cmd.
      invert_lack_behind.
      invert_event_step.
      + invert_sem_step.
        assert (l1 = l2) by eauto 2.
        subst.
        assert (eval s e = Some (ValNum n)).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          invert_wt_cmd.
          remember_simple (eval_taint_eq_possibilistic H21 H17 H18 H8 H27).
          super_destruct'; subst.
          invert_val_taint_eq; eauto 2.
        }
        invert_wf_aux.
        do 2 specialize_gen.
        invert_wt_cmd.
        rewrite_inj.
        assert (exists u, eval s e0 = Some u /\ val_taint_eq Φ τ1 v u).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          invert_wt_cmd.
          destruct τ1 as [σ [ℓ' ι']].
          eapply eval_taint_eq_possibilistic; eauto 2.
        }
        super_destruct'; subst.
        assert (size l h = size l w).
        {
          eapply H11; eauto 2.
          intro.
          assert_wf_type.
          invert_wf_type.
          destruct_join_flowsto.
          eauto 4.
        }
        assert (size l w + n <= maxsize l w).
        {
          assert (size l w + n <= maxsize l h) by omega.
          erewrite -> constant_maxsize; eauto 2.
        }
        remember_simple (fresh_location w l n u H16).
        super_destruct'; subst.
        remember_simple (filter_bijection
                           (high ℓ (extend_memory i (ValLoc l2) m)
                                 (extend_heap v l2 l n h H4 H5))
                           (high_dec ℓ (extend_memory i (ValLoc l2) m)
                                     (extend_heap v l2 l n h H4 H5)) Φ).
        super_destruct'; subst.
        rename ψ into Ψ.
        assert (left Ψ l2 = None).
        {
          destruct (left Ψ l2) eqn:H_l1; try reflexivity.
          assert (left Φ l2 = Some l0).
          {
            eapply filtered_bijection_is_subset.
            - eapply high_dec.
            - eauto 2.
            - eauto 2.
          }
          assert (high ℓ m h l2).
          {
            eapply H1.
            eauto.
          }
          destruct_high.
          - assert (exists ℓ μ, heap_lookup l2 h = Some (ℓ, μ)).
            {
              repeat invert_wf_aux; eauto 2.
            }
            super_destruct'; congruence.
          - congruence.
        }
        assert (right Ψ loc = None).
        {
          destruct (right Ψ loc) eqn:H_loc; try reflexivity.
          assert (left Ψ l0 = Some loc) by (destruct Ψ; eauto 2).
          assert (left Φ l0 = Some loc).
          {
            eapply filtered_bijection_is_subset.
            - eapply high_dec.
            - eauto 2.
            - eauto 2.
          }
          assert (high ℓ m h l0).
          {
            eapply H1; eauto.
          }
          assert (high ℓ s w loc).
          {
            rewrite <- high_iff; eauto 2.
          }
          destruct_high.
          - assert (exists ℓ μ, heap_lookup loc w = Some (ℓ, μ)) by eauto 2.
            super_destruct; congruence.
          - congruence.
        }
        exists Stop (extend_memory i (ValLoc loc) s).
        exists (extend_heap u loc l n w H18 H16) (extend_stenv loc τ1 Σ2).
        exists (extend_bijection Ψ l2 loc H26 H31) (NewEvent ℓ_x i loc).
        assert (wf_taint_bijection ℓ (extend_bijection Ψ l2 loc H26 H31)
                                   (m [i → ValLoc l2]) (extend_heap v l2 l n h H4 H5)).
        {
          repeat invert_wf_aux.
          eapply wf_taint_bijection_extend_mem_and_heap1; intros; subst; eauto 2.
        }
        splits; eauto 2.
        * constructor.
          eapply event_sem_step_new; eauto 2.
          eapply step_new; eauto 2.
        * unfolds.
          splits; eauto 2.
          {
            destruct τ1 as [σ ε].
            repeat invert_wf_aux.
            eapply taint_eq_reach_extend_mem_and_heap; eauto 2.
            - intros; subst.
              assert (exists loc, v = ValLoc loc) by eauto 2.
              super_destruct'; subst.
              eauto.
            - intros; subst.
              assert (exists loc, u = ValLoc loc) by eauto 2.
              super_destruct'; subst.
              eauto.
            - intros; subst; eauto 2.
            - intros; subst; eauto 2.
          }
          {
            repeat invert_wf_aux.
            eapply taint_eq_heap_extend_mem_and_heap; intros; subst; eauto 3.
          }
          {
            unfolds.
            intros.
            destruct (T_dec l0 l); subst.
            - do 2 rewrite -> size_extend_heap_eq_level by solve[eauto 2].
              omega.
            - do 2 rewrite -> size_extend_heap_neq_level by solve[eauto 2].
              eauto.
          }
          {
            destruct τ1 as [σ ε].
            repeat invert_wf_aux.
            eapply taint_eq_heap_domain_eq_extend_mem_and_heap; eauto 2.
            - intros; subst.
              assert (exists loc, v = ValLoc loc) by eauto 2.
              super_destruct'; subst.
              eauto.
            - intros; subst.
              assert (exists loc, u = ValLoc loc) by eauto 2.
              super_destruct'; subst.
              eauto.
            - intros; subst; eauto 2.
            - intros; subst; eauto 2.
          }
          {
            unfolds.
            intros.
            destruct (decide (l2 = loc1)); subst.
            - _rewrite -> left_extend_bijection_eq in *.
              injects.
              do 2 rewrite -> extend_stenv_lookup_eq.
              splits*.
            - _rewrite -> left_extend_bijection_neq in * by solve[eauto 2].
              assert (loc <> loc2).
              {
                intro; subst.
                assert (right Ψ loc2 = Some loc1) by (destruct Ψ; eauto 2).
                congruence.
              }
              do 2 rewrite -> extend_stenv_lookup_neq by solve[eauto 2].
              eapply H13; eauto 2.
              eapply filtered_bijection_is_subset.
              + eapply high_dec.
              + eauto 2.
              + eauto 2.
          }
        * repeat invert_wf_aux.
          destruct τ1 as [σ [ℓ' ι']].
          eapply wf_taint_bijection_extend_mem_and_heap2 with (Φ := Φ) (v1 := v); intros; subst; eauto 2.
          {
            subst; eauto 2.
          }
          {
            subst; eauto 2.
          }
          { subst.
            assert (exists loc, v = ValLoc loc) by eauto 2.
            super_destruct'; subst; eauto. }
          { subst.
            assert (exists loc, u = ValLoc loc) by eauto 2.
            super_destruct'; subst; eauto. }
      + assert (gc_occurred_no_ex (NewArr i l e e0) (NewArr i l e e0) pc' pc' m' m'
                                  ([[h1_pc ⊎ h1_not_pc, H5] ⊎ h2, H4])
                                  t (t + δ0) Σ1' Σ1' δ0 H4 H5 H7) as H'.
        {
          unfold gc_occurred_no_ex.
          splits; reflexivity || eauto 2.
          splits; eauto 2.
          erewrite -> disjoint_union_proof_irrelevance; eauto 2.
        }
        remember_simple (taint_eq_gc_noninterference H6 H1 H2 H3 H H0 H').
        clear H'.
        super_destruct'; subst.
        unfold gc_occurred_no_ex in *; super_destruct'; subst.
        exists (NewArr i l e e0) s ([w2 ⊎ w3, H16]) Σ2 Ψ EmptyEvent.
        splits*.
        * replace (t + δ0 + δ) with ((t + δ) + δ0) by omega.
          eapply EventGCStep.
          eapply step_gc; reflexivity || eauto 2.    
    - assert (H6' := H6).
      invert_taint_eq; invert_taint_eq_cmd.
      invert_event_step.
      + invert_sem_step.
        rewrite_inj.
        assert (exists loc, left Φ l1 = Some loc /\ memory_lookup s i = Some (ValLoc loc)).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          invert_wt_cmd.
          invert_lifted.
          assert_wf_type.
          invert_wf_type.
          assert (eval m' (Var i) = Some (ValLoc l1)) by eauto 2.
          assert (expr_has_type Γ (Var i) (SecType (Array (SecType σ l2) ℓ1) (l_ref, ∘))) by eauto 2.
          remember_simple (eval_taint_eq_possibilistic H0 H17 H16 H8 H).
          super_destruct'; subst.
          invert_val_taint_eq.
          exists loc'.
          splits*.
        }
        assert (eval s e = Some (ValNum n0)).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          invert_wt_cmd.
          invert_lifted.
          destruct ε_idx as [ℓ_idx ι_idx].
          remember_simple (eval_taint_eq_possibilistic H14 H18 H17 H8 H31).
          super_destruct'; subst.
          invert_val_taint_eq.
          - eauto.
          - destruct ε_x as [ℓ_x'' ι_x''].
            assert (LH.flowsto (LH.join • ∘) ι_x'') by eauto 2.
            assert_wf_type.
            invert_wf_type.
            inverts H0.
        }
        super_destruct'; subst.
        invert_wf_aux.
        repeat specialize_gen.
        invert_wt_cmd.
        invert_lifted.
        assert (exists u, eval s e0 = Some u /\ val_taint_eq Φ (SecType σ ε) v0 u).
        {
          repeat invert_wf_aux.
          destruct ε as [ℓ' ι'].
          eauto 2 using eval_taint_eq_possibilistic.
        }
        super_destruct'; subst.
        remember_simple (filter_bijection
                           (high ℓ m' (update_heap l1 n0 v0 h))
                           (high_dec ℓ m' (update_heap l1 n0 v0 h)) Φ).
        super_destruct'; subst.
        rename ψ into Ψ.
        exists Stop s (update_heap loc n0 u w) Σ2 Ψ (SetEvent ℓ0 ℓ_x i n0 u).
        replace (S t + δ) with (S (t + δ)) by omega.
        assert (length_of loc w = Some length).
        {
          assert (high ℓ m' h l1).
          {
            eapply H1; eauto 2.
          }
          assert (exists ℓ μ, heap_lookup l1 h = Some (ℓ, μ)).
          {
            destruct_high; eauto.
          }
          assert (high ℓ s w loc).
          {
            rewrite <- high_iff; eauto.
          }
          assert (exists ℓ μ, heap_lookup loc w = Some (ℓ, μ)).
          {
            repeat invert_wf_aux.
            destruct_high; eauto.
          }
          super_destruct'; subst.
          assert (Σ1' l1 = Some (SecType σ l2)) by eauto 2.
          assert (Σ2 loc = Some (SecType σ l2)) by (invert_wf_aux; eauto 2).
          remember_simple (H10 l1 loc _ _ _ _ _ H4 H22 H33 H25 H38 H39 H40).
          super_destruct'; subst.
          congruence.
        }
        assert (wf_taint_bijection ℓ Ψ m' (update_heap l1 n0 v0 h)).
        {
          eapply taint_eq_update_bijection1; eauto 2.
          intros; subst; eauto 2.
        }
        assert (val_taint_eq Φ (SecType σ l2) v0 u).
        {
          destruct l2 as [ℓ' ι'].
          destruct ε as [ℓ'' ι''].
          destruct_prod_join_flowsto.
          eapply val_taint_eq_mon; eauto 2.
        }
        splits; eauto 2.
        * constructor.
          constructors; eauto 2.
        * unfolds.          
          splits; eauto 2.
          {
            eapply taint_eq_mem_update_heap; eauto 2.
          }
          {
            repeat invert_wf_aux.
            eapply taint_eq_reach_update_heap; eauto 2.
            - intros; subst.
              assert (exists loc, v0 = ValLoc loc) by eauto 2.
              super_destruct'; subst; eauto.
            - intros; subst.
              assert (exists loc, u = ValLoc loc) by eauto 2.
              super_destruct'; subst; eauto.
            - intros; subst; eauto 2.
            - intros; subst; eauto 2.
          }
          {
            repeat invert_wf_aux.
            eapply taint_eq_heap_update_heap; eauto 2.
            - intros; subst; eauto 2.
            - intros; subst; eauto 2.
          }
          {
            unfolds.
            intros.
            repeat rewrite -> size_update_heap; eauto 2.
          }
          {
            repeat invert_wf_aux.
            eapply taint_eq_heap_update_domain_eq_update_heap with (Φ := Φ) (Σ1 := Σ1') (Σ2 := Σ2); eauto 2.
            - intros; subst.
              assert (exists loc, v0 = ValLoc loc) by eauto 2.
              super_destruct'; subst; eauto.
            - intros; subst.
              assert (exists loc, u = ValLoc loc) by eauto 2.
              super_destruct'; subst; eauto.
            - intros; subst; eauto 2.
            - intros; subst; eauto 2.
          }
          {
            unfolds.
            intros.
            assert (left Φ loc1 = Some loc2).
            {
              eapply filtered_bijection_is_subset.
              - eapply high_dec.
              - eauto 2.
              - eauto 2.
            }
            eauto.
          }
        * repeat invert_wf_aux.
          eapply wf_taint_bijection_update_heap2 with (Φ := Φ); eauto 2.
          { intros; subst.
            assert (exists loc, v0 = ValLoc loc) by eauto 2.
            super_destruct'; subst; eauto. }
          { intros; subst.
            assert (exists loc, u = ValLoc loc) by eauto 2.
            super_destruct'; subst; eauto. }
          { intros; subst; eauto 2. }
          { intros; subst; eauto 2. }
        * assert (val_taint_eq Ψ (SecType σ l2) v0 u).
          {
            invert_val_taint_eq; eauto 3.
            assert (high ℓ m' (update_heap l1 n0 (ValLoc loc0) h) loc0) by eauto 3.
            eauto.
          }
          assert_wf_type.
          invert_wf_type.
          destruct l2 as [ℓ' ι'].
          rewrite_inj.
          constructors; eauto 2.
      + assert (gc_occurred_no_ex (SetArr i e e0) (SetArr i e e0) pc' pc' m' m'
                                  ([[h1_pc ⊎ h1_not_pc, H7] ⊎ h2, H4])
                                  t (t + δ0) Σ1' Σ1' δ0 H4 H7 H14) as H'.
        {
          unfold gc_occurred_no_ex.
          splits; reflexivity || eauto 2.
          splits; eauto 2.
          erewrite -> disjoint_union_proof_irrelevance; eauto 2.
        }
        remember_simple (taint_eq_gc_noninterference H6 H1 H2 H3 H H0 H').
        clear H'.
        super_destruct'; subst.
        unfold gc_occurred_no_ex in *; super_destruct'; subst.
        exists (SetArr i e e0) s ([w2 ⊎ w3, H17]) Σ2 Ψ EmptyEvent.
        splits*.
        * replace (t + δ0 + δ) with ((t + δ) + δ0) by omega.
          eapply EventGCStep.
          eapply step_gc; reflexivity || eauto 2.
    - assert (H6' := H6).
      invert_taint_eq; invert_taint_eq_cmd.
      invert_event_step.
      + invert_sem_step.
        invert_wf_aux.
        repeat specialize_gen.
        invert_wt_cmd.
        invert_lifted.
        rewrite_inj.
        assert (exists loc, memory_lookup s i0 = Some (ValLoc loc) /\ left Φ l1 = Some loc).
        {
          assert (exists v2, eval s (Var i0) = Some v2 /\ val_taint_eq Φ (SecType (Array (SecType σ ε) ℓ2) ε_y) (ValLoc l1) v2).
          {
            destruct ε_y as [ℓ_y ι_y].
            invert_wf_aux.
            eapply eval_taint_eq_possibilistic with (m1 := m) (m2 := s); eauto 3.
          }
          super_destruct'; subst.
          assert (wf_type bot (SecType (Array (SecType σ ε) ℓ2) ε_y)) by eauto 2.
          invert_wf_type.
          invert_val_taint_eq.
          exists loc'.
          splits*.
        }
        super_destruct'; subst.
        assert ((exists μ, heap_lookup loc w = Some (ℓ0, μ)) /\ high ℓ s w loc).
        {
          eapply H12; eauto.
        }
        super_destruct'; subst.
        assert (eval s e = Some (ValNum n0)).
        {
          assert (exists v2, eval s e = Some v2 /\ val_taint_eq Φ (SecType Int ε_idx) (ValNum n0) v2).
          {
            destruct ε_idx as [ℓ_idx ι_idx].
            repeat invert_wf_aux.
            eapply eval_taint_eq_possibilistic with (m1 := m) (m2 := s); eauto 2.
          }
          super_destruct'; subst.
          invert_val_taint_eq; eauto 2.
          destruct ε_y as [ℓ_y ι_y].
          assert (wf_type bot (SecType (Array (SecType σ ε) ℓ2) (ℓ_y, ι_y))) by eauto 2.
          invert_wf_type.
          destruct_prod_join_flowsto.
          match goal with
            [H: (_, •) ≼ (_, ∘) |- _] =>
            inverts H
          end.
        }
        assert (exists u, lookup μ0 n0 = Some u /\ val_taint_eq Φ (SecType σ ε) v0 u /\ length_of l1 h' = length_of loc w).
        {
          assert (high ℓ m h' l1).
          {
            eapply high_iff; eauto 2.
          }
          assert (Σ1' l1 = Some (SecType σ ε)) by eauto 2.
          assert (Σ2 loc = Some (SecType σ ε)) by (invert_wf_aux; eauto 2).
          remember_simple (H10 l1 loc _ _ _ _ _ H4 H21 H19 H36 H7 H23 H24).
          super_destruct'; subst.
          assert (exists u, lookup μ0 n0 = Some u) by firstorder 2.
          super_destruct'; subst.
          exists u.
          splits*.
        }
        super_destruct'; subst.
        remember_simple (filter_bijection
                           (high ℓ (extend_memory i v0 m) h')
                           (high_dec ℓ (extend_memory i v0 m) h') Φ).
        super_destruct'; subst.
        rename ψ into Ψ.
        exists Stop (extend_memory i u s) w Σ2 Ψ (GetEvent ℓ_x i i0 u).
        assert (length_of loc w = Some length) by congruence.
        assert (val_taint_eq Φ (SecType σ (ℓ_x, ι)) v0 u).
        {
          destruct_prod_join_flowsto.
          destruct ε.
          eapply val_taint_eq_mon; eauto 2.
        }
        assert (taint_eq_heap_domain_eq ℓ Ψ (m [i → v0]) (s [i → u]) h' w).
        {
          repeat invert_wf_aux.
          eapply taint_eq_heap_domain_eq_extend_mem; intros; subst; eauto 4.
          - subst.
            assert (exists loc, v0 = ValLoc loc) by eauto 3.
            super_destruct'; subst; eauto.
          - subst.
            eauto 4.
          - subst.
            assert (exists loc, u = ValLoc loc) by eauto 3.
            super_destruct'; subst; eauto.
          - subst; eauto 4.
        }
        assert (taint_eq_reach Ψ (m [i → v0]) h' (s [i → u]) w).
        {
          repeat invert_wf_aux.
          eapply taint_eq_reach_extend_mem; intros; subst; eauto 3.
        }
        splits; eauto 2.
        * replace (S t + δ) with (S (t + δ)) by omega.
          constructor.
          constructors; eauto 2.
        * unfolds.
          splits; eauto 2.
          {
            repeat invert_wf_aux.
            eapply taint_eq_heap_extend_mem; intros; subst; eauto 4.
            - subst; eauto 4.
            - subst; eauto 4.
            - subst.
              assert (exists loc, v0 = ValLoc loc) by eauto 3.
              super_destruct'; subst; eauto.
            - subst.
              assert (exists loc, u = ValLoc loc) by eauto 3.
              super_destruct'; subst; eauto.
          }
          {
            eapply taint_eq_stenv_extend_mem; eauto 2.
          }
        * eapply wf_taint_bijection_extend_mem1; eauto 2.
          intros; subst; eauto 3.
        * repeat invert_wf_aux; eauto 2.
          eapply wf_taint_bijection_extend_mem2; intros; subst; eauto 4.
          { subst; eauto 4. }
          { subst; eauto 4. }
          { subst.
            assert (exists loc, u = ValLoc loc) by eauto 3.
            super_destruct'; subst; eauto. }
        * assert (val_taint_eq Ψ (SecType σ (ℓ_x, ι)) v0 u).
          {
            invert_val_taint_eq; eauto 3.
            assert (high ℓ (m [i → ValLoc loc0]) h' loc0) by eauto.
            eauto 3.
          }
          constructors; eauto 3.
      + assert (gc_occurred_no_ex (GetArr i i0 e) (GetArr i i0 e) pc' pc' m' m'
                                  ([[h1_pc ⊎ h1_not_pc, H7] ⊎ h2, H4])
                                  t (t + δ0) Σ1' Σ1' δ0 H4 H7 H14) as H'.
        {
          unfold gc_occurred_no_ex.
          splits; reflexivity || eauto 2.
          splits; eauto 2.
          erewrite -> disjoint_union_proof_irrelevance; eauto 2.
        }
        remember_simple (taint_eq_gc_noninterference H6 H1 H2 H3 H H0 H').
        clear H'.
        super_destruct'; subst.
        unfold gc_occurred_no_ex in *; super_destruct'; subst.
        exists (GetArr i i0 e) s ([w2 ⊎ w3, H17]) Σ2 Ψ EmptyEvent.
        splits*.
        * replace (t + δ0 + δ) with ((t + δ) + δ0) by omega.
          eapply EventGCStep.
          eapply step_gc; reflexivity || eauto 2.
    - assert (H6' := H6).
      invert_taint_eq; invert_taint_eq_cmd.
      invert_event_step.
      + invert_sem_step.
        invert_wf_aux.
        repeat specialize_gen.
        invert_wt_cmd.
        rewrite_inj.
        remember_simple (
            filter_bijection
              (high ℓ (extend_memory i (ValNum t) m) h')
              (high_dec ℓ (extend_memory i (ValNum t) m) h') Φ).
        super_destruct'; subst.
        rename ψ into Ψ.
        exists Stop (extend_memory i (ValNum (t + δ)) s) w Σ2 Ψ (TimeEvent ℓ1 i (t + δ)).
        assert (taint_eq_heap_domain_eq ℓ Ψ
                                        (m [i → ValNum t])
                                        (s [i → ValNum (t + δ)])
                                        h' w).
        {
          repeat invert_wf_aux.
          eapply taint_eq_heap_domain_eq_extend_mem; eauto 2.
          - intros; discriminate.
          - intros; discriminate.
        }
        assert (taint_eq_reach Ψ
                               (m [i → ValNum t]) h'
                               (s [i → ValNum (t + δ)]) w).
        {
          repeat invert_wf_aux.
          eapply taint_eq_reach_extend_mem; eauto 2.
          - eauto 2.
          - intros; discriminate.
          - intros; discriminate.
        }
        
        splits; eauto 2.
        * replace (S t + δ) with (S (t + δ)) by omega.
          constructor; eauto.
        * unfolds.
          splits; eauto 3.
          {
            eapply taint_eq_heap_extend_mem; eauto 2.
            - intros; discriminate.
            - intros; discriminate.
          }
          {
            eapply taint_eq_stenv_extend_mem; eauto 2.
          }
        * eapply wf_taint_bijection_extend_mem1; eauto 2.
          intros; discriminate.
        * repeat invert_wf_aux.
          eapply wf_taint_bijection_extend_mem2; eauto 2.
          intros; discriminate.
      + assert (gc_occurred_no_ex (Time i) (Time i) pc' pc' m' m'
                                  ([[h1_pc ⊎ h1_not_pc, H7] ⊎ h2, H4])
                                  t (t + δ0) Σ1' Σ1' δ0 H4 H7 H14) as H'.
        {
          unfold gc_occurred_no_ex.
          splits; reflexivity || eauto 2.
          splits; eauto 2.
          erewrite -> disjoint_union_proof_irrelevance; eauto 2.
        }
        remember_simple (taint_eq_gc_noninterference H6 H1 H2 H3 H H0 H').
        clear H'.
        super_destruct'; subst.
        unfold gc_occurred_no_ex in *; super_destruct'; subst.
        exists (Time i) s ([w2 ⊎ w3, H17]) Σ2 Ψ EmptyEvent.
        splits*.
        * replace (t + δ0 + δ) with ((t + δ) + δ0) by omega.
          eapply EventGCStep.
          eapply step_gc; reflexivity || eauto 2.
    - invert_event_step; exfalso; eauto 2.
  Qed.
  
  Lemma offset_config_gives_taint_eq_bridge:
    forall n ℓ_adv Γ c d pc_end c' pc pc' m m' h h' t t' Σ1 Σ2 Σ1' Φ δ s w ev,
      wellformed_aux Γ Σ1 ⟨c, pc, m, h, t⟩ pc_end ->
      wellformed_aux Γ Σ2 ⟨d, pc, s, w, t + δ⟩ pc_end ->
      wf_taint_bijection ℓ_adv Φ m h ->
      wf_taint_bijection ℓ_adv (inverse Φ) s w ->
      ~ pc ⊑ ℓ_adv ->
      ~ contains_low_backat ℓ_adv c ->
      ⟨c, pc, m, h, t⟩ ↷ [ℓ_adv, Γ, Σ1, Σ1', ev, n] ⟨c', pc', m', h', t'⟩ ->
      c ≲ [δ] d ->
      taint_eq ℓ_adv Φ Γ Σ1 Σ2 c d m h s w ->
      exists d' s' w' Σ2' Ψ ev',
        ⟨d, pc, s, w, t + δ⟩ ↷ [ℓ_adv, Γ, Σ2, Σ2', ev', n] ⟨d', pc', s', w', t' + δ⟩
        /\ taint_eq ℓ_adv Ψ Γ Σ1' Σ2' c' d' m' h' s' w'
        /\ c' ≲ [δ] d'
        /\ wf_taint_bijection ℓ_adv Ψ m' h'
        /\ wf_taint_bijection ℓ_adv (inverse Ψ) s' w'
        /\ taint_eq_events Γ Ψ ev ev'.
  Proof.
    intros n ℓ_adv Γ.
    induction n; intros.
    - invert_bridge_step.
      + invert_low_event_step.
        remember_simple (offset_config_gives_taint_eq_event H H0 H1 H2 H3 H5 H6 H7).
        super_destruct'; subst.
        exists d' s' w' Σ2' Ψ ev'.
        splits*.
      + unfold is_stop_config, cmd_of in *; subst.
        invert_high_event_step.
        remember_simple (offset_config_gives_taint_eq_event H H0 H1 H2 H3 H5 H6 H7).
        super_destruct'; subst.
        exists d' s' w' Σ2' Ψ ev'.
        invert_lack_behind.
        splits; eauto 2.
        eapply bridge_stop_num.
        * splits*.
        * reflexivity.
    - invert_bridge_step.
      invert_high_event_step.
      destruct cfg2.
      remember_simple (offset_config_gives_taint_eq_event H H0 H1 H2 H3 H5 H6 H7).
      super_destruct'; subst.
      assert (wellformed_aux Γ Σ' ⟨c0, pc0, memory, heap, time⟩ pc_end) by eauto 2.
      assert (wellformed_aux Γ Σ2' ⟨d', pc0, s', w', time + δ⟩ pc_end) by eauto 2.
      assert (~ pc0 ⊑ ℓ_adv).
      {
        assert (c <> Stop).
        {
          intro; subst.
          invert_event_step; eauto.
        }
        assert (c <> TimeOut).
        {
          intro; subst.
          invert_event_step; eauto.
        }
        repeat invert_wf_aux.
        repeat specialize_gen.
        eapply high_pc_and_no_low_backat_implies_high_pc_event_step; eauto.
      }
      assert (~ contains_low_backat ℓ_adv c0).
      {
        eauto 2 using no_spurious_low_backats_event_step.
      }
      remember_simple (IHn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H17 H18 H14 H15 H20 H21 H19 H13 H12).
      super_destruct'; subst.
      exists d'0 s'0 w'0 Σ2'0 Ψ0 ev'0.
      splits*.
      constructors.
      + splits*.
      + unfold is_stop_config, cmd_of; intro; subst.
        invert_lack_behind.
        eauto 2.
      + unfold is_timeout_config, cmd_of; intro; subst.
        invert_lack_behind.
        eauto 2.
      + eauto.
  Qed.

  Lemma backat_free_implies_lack_behind_forall:
    forall c δ,
      ~ contains_backat c ->
      c ≲ [δ] c.
  Proof.
    intros.
    induction c; eauto 2.
    - assert (~ contains_backat c1) by eauto.
      assert (~ contains_backat c2) by eauto.
      eauto.
    - assert (~ contains_backat c) by eauto.
      eauto.
    - assert (~ contains_backat c1) by eauto.
      assert (~ contains_backat c2) by eauto.
      eauto.
    - assert (~ contains_backat c) by eauto.
      eauto.
    - exfalso; eauto.
  Qed.
  Hint Resolve backat_free_implies_lack_behind_forall.

  Lemma emulate_gc_or_inc_many:
    forall ℓ_adv Γ Σ1 Σ2 pc pc' m m' h h' t t' n s w Φ k δ pc_end l,
      gc_or_inc_many Γ Σ1 ⟨BackAt l k, pc, m, h, t⟩ ⟨BackAt l k, pc', m', h', t'⟩ n ->
      wellformed_aux Γ Σ1 ⟨BackAt l k, pc, m, h, t⟩ pc_end ->
      wellformed_aux Γ Σ2 ⟨BackAt l (k + δ), pc, s, w, t + δ⟩ pc_end ->
      wf_taint_bijection ℓ_adv Φ m h ->
      wf_taint_bijection ℓ_adv (inverse Φ) s w ->
      ~ pc ⊑ ℓ_adv ->
      taint_eq ℓ_adv Φ Γ Σ1 Σ2 (BackAt l k) (BackAt l (k + δ)) m h s w ->
      exists w' Ψ,
        gc_or_inc_many Γ Σ2
                       ⟨BackAt l (k + δ), pc, s, w, t + δ⟩
                       ⟨BackAt l (k + δ), pc, s, w', t' + δ⟩ n /\
        taint_eq ℓ_adv Ψ Γ Σ1 Σ2 (BackAt l k) (BackAt l (k + δ))
                 m' h' s w' /\
        wf_taint_bijection ℓ_adv Ψ m' h' /\
        wf_taint_bijection ℓ_adv (inverse Ψ) s w'.
  Proof.
    intros.
    revert Φ w H1 H2 H3 H5.
    dependent induction H; intros.
    - exists w Φ.
      splits*.
    - inverts H.
      + invert_sem_step.
        assert (wellformed_aux Γ Σ ⟨ BackAt l k, pc, m, h, S t ⟩ pc_end)
          by eauto 2.
        assert (wellformed_aux Γ Σ2 ⟨BackAt l (k + δ), pc, s, w, S t + δ ⟩
                               pc_end) by eauto 2.
        remember_simple (IHgc_or_inc_many _ _ _ _ _ _ _ _ _ _ eq_refl eq_refl
                                          H H4 Φ w H7 H3 H5 H6).
        super_destruct'; subst.
        exists w' Ψ.
        splits*.
        * eapply GCOrIncTrans.
          { eapply Inc; eauto 2.
            constructor.
            omega. }
          { eauto 2. }
      + _apply gc_occurred_implies_gc_occurred_no_ex in *.
        super_destruct'; subst.
        remember_simple (taint_eq_gc_noninterference H6 H3 H5 H4 H1 H2 H16).
        super_destruct'; subst.
        assert (wellformed_aux Γ Σ ⟨ BackAt l k, pc, m, h'0, t2 ⟩ pc_end).
        {
          unfold gc_occurred_no_ex in *; super_destruct; subst.
          eauto 2.
        }
        assert (wellformed_aux Γ Σ2 ⟨ BackAt l (k + δ), pc, s, w', t2 + δ ⟩ pc_end).
        {
          unfold gc_occurred_no_ex in *; super_destruct; subst.
          replace (t + δ0 + δ) with (t + δ + δ0) by omega.
          eapply gc_preserves_wf with (δ := δ0); eauto 2.
        }
        remember_simple (IHgc_or_inc_many _ _ _ _ _ _ _ _ _ _ eq_refl eq_refl H17 H4 Ψ w' H18 H14 H15 H13).
        super_destruct'; subst.
        exists w'0 Ψ0.
        splits*.
        constructors.
        * eapply GC; eauto 2.
        * unfold gc_occurred_no_ex in *; super_destruct'; subst.
          replace (t + δ + δ0) with (t + δ0 + δ) by omega.
          eauto 2.
  Qed.

  Lemma emulate_gc_or_inc_many2:
    forall ℓ_adv Γ Σ1 Σ2 pc pc' m m' h h' t t' n s w Φ k δ pc_end l,
      gc_or_inc_many Γ Σ1 ⟨BackAt l (k + δ), pc, m, h, t + δ⟩ ⟨BackAt l (k + δ), pc', m', h', t'⟩ n ->
      wellformed_aux Γ Σ1 ⟨BackAt l (k + δ), pc, m, h, t + δ⟩ pc_end ->
      wellformed_aux Γ Σ2 ⟨BackAt l k, pc, s, w, t⟩ pc_end ->
      wf_taint_bijection ℓ_adv Φ m h ->
      wf_taint_bijection ℓ_adv (inverse Φ) s w ->
      ~ pc ⊑ ℓ_adv ->
      taint_eq ℓ_adv Φ Γ Σ1 Σ2 (BackAt l (k + δ)) (BackAt l k) m h s w ->
      exists w' Ψ,
        t' >= δ /\
        gc_or_inc_many Γ Σ2
                       ⟨BackAt l k, pc, s, w, t⟩
                       ⟨BackAt l k, pc, s, w', t' - δ⟩ n /\
        taint_eq ℓ_adv Ψ Γ Σ1 Σ2 (BackAt l (k + δ)) (BackAt l k)
                 m' h' s w' /\
        wf_taint_bijection ℓ_adv Ψ m' h' /\
        wf_taint_bijection ℓ_adv (inverse Ψ) s w'.
  Proof.
    intros.
    revert Φ w H1 H2 H3 H5.
    dependent induction H; intros.
    - exists w Φ.
      replace (t + δ - δ) with t by omega.
      splits*; try omega.
    - inverts H.
      + invert_sem_step.
        assert (wellformed_aux Γ Σ ⟨ BackAt l (k + δ), pc, m, h, S t + δ ⟩ pc_end)
          by eauto 2.
        assert (wellformed_aux Γ Σ2 ⟨BackAt l k, pc, s, w, S t⟩
                               pc_end) by eauto 2.
        replace (S (t + δ)) with (S t + δ) in * by omega.
        remember_simple (IHgc_or_inc_many _ _ _ _ _ _ _ _ _ _ _ eq_refl eq_refl H H4 Φ w H7 H3 H5 H6).
        super_destruct'; subst.
        exists w' Ψ.
        splits*.
        * eapply GCOrIncTrans.
          { eapply Inc; eauto 2.
            constructor.
            omega. }
          { eauto 2. }
      + _apply gc_occurred_implies_gc_occurred_no_ex in *.
        super_destruct'; subst.
        remember_simple (taint_eq_gc_noninterference H6 H3 H5 H4 H1 H2 H16).
        super_destruct'; subst.
        assert (wellformed_aux Γ Σ ⟨ BackAt l (k + δ), pc, m, h'0, t2⟩ pc_end).
        {
          unfold gc_occurred_no_ex in *; super_destruct; subst.
          eauto 2.
        }
        assert (wellformed_aux Γ Σ2 ⟨ BackAt l k, pc, s, w', t2 - δ⟩ pc_end).
        {
          unfold gc_occurred_no_ex in *; super_destruct; subst.
          replace (t + δ + δ0 - δ) with (t + δ0) by omega.
          eapply gc_preserves_wf with (δ := δ0); eauto 2.
        }
        unfold gc_occurred_no_ex in *; super_destruct; subst.
        replace (t + δ + δ0) with (t + δ0 + δ) in * by omega.
        replace (t + δ0 + δ - δ) with (t + δ0) in * by omega.
        remember_simple (IHgc_or_inc_many _ _ _ _ _ _ _ _ _ _ _ eq_refl eq_refl H17 H4 Ψ _ H18 H14 H15 H13).
        super_destruct'; subst.
        exists w' Ψ0.
        splits*.
        constructors.
        * eapply GC.
          {
            unfolds.
            splits; reflexivity || eauto 2.
            do 7 eexists.
            splits; reflexivity || eauto 2.
          }
        * unfold gc_occurred_no_ex in *; super_destruct'; subst.
          replace (t + δ + δ0) with (t + δ0 + δ) by omega.
          eauto 2.
  Qed.

  Lemma prepend_gc_or_inc:
    forall ℓ_adv n Γ Σ pc pc' l m m' h h' t k,
      gc_or_inc_many Γ Σ ⟨BackAt l k, pc, m, h, t ⟩ ⟨BackAt l k, pc', m', h', k⟩ n ->
      (⟨BackAt l k, pc, m, h, t⟩) ↷ [ℓ_adv, Γ, Σ, Σ, RestoreEvent l k, n] ⟨Stop, l, m', h', S k⟩.
  Proof.
    intros ℓ_adv n.
    induction n; intros.
    - inverts H.
      destruct (flowsto_dec l ℓ_adv).
      + eapply bridge_low_num.
        splits*.
      + eapply bridge_stop_num; eauto 2.
        splits; eauto 3.
        intro.
        invert_low_event.
        contradiction.
    - inverts H.
      inverts H1.
      + invert_sem_step.
        constructors.
        * splits*.
        * intro; discriminate.
        * intro; discriminate.
        * eauto 2.
      + unfold gc_occurred in *; super_destruct'; subst.
        constructors*.
  Qed.
  
  Lemma construct_at_bridge_step:
    forall ℓ_adv Γ k1 k2 k3 Σ1 Σ2 Σ3 l e k pc pc' c m1 m2 m3 m4 h1 h2 h3 h4 t1 t2 t3 ev pc_end,
      gc_trans Σ1 Σ2
               ⟨AT l FOR e DO c, pc, m1, h1, t1⟩
               ⟨AT l FOR e DO c, pc, m2, h2, t2⟩ k1 ->
      pc ⊑ ℓ_adv ->
      ⟨AT l FOR e DO c, pc, m2, h2, t2⟩
        ⇒ (Γ, Σ2, Σ2) ⟨c;; BackAt pc k, l, m2, h2, S t2⟩ ->
      ⟨c, l, m2, h2, S t2⟩
        ↷ [ℓ_adv, Γ, Σ2, Σ3, ev, k2] (⟨ Stop, pc', m3, h3, t3⟩) ->
      high_event ℓ_adv ev ->
      gc_or_inc_many Γ Σ3 ⟨BackAt pc k, pc', m3, h3, t3⟩
                     ⟨BackAt pc k, pc', m4, h4, k⟩ k3 ->
      wellformed_aux Γ Σ1 ⟨AT l FOR e DO c, pc, m1, h1, t1⟩ pc_end ->
      ⟨AT l FOR e DO c, pc, m1, h1, t1 ⟩
        ↷ [ℓ_adv, Γ, Σ1, Σ3, RestoreEvent pc k,
           S k1 + k2 + k3 + 1] ⟨Stop, pc, m4, h4, S k⟩.
  Proof.
    intros ℓ_adv Γ k1.
    induction k1.
    - intros k2.
      induction k2.
      + intros k3.
        induction k3; intros.
        * replace (1 + 0 + 0 + 2) with 3 by omega.
          inverts H.
          inverts H4.
          invert_step.
          invert_bridge_step.
          {
            invert_low_event_step.
            contradiction.
          }
          {
            invert_high_event_step.
            constructors.
            - splits.
              + constructor.
                eapply event_sem_step_at.
                constructor; eauto.
              + eauto 2.
            - intro; discriminate.
            - intro; discriminate.
            - constructors.
              + splits*.
              + intro; discriminate.
              + intro; discriminate.
              + constructor.
                splits; eauto 2.
                constructor; eauto 2.
          }
        * replace (1 + 0 + S k3 + 1) with (S k3 + 2) by omega.
          inverts H4.
          inverts H7.
          {
            invert_sem_step.
            inverts H.
            assert (H2' := H2).
            invert_bridge_step.
            - invert_low_event_step.
              contradiction.
            - invert_high_event_step.
              replace (S k3 + 2) with (S (k3 + 2)) by omega.
              invert_bridge_step; try (invert_low_event_step; contradiction).
              invert_high_event_step.
              invert_step.
              constructors.
              + splits.
                * constructor.
                  constructor.
                  constructor; eauto 2.
                * eauto 2.
              + intro; discriminate.
              + intro; discriminate.
              + replace (k3 + 2) with (S (k3 + 1)) by omega.
                constructors.
                * splits*.
                * intro; discriminate.
                * intro; discriminate.
                * replace (k3 + 1) with (S k3) by omega.
                  constructors.
                  { splits*. }
                  { intro; discriminate. }
                  { intro; discriminate. }
                  { eapply prepend_gc_or_inc; eauto 2. }
          }
          {
            unfold gc_occurred in *; super_destruct'; subst.
            inverts H.
            assert (H2' := H2).
            invert_bridge_step.
            - invert_low_event_step.
              contradiction.
            - invert_high_event_step.
              replace (S k3 + 2) with (S (k3 + 2)) by omega.
              invert_bridge_step; try (invert_low_event_step; contradiction).
              invert_high_event_step.
              invert_step.
              constructors.
              + splits.
                * constructor.
                  constructor.
                  constructor; eauto 2.
                * eauto 2.
              + intro; discriminate.
              + intro; discriminate.
              + replace (k3 + 2) with (S (k3 + 1)) by omega.
                constructors.
                * splits*.
                * intro; discriminate.
                * intro; discriminate.
                * replace (k3 + 1) with (S k3) by omega.
                  constructors.
                  { splits*. }
                  { intro; discriminate. }
                  { intro; discriminate. }
                  { eapply prepend_gc_or_inc; eauto 2. }
          }
      + intro k3.
        induction k3; intros.
        * replace (1 + S k2 + 0 + 1) with (S (k2 + 2)) by omega.
          inverts H.
          inverts H4.
          invert_bridge_step.
          invert_high_event_step.
          assert (wellformed_aux Γ Σ2 ⟨ c;; BackAt pc k, l, m2, h2, S t2⟩ pc_end) by (eapply preservation; eauto 2).
          invert_step.
          constructors.
          {
            splits.
            - constructor.
              constructor; eauto 2.
            - eauto 2.
          }
          {
            intro; discriminate.
          }
          {
            intro; discriminate.
          }
          {
            replace (k2 + 2) with (S (S k2 + 0)) by omega.
            eapply concat_bridge_step_seq.
            - eauto 2.
            - constructors; eauto.
            - eauto 2.
            - constructors; eauto 2.
              splits*.
          }
        * inverts H.
          replace (1 + S k2 + S k3 + 1) with (S (S (S k2) + (S k3))) by omega.
          assert (wellformed_aux Γ Σ2 ⟨ c;; BackAt pc k, l, m2, h2, S t2⟩ pc_end) by (eapply preservation; eauto 2).
          invert_step.
          constructors.
          {
            splits*.
          }
          {
            intro; discriminate.
          }
          {
            intro; discriminate.
          }
          {
            eapply concat_bridge_step_seq.
            - eauto 2.
            - eauto 2.
            - eauto 2.
            - eapply prepend_gc_or_inc; eauto 2.
          }
    - intros.
      inverts H.
      unfold gc_occurred in *; super_destruct'; subst.
      assert (wellformed_aux Γ Σ' ⟨ AT l FOR e DO c, pc'0, m', [h1_1_pc ⊎ h1_1_not_pc, H13], t1 + δ ⟩ pc_end) by eauto 2.
      replace (S (S k1) + k2 + k3 + 1) with ((S (S k1 + k2 + k3 + 1))) by omega.
      constructors.
      + splits*.
      + intro; discriminate.
      + intro; discriminate.
      + eauto 2.
  Qed.

  Lemma high_gc_preserves_wf_bijection:
    forall c c' pc pc' m m' h h' t t' Σ Σ' Γ φ ℓ_adv,
      gc_occurred c c' pc pc' m m' h h' t t' Σ Σ' ->
      ~ pc ⊑ ℓ_adv ->
      wf_bijection ℓ_adv φ Γ Σ m h ->
      wf_bijection ℓ_adv φ Γ Σ' m' h'.
  Proof.
    intros.
    unfolds.
    intros.
    splits; intros.
    - super_destruct'; subst.
      assert (low ℓ_adv Γ Σ m h loc) by eauto 2.
      unfold gc_occurred in *; super_destruct'; subst.
      destruct_low.
      + eapply LowReachable.
        eapply low_reach_subset_if; eauto 2.
      + destruct_disjoint_heap_lookup; eauto 2.
        assert (pc' = ℓ) by eauto 2.
        subst.
        contradiction.
    - unfold gc_occurred in *; super_destruct'; subst.
      eapply H1; eauto 2.
  Qed.
  Hint Resolve high_gc_preserves_wf_bijection.
  
  Lemma high_gc_or_inc_many_preserves_wf_bijection:
    forall Γ Σ n c c' pc pc' m m' h h' t t' φ ℓ_adv,
      gc_or_inc_many Γ Σ ⟨c, pc, m, h, t⟩ ⟨c', pc', m', h', t'⟩ n ->
      ~ pc ⊑ ℓ_adv ->
      wf_bijection ℓ_adv φ Γ Σ m h ->
      wf_bijection ℓ_adv φ Γ Σ m' h'.
  Proof.
    intros.
    dependent induction H; eauto 2.
    destruct cfg2.
    inverts H; eauto 3.
  Qed.
  Hint Resolve high_gc_or_inc_many_preserves_wf_bijection.

  Lemma high_pc_preserves_wf_bijection:
    forall c Γ ℓ_adv Σ Σ' c' pc pc' m m' h h' t t' φ pc_end,
      wellformed_aux Γ Σ ⟨c, pc, m, h, t⟩ pc_end ->
      ⟨c, pc, m, h, t⟩ ⇒ (Γ, Σ, Σ') ⟨c', pc', m', h', t'⟩ ->
      ~ pc ⊑ ℓ_adv ->
      wf_bijection ℓ_adv φ Γ Σ m h ->
      wf_bijection ℓ_adv φ Γ Σ' m' h'.
  Proof.
    Ltac high_pc_preserves_wf_bijection_handle_gc :=
      solve[eapply high_gc_preserves_wf_bijection; eauto 2;
            unfolds;
            (splits; reflexivity || eauto 2);
            (do 7 eexists);
            (splits; reflexivity || eauto 2);
            (erewrite -> disjoint_union_proof_irrelevance; eauto 2)].
    
    intros c Γ ℓ_adv.
    induction c; intros.
    - invert_step; eauto 2 || high_pc_preserves_wf_bijection_handle_gc.
    - invert_step; exfalso; eauto 2.
    - invert_step; try high_pc_preserves_wf_bijection_handle_gc.
      invert_wf_aux.
      repeat specialize_gen.
      invert_wt_cmd.
      invert_lifted.
      rewrite_inj.
      destruct l2 as [ℓ ι].
      assert (pc_end ⊑ ℓ).
      {
        destruct_prod_join_flowsto.
        eauto 2.
      }
      assert (~ ℓ ⊑ ℓ_adv) by eauto 2.
      unfolds.
      intros.
      splits; intros.
      + super_destruct'; subst.
        assert (low ℓ_adv Γ Σ' m h' loc) by eauto 2.
        eapply extend_mem_with_high_preserves_low; eauto 2.
      + assert (low ℓ_adv Γ Σ' m h' loc) by eauto 2.
        eauto 2.
    - invert_step; eauto 2 || high_pc_preserves_wf_bijection_handle_gc.
    - invert_step; eauto 2 || high_pc_preserves_wf_bijection_handle_gc.
    - invert_step; try high_pc_preserves_wf_bijection_handle_gc
                   || (_apply wf_seq1 in *; super_destruct'; eauto 2).
    - invert_step; eauto 2 || high_pc_preserves_wf_bijection_handle_gc.
    - invert_step; eauto 2 || high_pc_preserves_wf_bijection_handle_gc.
    - invert_step; try high_pc_preserves_wf_bijection_handle_gc.
      unfolds.
      intros.
      invert_wf_aux.
      repeat specialize_gen.
      invert_wt_cmd.
      rewrite_inj.
      destruct_join_flowsto.
      splits; intros.
      + super_destruct'; subst.
        eapply low_extend_memory_heap_with_high; eauto 2.
      + eapply H2; eauto 2.                      
        eapply low_in_extended_memory_heap_with_high_implies_low; eauto 2.
    - invert_step; try high_pc_preserves_wf_bijection_handle_gc.
      invert_wf_aux.
      repeat specialize_gen.
      invert_wt_cmd.
      invert_lifted.
      rewrite_inj.
      destruct_prod_join_flowsto.
      unfolds.
      intros.
      destruct l2 as [ℓ' ι'].
      assert_wf_type.
      invert_wf_type.
      destruct_prod_join_flowsto.
      splits; intros.
      + super_destruct'; subst.
        eapply low_update_with_high; eauto 4.
      + eapply H2; eauto 2.                      
        eapply low_in_updated_heap_high_implies_low; eauto 4.
    - invert_step; try high_pc_preserves_wf_bijection_handle_gc.
      invert_wf_aux.
      repeat specialize_gen.
      invert_wt_cmd.
      invert_lifted.
      rewrite_inj.
      assert (wf_type bot (SecType (Array (SecType σ ε) ℓ0) ε_y)) by eauto 2.
      invert_wf_type.
      destruct l2 as [ℓ' ι'].
      assert (pc_end ⊑ ℓ').
      {
        repeat destruct_prod_join_flowsto.
        eauto 3.
      }
      assert (~ ℓ' ⊑ ℓ_adv) by eauto 2.
      unfolds.
      intros.
      splits; intros.
      + super_destruct'; subst.
        assert (low ℓ_adv Γ Σ' m h' loc) by eauto 2.
        eapply extend_mem_with_high_preserves_low; eauto 2.
      + assert (low ℓ_adv Γ Σ' m h' loc) by eauto 2.
        eauto 2.
    - invert_step; try high_pc_preserves_wf_bijection_handle_gc.
      unfolds.
      intros.
      invert_wf_aux.
      repeat specialize_gen.
      invert_wt_cmd.
      rewrite_inj.
      splits; intros.
      + super_destruct'; subst.
        eapply low_extend_mem_with_num2; eauto 2.
      + eapply H2; eauto 2.
    - invert_step; exfalso; eauto 2.

      Unshelve.
      + eauto 2.
      + eauto 2.
      + eauto 2.
      + eauto 2.
      + eauto 2.
      + eauto 2.
      + eauto 2.
      + eauto 2.
      + eauto 2.
      + eauto 2.
      + eauto 2.
  Qed.

  Lemma high_pc_preserves_wf_bijection_event:
    forall c Γ ℓ_adv Σ Σ' c' pc pc' m m' h h' t t' φ pc_end ev,
      wellformed_aux Γ Σ ⟨c, pc, m, h, t⟩ pc_end ->
      ⟨c, pc, m, h, t⟩ ⇒ [ev, Γ, Σ, Σ'] ⟨c', pc', m', h', t'⟩ ->
      ~ pc ⊑ ℓ_adv ->
      wf_bijection ℓ_adv φ Γ Σ m h ->
      wf_bijection ℓ_adv φ Γ Σ' m' h'.
  Proof.
    intros.
    _apply event_step_implies_step in *.
    eapply high_pc_preserves_wf_bijection; eauto 2.
  Qed.
  
  Lemma high_pc_preserves_wf_bijection_bridge:
    forall c Γ ℓ_adv Σ Σ' c' pc pc' m m' h h' t t' φ pc_end ev n,
      wellformed_aux Γ Σ ⟨c, pc, m, h, t⟩ pc_end ->
      ⟨c, pc, m, h, t⟩ ↷ [ℓ_adv, Γ, Σ, Σ', ev, n] ⟨c', pc', m', h', t'⟩ ->
      ~ pc ⊑ ℓ_adv ->
      ~ contains_low_backat ℓ_adv c ->
      wf_bijection ℓ_adv φ Γ Σ m h ->
      wf_bijection ℓ_adv φ Γ Σ' m' h'.
  Proof.
    intros.
    dependent induction H0.
    - invert_low_event_step.
      eapply high_pc_preserves_wf_bijection_event; eauto 2.
    - invert_high_event_step.
      eapply high_pc_preserves_wf_bijection_event; eauto 2.
    - invert_high_event_step.
      destruct cfg2.
      eapply IHbridge_step_num; eauto 2.
      + invert_wf_aux.
        assert (c <> Stop).
        {
          intro; subst.
          invert_event_step; eauto 2.
        }
        assert (c <> TimeOut).
        {
          intro; subst.
          invert_event_step; eauto 2.
        }
        eapply high_pc_and_no_low_backat_implies_high_pc; eauto 2.
      + eapply no_spurious_low_backats_event_step; eauto 2.
      + eapply high_pc_preserves_wf_bijection_event; eauto 2.
  Qed.

  Lemma offset_config_gives_taint_eq_event2:
    forall c ℓ_adv Γ d pc_end c' pc pc' m m' h h' t t' Σ1 Σ2 Σ1' Φ δ s w ev,
      wellformed_aux Γ Σ1 ⟨c, pc, m, h, t + δ⟩ pc_end ->
      wellformed_aux Γ Σ2 ⟨d, pc, s, w, t⟩ pc_end ->
      wf_taint_bijection ℓ_adv Φ m h ->
      wf_taint_bijection ℓ_adv (inverse Φ) s w ->
      ~ pc ⊑ ℓ_adv ->
      ⟨c, pc, m, h, t + δ⟩ ⇒ [ev, Γ, Σ1, Σ1'] ⟨c', pc', m', h', t'⟩ ->
      d ≲ [δ] c ->
      taint_eq ℓ_adv Φ Γ Σ1 Σ2 c d m h s w ->
      exists d' s' w' Σ2' Ψ ev',
        t' >= δ
        /\ ⟨d, pc, s, w, t⟩ ⇒ [ev', Γ, Σ2, Σ2'] ⟨d', pc', s', w', t' - δ⟩
        /\ taint_eq ℓ_adv Ψ Γ Σ1' Σ2' c' d' m' h' s' w'
        /\ d' ≲ [δ] c'
        /\ wf_taint_bijection ℓ_adv Ψ m' h'
        /\ wf_taint_bijection ℓ_adv (inverse Ψ) s' w'
        /\ taint_eq_events Γ Ψ ev ev'.
  Proof.
    intros c ℓ Γ.
    induction c; intros.
    - invert_lack_behind.
      invert_event_step.
      + invert_sem_step.
        exists Stop s w Σ2 Φ EmptyEvent.
        replace (S (t + δ) - δ) with (S t) by omega.
        splits*; try omega.
        unfold taint_eq in *; super_destruct.
        splits*.
      + assert (gc_occurred_no_ex Skip Skip pc' pc' m' m'
                                  ([[h1_pc ⊎ h1_not_pc, H5] ⊎ h2, H4])
                                  (t + δ) ((t + δ) + δ0) Σ1' Σ1' δ0 H4 H5 H7) as H'.
        {
          unfold gc_occurred_no_ex.
          splits; reflexivity || eauto 2.
          splits; eauto 2.
          erewrite -> disjoint_union_proof_irrelevance; eauto 2.
        }
        remember_simple (taint_eq_gc_noninterference H6 H1 H2 H3 H H0 H').
        clear H'.
        super_destruct'; subst.
        unfold gc_occurred_no_ex in *; super_destruct'; subst.
        exists Skip s ([w2 ⊎ w3, H10]) Σ2 Ψ EmptyEvent.
        splits*; try omega.
        * replace (t + δ + δ0 - δ) with (t + δ0) by omega.
          eapply EventGCStep.
          eapply step_gc; reflexivity || eauto 2.
    - invert_event_step; exfalso; eauto 2.
    - invert_lack_behind.
      invert_event_step.
      + invert_sem_step.
        repeat invert_wf_aux.
        repeat specialize_gen.
        invert_wt_cmd.
        invert_lifted.
        rewrite_inj.
        destruct ε as [ℓ' ι'].
        invert_taint_eq.
        remember_simple (eval_taint_eq_possibilistic H8 H10 H9 H0 H21).
        super_destruct'; subst.
        
        remember_simple (filter_bijection
                           (high ℓ (extend_memory i v0 m) h')
                           (high_dec ℓ (extend_memory i v0 m) h') Φ).
        super_destruct'; subst.
        rename ψ into Ψ.
        exists Stop (extend_memory i v2 s) w Σ2 Ψ.
        replace (S (t + δ) - δ) with (S t) by omega.
        assert (val_taint_eq Φ (SecType σ (ℓ0, ι)) v0 v2).
        {
          destruct_prod_join_flowsto.
          eapply val_taint_eq_mon.
          + eapply eval_taint_eq with (m1 := m) (m2 := s); eauto 2.
          + eauto 2.
        }
        assert (taint_eq_heap_domain_eq ℓ Ψ (m [i → v0]) (s [i → v2]) h' w).
        {
          eapply taint_eq_heap_domain_eq_extend_mem; eauto 2.
          - intros; subst.
            assert (exists loc, v0 = ValLoc loc) by eauto 2.
            super_destruct'; subst.
            eauto.
          - intros; subst; eauto 2.
          - intros; subst.
            assert (exists loc, v2 = ValLoc loc) by eauto 2.
            super_destruct'; subst.
            eauto.
          - intros; subst; eauto 2.
        }
        assert (taint_eq_reach Ψ (m [i → v0]) h' (s [i → v2]) w).
        {
          eapply taint_eq_reach_extend_mem; intros; subst; eauto 2.
        }
        exists (AssignEvent ℓ0 i v2).
        splits; omega || eauto 3.
        * constructor.
          constructors; eauto 2.
        * unfold taint_eq in *; super_destruct.
          splits; eauto 3.
          {
            eapply taint_eq_heap_extend_mem; intros; subst; eauto 2.
            - subst; eauto 2.
            - subst; eauto 2.
            - subst.
              assert (exists loc, v0 = ValLoc loc) by eauto 2.
              super_destruct'; subst.
              eauto.
            - subst.
              assert (exists loc, v2 = ValLoc loc) by eauto 2.
              super_destruct'; subst.
              eauto.
          }
          {
            eapply taint_eq_stenv_extend_mem; eauto 2.
          }
        * eapply wf_taint_bijection_extend_mem1; eauto 2.
          intros; subst; eauto 2.
        * eapply wf_taint_bijection_extend_mem2; eauto 2.
          { intros; subst; eauto 2. }
          { intros; subst; eauto 2. }
          { intros; subst.
            assert (exists loc, v2 = ValLoc loc) by eauto 2.
            super_destruct'; subst; eauto. }
        * assert (val_taint_eq Ψ (SecType σ (ℓ0, ι)) v0 v2).
          {
            invert_val_taint_eq; eauto 3.
            assert (high ℓ (m [i → ValLoc loc]) h' loc).
            {
              eauto.
            }
            eauto.
          }
          constructors; eauto 2.
      + assert (gc_occurred_no_ex (i ::= e) (i ::= e) pc' pc' m' m'
                                  ([[h1_pc ⊎ h1_not_pc, H5] ⊎ h2, H4])
                                  (t + δ) (t + δ + δ0) Σ1' Σ1' δ0 H4 H5 H7) as H'.
        {
          unfold gc_occurred_no_ex.
          splits; reflexivity || eauto 2.
          splits; eauto 2.
          erewrite -> disjoint_union_proof_irrelevance; eauto 2.
        }
        remember_simple (taint_eq_gc_noninterference H6 H1 H2 H3 H H0 H').
        clear H'.
        super_destruct'; subst.
        unfold gc_occurred_no_ex in *; super_destruct'; subst.
        exists (i ::= e) s ([w2 ⊎ w3, H10]) Σ2 Ψ EmptyEvent.
        splits*; try omega.
        * replace (t + δ + δ0 - δ) with (t + δ0) by omega.
          eapply EventGCStep.
          eapply step_gc; reflexivity || eauto 2.
    - assert (H6' := H6).
      invert_taint_eq; invert_taint_eq_cmd.
      invert_lack_behind.
      invert_event_step.
      + invert_sem_step.
        * exists c2' s w Σ2 Φ EmptyEvent.
          splits*; try omega.
          { replace (S (t + δ) - δ) with (S t) by omega.
            assert (eval s e = Some (ValNum 0)).
            {
              repeat invert_wf_aux.
              repeat specialize_gen.
              invert_wt_cmd.
              remember_simple (eval_taint_eq_possibilistic H5 H17 H15 H8 H27).
              super_destruct'; subst.
              invert_val_taint_eq; eauto 2.
            }
            eauto. }
          { unfolds.
            splits*. }
        * exists c1' s w Σ2 Φ EmptyEvent.
          splits*; try omega.
          { replace (S (t + δ) - δ) with (S t) by omega.
            assert (eval s e = Some (ValNum n)).
            {
              repeat invert_wf_aux.
              repeat specialize_gen.
              invert_wt_cmd.
              remember_simple (eval_taint_eq_possibilistic H5 H17 H15 H8 H27).
              super_destruct'; subst.
              invert_val_taint_eq; eauto 2.
            }
            eauto. }
          { unfolds.
            splits*. }
      + assert (gc_occurred_no_ex (If e c1 c2) (If e c1 c2) pc' pc' m' m'
                                  ([[h1_pc ⊎ h1_not_pc, H5] ⊎ h2, H4])
                                  (t + δ) (t + δ + δ0) Σ1' Σ1' δ0 H4 H5 H7) as H'.
        {
          unfold gc_occurred_no_ex.
          splits; reflexivity || eauto 2.
          splits; eauto 2.
          erewrite -> disjoint_union_proof_irrelevance; eauto 2.
        }
        remember_simple (taint_eq_gc_noninterference H6 H1 H2 H3 H H0 H').
        clear H'.
        super_destruct'; subst.
        unfold gc_occurred_no_ex in *; super_destruct'; subst.
        exists (If e c1' c2') s ([w2 ⊎ w3, H17]) Σ2 Ψ EmptyEvent.
        splits*; try omega.
        * replace (t + δ + δ0 - δ) with (t + δ0) by omega.
          eapply EventGCStep.
          eapply step_gc; reflexivity || eauto 2.
    - assert (H6' := H6).
      invert_taint_eq; invert_taint_eq_cmd.
      invert_event_step.
      + invert_sem_step.
        * exists Stop s w Σ2 Φ EmptyEvent.
          splits*; try omega.
          { replace (S (t + δ) - δ) with (S t) by omega.
            assert (eval s e = Some (ValNum 0)).
            {
              repeat invert_wf_aux.
              repeat specialize_gen.
              invert_wt_cmd.
              remember_simple (eval_taint_eq_possibilistic H4 H18 H16 H8 H24).
              super_destruct'; subst.
              invert_val_taint_eq; eauto 2.
            }
            eauto. }
          { unfolds.
            splits*. }
        * exists (c'0 ;; While e c'0) s w Σ2 Φ EmptyEvent.
          invert_lack_behind.
          splits*; try omega.
          { replace (S (t + δ) - δ) with (S t) by omega.
            assert (eval s e = Some (ValNum n)).
            {
              repeat invert_wf_aux.
              repeat specialize_gen.
              invert_wt_cmd.
              remember_simple (eval_taint_eq_possibilistic H4 H18 H16 H8 H24).
              super_destruct'; subst.
              invert_val_taint_eq; eauto 2.
            }
            eauto. }
          { unfolds.
            splits*. }
      + assert (gc_occurred_no_ex (While e c) (While e c) pc' pc' m' m'
                                  ([[h1_pc ⊎ h1_not_pc, H7] ⊎ h2, H4])
                                  (t + δ) (t + δ + δ0) Σ1' Σ1' δ0 H4 H7 H14) as H'.
        {
          unfold gc_occurred_no_ex.
          splits; reflexivity || eauto 2.
          splits; eauto 2.
          erewrite -> disjoint_union_proof_irrelevance; eauto 2.
        }
        remember_simple (taint_eq_gc_noninterference H6 H1 H2 H3 H H0 H').
        clear H'.
        super_destruct'; subst.
        unfold gc_occurred_no_ex in *; super_destruct'; subst.
        exists (While e c'0) s ([w2 ⊎ w3, H18]) Σ2 Ψ EmptyEvent.
        splits*; try omega.
        * replace (t + δ + δ0 - δ) with (t + δ0) by omega.
          eapply EventGCStep.
          eapply step_gc; reflexivity || eauto 2.
    - assert (H6' := H6).
      invert_taint_eq; invert_taint_eq_cmd.
      invert_lack_behind.
      invert_event_step.
      + _apply wf_seq1 in *.
        super_destruct'; subst.
        assert (c1 <> Stop).
        {
          intro; subst.
          invert_event_step; exfalso; eauto 2.
        }
        assert (c1 <> TimeOut).
        {
          intro; subst.
          invert_event_step; exfalso; eauto 2.
        }
        assert (c1' <> Stop).
        {
          intro; subst.
          invert_lack_behind.
          invert_event_step; exfalso; eauto 2.
        }
        assert (c1' <> TimeOut).
        {
          intro; subst.
          invert_lack_behind.
          invert_event_step; exfalso; eauto 2.
        }
        assert (pc''0 = pc'').
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          eauto.
        }
        subst.
        assert (taint_eq ℓ Φ Γ Σ1 Σ2 c1 c1' m h s w).
        {
          unfolds.
          splits*.
        }
        remember_simple (IHc1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H H0 H1 H2 H3 H31 H19 H15).
        super_destruct'; subst.
        exists (d' ;; c2') s' w' Σ2' Ψ ev'.
        assert (d' <> Stop).
        {
          intro; subst.
          invert_lack_behind.
          eauto.
        }
        assert (d' <> TimeOut).
        {
          intro; subst.
          invert_lack_behind.
          eauto.
        }
        splits*.
        unfold taint_eq in *; super_destruct'; splits*.
      + _apply wf_seq1 in *.
        super_destruct'; subst.
        assert (c1 <> Stop).
        {
          intro; subst.
          invert_event_step; exfalso; eauto 2.
        }
        assert (c1 <> TimeOut).
        {
          intro; subst.
          invert_event_step; exfalso; eauto 2.
        }
        assert (c1' <> Stop).
        {
          intro; subst.
          invert_lack_behind.
          invert_event_step; exfalso; eauto 2.
        }
        assert (c1' <> TimeOut).
        {
          intro; subst.
          invert_lack_behind.
          invert_event_step; exfalso; eauto 2.
        }
        assert (pc''0 = pc'').
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          eauto.
        }
        subst.
        assert (taint_eq ℓ Φ Γ Σ1 Σ2 c1 c1' m h s w).
        {
          unfolds.
          splits*.
        }
        remember_simple (IHc1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H H0 H1 H2 H3 H31 H19 H15).
        super_destruct'; subst.
        exists c2' s' w' Σ2' Ψ ev'.
        invert_lack_behind.
        splits*.
        unfold taint_eq in *; super_destruct'; splits*.
      + assert (gc_occurred_no_ex (c1 ;; c2) (c1 ;; c2) pc' pc' m' m'
                                  ([[h1_pc ⊎ h1_not_pc, H5] ⊎ h2, H4])
                                  (t + δ) (t + δ + δ0) Σ1' Σ1' δ0 H4 H5 H7) as H'.
        {
          unfold gc_occurred_no_ex.
          splits; reflexivity || eauto 2.
          splits; eauto 2.
          erewrite -> disjoint_union_proof_irrelevance; eauto 2.
        }
        remember_simple (taint_eq_gc_noninterference H6 H1 H2 H3 H H0 H').
        clear H'.
        super_destruct'; subst.
        unfold gc_occurred_no_ex in *; super_destruct'; subst.
        exists (c1' ;; c2') s ([w2 ⊎ w3, H17]) Σ2 Ψ EmptyEvent.
        splits*; try omega.
        * replace (t + δ + δ0 - δ) with (t + δ0) by omega.
          eapply EventGCStep.
          eapply step_gc; reflexivity || eauto 2.
    - assert (H6' := H6).
      invert_taint_eq; invert_taint_eq_cmd.
      invert_lack_behind.
      invert_event_step.
      + invert_sem_step.
        assert (eval s e = Some (ValNum n)).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          invert_wt_cmd.
          remember_simple (eval_taint_eq_possibilistic H23 H17 H16 H8 H25).
          super_destruct'; subst.
          invert_val_taint_eq; eauto 2.
        }
        exists (c'0 ;; BackAt pc (n + t)) s w Σ2 Φ EmptyEvent.
        replace (S (t + δ) - δ) with (S t) by omega.
        splits*; try omega.
        * unfold taint_eq in *; super_destruct'; splits*.
        * constructor; eauto 2.
          constructor; omega.
      + assert (gc_occurred_no_ex (At l e c) (At l e c) pc' pc' m' m'
                                  ([[h1_pc ⊎ h1_not_pc, H5] ⊎ h2, H4])
                                  (t + δ) (t + δ + δ0) Σ1' Σ1' δ0 H4 H5 H7) as H'.
        {
          unfold gc_occurred_no_ex.
          splits; reflexivity || eauto 2.
          splits; eauto 2.
          erewrite -> disjoint_union_proof_irrelevance; eauto 2.
        }
        remember_simple (taint_eq_gc_noninterference H6 H1 H2 H3 H H0 H').
        clear H'.
        super_destruct'; subst.
        unfold gc_occurred_no_ex in *; super_destruct'; subst.
        exists (At l e c'0) s ([w2 ⊎ w3, H17]) Σ2 Ψ EmptyEvent.
        splits*; try omega.
        * replace (t + δ + δ0 - δ) with (t + δ0) by omega.
          eapply EventGCStep.
          eapply step_gc; reflexivity || eauto 2.
    - assert (H6' := H6).
      invert_taint_eq; invert_taint_eq_cmd.
      invert_lack_behind.
      invert_event_step.
      + invert_sem_step; try omega.
        exists (BackAt l n2) s w Σ2 Φ EmptyEvent.
        replace (S (t + δ) - δ) with (S t) by omega.
        splits*; try omega.
        constructor.
        constructor.
        * omega.
        * constructor; eauto 2.
          omega.
      + invert_sem_step; try omega.
        assert (n2 = t) by omega.
        subst.
        exists Stop s w Σ2 Φ (RestoreEvent pc' t).
        replace (S (t + δ) - δ) with (S t) by omega.
        splits*; try omega.
        unfold taint_eq in *; super_destruct'; splits*.
      + invert_sem_step; try omega.
        exists TimeOut s w Σ2 Φ (RestoreEvent pc' t).
        replace (S (t + δ) - δ) with (S t) by omega.
        splits*; try omega.
        * constructor.
          constructor; omega || eauto 2.
          constructor; omega.
        * unfold taint_eq in *; super_destruct'; splits*.
      + assert (gc_occurred_no_ex (BackAt l (n2 + δ)) (BackAt l (n2 + δ)) pc' pc' m' m'
                                  ([[h1_pc ⊎ h1_not_pc, H5] ⊎ h2, H4])
                                  (t + δ) (t + δ + δ0) Σ1' Σ1' δ0 H4 H5 H7) as H'.
        {
          unfold gc_occurred_no_ex.
          splits; reflexivity || (intro; discriminate) || eauto 2.
          splits; eauto 2.
          erewrite -> disjoint_union_proof_irrelevance; eauto 2.
        }
        remember_simple (taint_eq_gc_noninterference H6 H1 H2 H3 H H0 H').
        clear H'.
        super_destruct'; subst.
        unfold gc_occurred_no_ex in *; super_destruct'; subst.
        exists (BackAt l n2) s ([w2 ⊎ w3, H16]) Σ2 Ψ EmptyEvent.
        splits*; try omega.
        * replace (t + δ + δ0 - δ) with (t + δ0) by omega.
          eapply EventGCStep.
          eapply step_gc; reflexivity || eauto 2.
    - assert (H6' := H6).
      invert_taint_eq; invert_taint_eq_cmd.
      invert_lack_behind.
      invert_event_step.
      + invert_sem_step.
        assert (l1 = l2) by eauto 2.
        subst.
        assert (eval s e = Some (ValNum n)).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          invert_wt_cmd.
          remember_simple (eval_taint_eq_possibilistic H21 H17 H18 H8 H27).
          super_destruct'; subst.
          invert_val_taint_eq; eauto 2.
        }
        invert_wf_aux.
        do 2 specialize_gen.
        invert_wt_cmd.
        rewrite_inj.
        assert (exists u, eval s e0 = Some u /\ val_taint_eq Φ τ1 v u).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          invert_wt_cmd.
          destruct τ1 as [σ [ℓ' ι']].
          eapply eval_taint_eq_possibilistic; eauto 2.
        }
        super_destruct'; subst.
        assert (size l h = size l w).
        {
          eapply H11; eauto 2.
          intro.
          assert_wf_type.
          invert_wf_type.
          destruct_join_flowsto.
          eauto 4.
        }
        assert (size l w + n <= maxsize l w).
        {
          assert (size l w + n <= maxsize l h) by omega.
          erewrite -> constant_maxsize; eauto 2.
        }
        remember_simple (fresh_location w l n u H16).
        super_destruct'; subst.

        remember_simple (filter_bijection
                           (high ℓ (extend_memory i (ValLoc l2) m)
                                 (extend_heap v l2 l n h H4 H5))
                           (high_dec ℓ (extend_memory i (ValLoc l2) m)
                                     (extend_heap v l2 l n h H4 H5)) Φ).
        super_destruct'; subst.
        rename ψ into Ψ.
        assert (left Ψ l2 = None).
        {
          destruct (left Ψ l2) eqn:H_l1; try reflexivity.
          assert (left Φ l2 = Some l0).
          {
            eapply filtered_bijection_is_subset.
            - eapply high_dec.
            - eauto 2.
            - eauto 2.
          }
          assert (high ℓ m h l2).
          {
            eapply H1.
            eauto.
          }
          destruct_high.
          - assert (exists ℓ μ, heap_lookup l2 h = Some (ℓ, μ)).
            {
              repeat invert_wf_aux; eauto 2.
            }
            super_destruct'; congruence.
          - congruence.
        }
        assert (right Ψ loc = None).
        {
          destruct (right Ψ loc) eqn:H_loc; try reflexivity.
          assert (left Ψ l0 = Some loc) by (destruct Ψ; eauto 2).
          assert (left Φ l0 = Some loc).
          {
            eapply filtered_bijection_is_subset.
            - eapply high_dec.
            - eauto 2.
            - eauto 2.
          }
          assert (high ℓ m h l0).
          {
            eapply H1; eauto.
          }
          assert (high ℓ s w loc).
          {
            rewrite <- high_iff; eauto 2.
          }
          destruct_high.
          - assert (exists ℓ μ, heap_lookup loc w = Some (ℓ, μ)) by eauto 2.
            super_destruct; congruence.
          - congruence.
        }
        exists Stop (extend_memory i (ValLoc loc) s).
        exists (extend_heap u loc l n w H18 H16).
        exists (extend_stenv loc τ1 Σ2) (extend_bijection Ψ l2 loc H26 H31) (NewEvent ℓ_x i loc).
        assert (wf_taint_bijection ℓ (extend_bijection Ψ l2 loc H26 H31)
                                   (m [i → ValLoc l2]) (extend_heap v l2 l n h H4 H5)).
        {
          repeat invert_wf_aux.
          eapply wf_taint_bijection_extend_mem_and_heap1; intros; subst; eauto 2.
        }
        replace (S (t + δ) - δ) with (S t) by omega.
        splits; try omega; eauto 2.
        * constructor.
          constructors; eauto 2.
        * unfolds.
          splits; eauto 2.
          {
            destruct τ1 as [σ ε].
            repeat invert_wf_aux.
            eapply taint_eq_reach_extend_mem_and_heap; intros; subst; eauto 2.
            - subst.
              assert (exists loc, v = ValLoc loc) by eauto 2.
              super_destruct'; subst.
              eauto.
            - subst.
              assert (exists loc, u = ValLoc loc) by eauto 2.
              super_destruct'; subst.
              eauto.
            - subst; eauto 2.
            - subst; eauto 2.
          }
          {
            repeat invert_wf_aux.
            eapply taint_eq_heap_extend_mem_and_heap; intros; subst; eauto 3.
          }
          {
            unfolds.
            intros.
            destruct (T_dec l0 l); subst.
            - do 2 rewrite -> size_extend_heap_eq_level by solve[eauto 2].
              omega.
            - do 2 rewrite -> size_extend_heap_neq_level by solve[eauto 2].
              eauto.
          }
          {
            destruct τ1 as [σ ε].
            repeat invert_wf_aux.
            eapply taint_eq_heap_domain_eq_extend_mem_and_heap; intros; subst; eauto 2.
            - subst.
              assert (exists loc, v = ValLoc loc) by eauto 2.
              super_destruct'; subst.
              eauto.
            - subst.
              assert (exists loc, u = ValLoc loc) by eauto 2.
              super_destruct'; subst.
              eauto.
            - subst; eauto 2.
            - subst; eauto 2.
          }
          {
            unfolds.
            intros.
            destruct (decide (l2 = loc1)); subst.
            - _rewrite -> left_extend_bijection_eq in *.
              injects.
              do 2 rewrite -> extend_stenv_lookup_eq.
              splits*.
            - _rewrite -> left_extend_bijection_neq in * by solve[eauto 2].
              assert (loc <> loc2).
              {
                intro; subst.
                assert (right Ψ loc2 = Some loc1) by (destruct Ψ; eauto 2).
                congruence.
              }
              do 2 rewrite -> extend_stenv_lookup_neq by solve[eauto 2].
              eapply H13; eauto 2.
              eapply filtered_bijection_is_subset.
              + eapply high_dec.
              + eauto 2.
              + eauto 2.
          }
        * repeat invert_wf_aux.
          destruct τ1 as [σ [ℓ' ι']].
          eapply wf_taint_bijection_extend_mem_and_heap2 with (Φ := Φ) (v1 := v); intros; subst; eauto 2.
          { subst; eauto 2. }
          { subst; eauto 2. }
          { subst.
            assert (exists loc, v = ValLoc loc) by eauto 2.
            super_destruct'; subst; eauto. }
          { subst.
            assert (exists loc, u = ValLoc loc) by eauto 2.
            super_destruct'; subst; eauto. }
      + assert (gc_occurred_no_ex (NewArr i l e e0) (NewArr i l e e0) pc' pc' m' m'
                                  ([[h1_pc ⊎ h1_not_pc, H5] ⊎ h2, H4])
                                  (t + δ) (t + δ + δ0) Σ1' Σ1' δ0 H4 H5 H7) as H'.
        {
          unfold gc_occurred_no_ex.
          splits; reflexivity || eauto 2.
          splits; eauto 2.
          erewrite -> disjoint_union_proof_irrelevance; eauto 2.
        }
        remember_simple (taint_eq_gc_noninterference H6 H1 H2 H3 H H0 H').
        clear H'.
        super_destruct'; subst.
        unfold gc_occurred_no_ex in *; super_destruct'; subst.
        exists (NewArr i l e e0) s ([w2 ⊎ w3, H16]) Σ2 Ψ EmptyEvent.
        splits*; try omega.
        * replace (t + δ + δ0 - δ) with (t + δ0) by omega.
          eapply EventGCStep.
          eapply step_gc; reflexivity || eauto 2.    
    - assert (H6' := H6).
      invert_taint_eq; invert_taint_eq_cmd.
      invert_event_step.
      + invert_sem_step.
        rewrite_inj.
        assert (exists loc, left Φ l1 = Some loc /\ memory_lookup s i = Some (ValLoc loc)).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          invert_wt_cmd.
          invert_lifted.
          assert_wf_type.
          invert_wf_type.
          assert (eval m' (Var i) = Some (ValLoc l1)) by eauto 2.
          assert (expr_has_type Γ (Var i) (SecType (Array (SecType σ l2) ℓ1) (l_ref, ∘))) by eauto 2.
          remember_simple (eval_taint_eq_possibilistic H0 H17 H16 H8 H).
          super_destruct'; subst.
          invert_val_taint_eq.
          exists loc'.
          splits*.
        }
        assert (eval s e = Some (ValNum n0)).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          invert_wt_cmd.
          invert_lifted.
          destruct ε_idx as [ℓ_idx ι_idx].
          remember_simple (eval_taint_eq_possibilistic H14 H18 H17 H8 H31).
          super_destruct'; subst.
          invert_val_taint_eq.
          - eauto.
          - destruct ε_x as [ℓ_x'' ι_x''].
            assert (LH.flowsto (LH.join • ∘) ι_x'') by eauto 2.
            assert_wf_type.
            invert_wf_type.
            inverts H0.
        }
        super_destruct'; subst.
        invert_wf_aux.
        repeat specialize_gen.
        invert_wt_cmd.
        invert_lifted.
        assert (exists u, eval s e0 = Some u /\ val_taint_eq Φ (SecType σ ε) v0 u).
        {
          repeat invert_wf_aux.
          destruct ε as [ℓ' ι'].
          eauto 2 using eval_taint_eq_possibilistic.
        }
        super_destruct'; subst.
        remember_simple (filter_bijection
                           (high ℓ m' (update_heap l1 n0 v0 h))
                           (high_dec ℓ m' (update_heap l1 n0 v0 h)) Φ).
        super_destruct'; subst.
        rename ψ into Ψ.
        exists Stop s (update_heap loc n0 u w) Σ2 Ψ (SetEvent ℓ0 ℓ_x i n0 u).
        replace (S t + δ) with (S (t + δ)) by omega.
        assert (length_of loc w = Some length).
        {
          assert (high ℓ m' h l1).
          {
            eapply H1; eauto 2.
          }
          assert (exists ℓ μ, heap_lookup l1 h = Some (ℓ, μ)).
          {
            destruct_high; eauto.
          }
          assert (high ℓ s w loc).
          {
            rewrite <- high_iff; eauto.
          }
          assert (exists ℓ μ, heap_lookup loc w = Some (ℓ, μ)).
          {
            repeat invert_wf_aux.
            destruct_high; eauto.
          }
          super_destruct'; subst.
          assert (Σ1' l1 = Some (SecType σ l2)) by eauto 2.
          assert (Σ2 loc = Some (SecType σ l2)) by (invert_wf_aux; eauto 2).
          remember_simple (H10 l1 loc _ _ _ _ _ H4 H22 H33 H25 H38 H39 H40).
          super_destruct'; subst.
          congruence.
        }
        assert (wf_taint_bijection ℓ Ψ m' (update_heap l1 n0 v0 h)).
        {
          eapply taint_eq_update_bijection1; eauto 2.
          intros; subst; eauto 2.
        }
        assert (val_taint_eq Φ (SecType σ l2) v0 u).
        {
          destruct l2 as [ℓ' ι'].
          destruct ε as [ℓ'' ι''].
          destruct_prod_join_flowsto.
          eapply val_taint_eq_mon; eauto 2.
        }
        replace (S (t + δ) - δ) with (S t) by omega.
        splits; try omega; eauto 2.
        * constructor.
          constructors; eauto 2.
        * unfolds.          
          splits; eauto 2.
          {
            eapply taint_eq_mem_update_heap; eauto 2.
          }
          {
            repeat invert_wf_aux.
            eapply taint_eq_reach_update_heap; eauto 2.
            - intros; subst.
              assert (exists loc, v0 = ValLoc loc) by eauto 2.
              super_destruct'; subst; eauto.
            - intros; subst.
              assert (exists loc, u = ValLoc loc) by eauto 2.
              super_destruct'; subst; eauto.
            - intros; subst; eauto 2.
            - intros; subst; eauto 2.
          }
          {
            repeat invert_wf_aux.
            eapply taint_eq_heap_update_heap; eauto 2.
            - intros; subst; eauto 2.
            - intros; subst; eauto 2.
          }
          {
            unfolds.
            intros.
            repeat rewrite -> size_update_heap; eauto 2.
          }
          {
            repeat invert_wf_aux.
            eapply taint_eq_heap_update_domain_eq_update_heap with (Φ := Φ) (Σ1 := Σ1') (Σ2 := Σ2); eauto 2.
            - intros; subst.
              assert (exists loc, v0 = ValLoc loc) by eauto 2.
              super_destruct'; subst; eauto.
            - intros; subst.
              assert (exists loc, u = ValLoc loc) by eauto 2.
              super_destruct'; subst; eauto.
            - intros; subst; eauto 2.
            - intros; subst; eauto 2.
          }
          {
            unfolds.
            intros.
            assert (left Φ loc1 = Some loc2).
            {
              eapply filtered_bijection_is_subset.
              - eapply high_dec.
              - eauto 2.
              - eauto 2.
            }
            eauto.
          }
        * repeat invert_wf_aux.
          eapply wf_taint_bijection_update_heap2 with (Φ := Φ); eauto 2.
          { intros; subst.
            assert (exists loc, v0 = ValLoc loc) by eauto 2.
            super_destruct'; subst; eauto. }
          { intros; subst.
            assert (exists loc, u = ValLoc loc) by eauto 2.
            super_destruct'; subst; eauto. }
          { intros; subst; eauto 2. }
          { intros; subst; eauto 2. }
        * assert (val_taint_eq Ψ (SecType σ l2) v0 u).
          {
            invert_val_taint_eq; eauto 3.
            assert (high ℓ m' (update_heap l1 n0 (ValLoc loc0) h) loc0) by eauto 3.
            eauto.
          }
          assert_wf_type.
          invert_wf_type.
          destruct l2 as [ℓ' ι'].
          rewrite_inj.
          constructors; eauto 2.
      + assert (gc_occurred_no_ex (SetArr i e e0) (SetArr i e e0) pc' pc' m' m'
                                  ([[h1_pc ⊎ h1_not_pc, H7] ⊎ h2, H4])
                                  (t + δ) (t + δ + δ0) Σ1' Σ1' δ0 H4 H7 H14) as H'.
        {
          unfold gc_occurred_no_ex.
          splits; reflexivity || eauto 2.
          splits; eauto 2.
          erewrite -> disjoint_union_proof_irrelevance; eauto 2.
        }
        remember_simple (taint_eq_gc_noninterference H6 H1 H2 H3 H H0 H').
        clear H'.
        super_destruct'; subst.
        unfold gc_occurred_no_ex in *; super_destruct'; subst.
        exists (SetArr i e e0) s ([w2 ⊎ w3, H17]) Σ2 Ψ EmptyEvent.
        splits*; try omega.
        * replace (t + δ + δ0 - δ) with (t + δ0) by omega.
          eapply EventGCStep.
          eapply step_gc; reflexivity || eauto 2.
    - assert (H6' := H6).
      invert_taint_eq; invert_taint_eq_cmd.
      invert_event_step.
      + invert_sem_step.
        invert_wf_aux.
        repeat specialize_gen.
        invert_wt_cmd.
        invert_lifted.
        rewrite_inj.
        assert (exists loc, memory_lookup s i0 = Some (ValLoc loc) /\ left Φ l1 = Some loc).
        {
          assert (exists v2, eval s (Var i0) = Some v2 /\ val_taint_eq Φ (SecType (Array (SecType σ ε) ℓ2) ε_y) (ValLoc l1) v2).
          {
            destruct ε_y as [ℓ_y ι_y].
            invert_wf_aux.
            eapply eval_taint_eq_possibilistic with (m1 := m) (m2 := s); eauto 2.
          }
          super_destruct'; subst.
          assert (wf_type bot (SecType (Array (SecType σ ε) ℓ2) ε_y)) by eauto 2.
          invert_wf_type.
          invert_val_taint_eq.
          exists loc'.
          splits*.
        }
        super_destruct'; subst.
        assert ((exists μ, heap_lookup loc w = Some (ℓ0, μ)) /\ high ℓ s w loc).
        {
          eapply H12; eauto.
        }
        super_destruct'; subst.
        assert (eval s e = Some (ValNum n0)).
        {
          assert (exists v2, eval s e = Some v2 /\ val_taint_eq Φ (SecType Int ε_idx) (ValNum n0) v2).
          {
            destruct ε_idx as [ℓ_idx ι_idx].
            repeat invert_wf_aux.
            eapply eval_taint_eq_possibilistic with (m1 := m) (m2 := s); eauto 2.
          }
          super_destruct'; subst.
          invert_val_taint_eq; eauto 2.
          destruct ε_y as [ℓ_y ι_y].
          assert (wf_type bot (SecType (Array (SecType σ ε) ℓ2) (ℓ_y, ι_y))) by eauto 2.
          invert_wf_type.
          destruct_prod_join_flowsto.
          match goal with
            [H: (_, •) ≼ (_, ∘) |- _] =>
            inverts H
          end.
        }
        assert (exists u, lookup μ0 n0 = Some u /\ val_taint_eq Φ (SecType σ ε) v0 u /\ length_of l1 h' = length_of loc w).
        {
          assert (high ℓ m h' l1).
          {
            eapply high_iff; eauto 2.
          }
          assert (Σ1' l1 = Some (SecType σ ε)) by eauto 2.
          assert (Σ2 loc = Some (SecType σ ε)) by (invert_wf_aux; eauto 2).
          remember_simple (H10 l1 loc _ _ _ _ _ H4 H21 H19 H36 H7 H23 H24).
          super_destruct'; subst.
          assert (exists u, lookup μ0 n0 = Some u) by firstorder 2.
          super_destruct'; subst.
          exists u.
          splits*.
        }
        super_destruct'; subst.
        remember_simple (filter_bijection
                           (high ℓ (extend_memory i v0 m) h')
                           (high_dec ℓ (extend_memory i v0 m) h') Φ).
        super_destruct'; subst.
        rename ψ into Ψ.
        exists Stop (extend_memory i u s) w Σ2 Ψ (GetEvent ℓ_x i i0 u).
        assert (length_of loc w = Some length) by congruence.
        assert (val_taint_eq Φ (SecType σ (ℓ_x, ι)) v0 u).
        {
          destruct_prod_join_flowsto.
          destruct ε.
          eapply val_taint_eq_mon; eauto 2.
        }
        assert (taint_eq_heap_domain_eq ℓ Ψ (m [i → v0]) (s [i → u]) h' w).
        {
          repeat invert_wf_aux.
          eapply taint_eq_heap_domain_eq_extend_mem; intros; subst; eauto 4.
          - subst.
            assert (exists loc, v0 = ValLoc loc) by eauto 3.
            super_destruct'; subst; eauto.
          - subst.
            eauto 4.
          - subst.
            assert (exists loc, u = ValLoc loc) by eauto 3.
            super_destruct'; subst; eauto.
          - subst; eauto 4.
        }
        assert (taint_eq_reach Ψ (m [i → v0]) h' (s [i → u]) w).
        {
          repeat invert_wf_aux.
          eapply taint_eq_reach_extend_mem; intros; subst; eauto 3.
        }
        replace (S (t + δ) - δ) with (S t) by omega.
        splits; try omega; eauto 2.
        * replace (S t + δ) with (S (t + δ)) by omega.
          constructor.
          constructors; eauto 2.
        * unfolds.
          splits; eauto 2.
          {
            repeat invert_wf_aux.
            eapply taint_eq_heap_extend_mem; intros; subst; eauto 4.
            - subst; eauto 4.
            - subst; eauto 4.
            - subst.
              assert (exists loc, v0 = ValLoc loc) by eauto 3.
              super_destruct'; subst; eauto.
            - subst.
              assert (exists loc, u = ValLoc loc) by eauto 3.
              super_destruct'; subst; eauto.
          }
          {
            eapply taint_eq_stenv_extend_mem; eauto 2.
          }
        * eapply wf_taint_bijection_extend_mem1; eauto 2.
          intros; subst; eauto 3.
        * repeat invert_wf_aux; eauto 2.
          eapply wf_taint_bijection_extend_mem2; intros; subst; eauto 4.
          { subst; eauto 4. }
          { subst; eauto 4. }
          { subst.
            assert (exists loc, u = ValLoc loc) by eauto 3.
            super_destruct'; subst; eauto. }
        * assert (val_taint_eq Ψ (SecType σ (ℓ_x, ι)) v0 u).
          {
            invert_val_taint_eq; eauto 3.
            assert (high ℓ (m [i → ValLoc loc0]) h' loc0) by eauto.
            eauto 3.
          }
          constructors; eauto 3.
      + assert (gc_occurred_no_ex (GetArr i i0 e) (GetArr i i0 e) pc' pc' m' m'
                                  ([[h1_pc ⊎ h1_not_pc, H7] ⊎ h2, H4])
                                  (t + δ) (t + δ + δ0) Σ1' Σ1' δ0 H4 H7 H14) as H'.
        {
          unfold gc_occurred_no_ex.
          splits; reflexivity || eauto 2.
          splits; eauto 2.
          erewrite -> disjoint_union_proof_irrelevance; eauto 2.
        }
        remember_simple (taint_eq_gc_noninterference H6 H1 H2 H3 H H0 H').
        clear H'.
        super_destruct'; subst.
        unfold gc_occurred_no_ex in *; super_destruct'; subst.
        exists (GetArr i i0 e) s ([w2 ⊎ w3, H17]) Σ2 Ψ EmptyEvent.
        splits*; try omega.
        * replace (t + δ + δ0 - δ) with (t + δ0) by omega.
          eapply EventGCStep.
          eapply step_gc; reflexivity || eauto 2.
    - assert (H6' := H6).
      invert_taint_eq; invert_taint_eq_cmd.
      invert_event_step.
      + invert_sem_step.
        invert_wf_aux.
        repeat specialize_gen.
        invert_wt_cmd.
        rewrite_inj.
        remember_simple (
            filter_bijection
              (high ℓ (extend_memory i (ValNum (t + δ)) m) h')
              (high_dec ℓ (extend_memory i (ValNum (t + δ)) m) h') Φ).
        super_destruct'; subst.
        rename ψ into Ψ.
        exists Stop (extend_memory i (ValNum t) s) w Σ2 Ψ (TimeEvent ℓ1 i t).
        assert (
            taint_eq_heap_domain_eq ℓ Ψ
                                    (m [i → ValNum (t + δ)])
                                    (s [i → ValNum t])
                                    h' w).
        {
          repeat invert_wf_aux.
          eapply taint_eq_heap_domain_eq_extend_mem; eauto 2.
          - intros; discriminate.
          - intros; discriminate.
        }
        assert (taint_eq_reach Ψ
                               (m [i → ValNum (t + δ)]) h'
                               (s [i → ValNum t]) w).
        {
          repeat invert_wf_aux.
          eapply taint_eq_reach_extend_mem; eauto 2.
          - eauto 2.
          - intros; discriminate.
          - intros; discriminate.
        }
        
        splits; try omega; eauto 2.
        * replace (S (t + δ) - δ) with (S t) by omega.
          constructor; eauto.
        * unfolds.
          splits; eauto 3.
          {
            eapply taint_eq_heap_extend_mem; eauto 2.
            - intros; discriminate.
            - intros; discriminate.
          }
          {
            eapply taint_eq_stenv_extend_mem; eauto 2.
          }
        * eapply wf_taint_bijection_extend_mem1; eauto 2.
          intros; discriminate.
        * repeat invert_wf_aux.
          eapply wf_taint_bijection_extend_mem2; eauto 2.
          intros; discriminate.
      + assert (gc_occurred_no_ex (Time i) (Time i) pc' pc' m' m'
                                  ([[h1_pc ⊎ h1_not_pc, H7] ⊎ h2, H4])
                                  (t + δ) (t + δ + δ0) Σ1' Σ1' δ0 H4 H7 H14) as H'.
        {
          unfold gc_occurred_no_ex.
          splits; reflexivity || eauto 2.
          splits; eauto 2.
          erewrite -> disjoint_union_proof_irrelevance; eauto 2.
        }
        remember_simple (taint_eq_gc_noninterference H6 H1 H2 H3 H H0 H').
        clear H'.
        super_destruct'; subst.
        unfold gc_occurred_no_ex in *; super_destruct'; subst.
        exists (Time i) s ([w2 ⊎ w3, H17]) Σ2 Ψ EmptyEvent.
        splits*; try omega.
        * replace (t + δ + δ0 - δ) with (t + δ0) by omega.
          eapply EventGCStep.
          eapply step_gc; reflexivity || eauto 2.
    - invert_event_step; exfalso; eauto 2.
  Qed.

  Lemma offset_config_gives_taint_eq_bridge2:
    forall n ℓ_adv Γ c d pc_end c' pc pc' m m' h h' t t' Σ1 Σ2 Σ1' Φ δ s w ev,
      wellformed_aux Γ Σ1 ⟨c, pc, m, h, t + δ⟩ pc_end ->
      wellformed_aux Γ Σ2 ⟨d, pc, s, w, t⟩ pc_end ->
      wf_taint_bijection ℓ_adv Φ m h ->
      wf_taint_bijection ℓ_adv (inverse Φ) s w ->
      ~ pc ⊑ ℓ_adv ->
      ~ contains_low_backat ℓ_adv c ->
      ⟨c, pc, m, h, t + δ⟩ ↷ [ℓ_adv, Γ, Σ1, Σ1', ev, n] ⟨c', pc', m', h', t'⟩ ->
      d ≲ [δ] c ->
      taint_eq ℓ_adv Φ Γ Σ1 Σ2 c d m h s w ->
      exists d' s' w' Σ2' Ψ ev',
        t' >= δ
        /\ ⟨d, pc, s, w, t⟩ ↷ [ℓ_adv, Γ, Σ2, Σ2', ev', n] ⟨d', pc', s', w', t' - δ⟩
        /\ taint_eq ℓ_adv Ψ Γ Σ1' Σ2' c' d' m' h' s' w'
        /\ d' ≲ [δ] c'
        /\ wf_taint_bijection ℓ_adv Ψ m' h'
        /\ wf_taint_bijection ℓ_adv (inverse Ψ) s' w'
        /\ taint_eq_events Γ Ψ ev ev'.
  Proof.
    intros n ℓ_adv Γ.
    induction n; intros.
    - invert_bridge_step.
      + invert_low_event_step.
        remember_simple (offset_config_gives_taint_eq_event2 H H0 H1 H2 H3 H5 H6 H7).
        super_destruct'; subst.
        exists d' s' w' Σ2' Ψ ev'.
        splits*.
      + unfold is_stop_config, cmd_of in *; subst.
        invert_high_event_step.
        remember_simple (offset_config_gives_taint_eq_event2 H H0 H1 H2 H3 H5 H6 H7).
        super_destruct'; subst.
        exists d' s' w' Σ2' Ψ ev'.
        invert_lack_behind.
        splits; eauto 2.
        eapply bridge_stop_num.
        * splits*.
        * reflexivity.
    - invert_bridge_step.
      invert_high_event_step.
      destruct cfg2.
      remember_simple (offset_config_gives_taint_eq_event2 H H0 H1 H2 H3 H5 H6 H7).
      super_destruct'; subst.
      assert (wellformed_aux Γ Σ' ⟨c0, pc0, memory, heap, time⟩ pc_end) by eauto 2.
      assert (wellformed_aux Γ Σ2' ⟨d', pc0, s', w', time - δ⟩ pc_end) by eauto 2.
      assert (~ pc0 ⊑ ℓ_adv).
      {
        assert (c <> Stop).
        {
          intro; subst.
          invert_event_step; eauto.
        }
        assert (c <> TimeOut).
        {
          intro; subst.
          invert_event_step; eauto.
        }
        repeat invert_wf_aux.
        repeat specialize_gen.
        eapply high_pc_and_no_low_backat_implies_high_pc_event_step; eauto.
      }
      assert (~ contains_low_backat ℓ_adv c0).
      {
        eauto 2 using no_spurious_low_backats_event_step.
      }
      replace time with (time - δ + δ) in H18 by omega.
      replace time with (time - δ + δ) in H19 by omega.
      remember_simple (IHn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H18 H20 H15 H16 H21 H22 H19 H14 H13).
      super_destruct'; subst.
      exists d'0 s'0 w'0 Σ2'0 Ψ0 ev'0.
      splits*.
      constructors.
      + splits*.
      + unfold is_stop_config, cmd_of; intro; subst.
        invert_lack_behind.
        eauto 2.
      + unfold is_timeout_config, cmd_of; intro; subst.
        invert_lack_behind.
        eauto 2.
      + eauto.
  Qed.
  
  Lemma ni_bridge_num_at_case:
    forall n1 ℓ Γ l e Σ1 Σ2 Σ3 Σ1' Σ3' φ Φ pc pc1' pc2'' c c' c2 c2' m1 m2 s1 s2'' h1 h2
      w1 w2'' t t2 g2'' s1' w1' ev1 ev2 pc_end n2 t',
      (forall m, m <= n1 -> ni_bridge m ℓ) ->
      wf_bijection ℓ φ Γ Σ1 m1 h1 ->
      wf_bijection ℓ (inverse φ) Γ Σ2 s1 w1 ->
      wf_taint_bijection ℓ Φ s1 w1 ->
      wf_taint_bijection ℓ (inverse Φ) s1' w1' ->
      wellformed_aux Γ Σ1 ⟨AT l FOR e DO c, pc, m1, h1, t⟩ pc_end ->
      wellformed_aux Γ Σ2 ⟨AT l FOR e DO c, pc, s1, w1, t⟩ pc_end ->
      wellformed_aux Γ Σ3 ⟨c', pc, s1', w1', t'⟩ pc_end ->
      state_low_eq ℓ φ m1 h1 s1 w1 Γ Σ1 Σ2 ->
      pc ⊑ ℓ ->
      taint_eq ℓ Φ Γ Σ2 Σ3 (AT l FOR e DO c) c' s1 w1 s1' w1' ->
      ⟨AT l FOR e DO c, pc, m1, h1, t⟩ ↷ [ℓ, Γ, Σ1, Σ1', ev1, S n1] ⟨c2, pc1', m2, h2, t2⟩ ->
      ⟨c', pc, s1', w1', t'⟩ ↷ [ℓ, Γ, Σ3, Σ3', ev2, n2] ⟨c2', pc2'', s2'', w2'', g2''⟩ ->
      c2 <> TimeOut ->
      c2' <> TimeOut ->
      exists ev1' n1' ψ Ψ s2' w2' Σ2',
        ⟨AT l FOR e DO c, pc, s1, w1, t⟩ ↷ [ℓ, Γ, Σ2, Σ2', ev1', n1'] ⟨c2, pc1', s2', w2', t2⟩ /\
        pc1' ⊑ ℓ /\
        pc2'' = pc1' /\
        state_low_eq ℓ ψ m2 h2 s2' w2' Γ Σ1' Σ2'/\
        event_low_eq ℓ (left ψ) ev1 ev1' /\
        taint_eq_events Γ Ψ ev1' ev2 /\
        wf_bijection ℓ ψ Γ Σ1' m2 h2 /\
        wf_bijection ℓ (inverse ψ) Γ Σ2' s2' w2' /\
        wf_taint_bijection ℓ Ψ s2' w2' /\
        wf_taint_bijection ℓ (inverse Ψ) s2'' w2'' /\
        taint_eq ℓ Ψ Γ Σ2' Σ3' c2 c2' s2' w2' s2'' w2''.
  Proof.
    intros.
    invert_taint_eq; invert_taint_eq_cmd.
    _apply at_bridge_properties in *.
    super_destruct'; subst.
    construct_many_gc_run.
    super_destruct'; subst.
    assert (eval s1 e = Some (ValNum v)).
    {
      repeat invert_wf_aux.
      repeat specialize_gen.
      invert_wt_cmd.
      assert (taint_eq_mem (inverse Φ) Γ s1' s1) by eauto 2.
      remember_simple (eval_taint_eq_possibilistic H46 H35 H34 H4 H11).
      super_destruct'.
      invert_val_taint_eq; eauto 2.
    }
    assert (c = c'0).
    {
      assert (~ contains_backat c).
      {
        repeat invert_wf_aux.
        repeat specialize_gen.
        invert_wt_cmd.
        eauto 2.
      }
      eauto 2.
    }
    subst.
    assert (taint_eq ℓ Φ Γ Σ2' Σ3
                     (c'0;; BackAt pc (v + t0))
                     (c'0;; BackAt pc (v + t1)) m2' h2' s1' h0).
    {
      remember_simple (low_gc_trans_preserves_taint_eq H5 H8 H26).
      remember_simple (low_gc_trans_preserves_taint_eq H6 H8 H9).
      rewrite <- inverse_identity_is_identity in H31.
      eapply taint_eq_symmetry in H31.
      rewrite <- inverse_is_involutive in H31.
      assert (taint_eq ℓ Φ Γ Σ2' Σ3 (c'0;; BackAt pc (v + t0)) (c'0;; BackAt pc (v + t0)) m2' h2' s1' w1').
      {
        rewrite <- (compose_id_left Φ).
        eapply taint_eq_trans with (m' := s1) (h' := w1).
        - repeat invert_wf_aux; eauto 2.
        - unfold taint_eq in *; super_destruct'; splits*.
        - unfold taint_eq in *; super_destruct'; splits*.
      }
      
      rewrite <- (compose_id_right Φ).
      eapply taint_eq_trans with (m' := s1') (h' := w1').
      { repeat invert_wf_aux; eauto 2. }
      { eauto 2. }
      { unfold taint_eq in *; super_destruct'; splits*. }
    }
    assert (wellformed_aux Γ Σ1 ⟨AT l FOR e DO c'0, pc, m1, h3, t0⟩ pc_end) by eauto 2.
    assert (wellformed_aux Γ Σ1 ⟨ c'0;; BackAt pc (v0 + t0), l, m1, h3, S t0⟩ pc_end).
    {
      eapply preservation; eauto 2.
    }
    assert (wellformed_aux Γ Σ3 ⟨AT l FOR e DO c'0, pc, s1', h0, t1⟩ pc_end) by eauto 2.
    assert (wellformed_aux Γ Σ3 ⟨c'0;; BackAt pc (v + t1), l, s1', h0, S t1⟩ pc_end).
    {
      eapply preservation; eauto 2.
    }
    assert (wellformed_aux Γ Σ2' ⟨AT l FOR e DO c'0, pc, m2', h2', t0⟩ pc_end) by eauto 2.
    assert (⟨AT l FOR e DO c'0, pc, m2', h2', t0⟩ ⇒ (Γ, Σ2', Σ2') ⟨c'0;; BackAt pc (v + t0), l, m2', h2', S t0⟩).
    {
      constructor.
      constructor; eauto 2.
    }
    assert (wellformed_aux Γ Σ2' ⟨c'0;; BackAt pc (v + t0), l, m2', h2', S t0⟩ pc_end).
    {
      eapply preservation; eauto 2.
    }
    destruct (flowsto_dec l ℓ).
    - replace (S n1 - k0 - 1) with (n1 - k0) in * by omega.
      assert (n1 - k0 <= n1) by omega.          
      assert (wf_taint_bijection ℓ Φ m2' h2').
      {
        eapply low_gc_trans_preserves_wf_taint_bijection with (pc := pc); eauto 2.
      }
      assert (wf_taint_bijection ℓ (inverse Φ) s1' h0).
      {
        eapply low_gc_trans_preserves_wf_taint_bijection with (pc := pc); eauto 2.
      }
      assert (v = v0).
      {
        repeat invert_wf_aux.
        repeat specialize_gen.
        invert_wt_cmd.
        repeat invert_state_low_eq.
        
        assert (val_low_eq ℓ (SecType Int (ℓ', ∘)) (ValNum v0) (ValNum v) φ) by eauto 2 using eval_low_eq.
        invert_val_low_eq.
        - assert (ℓ' ⊑ ℓ) by eauto.
          contradiction.
        - reflexivity.
      }
      subst.
      apply_IH.
      super_destruct'; subst.
      exists ev1' (k0 + n1' + 1) ψ0 Ψ s2' w2'; exists Σ2'0.
      splits; eauto 2.
      + eapply gc_trans_high_event_bridge_implies_bridge; eauto 2.
        constructor.
        eapply event_sem_step_at.
        eapply step_at; eauto 2.
      + splits*.
    - replace (1 + n1 - k0 - 1) with (n1 - k0) in H23 by omega.
      remember_simple (about_seq_bridge_step H35 H21).
      remember_simple (about_seq_bridge_step H33 H25).
      assert (~ contains_backat c'0).
      {
        inverts H36.
        repeat specialize_gen.
        invert_wt_cmd.
        eauto 2.
      }
      super_destruct; subst.
      + destruct (eq_cmd_dec c1' Stop).
        * subst.
          assert (high_event ℓ ev1).
          {
            _apply wf_seq1 in *.
            super_destruct'; subst.
            eapply bridge_step_stop_implies_high_event with (c := c'0) (m := m1); eauto 2.
          }
          contradiction.
        * assert (high_event ℓ ev1).
          {
            _apply wf_seq1 in *.
            super_destruct'; subst.
            eapply bridge_step_nonstop_implies_high_event with (c := c'0) (m := m1); eauto 2.
          }
          contradiction.
      + destruct (eq_cmd_dec c1' Stop).
        * subst.
          assert (high_event ℓ ev1).
          {
            _apply wf_seq1 in *.
            super_destruct'; subst.
            eapply bridge_step_stop_implies_high_event with (c := c'0) (m := m1); eauto 2.
          }
          contradiction.
        * assert (high_event ℓ ev1).
          {
            _apply wf_seq1 in *.
            super_destruct'; subst.
            eapply bridge_step_nonstop_implies_high_event with (c := c'0) (m := m1); eauto 2.
          }
          contradiction.
      + destruct (eq_cmd_dec c1' Stop).
        * subst.
          assert (high_event ℓ ev2).
          {
            _apply wf_seq1 in *.
            super_destruct'; subst.
            eapply bridge_step_stop_implies_high_event with (c := c'0) (m := s1'); eauto 2.
          }
          contradiction.
        * assert (high_event ℓ ev2).
          {
            _apply wf_seq1 in *.
            super_destruct'; subst.
            eapply bridge_step_nonstop_implies_high_event with (c := c'0) (m := s1'); eauto 2.
          }
          contradiction.
      + remember_simple (wf_seq_half_step_implies_wf_bridge_step H33 H44).
        remember_simple (wf_seq_half_step_implies_wf_bridge_step H35 H48).
        apply wf_seq1 in H33.
        apply wf_seq1 in H35.
        assert (H38' := H38).
        apply wf_seq in H38.
        super_destruct'; subst.
        assert (pc''1 = pc''2 /\ pc''1 = pc''3).
        {
          assert (c'0 <> Stop).
          {
            intro; subst.
            inverts H4.
            repeat specialize_gen.
            invert_wt_cmd.
            invert_wt_stop.
          }
          assert (c'0 <> TimeOut).
          {
            intro; subst.
            inverts H4.
            repeat specialize_gen.
            invert_wt_cmd.
            invert_wt_timeout.
          }
          inverts H35.
          inverts H33.
          inverts H38.
          repeat specialize_gen.
          splits*.
        }
        
        super_destruct'; repeat subst.
        assert (exists k, t0 = t1 + k \/ (t1 = t0 + k)) as H'.
        {
          assert ({t0 <= t1} + {t1 < t0}) as H'.
          {
            eapply le_lt_dec; eauto 2.
          }
          destruct H'.
          - exists (t1 - t0).
            right.
            eapply le_plus_minus; eauto 2.
          - exists (t0 - t1).
            left.
            eapply le_plus_minus; eauto 2 with arith.
        }
        super_destruct'; subst.
        assert (wf_taint_bijection ℓ Φ m2' h2').
        {
          eapply low_gc_trans_preserves_wf_taint_bijection; eauto 2.
        }
        assert (wf_taint_bijection ℓ (inverse Φ) s1' h0) by (eapply low_gc_trans_preserves_wf_taint_bijection; eauto 2).
        destruct H'.
        * subst.
          replace (S (t1 + k3)) with (S t1 + k3) in * by omega.
          assert (~ contains_low_backat ℓ c'0) by eauto 2.
          assert (wf_taint_bijection ℓ (inverse (inverse Φ)) m2' h2').
          {
            rewrite <- inverse_is_involutive; eauto 2.
          }
          assert (c'0 ≲ [k3] c'0) by eauto 2.
          assert (taint_eq ℓ (inverse Φ) Γ Σ3 Σ2' c'0 c'0 s1' h0 m2' h2').
          {
            apply taint_eq_symmetry in H31.
            unfold taint_eq in *; super_destruct'; splits*.
          }
          remember_simple (offset_config_gives_taint_eq_bridge H35 H38 H54 H56 n H55 H48 H57 H58).
          super_destruct'; subst.
          invert_lack_behind.
          assert (pc''0 = pc''3).
          {
            eauto 2 using wt_aux_soundness_bridge.
          }
          subst.
          assert (wellformed_aux Γ Σ'0 ⟨Stop, pc''3, m''0, h''0, t''0⟩ pc''3).
          {
            eauto 2 using preservation_bridge_step.
          }
          assert (wellformed_aux Γ Σ2' ⟨c'0;; BackAt pc (v + (t1 + k3)), l, m2', h2', S t1 + k3⟩ pc_end).
          {
            eauto 2 using preservation.
          }
          remember_simple (wf_seq_half_step_implies_wf_bridge_step H65 H59).
          remember_simple (backat_bridge_properties H51 H49).
          remember_simple (backat_bridge_properties H50 H45).
          
          super_destruct; subst; try solve[exfalso; eauto 2].
          rename h0 into w2'.
          rename t1 into t2'.
          rename pc''3 into pc'.
          rename m''0 into s2'.
          rename h''0 into w3'.
          rename t''0 into t3'.
          rename h3 into h2.
          rename m2' into s2.
          rename h2' into w2.
          rename h''2 into w4'.
          rename t''2 into t4'.
          rename m'' into m3.
          rename h'' into h3.
          rename t'' into t3.
          rename h''1 into h4.
          rename t''1 into t4.
          replace (v + (t2' + k3)) with (v + t2' + k3) in * by omega.
          assert (~ pc' ⊑ ℓ).
          {
            eauto 2 using high_pc_and_no_low_backat_implies_high_pc_bridge_step.
          }
          assert (taint_eq ℓ Ψ Γ Σ'0 Σ2'0 (BackAt pc (v + t2')) (BackAt pc (v + t2' + k3)) s2' w3' s' w').
          {
            unfold taint_eq in *; super_destruct'; splits*.
          }
          remember_simple (emulate_gc_or_inc_many _ H67 H51 H66 H62 H63 H70 H71).
          super_destruct'; subst.
          exists (RestoreEvent pc t4).
          exists (S k0 + k2 + (n2 - k1 - 1 - k2 - 1) + 1).
          exists ψ (inverse Ψ0).
          exists s' w'0 Σ2'0.
          rewrite <- inverse_is_involutive.
          
          invert_step.
          invert_step.
          subst.
          assert (v = v0).
          {
            repeat invert_wf_aux.
            repeat specialize_gen.
            repeat invert_state_low_eq.
            invert_wt_cmd.
            cut (val_low_eq ℓ (SecType Int (ℓ', ∘)) (ValNum v0) (ValNum v) φ).
            {
              intros.
              invert_val_low_eq.
              - assert (ℓ' ⊑ ℓ) by eauto 2.
                contradiction.
              - reflexivity.
            }
            eauto 2 using eval_low_eq.
          }
          subst.

          remember_simple (high_pc_lemma n H55 H38 H59).
          super_destruct'; subst.
          
          splits; eauto 2.
          {
            replace (v0 + (t2' + k3)) with (v0 + t2' + k3) by omega.
            replace (S (t2' + k3)) with (S t2' + k3) by omega.
            eapply construct_at_bridge_step; eauto 2.
          }
          {
            assert (~ pc'' ⊑ ℓ).
            {
              eauto 2 using high_pc_and_no_low_backat_implies_high_pc_bridge_step.
            }
            assert (state_low_eq ℓ (identity_bijection loc) m3 h3 m3 h4 Γ Σ' Σ').
            {
              eauto 2 using high_gc_or_inc_many_preserves_state_low_eq.
            }
            remember_simple (high_pc_lemma n H55 H33 H44).
            super_destruct'; subst.
            assert (state_low_eq ℓ (identity_bijection loc) s' w' s' w'0 Γ Σ2'0 Σ2'0).
            {
              eauto 2 using high_gc_or_inc_many_preserves_state_low_eq.
            }

            assert (wellformed_aux Γ Σ' ⟨BackAt pc (v0 + (t2' + k3)), pc'', m3, h4, v0 + (t2' + k3)⟩ pc_end) by eauto 2.
            assert (wellformed_aux Γ Σ2'0 ⟨BackAt pc (v0 + t2' + k3), pc', s', w'0, v0 + t2' + k3⟩ pc_end) by eauto 2.

            assert (state_low_eq ℓ (identity_bijection loc) m3 h4 m1 h2 Γ Σ' Σ1).
            {
              rewrite <- (compose_id_right (identity_bijection loc)).
              repeat invert_wf_aux.
              eapply state_low_eq_trans with (m2 := m3) (h2 := h3) (Σ2 := Σ'); eauto 2.
              - rewrite <- inverse_identity_is_identity.
                apply state_low_eq_symmetry; eauto 2.
              - rewrite <- inverse_identity_is_identity.
                apply state_low_eq_symmetry; eauto 2.
            }
            
            assert (state_low_eq ℓ (identity_bijection loc) s' w'0 s2 w2 Γ Σ2'0 Σ2').
            {
              rewrite <- (compose_id_right (identity_bijection loc)).
              repeat invert_wf_aux.
              eapply state_low_eq_trans with (m2 := s') (h2 := w') (Σ2 := Σ2'0); eauto 2.
              - rewrite <- inverse_identity_is_identity.
                apply state_low_eq_symmetry; eauto 2.
              - rewrite <- inverse_identity_is_identity.
                apply state_low_eq_symmetry; eauto 2.
            }
            assert (state_low_eq ℓ ψ m3 h4 s2 w2 Γ Σ' Σ2').
            {
              rewrite <- (compose_id_left ψ).
              repeat invert_wf_aux.
              eapply state_low_eq_trans with (m2 := m1) (h2 := h2) (Σ2 := Σ1); eauto 2.
            }
            
            rewrite <- (compose_id_right ψ).
            repeat invert_wf_aux.
            eapply state_low_eq_trans with (m2 := s2) (h2 := w2) (Σ2 := Σ2'); eauto 2.
            rewrite <- (compose_id_right (identity_bijection loc)).
            eapply state_low_eq_trans with (m2 := s') (h2 := w') (Σ2 := Σ2'0); eauto 2.
          }
          { splits*. }
          {
            eapply high_gc_or_inc_many_preserves_wf_bijection; eauto 2.
            eapply high_pc_preserves_wf_bijection_bridge
            with (c := c'0) (pc := l) (m := m1) (h := h2) (t := S t2' + k3); eauto 2.
          }
          {
            splits; eauto 2.
            - eapply high_gc_or_inc_many_preserves_wf_bijection; eauto 2.
              eauto 2 using high_pc_preserves_wf_bijection_bridge.
            - unfold taint_eq in *; super_destruct'; splits*.
              eapply taint_eq_heap_size_sym; eauto 2.
          }
        * subst.
          replace (S (t0 + k3)) with (S t0 + k3) in * by omega.
          assert (~ contains_low_backat ℓ c'0) by eauto 2.
          assert (c'0 ≲ [k3] c'0) by eauto 2.
          assert (wf_taint_bijection ℓ (inverse (inverse Φ)) m2' h2').
          {
            rewrite <- inverse_is_involutive; eauto 2.
          }
          assert (c'0 ≲ [k3] c'0) by eauto 2.
          assert (taint_eq ℓ (inverse Φ) Γ Σ3 Σ2' c'0 c'0 s1' h0 m2' h2').
          {
            apply taint_eq_symmetry in H31.
            unfold taint_eq in *; super_destruct'; splits*.
          }
          remember_simple (offset_config_gives_taint_eq_bridge2 H35 H38 H54 H57 n H55 H48 H58 H59).
          super_destruct'; subst.
          invert_lack_behind.
          assert (pc''0 = pc''3).
          {
            eauto 2 using wt_aux_soundness_bridge.
          }
          subst.
          assert (wellformed_aux Γ Σ'0 ⟨Stop, pc''3, m''0, h''0, t''0⟩ pc''3).
          {
            idtac.
            eauto 2 using preservation_bridge_step.
          }
          idtac.
          assert (wellformed_aux Γ Σ2' ⟨c'0;; BackAt pc (v + t0), l, m2', h2', S t0⟩ pc_end).
          {
            eauto 2 using preservation.
          }
          idtac.
          remember_simple (wf_seq_half_step_implies_wf_bridge_step H67 H61).
          remember_simple (backat_bridge_properties H51 H49).
          remember_simple (backat_bridge_properties H50 H45).
          
          super_destruct; subst; try solve[exfalso; eauto 2].
          rename h0 into w2'.
          rename pc''3 into pc'.
          rename m''0 into s2'.
          rename h''0 into w3'.
          rename t''0 into t3'.
          rename h3 into h2.
          rename m2' into s2.
          rename h2' into w2.
          rename h''2 into w4'.
          rename t''2 into t4'.
          rename m'' into m3.
          rename h'' into h3.
          rename t'' into t3.
          rename h''1 into h4.
          rename t''1 into t4.
          replace (v + (t0 + k3)) with (v + t0 + k3) in * by omega.
          assert (~ pc' ⊑ ℓ).
          {
            eauto 2 using high_pc_and_no_low_backat_implies_high_pc_bridge_step.
          }
          
          replace t3' with (t3' - k3 + k3) in H69 by omega.
          replace t3' with (t3' - k3 + k3) in H51 by omega.

          assert (taint_eq ℓ Ψ Γ Σ'0 Σ2'0 (BackAt pc (v + t0 + k3)) (BackAt pc (v + t0)) s2' w3' s' w').
          {
            unfold taint_eq in *; super_destruct'; splits*.
          }
          
          remember_simple (emulate_gc_or_inc_many2 _ H69 H51 H68 H64 H65 H72 H73).
          super_destruct'; subst.
          exists (RestoreEvent pc t4).
          exists (S k0 + k2 + (n2 - k1 - 1 - k2 - 1) + 1).
          exists ψ (inverse Ψ0).
          exists s' w'0 Σ2'0.
          rewrite <- inverse_is_involutive.
          
          invert_step.
          invert_step.
          subst.
          assert (v = v0).
          {
            repeat invert_wf_aux.
            repeat specialize_gen.
            repeat invert_state_low_eq.
            invert_wt_cmd.
            cut (val_low_eq ℓ (SecType Int (ℓ', ∘)) (ValNum v0) (ValNum v) φ).
            {
              intros.
              invert_val_low_eq.
              - assert (ℓ' ⊑ ℓ) by eauto 2.
                contradiction.
              - reflexivity.
            }
            eauto 2 using eval_low_eq.
          }
          subst.
          remember_simple (high_pc_lemma n H55 H38 H61).
          super_destruct'; subst.
          
          splits; eauto 2.
          {
            replace (v0 + t0 + k3 - k3) with (v0 + t0) in H75 by omega.
            eapply construct_at_bridge_step; eauto 2.
          }
          {
            assert (~ pc'' ⊑ ℓ).
            {
              eauto 2 using high_pc_and_no_low_backat_implies_high_pc_bridge_step.
            }
            assert (state_low_eq ℓ (identity_bijection loc) m3 h3 m3 h4 Γ Σ' Σ').
            {
              eauto 2 using high_gc_or_inc_many_preserves_state_low_eq.
            }
            idtac.
            remember_simple (high_pc_lemma n H55 H33 H44).
            super_destruct'; subst.
            assert (state_low_eq ℓ (identity_bijection loc) s' w' s' w'0 Γ Σ2'0 Σ2'0).
            {
              eauto 2 using high_gc_or_inc_many_preserves_state_low_eq.
            }

            assert (wellformed_aux Γ Σ' ⟨BackAt pc (v0 + t0), pc'', m3, h4, v0 + t0⟩ pc_end) by eauto 2.
            assert (wellformed_aux Γ Σ2'0 ⟨BackAt pc (v0 + t0), pc', s', w'0, v0 + t0 + k3 - k3⟩ pc_end) by eauto 2.

            assert (state_low_eq ℓ (identity_bijection loc) m3 h4 m1 h2 Γ Σ' Σ1).
            {
              rewrite <- (compose_id_right (identity_bijection loc)).
              repeat invert_wf_aux.
              eapply state_low_eq_trans with (m2 := m3) (h2 := h3) (Σ2 := Σ'); eauto 2.
              - rewrite <- inverse_identity_is_identity.
                apply state_low_eq_symmetry; eauto 2.
              - rewrite <- inverse_identity_is_identity.
                apply state_low_eq_symmetry; eauto 2.
            }
            
            assert (state_low_eq ℓ (identity_bijection loc) s' w'0 s2 w2 Γ Σ2'0 Σ2').
            {
              rewrite <- (compose_id_right (identity_bijection loc)).
              repeat invert_wf_aux.
              eapply state_low_eq_trans with (m2 := s') (h2 := w') (Σ2 := Σ2'0); eauto 2.
              - rewrite <- inverse_identity_is_identity.
                apply state_low_eq_symmetry; eauto 2.
              - rewrite <- inverse_identity_is_identity.
                apply state_low_eq_symmetry; eauto 2.
            }
            assert (state_low_eq ℓ ψ m3 h4 s2 w2 Γ Σ' Σ2').
            {
              rewrite <- (compose_id_left ψ).
              repeat invert_wf_aux.
              eapply state_low_eq_trans with (m2 := m1) (h2 := h2) (Σ2 := Σ1); eauto 2.
            }
            
            rewrite <- (compose_id_right ψ).
            repeat invert_wf_aux.
            eapply state_low_eq_trans with (m2 := s2) (h2 := w2) (Σ2 := Σ2'); eauto 2.
            rewrite <- (compose_id_right (identity_bijection loc)).
            eapply state_low_eq_trans with (m2 := s') (h2 := w') (Σ2 := Σ2'0); eauto 2.
          }
          { splits*. }
          {
            eapply high_gc_or_inc_many_preserves_wf_bijection; eauto 2.
            eapply high_pc_preserves_wf_bijection_bridge
            with (c := c'0) (pc := l) (m := m1) (h := h2) (t := S t0); eauto 2.
          }
          {
            idtac.
            splits; eauto 2.
            - eapply high_gc_or_inc_many_preserves_wf_bijection; eauto 2.
              eauto 2 using high_pc_preserves_wf_bijection_bridge.
            - unfold taint_eq in *; super_destruct'; splits*.
              eapply taint_eq_heap_size_sym; eauto 2.
          }
  Qed.

  Lemma ni_bridge_num_backat_case:
    forall ℓ n1 Γ Σ1 Σ2 Σ3 Σ1' l k c' Σ3' φ Φ pc pc1' pc2'' c2 c2' m1 m2 s1 s2'' h1 h2
      w1 w2'' t t2 g2'' s1' w1' ev1 ev2 pc_end n2 t',
      (forall m : nat, m <= n1 -> ni_bridge m ℓ) ->
      wf_bijection ℓ φ Γ Σ1 m1 h1 ->
      wf_bijection ℓ (inverse φ) Γ Σ2 s1 w1 ->
      wf_taint_bijection ℓ Φ s1 w1 ->
      wf_taint_bijection ℓ (inverse Φ) s1' w1' ->
      wellformed_aux Γ Σ1 ⟨BackAt l k, pc, m1, h1, t⟩ pc_end ->
      wellformed_aux Γ Σ2 ⟨BackAt l k, pc, s1, w1, t⟩ pc_end ->
      wellformed_aux Γ Σ3 ⟨c', pc, s1', w1', t'⟩ pc_end ->
      state_low_eq ℓ φ m1 h1 s1 w1 Γ Σ1 Σ2 ->
      pc ⊑ ℓ ->
      taint_eq ℓ Φ Γ Σ2 Σ3 (BackAt l k) c' s1 w1 s1' w1' ->
      ⟨BackAt l k, pc, m1, h1, t⟩ ↷ [ℓ, Γ, Σ1, Σ1', ev1, S n1] ⟨c2, pc1', m2, h2, t2⟩ ->
      ⟨c', pc, s1', w1', t'⟩ ↷ [ℓ, Γ, Σ3, Σ3', ev2, n2] ⟨c2', pc2'', s2'', w2'', g2''⟩ ->
      c2 <> TimeOut ->
      c2' <> TimeOut ->
      exists ev1' n1' ψ Ψ s2' w2' Σ2',
        ⟨BackAt l k, pc, s1, w1, t⟩ ↷ [ℓ, Γ, Σ2, Σ2', ev1', n1'] ⟨c2, pc1', s2', w2', t2⟩ /\
        pc1' ⊑ ℓ /\
        pc2'' = pc1' /\
        state_low_eq ℓ ψ m2 h2 s2' w2' Γ Σ1' Σ2'/\
        event_low_eq ℓ (left ψ) ev1 ev1' /\
        taint_eq_events Γ Ψ ev1' ev2 /\
        wf_bijection ℓ ψ Γ Σ1' m2 h2 /\
        wf_bijection ℓ (inverse ψ) Γ Σ2' s2' w2' /\
        wf_taint_bijection ℓ Ψ s2' w2' /\
        wf_taint_bijection ℓ (inverse Ψ) s2'' w2'' /\
        taint_eq ℓ Ψ Γ Σ2' Σ3' c2 c2' s2' w2' s2'' w2''.
  Proof.
    intros.
    assert (H9' := H9).
    invert_taint_eq; invert_taint_eq_cmd.
    remember_simple (backat_bridge_properties H4 H10).
    remember_simple (backat_bridge_properties H6 H11).
    super_destruct; subst.
    - exfalso; eauto 2.
    - exfalso; eauto 2.
    - exfalso; eauto 2.
    - do 2 invert_step.
      remember_simple (construct_gc_or_inc_many H7 H14 H8 H4 H5 H0 H1).
      super_destruct'; subst.
      exists (RestoreEvent l t''0) (S n1) ψ Φ s1 w'; exists Σ2.
      splits; eauto 2.
      + eapply prepend_gc_or_inc; eauto 2.
      + invert_wf_aux.
        repeat specialize_gen.
        invert_wt_cmd.
        eauto 2.
      + splits*.
      + splits.
        * eauto 2.
        * eapply gc_or_inc_many_preserves_wf_taint_eq; eauto 2.
        * eapply gc_or_inc_many_preserves_wf_taint_eq; eauto 2.
        * remember_simple (low_gc_or_inc_many_preserves_taint_eq H5 H8 H23).
          remember_simple (low_gc_or_inc_many_preserves_taint_eq H6 H8 H21).
          apply taint_eq_symmetry in H27.
          rewrite -> inverse_identity_is_identity in H27.
          rewrite <- (compose_id_left Φ).
          eapply taint_eq_trans with (m' := s1) (h' := w1) (Σ' := Σ2).
          {
            repeat invert_wf_aux; eauto 2.
          }
          {
            unfold taint_eq in *; super_destruct'; splits*.
          }
          {
            rewrite <- (compose_id_right Φ).
            eapply taint_eq_trans with (m' := s1') (h' := w1') (Σ' := Σ3).
            - repeat invert_wf_aux; eauto 2.
            - unfold taint_eq in *; super_destruct'; splits*.
            - unfold taint_eq in *; super_destruct'; splits*.
          }    
  Qed.
  
End NIBridgeHelper.