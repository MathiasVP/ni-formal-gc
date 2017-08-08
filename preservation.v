Require Import mimperative mlattice language types mmemory id_and_loc Arith LibTactics tactics decision Coq.Program.Equality augmented low_equivalence List Coq.Program.Tactics.

Module Preservation (L : Lattice) (M : Memory L).
  Module LowEq := LowEquivalence L M.
  Import LowEq B Aug Imp TDefs M T MemProp LatProp Lang L.
  
  Ltac invert_var_typing :=
    match goal with
      [H: expr_has_type _ (Var _) _ |- _] =>
      inverts H
    end.

Lemma array_type_is_not_recursive:
  forall t l ℓ,
    SecType (Array t ℓ) l = t -> False.
Proof.
  apply (sectype_mut (fun t => forall l ℓ, Array (SecType t l) ℓ = t -> False)
                     (fun sect => forall l ℓ, SecType (Array sect ℓ) l = sect -> False)).
  - intros.
    discriminate.
  - intros.
    injects.
    eauto.
  - intros.
    injects.
    eauto.
Qed.

Lemma lookup_in_bounds_extend:
  forall x m h loc l n v H1 H2,
    (forall loc', v = ValLoc loc' -> reach m h loc') ->
    ~ reach m h loc ->
    dangling_pointer_free m h ->
    lookup_in_bounds m h ->
    lookup_in_bounds (extend_memory x (ValLoc loc) m) (h [loc → (n × v, l), H1, H2]).
Proof.
  intros.
  unfolds.
  intros.
  destruct (decide (loc0 = loc)); subst.
  - rewrite -> length_of_extend_eq in *.
    rewrite_inj.
    apply_heap_lookup_extend_eq.
    rewrite_inj.
    eauto.
  - rewrite -> length_of_extend_neq in * by solve[eauto].
    rewrite -> heap_lookup_extend_neq in * by solve[eauto 2].
    rewrite_inj.
    assert (reach m h loc0) by eauto 2 using reach_extend_implies_reach_if.
    eauto.
Qed.

Lemma wf_stenv_subset:
  forall Σ h1 h2 H,
    wf_stenv Σ ([h1 ⊎ h2, H]) -> wf_stenv Σ h1.
Proof.
  intros.
  unfold wf_stenv in *.
  intros.
  super_destruct'.
  splits*.
Qed.
Hint Resolve wf_stenv_subset.

Lemma reach_supset:
  forall m h1 h2 loc H,
    reach m h1 loc ->
    reach m ([h1 ⊎ h2, H]) loc.
Proof.
  intros.
  induction H0; eauto.

  Unshelve.
  - repeat constructor.
Qed.
Hint Resolve reach_supset.

Lemma reach_supset':
  forall m h1 h2 loc H,
    reach m h2 loc ->
    reach m ([h1 ⊎ h2, H]) loc.
Proof.
  intros.
  induction H0; eauto.

  specialize (IHreach H).
  assert (heap_lookup loc ([h1 ⊎ h, H]) = Some (ℓ, μ)).
  {
    rewrite -> disjoint_union_sym.
    eauto.
  }
  eauto.
  Unshelve.
  - repeat constructor.
Qed.
Hint Resolve reach_supset'.

Lemma consistent_subset_helper:
  forall m h1 h2 Γ Σ H,
    consistent m ([h1 ⊎ h2, H]) Γ Σ ->
    consistent m h1 Γ Σ /\ consistent m h2 Γ Σ.
Proof.
  intros.
  destruct_consistent.
  splits*.
  - unfolds.
    splits*.
  - unfolds.
    splits*.
    intros.
    eapply H1.
    + eauto.
    + eauto.
    + rewrite -> disjoint_union_sym by eauto.
      eauto.
    + eauto.

Qed.
Hint Resolve consistent_subset_helper.

Lemma consistent_subset:
  forall m h1 h2 Γ Σ H,
    consistent m ([h1 ⊎ h2, H]) Γ Σ ->
    consistent m h1 Γ Σ.
Proof.
  intros.
  edestruct consistent_subset_helper; eauto.
Qed.
Hint Resolve consistent_subset.

Lemma dangling_pointer_free_subset:
  forall m h1 h2 H,
    dangling_pointer_free m ([h1 ⊎ h2, H]) ->
    (forall loc ℓ μ,
        heap_lookup loc h2 = Some (ℓ, μ) -> ~ reach m ([h1 ⊎ h2, H]) loc) ->
    dangling_pointer_free m h1.
Proof.
  intros.
  unfolds.
  intros.
  assert (exists ℓ μ, heap_lookup loc ([h1 ⊎ h2, H]) = Some (ℓ, μ)) by eauto.
  super_destruct.
  exists ℓ μ.
  destruct (disjoint_union_heap_lookup2 h1 h2 loc ℓ μ _ H3).
  - eauto.
  - assert (~ reach m ([h1 ⊎ h2, H]) loc) by eauto.
    assert (reach m ([h1 ⊎ h2, H]) loc) by eauto using reach_supset.
    contradiction.
Qed.
Hint Resolve dangling_pointer_free_subset.

Lemma lookup_in_bounds_subset:
  forall m h1 h2 H,
    dangling_pointer_free m h1 ->
    lookup_in_bounds m ([h1 ⊎ h2, H]) ->
    (forall loc ℓ μ,
        heap_lookup loc h2 = Some (ℓ, μ) -> ~ reach m ([h1 ⊎ h2, H]) loc) ->
    lookup_in_bounds m h1.
Proof.
  intros.
  unfold lookup_in_bounds in *.
  intros.
  assert (exists ν, heap_lookup loc ([h1 ⊎ h2, H]) = Some (ℓ, ν)) by eauto.
  super_destruct.
  assert (exists v, lookup ν n = Some v) by eauto.
  super_destruct.
  exists v.
  super_destruct.
  destruct_disjoint_heap_lookup.
  + congruence.
  + assert (heap_lookup loc h1 = None).
    {
      eapply disjoint_union_heap_lookup3.
      - rewrite -> disjoint_union_sym.
        erewrite -> disjoint_union_proof_irrelevance.
        eauto.
        Unshelve.
        eauto.
      - eauto.
    }      
    match goal with
      [H: dangling_pointer_free _ _,
          H2: reach _ _ _ |- _] =>
      unfolds in H;
        specialize (H loc H2)
    end.
    destruct_exists.
    rewrite_inj.
    discriminate.
Qed.
Hint Resolve lookup_in_bounds_subset.

Lemma heap_level_bound_subset:
  forall m h1 h2 Γ Σ H,
    heap_level_bound Γ m ([h1 ⊎ h2, H]) Σ ->
    heap_level_bound Γ m h1 Σ.
Proof.
  intros.
  splits*.
Qed.
Hint Resolve heap_level_bound_subset.

Lemma reach_from_supset:
  forall x m h1 h2 loc H,
    reach_from x m h1 loc ->
    reach_from x m ([h1 ⊎ h2, H]) loc.
Proof.
  intros.
  unfold reach_from in *.
  super_destruct.
  eexists.
  dependent induction H0; eauto.
  specialize_gen; eauto.
Qed.
Hint Resolve reach_from_supset.

Lemma gc_preserves_wf:
  forall c pc pc' m h1 h2 h3 t Γ Σ δ H1 H2 H3,
    ([h1 ⊎ h3, H1]) ⇝ (m, δ) h1 ->
    disjoint ([h1 ⊎ h2, H2]) h3 ->
    (forall loc ℓ μ, heap_lookup loc h3 = Some (ℓ, μ) -> ~ reach m ([([h1 ⊎ h2, H2]) ⊎ h3, H3]) loc) ->
    wellformed_aux Γ Σ ⟨ c, pc, m, [([h1 ⊎ h2, H2]) ⊎ h3, H3], t ⟩ pc' ->
    wellformed_aux Γ Σ ⟨ c, pc, m, [h1 ⊎ h2, H2], t + δ ⟩ pc'.
Proof.
  intros.
  induction c; constructor; invert_wf_aux; eauto.
Qed.
Hint Resolve gc_preserves_wf.

Lemma location_is_from_lookup_simple:
  forall Γ level m e loc,
    wf_tenv Γ m ->
    {{Γ ⊢ e : level}} ->
    eval m e = Some (ValLoc loc) ->
    exists x,
      memory_lookup m x = Some (ValLoc loc) /\ e = Var x.
Proof.
  intros.
  assert (exists x, e = Var x) by eauto using location_is_from_lookup.
  super_destruct; subst.
  exists x.
  splits*.
Qed.
Hint Resolve location_is_from_lookup_simple.

Lemma var_exp_has_type_is_env_lookup:
  forall Γ x t,
    {{Γ ⊢ Var x : t}} ->
    Γ x = Some t.
Proof.
  intros.
  inverts H; eauto.
Qed.
Hint Resolve var_exp_has_type_is_env_lookup.

Lemma reach_update_with_num:
  forall m h loc1 loc2 n k,
    reach m (update_heap loc1 n (ValNum k) h) loc2 ->
    reach m h loc2.
Proof.
  intros.
  dependent induction H.
  - eauto.
  - destruct (decide (loc1 = loc)); subst.
    + assert (exists ν, heap_lookup loc h = Some (ℓ, ν) /\ μ = update_lookup ν n (ValNum k)) by eauto.
      super_destruct; subst.
      destruct (decide (n = n0)); subst.
      * rewrite -> lookup_update_eq in *.
        discriminate.
      * rewrite -> lookup_update_neq in * by solve[eauto].
        eauto.
    + rewrite -> heap_lookup_update_neq in * by solve[eauto].
      eauto.
      Unshelve.
      * constructor; eauto.
      * repeat constructor; eauto.
Qed.

Lemma reach_by_update_implies_reach_if:
  forall m h l n loc1 loc2,
    reach m (update_heap l n (ValLoc loc1) h) loc2 ->
    reach m h loc1 ->
    reach m h loc2.
Proof.
  intros.
  dependent induction H; eauto.
  - specialize_gen.
    specialize (IHreach _ _ _ eq_refl).
    destruct (decide (loc = l)); subst.
    + assert (exists ν, heap_lookup l h = Some (ℓ, ν) /\ μ = update_lookup ν n (ValLoc loc1))
        by eauto.
      super_destruct; subst.
      destruct (decide (n = n0)); subst.
      * rewrite -> lookup_update_eq in *.
        rewrite_inj.
        eauto.
      * rewrite -> lookup_update_neq in * by solve[eauto].
        eauto.
    + rewrite -> heap_lookup_update_neq in * by solve[eauto].
      eauto.
      Unshelve.
      * constructor; eauto.
      * repeat constructor; eauto.
Qed.

Lemma reach_extend2:
  forall m h x loc1 loc2 loc3 n ℓ μ,
    heap_lookup loc1 h = Some (ℓ, μ) ->
    lookup μ n = Some (ValLoc loc2) ->
    reach m h loc1 -> 
    reach (extend_memory x (ValLoc loc2) m) h loc3 -> reach m h loc3.
Proof.
  intros.
  dependent induction H2.
  - destruct (decide (x = x0)); subst.
    * rewrite -> extend_memory_lookup_eq in *.
      rewrite_inj.
      eauto.
    * rewrite -> extend_memory_lookup_neq in * by solve[eauto].
      eauto.
  - assert (reach m h loc) by eauto.
    eauto.

    Unshelve.
    + constructor; eauto.
    + repeat constructor; eauto.
    + constructor; eauto.
Qed.

Lemma reach_from_implies_array_type:
  forall Γ x t l m h loc,
    wf_tenv Γ m ->
    Γ x = Some (SecType t l) ->
    reach_from x m h loc ->
    exists s ℓ, t = Array s ℓ.
Proof.
  intros.
  unfold reach_from in *.
  super_destruct.
  revert loc H1.
  induction k; intros; subst.
  - inverts H0.
    inverts H1.
    destruct t; eauto.
    assert (exists n, ValLoc loc = ValNum n) by eauto.
    super_destruct; discriminate.
  - inverts H1.
    eauto.
Qed.
Hint Resolve reach_from_implies_array_type.

Lemma no_backat_implies_wt_aux_mono:
  forall Γ pc c pc',
    ~ contains_backat c ->
    wt_aux Γ pc c pc' ->
    pc = pc'.
Proof.
  intros.
  dependent induction H0; eauto 2.
  - firstorder.
    congruence.
  - exfalso; eauto 2.
Qed.
Hint Resolve no_backat_implies_wt_aux_mono.

Lemma preservation:
  forall tenv stenv stenv' c1 pc1 m1 h1 t1 c2 pc2 m2 h2 t2 pc',
    wellformed_aux tenv stenv (Config c1 pc1 m1 h1 t1) pc' ->
    step (Config c1 pc1 m1 h1 t1) (Config c2 pc2 m2 h2 t2) tenv stenv stenv' ->
    wellformed_aux tenv stenv' (Config c2 pc2 m2 h2 t2) pc'.
Proof.
  intros tenv stenv stenv' c1 pc1 m1 h1 t1.
  intros c2 pc2 m2 h2 t2 pc' H_wf H_step.
  revert pc' c2 pc2 m2 h2 t2 H_wf H_step.
  induction c1; intros; invert_step; subst; invert_wf_aux; subst.
  (* Skip *)
  - apply WellformedAux; intros; auto || (exfalso; eauto).
  - eapply gc_preserves_wf.
    + eauto.
    + eauto.
    + eauto.
    + erewrite -> disjoint_union_proof_irrelevance; eauto. 
  - eauto.
  (* Assign *)
  - assert ((i ::= e) <> Stop) by (intro H_absurd; discriminate H_absurd).
    do 2 specialize_gen.
    invert_wt_cmd.
    apply WellformedAux; eauto.
    + invert_lifted.
      rewrite_inj.
      eapply wf_tenv_extend with (t := σ); intros; (repeat subst); eauto.
    + unfolds.
      splits*.
      { intros.
        destruct (decide (i = x)); subst.
        - rewrite -> extend_memory_lookup_eq in *.
          rewrite_inj.
          assert (exists x, memory_lookup m1 x = Some (ValLoc loc) /\ e = Var x) by eauto 2.
          super_destruct'; subst.
          invert_var_typing.
          invert_lifted.
          eauto.
        - rewrite -> extend_memory_lookup_neq in * by solve[eauto].
          eauto 2.
      }
      {
        intros.
        destruct_consistent.
        destruct v.
        {
          assert (reach m1 h2 loc1) by eauto 2 using reach_extend_with_num.
          eauto.
        }
        {
          destruct (decide (l0 = loc1)); subst.
          - assert (exists x, memory_lookup m1 x = Some (ValLoc loc1) /\ e = Var x) by eauto.
            super_destruct; subst.
            eauto.
          - assert (exists x, memory_lookup m1 x = Some (ValLoc l0) /\ e = Var x) by eauto.
            super_destruct; subst.
            eauto.
        }
      }
    + intros; exfalso; eauto.
    + (* Show: New memory is free of dangling pointers *)
      unfolds.
      intros.
      invert_lifted.
      rewrite_inj.      
      invert_reach.
      * destruct (decide (i = x)); subst.
        {
          rewrite -> extend_memory_lookup_eq in *.
          rewrite_inj.
          match goal with
            [H: eval _ ?e = Some (ValLoc _) |- _] => destruct e
          end.
          - discriminate.
          - eauto.
          - assert (exists n, ValLoc loc = ValNum n)
              by eauto using eval_binop_is_num.
            destruct_exists.
            discriminate.
        }
        {
          rewrite -> extend_memory_lookup_neq in * by solve[eauto].
          eauto.
        }
      * unfold dangling_pointer_free in *.
        inverts H1.
        {
          destruct (decide (i = x)); subst.
          - rewrite -> extend_memory_lookup_eq in *.
            rewrite_inj.
            assert (exists x, memory_lookup m1 x = Some (ValLoc loc0) /\ e = Var x) by eauto.
            super_destruct; subst.
            eauto.
          - rewrite -> extend_memory_lookup_neq in * by solve[eauto].
            eauto.
        }
        {
          destruct v.
          - assert (reach m1 h2 loc) by eauto using reach_extend_with_num.
            eauto.
          - assert (exists x, memory_lookup m1 x = Some (ValLoc l) /\ e = Var x) by eauto.
            super_destruct; subst.
            destruct (decide (loc1 = l)); subst.
            + eauto.
            + assert (reach m1 h2 l) by eauto.
              eauto using reach_extend.
        }
    + invert_lifted.
      rewrite_inj.
      unfolds.
      intros.
      destruct v.
      * assert (reach m1 h2 loc) by eauto using reach_extend_with_num.
        eauto.
      * assert (exists x, memory_lookup m1 x = Some (ValLoc l) /\ e = Var x) by eauto.
        super_destruct; subst.
        destruct (decide (loc = l)); subst; eauto using reach_extend.
    + unfolds.
      splits; eauto 2.
      intros.
      invert_lifted.
      rewrite_inj.
      destruct (decide (i = x)); subst.
      * rewrite -> extend_memory_lookup_eq in *.
        rewrite_inj.
        assert (exists x, memory_lookup m1 x = Some (ValLoc loc) /\ e = Var x) by eauto.
        super_destruct'; subst.
        invert_var_typing.
        eauto 2.
      * rewrite -> extend_memory_lookup_neq in * by solve[eauto].
        eauto 2.
      * intros.
        invert_lifted.
        destruct σ.
        { assert (exists n, v = ValNum n) by eauto.
          super_destruct'; subst.
          eauto using reach_extend_with_num.
        }
        { assert (exists loc, v = ValLoc loc) by eauto.
          super_destruct'; subst.
          destruct (decide (loc0 = loc)); subst.
          - assert (exists x, memory_lookup m1 x = Some (ValLoc loc) /\ e = Var x) by eauto.
            super_destruct; subst.
            eauto.
          - rewrite_inj.
            assert (reach m1 h2 loc).
            {
              eapply reach_extend.
              - eapply H0.
              - assert (exists x, memory_lookup m1 x = Some (ValLoc loc0) /\ e = Var x) by eauto.
                super_destruct; subst.
                eauto.
            }
            eauto 3.
        }
      * intros.
        invert_lifted.
        rewrite_inj.
        destruct σ.
        {
          assert (exists n, v = ValNum n) by eauto.
          super_destruct; subst.
          assert (reach m1 h2 loc1) by eauto 3 using reach_extend_with_num.
          eauto.
        }
        {
          assert (exists loc, v = ValLoc loc) by eauto.
          super_destruct; subst.
          assert (exists x, memory_lookup m1 x = Some (ValLoc loc) /\ e = Var x) by eauto.
          super_destruct; subst.
          assert (reach m1 h2 loc1).
          {
            eapply reach_extend.
            - eapply H0.
            - eauto.
          }
          eauto.
        }
  - eapply gc_preserves_wf.
    + eauto.
    + eauto.
    + eauto.
    + erewrite -> disjoint_union_proof_irrelevance; eauto.
  - (* If *)
    assert ((If e c1_1 c2) <> Stop) by congruence.
    assert ((If e c1_1 c2) <> TimeOut) by congruence.
    do 2 specialize_gen.
    invert_wt_cmd.
    apply WellformedAux; intros; eauto.
  - assert ((If e c2 c1_2) <> Stop) by congruence.
    assert ((If e c2 c1_2) <> TimeOut) by congruence.
    do 2 specialize_gen.
    invert_wt_cmd.
    apply WellformedAux; intros; eauto.
  - eapply gc_preserves_wf.
    + eauto.
    + eauto.
    + eauto.
    + erewrite -> disjoint_union_proof_irrelevance; eauto 2.
  - (* While *)
    assert ((While e c1) <> Stop) by congruence.
    assert ((While e c1) <> TimeOut) by congruence.
    do 2 specialize_gen.
    invert_wt_cmd.
    apply WellformedAux; try assumption.
    intros; exfalso; eauto.
  - assert ((While e c1) <> Stop) by congruence.
    assert ((While e c1) <> TimeOut) by congruence.
    do 2 specialize_gen.
    invert_wt_cmd.
    apply WellformedAux; intros; try assumption.
    apply (wt_aux_seq tenv pc' pc' pc'); eauto.
  - eapply gc_preserves_wf.
    + eauto.
    + eauto.
    + eauto.
    + erewrite -> disjoint_union_proof_irrelevance; eauto.
  (* Sequencing *)
  - assert ((c1_1;; c2) <> Stop) by congruence.
    assert ((c1_1;; c2) <> TimeOut) by congruence.
    do 2 specialize_gen.
    invert_wt_cmd.
    assert (pc2 = pc'0).
    {      
      eauto 3 using wt_aux_soundness.
    }
    subst.
    assert (exists pc1', wellformed_aux tenv stenv ⟨c1_1, pc1, m1, h1, t1⟩ pc1') by eauto.
    super_destruct; subst.
    assert (wellformed_aux tenv stenv' ⟨STOP, pc'0, m2, h2, t2⟩ pc1') by eauto.
    destruct_exists.
    invert_wf_aux.
    apply WellformedAux; intros; eauto.
  - assert ((c1_1 ;; c1_2) <> Stop) by congruence.
    assert ((c1_1 ;; c1_2) <> TimeOut) by congruence.
    do 2 specialize_gen. 
    clear H.
    invert_wt_cmd.
    assert (wellformed_aux tenv stenv ⟨c1_1, pc1, m1, h1, t1⟩ pc'0) by eauto.
    assert (wellformed_aux tenv stenv' ⟨c1', pc2, m2, h2, t2⟩ pc'0) by eauto.
    destruct_exists.
    invert_wf_aux.
    apply WellformedAux; intros; try assumption.
    + repeat specialize_gen.
      eapply wt_aux_seq; eauto.
  - eapply gc_preserves_wf.
    + eauto.
    + eauto.
    + eauto.
    + erewrite -> disjoint_union_proof_irrelevance; eauto.
  (* At *)
  - apply WellformedAux; intros; try assumption.
    assert (At pc2 e c1 <> Stop) by congruence.
    assert (At pc2 e c1 <> TimeOut) by congruence.    
    do 2 specialize_gen.
    invert_wt_cmd.
    eapply wt_aux_seq.
    + eauto.
    + assert (pc2 = ℓ'') by eauto 2 using no_backat_implies_wt_aux_mono.
      subst.
      constructors; eauto 2 using flowsto_refl.
  - eapply gc_preserves_wf.
    + eauto.
    + eauto.
    + eauto.
    + erewrite -> disjoint_union_proof_irrelevance; eauto.
  (* Backat with wait *)
  - apply WellformedAux; eauto. 
  (* Backat with progress *)
  - assert (BackAt pc2 t1 <> Stop) by congruence.
    assert (BackAt pc2 t1 <> TimeOut) by congruence.
    do 2 specialize_gen.
    clear H.
    invert_wt_cmd.
    apply WellformedAux; eauto.
    intro; exfalso; eauto.
  - assert (BackAt pc2 t1 <> Stop) by congruence.
    assert (BackAt pc2 t1 <> TimeOut) by congruence.
    do 2 specialize_gen.
    constructor; eauto 2.
    intros.
    exfalso; eauto 2.
  - eapply gc_preserves_wf.
    + eauto.
    + eauto.
    + eauto.
    + erewrite -> disjoint_union_proof_irrelevance; eauto.
  (* new *)
  - let H1 := fresh in let H2 := fresh in
    assert (NewArr i l e e0 <> Stop) as H1 by congruence;
      assert (NewArr i l e e0 <> TimeOut) as H2 by congruence;
      do 2 specialize_gen;
      clear H1; clear H2.
    invert_wt_cmd.
    rewrite_inj.
    apply WellformedAux; eauto.
    + destruct τ0 as [σ ℓ].
      eapply wf_tenv_extend; eauto.
      intro; discriminate.
    + destruct τ0 as [σ ℓ].
      eapply wf_stenv_extend; intros; subst; eauto.   
    + unfolds.
      splits.
      * intros.
        destruct (decide (i = x)); subst.
        {
          rewrite -> extend_memory_lookup_eq in *.
          rewrite_inj.
          unfold extend_stenv.
          rewrite -> eq_loc.
          rewrite_inj.
          reflexivity.
        }
        {
          rewrite -> extend_memory_lookup_neq in * by solve[eauto].
          destruct (decide (l1 = loc)); subst.
          - invert_dang_free; eauto.
            assert (exists ℓ μ, heap_lookup loc h1 = Some (ℓ, μ)) by eauto.
            destruct_exists.
            rewrite_inj.
            discriminate.
          - unfold extend_stenv.
            rewrite -> neq_loc by eauto.
            destruct_consistent.
            eauto.
        }
      * intros.
        destruct (decide (loc1 = l1)); subst.
        {
          rewrite -> extend_stenv_lookup_eq in *.
          apply_heap_lookup_extend_eq.
          assert (v = ValLoc loc2).
          {
            match goal with
              [H1: forall _, lookup _ _ = Some _,
               H2: lookup _ ?n = Some _ |- _] =>
              specialize (H1 n)
            end.
            rewrite_inj.
            reflexivity.
          }
          subst.
          rewrite_inj.
          assert (exists y, memory_lookup m1 y = Some (ValLoc loc2) /\ e0 = Var y) by eauto.
          super_destruct; subst.
          assert (exists ℓ μ, heap_lookup loc2 h1 = Some (ℓ, μ)) by eauto.
          super_destruct.
          rewrite_inj.
          assert (l1 <> loc2).
          {
            intro.
            subst.
            rewrite_inj.
            discriminate.
          }
          rewrite -> extend_stenv_lookup_neq by solve[eauto].
          eauto.
        }
        {
          rewrite -> extend_stenv_lookup_neq in * by solve[eauto].
          rewrite -> heap_lookup_extend_neq in * by solve[eauto 2].
          destruct (decide (l1 = loc2)); subst.
          - assert (~ reach m1 h1 loc2).
            {
              intro.
              assert (exists ℓ μ, heap_lookup loc2 h1 = Some (ℓ, μ)) by eauto.
              super_destruct.
              rewrite_inj.
              discriminate.
            }
            assert (~ reach m1 h1 loc1).
            {
              intro.
              eauto.
            }
            assert (forall loc' : loc, v = ValLoc loc' -> reach m1 h1 loc').
            {
              intros; subst.
              assert (exists x, memory_lookup m1 x = Some (ValLoc loc') /\ e0 = Var x) by eauto.
              super_destruct; subst.
              eauto.
            }
            match goal with
              [H: ~ reach _ _ loc1 |- _] =>
              contradict H
            end.
            eauto 2 using reach_extend_implies_reach_if.
          - rewrite -> extend_stenv_lookup_neq by solve[eauto].
            destruct_consistent.
            assert (forall loc' : loc, v = ValLoc loc' -> reach m1 h1 loc').
            {
              intros; subst.
              assert (exists x, memory_lookup m1 x = Some (ValLoc loc') /\ e0 = Var x) by eauto.
              super_destruct; subst.
              eauto.
            }
            assert (~ reach m1 h1 l1).
            {
              intro.
              assert (exists l μ, heap_lookup l1 h1 = Some (l, μ)) by eauto.
              super_destruct; subst.
              rewrite_inj.
              discriminate.
            }
            assert (reach m1 h1 loc1) by eauto 2 using reach_extend_implies_reach_if.
            eauto.
        }
    + (* Show: Stop is Welltyped *)
      intro.
      exfalso; eauto.
      
    + (* Show: Dangling free memory and heap *)
      unfolds.
      intros.
      destruct (decide (l1 = loc)); subst.
      * assert (exists μ,
                   heap_lookup loc (h1 [loc → (n × v, l), H1, H2]) = Some (l, μ) /\
                   (forall n0 : nat, lookup μ n0 = Some v)) by eauto.
        super_destruct; subst.
        eauto.
      * assert (forall loc' : id_and_loc.loc, v = ValLoc loc' -> reach m1 h1 loc').
        {
          intros; subst.
          assert (exists x, memory_lookup m1 x = Some (ValLoc loc') /\ e0 = Var x) by eauto.
          super_destruct; subst.
          eauto.
        }
        assert (loc <> l1) by eauto.
        assert (~ reach m1 h1 l1).
        {
          intro.
          assert (exists l μ, heap_lookup l1 h1 = Some (l, μ)) by eauto.
          super_destruct; subst.
          rewrite_inj.
          discriminate.
        }
        assert (reach m1 h1 loc) by eauto 2 using reach_extend_implies_reach_if.
        destruct_consistent.
        rewrite -> heap_lookup_extend_neq by solve[eauto].
        eauto.      
    + eapply lookup_in_bounds_extend; eauto 2.
      * intros; subst.
        assert (exists x, memory_lookup m1 x = Some (ValLoc loc') /\ e0 = Var x) by eauto.
        super_destruct; subst.
        eauto.
      * intro.
        assert (exists l μ, heap_lookup l1 h1 = Some (l, μ)) by eauto.
        super_destruct; subst.
        rewrite_inj.
        discriminate.
    + unfolds.
      splits.
      * intros.
        destruct (decide (i = x)); subst.
        {
          rewrite -> extend_memory_lookup_eq in *.
          rewrite_inj.
          apply_heap_lookup_extend_eq.
          rewrite_inj.
          reflexivity.
        }
        {
          rewrite -> extend_memory_lookup_neq in * by solve[eauto].
          destruct (decide (loc = l1)); subst.
          - edestruct (heap_lookup_extend_eq l1 l n v h1); eauto 2.
            super_destruct.
            rewrite_inj.
            invert_dang_free.
            assert (exists ℓ μ, heap_lookup l1 h1 = Some (ℓ, μ)) by eauto.
            destruct_exists.
            rewrite_inj.
            discriminate.
          - rewrite -> heap_lookup_extend_neq in * by solve[eauto].
            eauto 2.
        }
      * intros.
        destruct (decide (loc = l1)); subst.
        {
          rewrite -> extend_stenv_lookup_eq in *.
          rewrite_inj.
          apply_heap_lookup_extend_eq.
          rewrite_inj.
          destruct (decide (loc' = l1)); subst.
          - rewrite_inj.
            assert (v = ValLoc l1) by congruence.
            subst.
            assert (exists x, memory_lookup m1 x = Some (ValLoc l1) /\ e0 = Var x) by eauto.
            super_destruct'; subst.
            assert (reach m1 h1 l1) by eauto.
            assert (exists l μ, heap_lookup l1 h1 = Some (l, μ)) by eauto.
            super_destruct; subst.
            congruence.
          - rewrite -> heap_lookup_extend_neq in * by solve[eauto].
            assert (exists loc, v = ValLoc loc) by eauto.
            super_destruct'; subst.
            assert (exists x, memory_lookup m1 x = Some (ValLoc loc) /\ e0 = Var x) by eauto.
            super_destruct; subst.
            invert_var_typing.
            assert (loc = loc') by congruence; subst.
            symmetry.
            eauto 2.
        }
        {
          rewrite -> heap_lookup_extend_neq in * by solve[eauto].
          rewrite -> extend_stenv_lookup_neq in * by solve[eauto].
          destruct (decide (loc' = l1)); subst.
          - apply_heap_lookup_extend_eq.
            rewrite_inj.
            assert (~ reach m1 h1 l1).
            {
              intro.
              assert (exists l μ, heap_lookup l1 h1 = Some (l, μ)) by eauto.
              super_destruct; congruence.
            }
            assert (reach m1 h1 loc).
            {
              assert (forall loc', v = ValLoc loc' -> reach m1 h1 loc').
              {
                intros; subst.
                assert (exists x, memory_lookup m1 x = Some (ValLoc loc') /\ e0 = Var x) by eauto.
                super_destruct; subst.
                eauto.
              }              
              eapply reach_extend_implies_reach_if; eauto.
            }
            assert (reach m1 h1 l1) by eauto 2.
            contradiction.
          - rewrite -> heap_lookup_extend_neq in * by solve[eauto].
            assert (~ reach m1 h1 l1).
            {
              intro.
              assert (exists l μ, heap_lookup l1 h1 = Some (l, μ)) by eauto.
              super_destruct; congruence.
            }
            assert (reach m1 h1 loc).
            {
              assert (forall loc', v = ValLoc loc' -> reach m1 h1 loc').
              {
                intros; subst.
                assert (exists x, memory_lookup m1 x = Some (ValLoc loc'0) /\ e0 = Var x) by eauto.
                super_destruct; subst.
                eauto.
              }              
              eapply reach_extend_implies_reach_if; eauto.
            }
            eauto 2.
        }
      * intros.
        destruct (decide (loc1 = l1)); subst.
        {
          apply_heap_lookup_extend_eq.
          rewrite_inj.
          destruct (decide (loc2 = l1)); subst.
          - rewrite_inj.
            eapply flowsto_refl.
          - rewrite -> heap_lookup_extend_neq in * by solve[eauto].
            assert (wf_type bot (SecType (Array τ0 l) (ℓ_x, ∘))) by eauto.
            invert_wf_type.
            assert (v = ValLoc loc2) by congruence; subst.
            assert (exists x, memory_lookup m1 x = Some (ValLoc loc2) /\ e0 = Var x) by eauto.
            super_destruct; subst.
            invert_var_typing.
            destruct τ0 as [τ ε].
            assert (exists t, τ = Array t ℓ2).
            {
              destruct τ.
              - assert (exists n, ValLoc loc2 = ValNum n) by eauto.
                super_destruct; congruence.
              - exists s.
                eapply f_equal2; eauto 2.
            }
            super_destruct'; subst.
            invert_wf_type.
            eauto.
        }
        {
          rewrite -> heap_lookup_extend_neq in * by solve[eauto].
          assert (reach m1 h1 loc1).
          {
            assert (~ reach m1 h1 l1).
            {
              intro.
              assert (exists l μ, heap_lookup l1 h1 = Some (l, μ)) by eauto.
              super_destruct; congruence.
            }
            assert (forall loc' : loc, v = ValLoc loc' -> reach m1 h1 loc').
            {
              intros; subst.
              assert (exists x, memory_lookup m1 x = Some (ValLoc loc') /\ e0 = Var x) by eauto.
              super_destruct; subst.
              eauto.
            }
            eapply reach_extend_implies_reach_if; eauto.
          }
          destruct (decide (loc2 = l1)); subst.
          - apply_heap_lookup_extend_eq.
            rewrite_inj.            
            assert (reach m1 h1 l1) by eauto 2.
            assert (exists l μ, heap_lookup l1 h1 = Some (l, μ)) by eauto.
            super_destruct; subst.
            congruence.
          - rewrite -> heap_lookup_extend_neq in * by solve[eauto].
            eauto 2.
        }
  - eapply gc_preserves_wf.
    + eauto.
    + eauto.
    + eauto.
    + erewrite -> disjoint_union_proof_irrelevance; eauto.
  (* Set array *)
  - let H1 := fresh in let H2 := fresh in
      assert (SetArr i e e0 <> Stop) as H1 by congruence;
        assert (SetArr i e e0 <> TimeOut) as H2 by congruence;
      do 2 specialize_gen;
      clear H1; clear H2.
    apply WellformedAux; eauto.
    + unfolds.
      intros.
      splits~.
      * intros.
        destruct (decide (loc = l0)); subst.
        {
          _apply heap_lookup_update_eq2 in *.
          super_destruct; subst.

          destruct (decide (n0 = n)); subst.
          - rewrite -> lookup_update_eq in *.
            rewrite_inj.
            invert_wt_cmd.
            invert_lifted.
            assert (σ = Int).
            {
              match goal with
                [H: consistent _ _ _ _,
                    H2: stenv' _ = Some _ |- _] =>
                destruct H as [H _];
                  erewrite -> H in H2; eauto
              end.
              rewrite_inj.
              reflexivity.
            }
            subst.
            eauto.
          - rewrite -> lookup_update_neq in * by solve[eauto].
            eauto.
        }
        {
          assert (heap_lookup loc (update_heap l0 n v h1) = heap_lookup loc h1) by (apply heap_lookup_update_neq; assumption).
          rewrite -> heap_lookup_update_neq in * by solve[eauto].
          rewrite_inj.
          eauto.
        }
      * intros.
        destruct (decide (loc = l0)); subst.
        {
          _apply heap_lookup_update_eq2 in *; eauto 2.
          destruct_exists.
          super_destruct; subst.
          destruct (decide (n0 = n)); subst.
          - assert (heap_lookup l0 h1 <> None).
            {
              intro.
              assert (exists ℓ μ, heap_lookup l0 h1 = Some (ℓ, μ)) by eauto.
              super_destruct; congruence.
            }
            rewrite -> lookup_update_eq in *.
            rewrite_inj.
            assert (SetArr i e e0 <> Stop) by (intro H_absurd; discriminate H_absurd).
            invert_wt_cmd.
            invert_lifted.            
            assert (exists ℓ, σ = Array t ℓ).
            {
              match goal with
                [H: consistent _ _ _ _,
                    H2: stenv' _ = Some _ |- _] =>
                destruct H as [H _];
                  erewrite -> H in H2; eauto
              end.
              rewrite_inj.
              eauto.
            }
            super_destruct; subst.
            eauto using wt_array_e_is_loc.
          - rewrite -> lookup_update_neq in *; eauto 2.
        }
        {
          rewrite -> heap_lookup_update_neq in * by solve[eauto].
          eauto.
        }
      * eauto.
      * intros.
        destruct (decide (loc = l0)); subst.
        {
          _apply heap_lookup_update_eq2 in *.
          super_destruct; eauto 2.
        }
        {
          rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
          eauto 2.
        }
    + unfolds.
      splits~; eauto 2.
      intros.
      destruct (decide (loc1 = l0)); subst.
      * destruct (decide (n0 = n)); subst.
        {
          _apply heap_lookup_update_eq2 in *.
          destruct_exists.
          super_destruct; subst.
          rewrite -> lookup_update_eq in *.
          rewrite_inj.
          invert_wt_cmd.
          invert_lifted.
          edestruct location_is_from_lookup; eauto; subst.
          repeat match goal with
                   [H: expr_has_type _ (Var _) _ |- _] =>
                   inverts H
                 | [H: eval _ (Var _) = _ |- _] =>
                   inverts H
                 end.
          invert_dang_free.
          assert (exists ℓ μ, heap_lookup loc2 h1 = Some (ℓ, μ)) by eauto.
          match goal with
            [H: consistent _ _ _ _ |- _] =>
            destruct H as [H _]; erewrite -> H in * by eauto
          end.
          rewrite_inj.
          eauto.
        }
        {
          _apply heap_lookup_update_eq2 in *.
          super_destruct.
          subst.
          rewrite -> lookup_update_neq in * by solve[eauto 2].
          destruct_consistent; eauto.
        }
      * invert_wt_cmd.
        invert_lifted.
        rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
        destruct_consistent.
        destruct v.
        {
          eauto using reach_update_with_num.
        }
        {
          assert (exists x, memory_lookup m2 x = Some (ValLoc l1) /\ e0 = Var x) by eauto.
          super_destruct; subst.
          destruct (decide (l0 = loc1)); subst.
          - eauto.
          - invert_var_typing.
            assert (reach m2 h1 loc1).
            {
              eapply reach_by_update_implies_reach_if; eauto.
            }
            assert (reach m2 h1 l0) by eauto. 
            eauto.
        }
    + intro; exfalso; eauto.
    + unfolds.
      intros.
      inverts H.
      * assert (exists ℓ μ, heap_lookup loc h1 = Some (ℓ, μ)) by (invert_dang_free; eauto).
        destruct_exists.
        destruct (decide (loc = l0)); subst.
        {
          eauto.
        }
        {
          rewrite -> heap_lookup_update_neq by solve[eauto].
          eauto.
        }
      * destruct (decide (loc0 = l0)); subst.
        {
          destruct (decide (n0 = n)); subst.
          - _apply heap_lookup_update_eq2 in *; eauto 2.
            destruct_exists.
            super_destruct; subst.
            rewrite -> lookup_update_eq in *.
            rewrite_inj.        
            invert_wt_cmd.
            + assert (exists x, memory_lookup m2 x = Some (ValLoc loc) /\ e0 = Var x) by eauto.
              super_destruct; subst.
              invert_var_typing.
              destruct (decide (loc = l0)); subst.
              * eauto.
              * rewrite -> heap_lookup_update_neq by solve[eauto].
                eauto.
          - assert (exists ν, heap_lookup l0 h1 = Some (ℓ, ν) /\ μ = update_lookup ν n v) by eauto.
            super_destruct; subst.
            rewrite -> lookup_update_neq in * by solve[eauto].
            destruct (decide (loc = l0)); subst.
            {
              eauto.
            }
            {
              rewrite -> heap_lookup_update_neq by eauto 2.
              eauto.
            }
        }
        {
          rewrite -> heap_lookup_update_neq in * by solve[eauto].
          assert (reach m2 h1 l0) by eauto.
          destruct (decide (loc = l0)); subst.
          - assert (exists ℓ μ, heap_lookup l0 h1 = Some (ℓ, μ)) by eauto.
            super_destruct; subst.
            eauto.
          - rewrite -> heap_lookup_update_neq by solve[eauto].
            assert (reach m2 h1 loc0).
            {
              destruct v.
              - eauto using reach_update_with_num.
              - invert_wt_cmd;
                  assert (exists x, memory_lookup m2 x = Some (ValLoc l) /\ e0 = Var x)
                    by eauto;
                  super_destruct; subst;
                    eauto 3 using reach_by_update_implies_reach_if.
            }
            eauto.
        } 
    + unfolds.
      intros.
      destruct (decide (loc = l0)); subst.
      * rewrite -> length_of_update in *.
        destruct (decide (n0 = n)); subst.
        {
          exists v.      
          assert (reach m2 h1 l0) by eauto.
          assert (exists ℓ μ, heap_lookup l0 h1 = Some (ℓ, μ)) by eauto.
          super_destruct; subst.
          rewrite_inj.
          _apply heap_lookup_update_eq2 in *.
          super_destruct; subst.
          eauto.
        }
        {
          _apply heap_lookup_update_eq2 in *.
          super_destruct; subst.
          rewrite -> lookup_update_neq by solve[eauto 2].
          eauto.
        }
      * rewrite -> heap_lookup_update_neq in * by solve[eauto 2].
        rewrite -> length_of_update in *.
        unfold lookup_in_bounds in *.
        assert (reach m2 h1 l0) by eauto.
        destruct v.
        {
          eauto using reach_update_with_num.
        }
        {
          invert_wt_cmd.
          assert (exists x, memory_lookup m2 x = Some (ValLoc l) /\ e0 = Var x)
            by eauto.
          super_destruct; subst.
          invert_var_typing.
          assert (reach m2 h1 l) by eauto.
          assert (reach m2 h1 loc) by eauto 2 using reach_by_update_implies_reach_if.
          eauto.
        }
    + unfolds.
      splits~.
      * intros.
        destruct (decide (loc = l0)); subst.
        {
          assert (exists ν, heap_lookup l0 h1 = Some (l2, ν) /\ μ = update_lookup ν n v)
            by eauto.
          super_destruct; subst.
          eauto 2.
        }
        {
          rewrite -> heap_lookup_update_neq in * by solve[eauto].
          eauto 2.
        }
      * intros.
        assert (exists μ, heap_lookup loc' h1 = Some (ℓ', μ)).
        {
          destruct (decide (loc' = l0)); subst.
          - assert (exists ν0, heap_lookup l0 h1 = Some (ℓ', ν0) /\ ν = update_lookup ν0 n v) by eauto.
            super_destruct; subst.
            eauto.
          - rewrite -> heap_lookup_update_neq in * by solve[eauto].
            eauto.
        }
        assert (reach m2 h1 loc).
        {
          destruct v.
          - eauto using reach_update_with_num.
          - assert (reach m2 h1 l0) by eauto.
            invert_wt_cmd.
            assert (exists x, memory_lookup m2 x = Some (ValLoc l1) /\ e0 = Var x) by eauto.
            super_destruct; subst.
            eapply reach_by_update_implies_reach_if; eauto 2.
        }
        
        destruct (decide (loc = l0)); subst.
        {
          assert (exists ν, heap_lookup l0 h1 = Some (ℓ, ν) /\ μ = update_lookup ν n v)
            by eauto.
          super_destruct; subst.
          destruct (decide (n = n0)); subst.
          - rewrite -> lookup_update_eq in *.
            rewrite_inj.
            invert_wt_cmd.
            assert (exists x, memory_lookup m2 x = Some (ValLoc loc') /\ e0 = Var x) by eauto.
            super_destruct; subst.
            invert_var_typing.
            invert_lifted.
            assert (exists τ, σ = Array τ ℓ').
            {
              destruct σ.
              - assert (exists n, ValLoc loc' = ValNum n) by eauto.
                super_destruct; discriminate.
              - exists s0.
                eapply f_equal2; eauto 2.
            }
            super_destruct; subst.
            assert (stenv' loc' = Some τ) by eauto.
            rename l3 into ε_arr.
            assert (ℓ0 = ℓ) by eauto 2; subst.
            assert (stenv' l0 = Some (SecType (Array τ ℓ') ε_arr)) by eauto.
            rewrite_inj.
            reflexivity.
          - rewrite -> lookup_update_neq in * by solve[eauto].
            eauto 2.
        }
        {
          rewrite -> heap_lookup_update_neq in * by solve[eauto].
          super_destruct; subst.
          eauto 2.
        }
      * intros.
        
        assert (exists μ, heap_lookup loc2 h1 = Some (ℓ2, μ)).
        {
          destruct (decide (loc2 = l0)); subst.
          - assert (exists ν0, heap_lookup l0 h1 = Some (ℓ2, ν0) /\ ν = update_lookup ν0 n v) by eauto.
            super_destruct; subst.
            eauto.
          - rewrite -> heap_lookup_update_neq in * by solve[eauto].
            eauto.
        }
        destruct (decide (loc1 = l0)); subst.
        {
          assert (exists ν, heap_lookup l0 h1 = Some (ℓ1, ν) /\ μ = update_lookup ν n v) by eauto.
          super_destruct; subst.
          destruct (decide (n = n0)); subst.
          - rewrite -> lookup_update_eq in *.
            rewrite_inj.
            invert_wt_cmd.
            assert (exists x, memory_lookup m2 x = Some (ValLoc loc2) /\ e0 = Var x) by eauto.
            super_destruct; subst.
            invert_var_typing.
            invert_lifted.
            assert (exists τ, σ = Array τ ℓ2).
            {
              destruct σ.
              - assert (exists n, ValLoc loc2 = ValNum n) by eauto.
                super_destruct; discriminate.
              - exists s.
                eapply f_equal2; eauto 2.
            }
            super_destruct; subst.
            assert (ℓ = ℓ1) by eauto 2; subst.
            assert (stenv' l0 = Some (SecType (Array τ ℓ2) l2)) by eauto.
            assert (wf_type bot (SecType (Array (SecType (Array τ ℓ2) l2) ℓ1) ε_x)) by eauto.
            do 2 invert_wf_type.
            eauto.
          - rewrite -> lookup_update_neq in * by solve[eauto].
            eauto 3.
        }
        {
          rewrite -> heap_lookup_update_neq in * by solve[eauto].
          super_destruct; subst.
          assert (reach m2 h1 loc1).
          {
            destruct v; eauto 3 using reach_update_with_num.
            assert (reach m2 h1 l).
            {
              invert_wt_cmd.
              assert (exists x, memory_lookup m2 x = Some (ValLoc l) /\ e0 = Var x) by eauto.
              super_destruct; subst.
              eauto.
            }
            eapply reach_by_update_implies_reach_if; eauto 3.
          }
          eauto 2.
        }
  - eapply gc_preserves_wf.
    + eauto.
    + eauto.
    + eauto.
    + erewrite -> disjoint_union_proof_irrelevance; eauto.
  - do 2 specialize_gen.
    apply WellformedAux; eauto.
    + invert_wt_cmd.
      invert_lifted.
      rewrite_inj.
      eapply wf_tenv_extend; eauto.
      * intros; subst.
        eauto.
      * intros; subst.
        eauto.
    + invert_wt_cmd.
      invert_lifted.
      unfold consistent.
      splits.
      * intros.
        destruct (decide (i = x)); subst.
        {
          rewrite -> extend_memory_lookup_eq in *.
          rewrite_inj.
          destruct_consistent.
          eauto.
        }
        {
          rewrite -> extend_memory_lookup_neq in * by solve[eauto].
          eauto.
        }
      * intros.
        assert (reach m1 h2 loc1).
        {
          destruct v.
          - eauto 2 using reach_extend_with_num.
          - assert (reach m1 h2 l0) by eauto.
            assert (reach m1 h2 l0) by eauto 3.
            eapply reach_extend2 with (loc1 := l0).
            + eauto
            + match goal with
                [H: lookup _ _ = Some (ValLoc l1) |- _] =>
                eapply H
              end.
            + eauto.
            + eauto.
            + eauto.
        }
        destruct_consistent.
        eauto.
    + intro; exfalso; eauto.
    + unfolds.
      intros.
      destruct v.
      * eauto using reach_extend_with_num.
      * assert (reach m1 h2 l0) by eauto 3.
        eauto using reach_extend2.
    + unfolds.
      intros.
      destruct v.
      * eauto using reach_extend_with_num.
      * assert (reach m1 h2 l) by eauto 3.
        assert (reach m1 h2 loc) by eauto 2 using reach_extend2.
        eauto.
    + unfolds.
      splits~.
      * intros.
        destruct (decide (i = x)); subst.
        {
          rewrite -> extend_memory_lookup_eq in *.
          rewrite_inj.
          invert_wt_cmd.
          invert_lifted.
          rewrite_inj.
          assert (ℓ0 = ℓ) by eauto 2.
          rewrite_inj.
          subst.
          rewrite_inj.
          assert (reach m1 h2 l0) by eauto.
          assert (stenv' l0 = Some (SecType (Array s l1) ε0)) by eauto.
          destruct ε0 as [l3 ι].
          symmetry.
          eauto 3.
        }
        {
          rewrite -> extend_memory_lookup_neq in * by solve[eauto].
          eauto 2.
        }
      * intros.
        assert (reach m1 h2 loc).
        {
          destruct v; eauto 2 using reach_extend_with_num.
          assert (reach m1 h2 l0) by eauto.
          assert (reach m1 h2 l1).
          {
            eauto 2.
          }
          eauto 3.
        }
        eauto 3.
      * intros.
        assert (reach m1 h2 loc1).
        {
          destruct v; eauto 2 using reach_extend_with_num.
          assert (reach m1 h2 l0) by eauto.
          assert (reach m1 h2 l) by eauto 2.
          eauto 3.
        }
        eauto 3.
  - eapply gc_preserves_wf.
    + eauto.
    + eauto.
    + eauto.
    + erewrite -> disjoint_union_proof_irrelevance; eauto.
  - let H1 := fresh in let H2 := fresh in
    assert (Time i <> Stop) as H1 by congruence;
      assert (Time i <> TimeOut) as H2 by congruence;
      do 2 specialize_gen;
      clear H1; clear H2.
    apply WellformedAux; try eauto 2.
    + invert_wt_cmd.
      rewrite_inj.
      eapply wf_tenv_extend; eauto.
      * intros; subst.
        discriminate.
    + invert_wt_cmd.
      unfolds.
      splits.
      * intros.
        destruct (decide (i = x)); subst.
        {
          rewrite -> extend_memory_lookup_eq in *.
          discriminate.
        }
        {
          rewrite -> extend_memory_lookup_neq in * by solve[eauto].
          eauto.
        }
      * intros.
        destruct_consistent.
        eauto using reach_extend_with_num.
    + intro; exfalso; eauto.
    + unfolds.
      intros.
      assert (reach m1 h2 loc) by eauto 2 using reach_extend_with_num.
      eauto.
    + unfolds.
      intros.
      assert (reach m1 h2 loc) by eauto 2 using reach_extend_with_num.
      eauto.
    + unfolds.
      splits; eauto 3 using reach_extend_with_num.
      intros.
      destruct (decide (i = x)); subst.
      * rewrite -> extend_memory_lookup_eq in *.
        discriminate.
      * rewrite -> extend_memory_lookup_neq in * by solve[eauto].
        eauto 2 using reach_extend_with_num.
  - eapply gc_preserves_wf.
    + eauto.
    + eauto.
    + eauto.
    + erewrite -> disjoint_union_proof_irrelevance; eauto.
  - eapply gc_preserves_wf.
    + eauto.
    + eauto.
    + eauto.
    + erewrite -> disjoint_union_proof_irrelevance; eauto.

      Unshelve.
      * repeat constructor; eauto.
      * repeat constructor; eauto.
      * eauto.
      * eauto.
Qed.

End Preservation.