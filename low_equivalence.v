Require Import id_and_loc augmented mmemory mimperative language mlattice bridge types bijection Coq.Program.Tactics Coq.Program.Equality Arith Omega tactics FunctionalExtensionality decision List.
Require Import LibTactics Setoid.
Set Implicit Arguments.

Module LowEquivalence(L: Lattice) (M: Memory L).
  Module B := Bridge L M.
  Import B Aug Imp TDefs M T MemProp LatProp Lang L.

  Lemma onvals_sym:
    forall u v φ,
      onvals (left φ) v = Some u <->
      onvals (right φ) u = Some v.
  Proof.
    intros.
    destruct u eqn:H_u; subst.
    - destruct v eqn:H_v; subst.
      + unfold onvals in *.
        rewrite_inj.
        splits*.
      + splits; intros; unfold onvals in *.
        * destruct (left φ l); discriminate.
        * discriminate.
    - splits; intros.
      + destruct v eqn:H_v; subst; unfold onvals in *.
        * discriminate.
        * destruct (left φ l0) eqn:H_l1; try discriminate.
          rewrite_inj.
          assert (right φ l = Some l0) by (destruct φ; eauto).
          decide_exist.
          reflexivity.
      + unfold onvals in *.
        * destruct v eqn:H_v; subst.
          { destruct (right φ l); discriminate. }
          { destruct (right φ l) eqn:H_l; try discriminate.
            rewrite_inj.
            assert (left φ l0 = Some l) by (destruct φ; eauto).
            decide_exist.
            reflexivity.
          }
  Qed.
  Hint Resolve onvals_sym.

  Lemma onvals_sym1:
    forall u v φ,
      onvals (left φ) v = Some u ->
      onvals (right φ) u = Some v.
  Proof.
    intros.
    eapply onvals_sym; eauto.
  Qed.
  Hint Resolve onvals_sym1.

  Lemma onvals_sym2:
    forall u v φ,
      onvals (right φ) v = Some u ->
      onvals (left φ) u = Some v.
  Proof.
    intros.
    eapply onvals_sym; eauto.
  Qed.
  Hint Resolve onvals_sym2.
  

  Lemma low_reach_implies_reach:
    forall ℓ Γ Σ m h loc,
      low_reach ℓ Γ Σ m h loc ->
      reach m h loc.
  Proof.
    intros.
    dependent induction H; eauto.

    Unshelve.
    - constructor; eauto.
  Qed.
  Hint Resolve low_reach_implies_reach.
    
  Ltac invert_low_reach :=
    match goal with
      [H: low_reach _ _ _ _ _ _ |- _] =>
      inverts H
    end.

  Inductive reach_from_loc: Memory -> Heap -> loc -> loc -> Prop :=
    ReachFromLocRefl:
      forall m h loc,
        reach_from_loc m h loc loc
  | ReachFromLocTrans:
      forall m h loc1 loc2 loc3 μ ℓ n,
        reach_from_loc m h loc1 loc2 ->
        heap_lookup loc2 h = Some (ℓ, μ) ->
        lookup μ n = Some (ValLoc loc3) ->
        reach_from_loc m h loc1 loc3.
  Hint Constructors reach_from_loc.
  
  Inductive low : level_proj1 -> tenv -> stenv -> Memory -> Heap -> loc -> Prop :=
  | LowReachable:
      forall ℓ_adv m h loc Γ Σ,
        low_reach ℓ_adv Γ Σ m h loc ->
        low ℓ_adv Γ Σ m h loc
  | LowHeapLevel:
      forall ℓ_adv m h loc Γ Σ ℓ μ,
        heap_lookup loc h = Some (ℓ, μ) ->
        ℓ ⊑ ℓ_adv ->
        low ℓ_adv Γ Σ m h loc.
  Hint Constructors low.

  Ltac destruct_low :=
    match goal with
      [H: low _ _ _ _ _ _ |- _] =>
      dependent destruction H
    end.

  Lemma low_dec:
    forall ℓ_adv Γ Σ m h loc,
      { low ℓ_adv Γ Σ m h loc} + { ~ low ℓ_adv Γ Σ m h loc }.
  Proof.
    intros.
    destruct (low_reach_dec ℓ_adv Γ Σ m h loc); eauto.
    destruct (heap_lookup loc h) eqn:H_loc.
    - destruct p.
      destruct (flowsto_dec l ℓ_adv); eauto.
      right.
      intro.
      destruct_low.
      + contradiction.
      + congruence.
    - right.
      intro.
      destruct_low.
      + contradiction.
      + congruence.
  Qed.
  Hint Resolve low_dec.

  
Lemma low_left:
  forall (T : Type)
    (p q : T)
    ℓ_adv Γ Σ m h loc,
    low ℓ_adv Γ Σ m h loc ->
    (if low_dec ℓ_adv Γ Σ m h loc then p else q) = p.
Proof.
  intros.
  destruct (low_dec ℓ_adv Γ Σ m h loc) eqn:H_loc.
  - reflexivity.
  - contradiction.
Qed.

  Lemma low_right:
    forall (T : Type)
      (p q : T)
      ℓ_adv Γ Σ m h loc,
      ~ low ℓ_adv Γ Σ m h loc ->
      (if low_dec ℓ_adv Γ Σ m h loc then p else q) = q.
  Proof.
    intros.
    destruct (low_dec ℓ_adv Γ Σ m h loc) eqn:H_loc.
    - contradiction.
    - reflexivity.
  Qed.
  
  Definition low_eq_stenv (ℓ_adv : level_proj1) (φ: bijection loc loc) (m1 m2 : Memory) (h1 h2 : Heap) (Γ : tenv) (Σ1 Σ2 : stenv) :=
    forall loc1 loc2 τ,
      left φ loc1 = Some loc2 ->
      (Σ1 loc1 = Some τ /\ low ℓ_adv Γ Σ1 m1 h1 loc1) <->
      (Σ2 loc2 = Some τ /\ low ℓ_adv Γ Σ2 m2 h2 loc2).
  Hint Unfold low_eq_stenv.

  Definition wf_bijection ℓ_adv (φ : bijection loc loc) Γ Σ m h :=
    forall loc,
      (exists loc', left φ loc = Some loc') <-> low ℓ_adv Γ Σ m h loc.
  Hint Unfold wf_bijection.  
  
  Lemma low_eq_stenv_refl:
    forall ℓ_adv Γ Σ m h,
      low_eq_stenv ℓ_adv (identity_bijection loc) m m h h Γ Σ Σ.
  Proof.
    intros.
    unfolds.
    intros.
    unfold left, identity_bijection in *.
    rewrite_inj.
    splits*.
  Qed.
  Hint Resolve low_eq_stenv_refl.
  
  Lemma low_eq_stenv_symmetry:
    forall φ ℓ_adv Γ Σ1 Σ2 m1 m2 h1 h2,
      low_eq_stenv ℓ_adv φ m1 m2 h1 h2 Γ Σ1 Σ2 ->
      low_eq_stenv ℓ_adv (inverse φ) m2 m1 h2 h1 Γ Σ2 Σ1.
  Proof.
    intros.
    unfold low_eq_stenv in *.
    intros.
    assert (left φ loc2 = Some loc1) by (destruct φ; eauto).
    eauto using iff_sym.
  Qed.
  Hint Resolve low_eq_stenv_symmetry.

  Lemma low_eq_stenv_trans:
    forall ℓ_adv φ ψ m1 m2 m3 h1 h2 h3 Γ Σ1 Σ2 Σ3,
      low_eq_stenv ℓ_adv φ m1 m2 h1 h2 Γ Σ1 Σ2 ->
      low_eq_stenv ℓ_adv ψ m2 m3 h2 h3 Γ Σ2 Σ3 ->
      low_eq_stenv ℓ_adv (bijection_compose φ ψ) m1 m3 h1 h3 Γ Σ1 Σ3.
  Proof.
    intros.
    unfold low_eq_stenv in *.
    intros.
    edestruct (left_compose φ ψ); eauto.
    super_destruct'.
    rename loc2 into loc3.
    destruct x as [loc2 | ]; subst.
    - assert (left ψ loc2 = Some loc3) by eauto.
      erewrite -> H by solve[eauto].
      erewrite -> H0 by solve[eauto].
      reflexivity.
    - repeat specialize_gen.
      discriminate.
  Qed.

  Definition low_heap_domain_eq (ℓ_adv : level_proj1) (φ: bijection loc loc)
             (m1 m2 : Memory) (h1 h2 : Heap) (Γ : tenv) (Σ1 Σ2 : stenv) :=
    forall l1 l2 ℓ,
      left φ l1 = Some l2 ->
      ((exists μ, heap_lookup l1 h1 = Some (ℓ, μ)) /\ low ℓ_adv Γ Σ1 m1 h1 l1)
      <->
      ((exists ν, heap_lookup l2 h2 = Some (ℓ, ν)) /\ low ℓ_adv Γ Σ2 m2 h2 l2).
  Hint Unfold low_heap_domain_eq.

  Lemma low_heap_domain_eq_proj1:
    forall ℓ_adv φ h1 h2 l1 l2 ℓ μ m1 m2 Γ Σ1 Σ2,
      low_heap_domain_eq ℓ_adv φ m1 m2 h1 h2 Γ Σ1 Σ2 ->
      left φ l1 = Some l2 ->
      heap_lookup l1 h1 = Some (ℓ, μ) ->
      low ℓ_adv Γ Σ1 m1 h1 l1 ->
      exists ν, heap_lookup l2 h2 = Some (ℓ, ν).
  Proof.
    intros.
    eapply H; eauto.
  Qed.
  Hint Resolve low_heap_domain_eq_proj1.

  Lemma low_heap_domain_eq_proj2:
    forall ℓ_adv φ h1 h2 l1 l2 ℓ μ m1 m2 Γ Σ1 Σ2,
      low_heap_domain_eq ℓ_adv φ m1 m2 h1 h2 Γ Σ1 Σ2 ->
      left φ l1 = Some l2 ->
      low ℓ_adv Γ Σ2 m2 h2 l2 ->
      heap_lookup l2 h2 = Some (ℓ, μ) ->
      exists ν, heap_lookup l1 h1 = Some (ℓ, ν).
  Proof.
    intros.
    eapply H; eauto.
  Qed.
  Hint Resolve low_heap_domain_eq_proj2.
  
  Lemma low_heap_domain_eq_refl:
    forall ℓ_adv Γ Σ m h,
      low_heap_domain_eq ℓ_adv (identity_bijection loc) m m h h Γ Σ Σ.
  Proof.
    intros.
    unfolds.
    intros.
    unfold left, identity_bijection in *.
    rewrite_inj.
    splits*.
  Qed.
  Hint Resolve low_heap_domain_eq_refl.

  Lemma low_heap_domain_eq_sym:
    forall ℓ_adv φ m1 m2 h1 h2 Γ Σ1 Σ2,
      low_heap_domain_eq ℓ_adv φ m1 m2 h1 h2 Γ Σ1 Σ2 ->
      low_heap_domain_eq ℓ_adv (inverse φ) m2 m1 h2 h1 Γ Σ2 Σ1.
  Proof.
    intros.
    unfold low_heap_domain_eq in *.
    intros.
    assert (left φ l2 = Some l1) by (destruct φ; eauto).
    eauto using iff_sym.
  Qed.
  Hint Resolve low_heap_domain_eq_sym.

  Lemma low_heap_domain_eq_trans:
    forall ℓ_adv φ ψ m1 m2 m3 h1 h2 h3 Γ Σ1 Σ2 Σ3,
      low_heap_domain_eq ℓ_adv φ m1 m2 h1 h2 Γ Σ1 Σ2 ->
      low_heap_domain_eq ℓ_adv ψ m2 m3 h2 h3 Γ Σ2 Σ3 ->
      low_heap_domain_eq ℓ_adv (bijection_compose φ ψ) m1 m3 h1 h3 Γ Σ1 Σ3.
  Proof.
    intros.
    unfolds.
    intros.
    _apply left_compose in *.
    super_destruct.
    destruct my; try solve[repeat specialize_gen; discriminate].
    rename l2 into l3.
    rename l into l2.
    eapply iff_trans.
    - eapply H; eauto.
    - eapply H0; eauto.
  Qed.
  Hint Resolve low_heap_domain_eq_trans.      
  
  Lemma low_reach_extend_mem_with_num:
    forall ℓ Γ Σ x n m h loc,
      low_reach ℓ Γ Σ (extend_memory x (ValNum n) m) h loc ->
      low_reach ℓ Γ Σ m h loc.
  Proof.
    intros.
    dependent induction H; eauto.
    destruct (decide (x = x0)); subst.
    - rewrite -> extend_memory_lookup_eq in *.
      discriminate.
    - rewrite -> extend_memory_lookup_neq in * by solve[eauto].
      now eauto.
  Qed.

  Lemma wf_bijection_proj1:
    forall loc loc' φ ℓ_adv Γ Σ m h,
      wf_bijection ℓ_adv φ Γ Σ m h ->
      left φ loc = Some loc' ->
      low ℓ_adv Γ Σ m h loc.
  Proof.
    intros.
    eapply H; eauto.
  Qed.
  Hint Resolve wf_bijection_proj1.

  Lemma wf_bijection_proj2:
    forall loc φ ℓ_adv Γ Σ m h,
      wf_bijection ℓ_adv φ Γ Σ m h ->
      low ℓ_adv Γ Σ m h loc ->
      exists loc', left φ loc = Some loc'.
  Proof.
    intros.
    eapply H; eauto.
  Qed.
  Hint Resolve wf_bijection_proj2.
  
  Lemma bijection_implies_in_heap:
    forall loc loc' φ ℓ_adv Γ Σ m h,
      wf_bijection ℓ_adv φ Γ Σ m h ->
      left φ loc = Some loc' ->
      dangling_pointer_free m h ->
      exists ℓ μ, heap_lookup loc h = Some (ℓ, μ).
  Proof.
    intros.
    assert (low ℓ_adv Γ Σ m h loc) by eauto.
    destruct H2; eauto.
  Qed.
  Hint Resolve bijection_implies_in_heap.


  Definition low_domain_eq (ℓ : level_proj1) (Γ : tenv) (m s : Memory) :=
    (forall x t l ι,
        Γ x = Some (SecType t (l, ι)) ->
        l ⊑ ℓ ->
        (exists v, memory_lookup m x = Some v) <->
        (exists u, memory_lookup s x = Some u)).
  Hint Unfold low_domain_eq.

  Ltac destruct_low_domain_eq :=
    match goal with
      [H: low_domain_eq _ _ _ _ _ _ _ |- _] =>
      destruct H
    end.
  
  Lemma low_domain_eq_refl:
    forall ℓ Γ m,
      low_domain_eq ℓ Γ m m.
  Proof.
    intros.
    unfolds.
    intros.
    splits*.
  Qed.
  Hint Resolve low_domain_eq_refl.
  
  Lemma low_domain_eq_symmetry:
    forall ℓ Γ m s,
      low_domain_eq ℓ Γ m s ->
      low_domain_eq ℓ Γ s m.
  Proof.
    intros.
    unfold low_domain_eq in *.
    intros.
    splits.
    - intros.
      erewrite -> H; eauto.
    - intros.
      erewrite <- H; eauto.
  Qed.
  Hint Resolve low_domain_eq_symmetry.

  Lemma low_domain_eq_trans:
    forall ℓ Γ m1 m2 m3,
      low_domain_eq ℓ Γ m1 m2 ->
      low_domain_eq ℓ Γ m2 m3 ->
      low_domain_eq ℓ Γ m1 m3.
  Proof.
    intros.
    unfold low_domain_eq in *.
    super_destruct.
    intros.
    splits.
    - intros.
      rewrite <- H0 by eauto.
      rewrite <- H by eauto.
      eauto.
    - rewrite -> H by eauto.
      rewrite -> H0 by eauto.
      eauto.
  Qed.

  Ltac eapply_low_domain_eq :=
    match goal with
      [H: low_domain_eq _ _ _ _ |- _] =>
      eapply H
    end.

  Inductive val_low_eq: level_proj1 -> sectype -> value -> value -> bijection loc loc -> Prop :=
  | ValNumLowEqH:
      forall ℓ_adv ℓ n1 n2 φ ι,
        not (ℓ ⊑ ℓ_adv) -> val_low_eq ℓ_adv (SecType Int (ℓ, ι)) (ValNum n1) (ValNum n2) φ
  | ValLocLowEqH:
      forall ℓ_adv ℓ l1 l2 φ τ ι ℓ_p,
        not (ℓ ⊑ ℓ_adv) -> val_low_eq ℓ_adv (SecType (Array τ ℓ_p) (ℓ, ι)) (ValLoc l1) (ValLoc l2) φ
  | ValNumLowEqL:
      forall ℓ_adv ℓ n φ ι,
        ℓ ⊑ ℓ_adv ->
        val_low_eq ℓ_adv (SecType Int (ℓ, ι)) (ValNum n) (ValNum n) φ
  | ValLocLowEqL:
      forall ℓ_adv ℓ φ τ l1 l2 ℓ_p ι,
        ℓ ⊑ ℓ_adv ->
        left φ l1 = Some l2 ->
        val_low_eq ℓ_adv (SecType (Array τ ℓ_p) (ℓ, ι)) (ValLoc l1) (ValLoc l2) φ.
  Hint Constructors val_low_eq.

  Lemma val_low_eq_symmetry:
    forall ℓ τ v1 v2 φ,
      val_low_eq ℓ τ v1 v2 φ ->
      val_low_eq ℓ τ v2 v1 (inverse φ).
  Proof.
    intros.
    destruct φ.
    inverts H; eauto.
  Qed.
  Hint Resolve val_low_eq_symmetry.

  Ltac invert_val_low_eq := 
    match goal with
      [H: context[val_low_eq] |- _] => inverts H
    end.

  Lemma val_low_eq_num_refl:
    forall ℓ_adv l n,
      val_low_eq ℓ_adv (SecType Int l) (ValNum n) (ValNum n)
                 (identity_bijection loc).
  Proof.
    intros.
    destruct l as [l ι].
    destruct (flowsto_dec l ℓ_adv); eauto.
  Qed.
  Hint Resolve val_low_eq_num_refl.

  Lemma val_low_eq_loc_refl:
    forall ℓ_adv s loc0 ℓ_p ε,
      val_low_eq ℓ_adv (SecType (Array s ℓ_p) ε) (ValLoc loc0) (ValLoc loc0)
                 (identity_bijection loc).
  Proof.
    intros.
    destruct ε as [ℓ ι].
    destruct (flowsto_dec ℓ ℓ_adv); eauto.
  Qed.
  Hint Resolve val_low_eq_loc_refl.

  Lemma val_low_eq_trans:
    forall ℓ τ v1 v2 v3 φ ψ,
      val_low_eq ℓ τ v1 v2 φ ->
      val_low_eq ℓ τ v2 v3 ψ ->
      val_low_eq ℓ τ v1 v3 (bijection_compose φ ψ).
  Proof.
    intros.
    destruct τ.
    destruct t.
    - inverts H; inverts H0; eauto.
    - inverts H.
      + invert_val_low_eq; eauto.
      + invert_val_low_eq.
        * contradiction.
        * apply ValLocLowEqL; eauto.
  Qed.

  Definition memory_lookup_low_eq ℓ Γ m1 m2 φ :=
    (forall x τ v1 v2,
        Γ x = Some τ ->
        memory_lookup m1 x = Some v1 ->
        memory_lookup m2 x = Some v2 ->
        val_low_eq ℓ τ v1 v2 φ).
  Hint Unfold memory_lookup_low_eq.

  Lemma val_low_eq_plus:
    forall ℓ l a1 a2 b1 b2 φ,
      val_low_eq ℓ (SecType Int l) (ValNum a1) (ValNum a2) φ ->
      val_low_eq ℓ (SecType Int l) (ValNum b1) (ValNum b2) φ ->
      val_low_eq ℓ (SecType Int l) (ValNum (a1 + b1)) (ValNum (a2 + b2)) φ.
  Proof.
    intros.
    destruct l as [l ι].
    destruct (flowsto_dec l ℓ).
    - invert_val_low_eq; invert_val_low_eq; contradiction || eauto.
    - eauto.
  Qed.

  Lemma val_low_eq_mult:
    forall ℓ l a1 a2 b1 b2 φ,
      val_low_eq ℓ (SecType Int l) (ValNum a1) (ValNum a2) φ ->
      val_low_eq ℓ (SecType Int l) (ValNum b1) (ValNum b2) φ ->
      val_low_eq ℓ (SecType Int l) (ValNum (a1 * b1)) (ValNum (a2 * b2)) φ.
  Proof.
    intros.
    destruct l as [l ι].
    destruct (flowsto_dec l ℓ).
    - invert_val_low_eq; invert_val_low_eq; contradiction || eauto.
    - eauto.
  Qed.

  Lemma val_low_eq_mon:
    forall ℓ τ l1 v1 v2 φ l2,
      val_low_eq ℓ (SecType τ l1) v1 v2 φ ->
      l1 ≼ l2 ->
      val_low_eq ℓ (SecType τ l2) v1 v2 φ.
  Proof.
    intros.
    destruct l1 as [l1 ι1].
    destruct l2 as [l2 ι2].
    invert_val_low_eq.
    - eauto.
    - eauto.
    - destruct (flowsto_dec l2 ℓ); eauto 2.
    - destruct (flowsto_dec l2 ℓ); eauto 2.
  Qed.
  Hint Resolve val_low_eq_mon.
  
  Lemma eval_low_eq:
    forall e φ m1 m2 Γ ℓ τ v u,
      wf_tenv Γ m1 ->
      wf_tenv Γ m2 ->
      memory_lookup_low_eq ℓ Γ m1 m2 φ ->
      expr_has_type Γ e τ ->
      eval m1 e = Some v ->
      eval m2 e = Some u ->
      val_low_eq ℓ τ v u φ.
  Proof.
    intros.
    revert v u τ H1 H2 H3 H4.
    induction e; intros; subst.
    (* e = n *)
    {
      do 2 invert_eval.
      invert_wt_expr.
      destruct l0 as [l0 ι].
      destruct (flowsto_dec l0 ℓ); intros; eauto.
    }
    (* e = x *)
    {
      do 2 invert_eval.
      invert_wt_expr.
      eauto.
    }
    (* e = e1 op e2 *)
    {
      invert_wt_expr.
      match goal with
        [H1: eval m1 (BinOp ?o ?e1 ?e2) = Some ?v,
             H2: eval m2 (BinOp ?o ?e1 ?e2) = Some ?u |- _] =>
        destruct (unfold_eval_binop m1 o e1 e2 v H1) as [v1 [v2 [H_v1 H_v2]]];
          destruct (unfold_eval_binop m2 o e1 e2 u H2) as [u1 [u2 [H_u1 H_u2]]]
      end.
      assert (val_low_eq ℓ (SecType Int l1) v1 u1 φ) by eauto.
      assert (val_low_eq ℓ (SecType Int l2) v2 u2 φ) by eauto.
      
      edestruct (wt_int_e_is_num Γ m1 e1 v1); eauto; subst.
      edestruct (wt_int_e_is_num Γ m1 e2 v2); eauto; subst.
      edestruct (wt_int_e_is_num Γ m2 e1 u1); eauto; subst.
      edestruct (wt_int_e_is_num Γ m2 e2 u2); eauto; subst.
      rewrite -> about_eval in *.
      repeat decide_exist in *.

      destruct l1 as [l1 ι1].
      destruct l2 as [l2 ι2].
      rewrite -> ProdL.join_is_pairwise.
      destruct o; subst; rewrite_inj.
      - destruct (flowsto_dec (l1 ⊔ l2) ℓ); subst.
        + eapply val_low_eq_plus; eapply val_low_eq_mon; eauto.
          * rewrite <- ProdL.join_is_pairwise.
            eapply ProdLatProp.flowsto_join.
          * rewrite <- ProdL.join_is_pairwise.
            rewrite -> ProdL.join_symmetry.
            eapply ProdLatProp.flowsto_join.
        + eauto.  
      - destruct (flowsto_dec (l1 ⊔ l2) ℓ); subst.
        + eapply val_low_eq_mult; eapply val_low_eq_mon; eauto.
          * rewrite <- ProdL.join_is_pairwise.
            eapply ProdLatProp.flowsto_join.
          * rewrite <- ProdL.join_is_pairwise.
            rewrite -> ProdL.join_symmetry.
            eapply ProdLatProp.flowsto_join.
        + eauto.
    }
  Qed.
  Hint Resolve eval_low_eq.

  Lemma new_low_reach_implies_flowsto_low:
    forall Γ x t ℓ ℓ_x ℓ_adv l n v m h loc Σ ℓ_p H1 H2,
      Γ x = Some (SecType (Array (SecType t ℓ) ℓ_p) (ℓ_x, ∘)) ->
      dangling_pointer_free m h ->
      (forall s ℓ, t = Array s ℓ -> exists loc', v = ValLoc loc' /\ reach m h loc') ->
      (t = Int -> exists n, v = ValNum n) ->
      low_reach ℓ_adv Γ Σ
                (m [x → ValLoc loc])
                (h [loc → (n × v, l), H1, H2]) loc ->
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
          eapply reach_extend_implies_reach_if with (v := v).
          - intros; subst.
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

  Lemma low_reach_extend_implies_low_reach_if:
    forall m h loc1 loc2 x v n Γ Σ ℓ_adv ℓ ι ℓ_p σ H1 H2,
      (forall s ℓ', σ = Array s ℓ' -> exists loc',
            v = ValLoc loc' /\ (ℓ ⊑ ℓ_adv -> low_reach ℓ_adv Γ Σ m h loc')) ->
      (σ = Int -> exists n, v = ValNum n) ->
      low_reach ℓ_adv Γ (extend_stenv loc1 (SecType σ (ℓ, ι)) Σ)
                (m [x → ValLoc loc1])
                (h [loc1 → (n × v, ℓ_p), H1, H2]) loc2 ->
      loc2 <> loc1 ->
      low_reach ℓ_adv Γ Σ m h loc2.
  Proof.
    intros.
    dependent induction H3.
    - destruct (decide (x = x0)); subst.
      + rewrite -> extend_memory_lookup_eq in *.
        rewrite_inj.
        exfalso; eauto.
      + rewrite -> extend_memory_lookup_neq in * by solve[eauto].
        eauto 2.
    - destruct (decide (loc0 = loc1)); subst.
      + rewrite_inj.
        rewrite -> extend_stenv_lookup_eq in *.
        rewrite_inj.
        apply_heap_lookup_extend_eq.
        super_destruct; subst.
        rewrite_inj.
        assert (v = ValLoc loc2) by congruence; subst.
        specialize (H τ ℓ_p0 eq_refl).
        super_destruct; subst.
        injects.
        eauto.
      + rewrite -> heap_lookup_extend_neq in * by solve[eauto].
        rewrite -> extend_stenv_lookup_neq in * by solve[eauto].
        assert (low_reach ℓ_adv Γ Σ m h loc0) by eauto 2. (* IH *)
        eauto 2.
  Qed.

  Definition low_reach_NI ℓ_adv (φ : bijection loc loc) m1 h1 m2 h2 Γ Σ1 Σ2 :=
    forall loc loc',
      left φ loc = Some loc' ->
      low_reach ℓ_adv Γ Σ1 m1 h1 loc <-> low_reach ℓ_adv Γ Σ2 m2 h2 loc'.
  Hint Unfold low_reach_NI.
  
  Lemma low_reach_NI_refl:
    forall ℓ_adv m h Γ Σ,
      low_reach_NI ℓ_adv (identity_bijection loc) m h m h Γ Σ Σ.
  Proof.
    intros.
    unfolds.
    intros.
    unfold left, identity_bijection in *.
    rewrite_inj.
    splits*.
  Qed.
  Hint Resolve low_reach_NI_refl.
  
  Lemma low_reach_NI_sym:
    forall ℓ_adv φ m1 m2 h1 h2 Γ Σ1 Σ2,
      low_reach_NI ℓ_adv φ m1 h1 m2 h2 Γ Σ1 Σ2 ->
      low_reach_NI ℓ_adv (inverse φ) m2 h2 m1 h1 Γ Σ2 Σ1.
  Proof.
    intros.
    unfolds.
    intros.
    assert (left φ loc' = Some loc) by (destruct φ; eauto).
    eauto using iff_sym.
  Qed.
  Hint Resolve low_reach_NI_sym.

  Lemma low_reach_NI_trans:
    forall ℓ_adv φ ψ m1 m2 m3 h1 h2 h3 Γ Σ1 Σ2 Σ3,
      low_reach_NI ℓ_adv φ m1 h1 m2 h2 Γ Σ1 Σ2 ->
      low_reach_NI ℓ_adv ψ m2 h2 m3 h3 Γ Σ2 Σ3 ->
      low_reach_NI ℓ_adv (bijection_compose φ ψ) m1 h1 m3 h3 Γ Σ1 Σ3.
  Proof.
    intros.
    unfolds.
    intros.
    remember_simple (left_compose φ ψ _ _ H1).
    super_destruct; subst.
    destruct (left φ loc) eqn:H_loc.
    - rename l into loc2.
      rewrite -> (H _) by solve[eauto].
      eauto.
    - repeat specialize_gen.
      discriminate.
  Qed.

  Definition heap_val := prod level_proj1 lookupfunc.
  Inductive heapval_low_eq: level_proj1 -> sectype -> loc -> loc ->
                            Memory -> Memory -> Heap -> Heap -> 
                            bijection loc loc -> Prop :=
  | HeapValLowEq:
      forall ℓ_adv τ ℓ_τ ℓ μ ν φ m1 m2 h1 h2 loc1 loc2,
        heap_lookup loc1 h1 = Some (ℓ, μ) ->
        heap_lookup loc2 h2 = Some (ℓ, ν) ->
        (forall n, (exists v, lookup μ n = Some v) <-> (exists u, lookup ν n = Some u)) ->
        (forall n u v, lookup μ n = Some u -> lookup ν n = Some v ->
                  reach m1 h1 loc1 ->
                  reach m2 h2 loc2 ->
                  val_low_eq ℓ_adv (SecType τ ℓ_τ) u v φ) ->
        heapval_low_eq ℓ_adv (SecType τ ℓ_τ) loc1 loc2 m1 m2 h1 h2 φ.
  Hint Constructors heapval_low_eq.

  Ltac invert_heapval_low_eq := 
    match goal with
      [H: context[heapval_low_eq] |- _] => inverts H
    end.

  Lemma heapval_low_eq_num_refl:
    forall ℓ_adv m l ℓ h μ loc0,
      heap_lookup loc0 h = Some (ℓ, μ) ->
      (forall v n, lookup μ n = Some v -> exists n0, lookup μ n = Some (ValNum n0)) ->
      heapval_low_eq ℓ_adv (SecType Int l) loc0 loc0 m m h h
                     (identity_bijection loc).
  Proof.
    intros.
    eapply HeapValLowEq; eauto.
    - intros.
      splits*.
    - intros.
      rewrite_inj.
      do 3 specialize_gen.
      destruct_exists.
      rewrite_inj.
      eauto.
  Qed.
  Hint Resolve heapval_low_eq_num_refl.
  
  Lemma heapval_low_eq_loc_refl:
    forall ℓ_adv μ s ℓ ℓ_p m loc0 h ε,
      heap_lookup loc0 h = Some (ℓ, μ) ->
      (forall v n, lookup μ n = Some v -> exists loc0, lookup μ n = Some (ValLoc loc0)) ->
      heapval_low_eq ℓ_adv (SecType (Array s ℓ_p) ε) loc0 loc0 m m h h
                     (identity_bijection loc).
  Proof.
    intros.
    eapply HeapValLowEq; eauto.
    - intros.
      splits*.
    - intros.
      rewrite_inj.
      do 3 specialize_gen.
      super_destruct; subst.
      rewrite_inj.
      eauto.
  Qed.
  Hint Resolve heapval_low_eq_loc_refl.
  
  Lemma heapval_low_eq_symmetry:
    forall ℓ τ loc1 loc2 φ m1 m2 h1 h2,
      heapval_low_eq ℓ τ loc1 loc2 m1 m2 h1 h2 φ ->
      heapval_low_eq ℓ τ loc2 loc1 m2 m1 h2 h1 (inverse φ).
  Proof.
    intros.
    invert_heapval_low_eq.
    eapply HeapValLowEq; eauto.
    intros.
    eapply iff_sym.
    eauto.
  Qed.
  Hint Resolve heapval_low_eq_symmetry.

  (*
  Lemma heapval_low_eq_trans:
    forall ℓ_adv τ loc1 loc2 loc3 φ ψ m1 m2 m3 h1 h2 h3,
      heapval_low_eq ℓ_adv τ loc1 loc2 m1 m2 h1 h2 φ ->
      heapval_low_eq ℓ_adv τ loc2 loc3 m2 m3 h2 h3 ψ ->
      heapval_low_eq ℓ_adv τ loc1 loc3 m1 m3 h1 h3 (bijection_compose φ ψ).
  Proof.
    intros.
    do 2 invert_heapval_low_eq.
    eapply HeapValLowEq.
    - eauto.
    - 
    - intros.
      split.
      + intros.
        eapply H10.
        eapply H12.
        eauto.
      + intros.
        eapply H12.
        eapply H10.
        eauto.
    - intros.
      assert (exists u, lookup ν n = Some u) by (eapply H12; eauto).
      destruct_exists.
      eapply val_low_eq_trans.
      * eapply H13; eauto.
      * eapply H11; eauto.
  Qed.
*)

  Definition heap_lookup_low_eq ℓ φ m1 m2 h1 h2 Γ Σ1 Σ2 :=
    forall loc1 loc2 τ,
      Σ1 loc1 = Some τ ->
      Σ2 loc2 = Some τ ->
      left φ loc1 = Some loc2 ->
      low ℓ Γ Σ1 m1 h1 loc1 ->
      low ℓ Γ Σ2 m2 h2 loc2 ->
      heapval_low_eq ℓ τ loc1 loc2 m1 m2 h1 h2 φ.
  Hint Unfold heap_lookup_low_eq.

  Ltac eapply_lookup_func_domain_eq :=
    match goal with
      [H: forall _, (exists _, _) <-> (exists _, _) |- _] =>
      eapply H
    end.

  
  Lemma bijection_implies_lookup:
    forall ℓ_adv ℓ ι τ m1 m2 h1 h2 n Γ Σ1 Σ2 loc1 loc2 loc1' loc2' φ l μ ν,
      wf_stenv Σ1 h1 ->
      wf_stenv Σ2 h2 ->
      heap_lookup_low_eq ℓ_adv φ m1 m2 h1 h2 Γ Σ1 Σ2 ->
      Σ1 loc1 = Some (SecType τ (ℓ, ι)) ->
      Σ2 loc2 = Some (SecType τ (ℓ, ι)) ->
      low ℓ_adv Γ Σ1 m1 h1 loc1 ->
      low ℓ_adv Γ Σ2 m2 h2 loc2 ->
      reach m1 h1 loc1 ->
      reach m2 h2 loc2 ->
      ℓ ⊑ ℓ_adv ->
      heap_lookup loc1 h1 = Some (l, μ) ->
      heap_lookup loc2 h2 = Some (l, ν) ->
      left φ loc1 = Some loc2 ->
      lookup μ n = Some (ValLoc loc1') ->
      left φ loc1' = Some loc2' ->
      lookup ν n = Some (ValLoc loc2').
  Proof.
    intros.
    super_destruct; subst.
    assert (heapval_low_eq ℓ_adv (SecType τ (ℓ, ι)) loc1 loc2 m1 m2 h1 h2 φ).
    {
      eauto.
    }
    invert_heapval_low_eq.
    rewrite_inj.
    assert (exists u, lookup ν0 n = Some u).
    {
      assert (exists v, lookup μ0 n = Some v) by eauto.
      eapply_lookup_func_domain_eq; eauto.
    }
    super_destruct; subst.
    assert (val_low_eq ℓ_adv (SecType τ (ℓ, ι)) (ValLoc loc1') u φ) by eauto.
    invert_val_low_eq.
    - contradiction.
    - congruence.
  Qed.

  (*
  Lemma low_reach_in_extended_memory_and_heap:
    forall ℓ Γ Σ1 Σ2 m1 h1 m2 h2 x n1 n2 v1 v2 l1 l2 loc1 loc2 φ ℓ_τ ℓ_p τ ℓ_x ι_τ,
      Γ x = Some (SecType (Array (SecType τ (ℓ_τ, ι_τ)) ℓ_p) (ℓ_x, ∘)) ->
      wf_bijection ℓ φ Γ Σ1 m1 h1 ->
      low_domain_eq ℓ Γ m1 m2 ->
      low_eq_stenv ℓ φ m1 m2 h1 h2 Γ Σ1 Σ2 ->
      low_reach_NI ℓ φ m1 h1 m2 h2 Γ Σ1 Σ2 ->
      low_heap_domain_eq ℓ φ m1 m2 h1 h2 Γ Σ1 Σ2 ->
      heap_lookup_low_eq ℓ φ m1 m2 h1 h2 Γ Σ1 Σ2 ->
      memory_lookup_low_eq ℓ Γ m1 m2 φ ->
      low_reach ℓ Γ (extend_stenv l1 (SecType τ (ℓ_τ, ι_τ)) Σ1)
                (m1 [SecType (Array (SecType τ (ℓ_τ, ι_τ)) ℓ_p) (ℓ_x, ∘), x → ValLoc l1])
                (h1 [l1 → (n1 × v1, ℓ_p)]) loc1 ->
      dangling_pointer_free m1 h1 ->
      dangling_pointer_free m2 h2 ->
      heap_is_some_implies_in_stenv h1 Σ1 ->
      heap_is_some_implies_in_stenv h2 Σ2 ->
      wf_tenv Γ m1 ->
      wf_tenv Γ m2 ->
      wf_stenv Σ1 h1 ->
      wf_stenv Σ2 h2 ->
      left φ loc1 = Some loc2 ->
      heap_lookup l1 h1 = None ->
      heap_lookup l2 h2 = None ->
      (forall s ℓ', τ = Array s ℓ' -> exists loc', v1 = ValLoc loc' /\ (ℓ_τ ⊑ ℓ -> low_reach ℓ Γ Σ1 m1 h1 loc')) ->
      (τ = Int -> exists n, v1 = ValNum n) ->
      (ℓ_τ ⊑ ℓ -> onvals (left φ) v1 = Some v2) ->
      size ℓ_p h1 + n1 <= maxsize ℓ_p h1 ->
      size ℓ_p h2 + n2 <= maxsize ℓ_p h2 ->
      low_reach ℓ Γ (extend_stenv l2 (SecType τ (ℓ_τ, ι_τ)) Σ2)
                (m2 [SecType (Array (SecType τ (ℓ_τ, ι_τ)) ℓ_p) (ℓ_x, ∘), x → ValLoc l2])
                (h2 [l2 → (n2 × v2, ℓ_p)]) loc2.
  Proof.
    intros.
    revert dependent loc2.
    match goal with
      [H: low_reach _ _ _ _ _ _ |- _] =>
      dependent induction H; intros
    end.
    - destruct (decide (x = x0)); subst.
      + rewrite extend_memory_lookup_eq in *.
        rewrite_inj.
        assert (exists ℓ μ, heap_lookup loc h1 = Some (ℓ, μ)) by eauto 2.
        super_destruct; congruence.
      + rewrite -> extend_memory_lookup_neq in * by solve[eauto].
        assert (exists v, memory_lookup m2 x0 = Some v).
        {
          eapply_low_domain_eq; eauto.
        }
        super_destruct; subst.
        assert (val_low_eq ℓ_adv (SecType (Array τ0 ℓ_p0) (l, ∘))
                           (ValLoc loc) v φ).
        {
          eauto 2 using eval_low_eq.
        }
        invert_val_low_eq; try contradiction.
        rewrite_inj.
        eapply LowReachMem with (x := x0); eauto.
        rewrite -> extend_memory_lookup_neq by solve[eauto].
        eauto.
    - destruct (decide (l1 = loc1)); subst.
      + rewrite_inj.
        rewrite -> extend_stenv_lookup_eq in *.
        rewrite_inj.
        assert (onvals (left φ) v1 = Some v2) by eauto.
        assert ({μ : lookupfunc |
                 heap_lookup loc1 (extend_heap loc1 ℓ_p n1 v1 h1) = Some (ℓ_p, μ) /\
                 (forall n : nat, lookup μ n = Some v1)}) by eauto 2.
        super_destruct; subst.
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
        assert ({μ : lookupfunc |
                 heap_lookup l2 (extend_heap l2 ℓ_p n2 (ValLoc loc0) h2) = Some (ℓ_p, μ)
                 /\ (forall n : nat, lookup μ n = Some (ValLoc loc0))}) by eauto 2.
        super_destruct; subst.
        rewrite_inj.
        assert (ℓ_x ⊑ ℓ_adv).
        {
          eapply new_low_reach_implies_flowsto_low with
          (m := m1) (h := h1) (v := ValLoc loc2).
          - eauto.
          - eauto.
          - eauto.
          - intros.
            injects.
            assert (exists loc', ValLoc loc2 = ValLoc loc' /\ (l ⊑ ℓ_adv -> low_reach ℓ_adv Γ Σ1 m1 h1 loc')) by eauto.
            super_destruct; subst.
            injects.
            exists loc'.
            splits*.
          - intros; discriminate.
          - eauto.
          - eauto.
        }
        eapply LowReachHeap with (loc1 := l2); eauto 2.
      + rewrite -> heap_lookup_extend_neq in * by solve[eauto].
        rewrite -> extend_stenv_lookup_neq in * by solve[eauto].
        assert (low_reach ℓ_adv Γ Σ1 m1 h1 loc1).
        {
          eapply (low_reach_extend_implies_low_reach_if (σ := τ) (v := v1) (ℓ := ℓ_τ)).
          - eauto.
          - intros; subst.
            specialize (H22 s ℓ' eq_refl).
            super_destruct; subst.
            exists loc'.
            splits~.          
          - intros; subst.
            eauto.
          - eauto.
          - eauto.
          - eauto.
        }
        assert (low ℓ_adv Γ Σ1 m1 h1 loc1) by eauto.
        assert (exists loc', left φ loc1 = Some loc') by eauto.
        super_destruct; subst.
        assert (Σ2 loc' = Some (SecType (Array τ0 ℓ_p0) (l, ∘))).
        {
          eapply H2; eauto.
        }
        assert (low_reach ℓ_adv Γ Σ2 m2 h2 loc').
        {
          eapply H3; eauto.
        }        
        assert ((exists μ, heap_lookup loc' h2 = Some (ℓ, μ)) /\ low ℓ_adv Γ Σ2 m2 h2 loc').
        {
          eauto 4.
        }
        super_destruct; subst.
       
        assert (lookup μ0 n = Some (ValLoc loc0)) by eauto using bijection_implies_lookup.
        assert (low_reach ℓ_adv Γ Σ2 m2 h2 loc0) by eauto 2.
        assert (l2 <> loc').
        {
          intro; subst.
          congruence.
        }

        assert (low_reach ℓ_adv Γ (extend_stenv l2 (SecType τ (ℓ_τ, ι_τ)) Σ2)
                          (m2 [SecType (Array (SecType τ (ℓ_τ, ι_τ)) ℓ_p) (ℓ_x, ∘), x → ValLoc l2])
                          (extend_heap l2 ℓ_p n2 v2 h2) loc').
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
  Qed.*)

  Ltac assert_wf_type :=
    match goal with
      [H: ?Γ ?x = Some (SecType ?τ ?ε) |- _] =>
      assert (wf_type bot (SecType τ ε)) by eauto
    end.

  Lemma heap_lookup_low_eq_sym:
    forall ℓ_adv φ m1 m2 h1 h2 Γ Σ1 Σ2,
      heap_lookup_low_eq ℓ_adv φ m1 m2 h1 h2 Γ Σ1 Σ2 ->
      heap_lookup_low_eq ℓ_adv (inverse φ) m2 m1 h2 h1 Γ Σ2 Σ1.
  Proof.
    intros.
    unfolds.
    intros.
    assert (left φ loc2 = Some loc1) by (destruct φ; eauto).
    assert (heapval_low_eq ℓ_adv τ loc2 loc1 m1 m2 h1 h2 φ) by eauto.
    eauto.
  Qed.
  Hint Resolve heap_lookup_low_eq_sym.

  Lemma memory_lookup_low_eq_sym:
    forall ℓ_adv Γ m1 m2 φ,
      memory_lookup_low_eq ℓ_adv Γ m1 m2 φ ->
      memory_lookup_low_eq ℓ_adv Γ m2 m1 (inverse φ).
  Proof.
    intros.
    unfolds.
    intros.
    eapply val_low_eq_symmetry.
    eauto.
  Qed.
  Hint Resolve memory_lookup_low_eq_sym.

  Lemma low_reach_update_with_num:
    forall m h loc1 loc2 n k ℓ Γ Σ,
      low_reach ℓ Γ Σ m (update_heap loc1 n (ValNum k) h) loc2 ->
      low_reach ℓ Γ Σ m h loc2.
  Proof.
    intros.
    dependent induction H.
    - eauto 2.
    - destruct (decide (loc1 = loc0)); subst.
      + super_destruct; subst.
        _apply heap_lookup_update_eq2 in *.
        super_destruct; subst.
        destruct (decide (n = n0)); subst.
        * rewrite -> lookup_update_eq in *.
          discriminate.
        * rewrite -> lookup_update_neq in * by solve[eauto].
          eauto 3.
      + rewrite -> heap_lookup_update_neq in * by solve[eauto].
        eauto.
  Qed.
  
  Lemma low_reach_update_implies_low_reach_if:
    forall m h loc1 loc2 n v ℓ_adv Γ Σ σ ℓ ι,
      Σ loc1 = Some (SecType σ (ℓ, ι)) ->
      low_reach ℓ_adv Γ Σ m (update_heap loc1 n v h) loc2 ->
      (forall loc', v = ValLoc loc' ->
               ℓ ⊑ ℓ_adv ->
               low_reach ℓ_adv Γ Σ m h loc') ->
      low_reach ℓ_adv Γ Σ m h loc2.
  Proof.
    intros.
    dependent induction H0.
    - eauto 2.
    - assert (low_reach ℓ_adv Γ Σ m h loc0) by eauto.
      clear IHlow_reach.
      destruct (decide (loc1 = loc0)); subst.
      + assert (exists ν, heap_lookup loc0 h = Some (ℓ0, ν) /\ μ = update_lookup ν n v) by eauto.
        super_destruct; subst.
        rewrite_inj.
        destruct v.
        * eapply low_reach_update_with_num; eauto.
        * assert (low_reach ℓ_adv Γ Σ m h l) by eauto.
          destruct (decide (n = n0)); subst.
          { rewrite -> lookup_update_eq in *.
            congruence.
          }
          { rewrite -> lookup_update_neq in * by solve[eauto].
            eauto 3. }
      + rewrite -> heap_lookup_update_neq in * by solve[eauto].
        eauto 3.
  Qed.
  Hint Resolve low_reach_update_implies_low_reach_if.

  Lemma low_reach_extend_mem_with_num2:
    forall ℓ Γ Σ m h loc x n l,
      wf_tenv Γ m ->
      Γ x = Some (SecType Int l) ->
      low_reach ℓ Γ Σ m h loc ->
      low_reach ℓ Γ Σ (extend_memory x (ValNum n) m) h loc.
  Proof.
    intros.
    dependent induction H1; eauto.
    assert (x <> x0).
    {
      intro; subst.
      rewrite_inj.
      discriminate.
    }
    eapply LowReachMem; eauto.
    rewrite -> extend_memory_lookup_neq by solve[eauto].
    eauto.
  Qed.

  Lemma no_longer_reach_implies:
    forall x y m h loc1 loc2,
      reach_from x m h loc1 ->
      ~ reach (extend_memory y (ValLoc loc2) m) h loc1 ->
      x = y /\ loc1 <> loc2.
  Proof.
    intros.
    unfold reach_from in *.
    super_destruct.
    revert loc1 H H0.
    induction k; intros.
    - inverts H.
      destruct (decide (x = y)).
      + splits~.
        intro; subst.
        eauto.
      + contradict H0.
        eapply reach_from_implies_reach.
        unfolds.
        exists 0.
        constructor.
        rewrite -> extend_memory_lookup_neq by solve[eauto].
        eauto.
    - inverts H.
      assert (~ reach (extend_memory y (ValLoc loc2) m) h loc) by eauto.
      assert (x = y /\ loc <> loc2) by eauto using IHk.
      super_destruct; subst; splits~.
      intro; subst.
      eauto 3.
  Qed.

  Lemma reach_from_extend_memory_heap_neq:
    forall x i m h v1 v2 loc1 loc2 n ℓ H1 H2,
      reach_from x m h loc1 ->
      x <> i ->
      reach_from x (extend_memory i v1 m) (h [loc2 → (n × v2, ℓ), H1, H2]) loc1.
  Proof.
    intros.
    unfold reach_from in * |-.
    super_destruct.
    revert loc1 H H1.
    induction k; intros.
    - inverts H.
      exists 0.
      constructor.
      rewrite -> extend_memory_lookup_neq by solve[eauto].
      eauto.
    - inverts H.
      assert (loc <> loc2).
      {
        intro; subst.
        rewrite_inj.
        discriminate.
      }
      specialize (IHk loc H4 H1).
      unfold reach_from in *.
      super_destruct.
      exists (S k0).
      eapply reach_from_heap.
      + eapply IHk.
      + rewrite -> heap_lookup_extend_neq by solve[eauto].
        eauto.
      + eauto.
  Qed.

  Lemma reach_from_extend_memory_heap_implies:
    forall x i loc1 loc2 m h ℓ n v H1 H2,
      dangling_pointer_free m h ->
      x <> i ->
      reach_from x (extend_memory i (ValLoc loc1) m)
                 (h [loc1 → (n × v, ℓ), H1, H2]) loc2 ->
      reach_from x m h loc2.
  Proof.
    intros.
    unfold reach_from in *.
    super_destruct.
    revert loc2 H3.
    induction k; intros.
    - inverts H3.
      rewrite -> extend_memory_lookup_neq in * by solve[eauto].
      eauto.
    - inverts H3.
      assert (exists k, idx_reach_from x m h loc k) by eauto using IHk.
      super_destruct.
      assert (loc <> loc1).
      {
        intro; subst.
        assert (exists ℓ μ, heap_lookup loc1 h = Some (ℓ, μ)) by eauto.
        super_destruct.
        rewrite_inj; discriminate.
      }
      rewrite -> heap_lookup_extend_neq in * by solve[eauto].
      eauto.
  Qed.

  Lemma reach_from_update_with_num:
    forall Σ x m h loc1 loc2 n1 n2 l,
      Σ loc2 = Some (SecType Int l) ->
      wf_stenv Σ h ->
      reach_from x m h loc1 ->
      reach_from x m (update_heap loc2 n1 (ValNum n2) h) loc1.
  Proof.
    intros.
    unfold reach_from in *.
    super_destruct.
    revert dependent loc1.
    induction k; intros.
    - inverts H1.
      eauto.
    - inverts H1.
      do 2 specialize_gen.
      super_destruct.
      exists (S k0).
      eapply (reach_from_heap m (update_heap loc2 n1 (ValNum n2) h) x
                              loc loc1 ℓ μ n k0).
      + eauto.
      + destruct (decide (loc = loc2)); subst.
        * assert (exists n, ValLoc loc1 = ValNum n) by eauto.
          super_destruct; discriminate.
        * rewrite -> heap_lookup_update_neq by solve[eauto].
          eauto.
      + eauto.
  Qed.

  Lemma reach_from_supset_if:
    forall x m h1 h2 loc H,
      reach_from x m ([h1 ⊎ h2, H]) loc ->
      (forall loc ℓ μ,
          heap_lookup loc h2 = Some (ℓ, μ) -> ~ reach m ([h1 ⊎ h2, H]) loc) ->
      reach_from x m h1 loc.
  Proof.
    intros.
    unfold reach_from in * |-.
    super_destruct.
    dependent induction H0; [eauto |].
    specialize (IHidx_reach_from _ _ H eq_refl).
    destruct (heap_lookup loc h2) eqn:H_loc.
    - destruct p.
      assert (~ reach m ([h1 ⊎ h2, H]) loc) by eauto.
      contradict H4; eauto.
    - repeat specialize_gen.
      assert (heap_lookup loc h1 = Some (ℓ, μ)).
      {
        rewrite -> disjoint_union_sym in * by solve[eauto].
        eauto.
      }
      unfold reach_from in *.
      super_destruct.
      eauto.
  Qed.

  Lemma reach_supset_if:
    forall m h1 h2 loc H,
      reach m ([h1 ⊎ h2, H]) loc ->
      (forall loc ℓ μ,
          heap_lookup loc h2 = Some (ℓ, μ) -> ~ reach m ([h1 ⊎ h2, H]) loc) ->
      reach m h1 loc.
  Proof.
    intros.
    _apply reach_implies_reach_from in *.
    super_destruct; subst.
    assert (reach_from x m h1 loc) by eauto 2 using reach_from_supset_if.
    eauto.
  Qed.
  
  Lemma reach_from_implies_in_tenv:
    forall Γ Σ m h loc x,
      heap_level_bound Γ m h Σ ->
      wf_tenv Γ m ->
      reach_from x m h loc ->
      exists τ ε ℓ,
        Γ x = Some (SecType (Array τ ℓ) ε).
  Proof.
    intros.
    unfold reach_from in *.
    super_destruct'; subst.
    revert dependent loc.
    induction k; intros.
    - match goal with
        [H: idx_reach_from _ _ _ _ _ |- _] =>
        inverts H
      end.
      assert (exists t, Γ x = Some t) by eauto.
      super_destruct'; subst.
      destruct t as [σ ε].
      destruct σ.
      + assert (exists n, ValLoc loc = ValNum n) by eauto.
        super_destruct; discriminate.
      + eauto.
    - match goal with
        [H: idx_reach_from _ _ _ _ _ |- _] =>
        inverts H
      end.
      eauto.
  Qed.
  Hint Resolve reach_from_implies_in_tenv.

  Lemma low_reach_adequacy:
    forall Γ Σ loc m h ℓ μ ℓ_adv,
      heap_level_bound Γ m h Σ ->
      wf_tenv Γ m ->
      wf_stenv Σ h ->
      heap_lookup loc h = Some (ℓ, μ) ->
      ℓ ⊑ ℓ_adv ->
      low_reach ℓ_adv Γ Σ m h loc <->
      reach m h loc.
  Proof.
    intros.
    splits*.
    intros.
    revert dependent ℓ.
    revert μ.
    super_destruct'; subst.
    dependent induction H4; intros.
    - assert (exists τ, Γ x = Some τ) by eauto 2.
      super_destruct'; subst.
      destruct τ as [σ ε].
      assert (exists τ , σ = Array τ ℓ).
      {
        destruct σ.
        - assert (exists n, ValLoc loc = ValNum n) by eauto.
          super_destruct; discriminate.
        - exists s.
          eapply f_equal2; eauto.
      }
      super_destruct'; subst.
      destruct ε as [ℓ_x ι_x].
      assert (wf_type bot (SecType (Array τ ℓ) (ℓ_x, ι_x))) by eauto 2.
      invert_wf_type.
      eauto.
    - do 3 specialize_gen.
      specialize (IHreach μ ℓ H2).
      assert (ℓ ⊑ ℓ0) by (destructs H; eauto).
      assert (ℓ ⊑ ℓ_adv) by eauto.
      specialize (IHreach H8).
      assert (exists τ, Σ loc = Some τ) by eauto.
      super_destruct; subst.
      destruct τ as [σ [l ι]].
      assert (exists τ, σ = Array τ ℓ0).
      {
        destruct σ.
        - assert (exists n, ValLoc loc' = ValNum n) by eauto.
          super_destruct'; discriminate.
        - exists s.
          symmetry.
          destructs H.
          eapply f_equal2; eauto.
      }
      super_destruct'; subst.
      assert (wf_type bot (SecType (Array τ ℓ0) (l, ι))) by eauto 2.
      invert_wf_type.
      eauto.
  Qed.

  Lemma low_reach_subset_if:
    forall ℓ Γ Σ m h1 h2 loc0 H,
      low_reach ℓ Γ Σ m ([h1 ⊎ h2, H]) loc0 ->
      (forall loc l μ,
          heap_lookup loc h2 = Some (l, μ) -> ~ reach m ([h1 ⊎ h2, H]) loc) ->
      low_reach ℓ Γ Σ m h1 loc0.
  Proof.
    intros.
    dependent induction H0; eauto.
    specialize (IHlow_reach _ _ H eq_refl).
    super_destruct.
    assert (heap_lookup loc1 h1 = Some (ℓ, μ) \/ heap_lookup loc1 h2 = Some (ℓ, μ)).
    {
      eapply disjoint_union_heap_lookup2; eauto.
    }
    match goal with
      [H: _ \/ _ |- _] =>
      destruct H
    end.
    - eauto.
    - assert (~ reach m ([h1 ⊎ h2, H]) loc1) by eauto.
      match goal with
        [H: ~ reach _ _ _ |- _] =>
        contradiction H; eauto
      end.
  Qed.
  Hint Resolve low_reach_subset_if.
  
  Lemma low_reach_supset:
    forall ℓ Γ Σ m h1 h2 loc H,
      low_reach ℓ Γ Σ m h1 loc ->
      low_reach ℓ Γ Σ m ([h1 ⊎ h2, H]) loc.
  Proof.
    intros.
    dependent induction H0; eauto.
  Qed.

  Lemma reach_supset:
    forall m h1 h2 loc H,
      reach m h1 loc ->
      reach m ([h1 ⊎ h2, H]) loc.
  Proof.
    intros.
    dependent induction H0; eauto.
    Unshelve.
    - constructor; eauto.
  Qed.
  Hint Resolve reach_supset.
  
  Lemma reach_from_extend_with_num2:
    forall Γ m h loc x i level n,
      reach_from x m h loc ->
      wf_tenv Γ m ->
      Γ i = Some (SecType Int level) ->
      reach_from x (extend_memory i (ValNum n) m) h loc.
  Proof.
    intros.
    unfold reach_from in * |-.
    super_destruct.
    revert loc H.
    induction k; intros.
    - inverts H.
      destruct (decide (i = x)); subst.
      + assert (exists n, ValLoc loc = ValNum n) by eauto 2.
        super_destruct'; discriminate.
      + unfolds.
        exists 0.
        constructor.
        rewrite -> extend_memory_lookup_neq by solve[eauto].
        eauto.
    - inverts H.
      assert (reach_from x (extend_memory i (ValNum n) m) h loc0) by eauto.
      unfold reach_from in *.
      super_destruct.
      eauto.
  Qed.
  Hint Resolve reach_from_extend_with_num2.

  Lemma idx_reach_from_extend_memory_neq:
    forall i x m h loc v k,
      i <> x ->
      idx_reach_from x m h loc k ->
      idx_reach_from x (extend_memory i v m) h loc k.
  Proof.
    intros.
    revert loc H0.
    induction k; intros.
    - inverts H0.
      constructor.
      rewrite -> extend_memory_lookup_neq by solve[eauto].
      eauto.
    - inverts H0.
      eauto.
  Qed.
  Hint Resolve idx_reach_from_extend_memory_neq.

  Lemma reach_from_reach_extend_implies_reach_from_extend:
    forall x m h loc i v,
      i <> x ->
      reach_from x m h loc ->
      reach (extend_memory i v m) h loc ->
      reach_from x (extend_memory i v m) h loc.
  Proof.
    intros.
    unfold reach_from in * |-.
    super_destruct.
    revert loc H0 H1.
    induction k; intros.
    - inverts H0.
      exists 0.
      constructor.
      rewrite -> extend_memory_lookup_neq by solve[eauto].
      eauto.
    - inverts H0.
      assert (reach (extend_memory i v m) h loc0) by eauto.
      eauto.
  Qed.
  Hint Resolve reach_from_reach_extend_implies_reach_from_extend.

  Lemma reach_from_extend_neq_implies:
    forall x i m h v loc,
      x <> i ->
      reach_from x (extend_memory i v m) h loc ->
      reach_from x m h loc.
  Proof.
    intros.
    unfold reach_from in * |-.
    super_destruct.
    revert loc H0.
    induction k; intros.
    - inverts H0.
      rewrite -> extend_memory_lookup_neq in * by solve[eauto].
      eauto.
    - inverts H0.
      assert (reach_from x m h loc0) by eauto.
      unfold reach_from in *.
      super_destruct.
      eauto.
  Qed.
  Hint Resolve reach_from_extend_neq_implies.

  Lemma extend_mem_with_high_preserves_low_reach:
    forall ℓ Γ Σ m h v loc l t x ι,
      Γ x = Some (SecType t (l, ι)) ->
      ~ l ⊑ ℓ ->
      low_reach ℓ Γ Σ m h loc ->
      low_reach ℓ Γ Σ (extend_memory x v m) h loc.
  Proof.
    intros.
    dependent induction H1; eauto 3.
    destruct (decide (x = x0)); subst.
    - rewrite_inj.
      contradiction.
    - eapply LowReachMem; eauto.
      rewrite -> extend_memory_lookup_neq by solve[eauto].
      eauto.
  Qed.
  Hint Resolve extend_mem_with_high_preserves_low_reach.

  Lemma low_reach_in_extend_memory_with_high_implies_low_reach:
    forall ℓ Γ Σ m h v loc l t x ι,
      Γ x = Some (SecType t (l, ι)) ->
      ~ l ⊑ ℓ ->
      low_reach ℓ Γ Σ (extend_memory x v m) h loc ->
      low_reach ℓ Γ Σ m h loc.
  Proof.
    intros.
    dependent induction H1; eauto.
    destruct (decide (x = x0)); subst.
    - rewrite_inj.
      contradiction.
    - rewrite -> extend_memory_lookup_neq in * by solve[eauto].
      eauto 2.
  Qed.
  Hint Resolve low_reach_in_extend_memory_with_high_implies_low_reach.

  Lemma low_reach_extend_memory_heap_with_high:
    forall x ℓ_adv Γ Σ m h loc1 loc2 v n l ℓ τ H1 H2,
      Γ x = Some (SecType (Array τ ℓ) (l, ∘)) ->
      ~ l ⊑ ℓ_adv ->
      low_reach ℓ_adv Γ Σ m h loc1 ->
      low_reach ℓ_adv Γ (extend_stenv loc2 τ Σ)
                (extend_memory x (ValLoc loc2) m) 
                (h [loc2 → (n × v, ℓ), H1, H2]) loc1.
  Proof.
    intros.
    dependent induction H3; eauto 3.
    - repeat specialize_gen.
      assert (loc1 <> loc2).
      {
        intro; subst.
        congruence.
      }
      eapply LowReachHeap.
      + eauto.
      + rewrite -> extend_stenv_lookup_neq by solve[eauto].
        eauto.
      + rewrite -> heap_lookup_extend_neq by solve[eauto].
        eauto.
      + eauto.
      + eauto.
  Qed.
  Hint Resolve low_reach_extend_memory_heap_with_high.

  Lemma low_reach_in_extended_memory_heap_with_high_implies_low_reach:
    forall x ℓ_adv Γ Σ m h loc1 loc2 v n l τ ι ℓ H1 H2,
      Γ x = Some (SecType (Array τ ℓ) (l, ι)) ->
      ~ l ⊑ ℓ_adv ->
      dangling_pointer_free m h ->
      low_reach ℓ_adv Γ (extend_stenv loc2 τ Σ)
                (extend_memory x (ValLoc loc2) m) 
                (h [loc2 → (n × v, ℓ), H1, H2]) loc1 ->
      low_reach ℓ_adv Γ Σ m h loc1.
  Proof.
    intros.
    dependent induction H4.
    - assert (x <> x0).
      {
        intro; subst.
        congruence.
      }
      rewrite -> extend_memory_lookup_neq in * by solve[eauto].
      eauto.
    - assert (low_reach ℓ_adv Γ Σ m h loc1) by eauto 2.
      destruct (decide (loc2 = loc1)); subst.
      + assert (exists ℓ μ, heap_lookup loc1 h = Some (ℓ, μ)) by eauto.
        super_destruct; subst.
        congruence.
      + rewrite -> heap_lookup_extend_neq in * by solve[eauto].
        rewrite -> extend_stenv_lookup_neq in * by solve[eauto].
        eauto 3.

        Unshelve.
  Qed.
  Hint Resolve low_reach_in_extended_memory_heap_with_high_implies_low_reach.
  
  Lemma low_domain_eq_extend:
    forall ℓ Γ m1 m2 x v1 v2,
      low_domain_eq ℓ Γ m1 m2 ->
      low_domain_eq ℓ Γ (extend_memory x v1 m1) (extend_memory x v2 m2).
  Proof.
    intros.
    unfold low_domain_eq in *.
    intros.
    destruct (decide (x = x0)); subst.
    - repeat rewrite -> extend_memory_lookup_eq in *.
      splits*.
    - repeat rewrite -> extend_memory_lookup_neq by solve[eauto].
      eapply H; eauto.
  Qed.
  Hint Resolve low_domain_eq_extend.

  Lemma val_low_eq_extend:
    forall ℓ_adv loc1 loc2 τ v u φ H1 H2,
      val_low_eq ℓ_adv τ v u φ ->
      val_low_eq ℓ_adv τ v u (extend_bijection φ loc1 loc2 H1 H2).
  Proof.
    intros.
    invert_val_low_eq.
    - eauto.
    - eauto.
    - eauto.
    - destruct (decide (l1 = loc1)); destruct (decide (l2 = loc2)); subst.
      { rewrite_inj; discriminate. }
      { rewrite_inj; discriminate. }
      {
        eapply ValLocLowEqL; eauto.
        unfold left.
        unfold extend_bijection.
        rewrite -> neq_loc by solve[eauto].
        eauto.
      }
      {
        eapply ValLocLowEqL; eauto.
        unfold left.
        unfold extend_bijection.
        rewrite -> neq_loc by solve[eauto].
        eauto.
      }
  Qed.
  
  Inductive state_low_eq : level_proj1 -> bijection loc loc ->
                           Memory -> Heap -> Memory -> Heap -> tenv ->
                           stenv -> stenv -> Prop :=
  | StateLowEq:
      forall ℓ φ m h m' h' Γ Σ1 Σ2,
        low_eq_stenv ℓ φ m m' h h' Γ Σ1 Σ2 ->
        low_domain_eq ℓ Γ m m' ->
        low_heap_domain_eq ℓ φ m m' h h' Γ Σ1 Σ2 ->
        memory_lookup_low_eq ℓ Γ m m' φ ->
        heap_lookup_low_eq ℓ φ m m' h h' Γ Σ1 Σ2 ->
        low_reach_NI ℓ φ m h m' h' Γ Σ1 Σ2 ->
        (forall l, l ⊑ ℓ -> size l h = size l h') ->
        (forall l loc loc' μ ν,
            l ⊑ ℓ ->
            heap_lookup loc h = Some (l, μ) ->
            heap_lookup loc' h' = Some (l, ν) ->
            left φ loc = Some loc' ->
            length_of loc h = length_of loc' h') ->
        state_low_eq ℓ φ m h m' h' Γ Σ1 Σ2.

  Ltac invert_state_low_eq :=
    match goal with
      [H: context[state_low_eq] |- _] => inverts H
    end.

  Lemma low_implies_in_heap:
    forall m h ℓ_adv Γ Σ loc,
      dangling_pointer_free m h ->
      low ℓ_adv Γ Σ m h loc ->
      exists ℓ μ, heap_lookup loc h = Some (ℓ, μ).
  Proof.
    intros.
    destruct_low; eauto.
  Qed.
  Hint Resolve low_implies_in_heap.
  
  Lemma state_low_eq_refl:
    forall ℓ_adv m h Γ Σ,
      wf_tenv Γ m ->
      wf_stenv Σ h ->
      dangling_pointer_free m h ->
      heap_level_bound Γ m h Σ ->
      state_low_eq ℓ_adv (identity_bijection loc) m h m h Γ Σ Σ.
  Proof.
    intros.
    apply StateLowEq; eauto.
    - unfolds.
      intros.
      rewrite_inj.
      destruct τ.
      destruct t.
      + assert (exists n, v2 = ValNum n) by eauto.
        destruct_exists.
        eauto.
      + assert (exists loc0, v2 = ValLoc loc0) by eauto.
        destruct_exists.
        destruct t0 as [ℓ ι].
        assert (ι = ∘).
        {
          assert (wf_type bot (SecType (Array s l) (ℓ, ι))) by eauto.
          invert_wf_type.
          reflexivity.
        }
        subst.
        eauto.
    - unfolds.
      intros.
      unfold left, identity_bijection in * |-.
      rewrite_inj.
      destruct τ as [τ ε].
      assert (exists ℓ μ, heap_lookup loc2 h = Some (ℓ, μ)) by eauto 2.
      super_destruct; subst.
      destruct τ.
      + eapply heapval_low_eq_num_refl.
        * eauto.
        * intros.
          assert (exists n0, v = ValNum n0) by eauto.
          super_destruct; subst.
          eauto.
      + eapply heapval_low_eq_loc_refl.
        * eauto.
        * intros.
          assert (exists loc0, v = ValLoc loc0) by eauto.
          super_destruct; subst.
          eauto.
    - intros.
      unfold left, identity_bijection in *.
      rewrite_inj.
      reflexivity.
  Qed.
  Hint Resolve state_low_eq_refl.

  Lemma state_low_eq_symmetry:
    forall ℓ_adv φ m h s w Γ Σ1 Σ2,
      state_low_eq ℓ_adv φ m h s w Γ Σ1 Σ2 ->
      state_low_eq ℓ_adv (inverse φ) s w m h Γ Σ2 Σ1.
  Proof.
    intros.
    inverts H.
    apply StateLowEq; eauto 2.
    - intros.
      symmetry.
      eauto.
    - intros.
      symmetry.
      eapply H7.
      + eauto.
      + destruct φ; eauto.
      + eauto.
      + destruct φ; eauto.
  Qed.
  Hint Resolve state_low_eq_symmetry.

  Lemma low_reach_NI_extend_memory_high:
    forall ℓ_adv m h Γ Σ l ι t v x,
      Γ x = Some (SecType t (l, ι)) ->
      ~ l ⊑ ℓ_adv ->
      low_reach_NI ℓ_adv (identity_bijection loc) m h (extend_memory x v m) h Γ Σ Σ.
  Proof.
    intros.
    unfolds.
    intros.
    splits;
      intros;
      unfold left, identity_bijection in *;
      rewrite_inj;
      eauto.
  Qed.
  Hint Resolve low_reach_NI_extend_memory_high.

  Ltac eapply_low_eq_stenv :=
    match goal with
      [H: low_eq_stenv _ _ _ _ _ _ _ _ _ |- _] =>
      eapply H
    end.

  Lemma implies_same_store_typing:
    forall ℓ_adv φ Σ1 Σ2 loc1 loc2 m1 m2 h1 h2 Γ t ℓ,
      low_eq_stenv ℓ_adv φ m1 m2 h1 h2 Γ Σ1 Σ2 ->
      left φ loc1 = Some loc2 ->
      low ℓ_adv Γ Σ1 m1 h1 loc1 ->
      Σ1 loc1 = Some (SecType t ℓ) ->
      Σ2 loc2 = Some (SecType t ℓ).
  Proof.
    intros.
    unfolds in H.    
    eapply proj1.
    erewrite <- H by solve[eauto].
    eauto.
  Qed.
  Hint Resolve implies_same_store_typing.

  Lemma low_iff:
    forall ℓ_adv φ m1 m2 h1 h2 Γ Σ1 Σ2 loc1 loc2,
      state_low_eq ℓ_adv φ m1 h1 m2 h2 Γ Σ1 Σ2 ->
      left φ loc1 = Some loc2 ->
      low ℓ_adv Γ Σ1 m1 h1 loc1 <->
      low ℓ_adv Γ Σ2 m2 h2 loc2.
  Proof.
    intros.
    splits.
    - intros.
      invert_state_low_eq.
      destruct H1.
      + eapply LowReachable.
        eapply H7; eauto.
      + assert ((exists μ, heap_lookup loc h = Some (ℓ, μ)) /\ low ℓ_adv Γ Σ m h loc)
          by eauto.
        assert ((exists μ, heap_lookup loc2 h2 = Some (ℓ, μ)) /\ low ℓ_adv Γ Σ2 m2 h2 loc2).
        {
          eapply H4; eauto.
        }
        super_destruct; subst.
        eauto.
    - intros.
      invert_state_low_eq.
      destruct H1.
      + eapply LowReachable.
        eapply H7; eauto.
      + assert ((exists μ, heap_lookup loc h = Some (ℓ, μ)) /\ low ℓ_adv Γ Σ m h loc)
          by eauto.
        assert ((exists μ, heap_lookup loc1 h1 = Some (ℓ, μ)) /\ low ℓ_adv Γ Σ1 m1 h1 loc1).
        {
          eapply H4; eauto.
        }
        super_destruct; subst.
        eauto.
  Qed.
  Hint Resolve low_iff.
      
  Lemma state_low_eq_trans:
    forall ℓ φ ψ m1 m2 m3 h1 h2 h3 Γ Σ1 Σ2 Σ3,
      wf_tenv Γ m1 ->
      wf_tenv Γ m2 ->
      wf_tenv Γ m3 ->
      wf_stenv Σ1 h1 ->
      wf_stenv Σ2 h2 ->
      wf_stenv Σ3 h3 ->
      dangling_pointer_free m1 h1 ->
      dangling_pointer_free m2 h2 ->
      dangling_pointer_free m3 h3 ->
      heap_level_bound Γ m1 h1 Σ1 ->
      heap_level_bound Γ m2 h2 Σ2 ->
      heap_level_bound Γ m3 h3 Σ3 ->
      state_low_eq ℓ φ m1 h1 m2 h2 Γ Σ1 Σ2 ->
      state_low_eq ℓ ψ m2 h2 m3 h3 Γ Σ2 Σ3 ->
      state_low_eq ℓ (bijection_compose φ ψ) m1 h1 m3 h3 Γ Σ1 Σ3.
  Proof.
    intros.
    apply StateLowEq; (try solve[do 2 invert_state_low_eq; eauto 2]).
    - do 2 invert_state_low_eq; eapply low_eq_stenv_trans; eauto.
    - do 2 invert_state_low_eq; eapply low_domain_eq_trans; eauto.
    - unfolds.
      intros.
      do 2 invert_state_low_eq.
      destruct τ as [σ [l ι]].
      destruct (flowsto_dec l ℓ).
      + assert (exists u, memory_lookup m2 x = Some u).
        {
          match goal with
            [H: context[low_domain_eq] |- _] =>
            eapply H; eauto
          end.
        }
        destruct_exists.
        assert (val_low_eq ℓ (SecType σ (l, ι)) v1 u φ) by eauto.
        assert (val_low_eq ℓ (SecType σ (l, ι)) u v2 ψ) by eauto.
        eapply val_low_eq_trans; eauto.
      + destruct σ.
        * assert (exists n, v1 = ValNum n) by eauto.
          assert (exists n, v2 = ValNum n) by eauto.
          destruct_exists.
          eauto.
        * assert (exists loc, v1 = ValLoc loc) by eauto.
          assert (exists loc, v2 = ValLoc loc) by eauto.
          destruct_exists.
          eauto.
    - unfolds.
      intros.
      rename loc2 into loc3.
      _apply left_compose in *.
      super_destruct.
      destruct my as [loc2 | ]; try solve[repeat specialize_gen; discriminate].
      assert (left ψ loc2 = Some loc3) by eauto.
      destruct τ as [σ [l ι]].

      assert (low ℓ Γ Σ2 m2 h2 loc2).
      {
        eapply low_iff; eauto.
      }
      
      assert (Σ2 loc2 = Some (SecType σ (l, ι))).
      {
        repeat invert_state_low_eq; eauto 2.
      }
      assert (exists ℓ μ, heap_lookup loc1 h1 = Some (ℓ, μ)) by eauto 2.
      super_destruct; subst.
      assert (exists ν, heap_lookup loc2 h2 = Some (ℓ0, ν)).
      {                
        repeat invert_state_low_eq.
        eauto 2.
      }
      super_destruct; subst.
      assert (exists σ, heap_lookup loc3 h3 = Some (ℓ0, σ)).
      {                
        repeat invert_state_low_eq.        
        eauto 2.
      }
      super_destruct'; subst.
      assert (heapval_low_eq ℓ (SecType σ (l, ι)) loc1 loc2 m1 m2 h1 h2 φ)
        by (do 2 invert_state_low_eq; iauto).
      assert (heapval_low_eq ℓ (SecType σ (l, ι)) loc2 loc3 m2 m3 h2 h3 ψ)
        by (do 2 invert_state_low_eq; iauto).
      do 2 invert_heapval_low_eq.
      rewrite_inj.
      eapply HeapValLowEq.
      + eauto.
      + eauto.
      + intros.
        eapply iff_trans; eauto.
      + intros.
        assert (reach m2 h2 loc2).
        {
          destruct_low.
          - eauto.
          - rewrite_inj.
            assert (low_reach ℓ_adv Γ Σ1 m1 h1 loc1).
            {
              eapply low_reach_adequacy; eauto.
            }
            assert (low_reach ℓ_adv Γ Σ m h loc).
            {
              inverts H11.
              eapply H38; eauto.
            }
            eauto.
        }
        assert (exists w, lookup ν1 n = Some w).
        {
          eapply_lookup_func_domain_eq; eauto.
        }
        super_destruct; subst.
        assert (val_low_eq ℓ (SecType σ (l, ι)) u w φ) by eauto.
        assert (val_low_eq ℓ (SecType σ (l, ι)) w v ψ) by eauto.
        eapply val_low_eq_trans; eauto.
    - do 2 invert_state_low_eq.
      eapply low_reach_NI_trans; eauto.
    - intros.
      do 2 invert_state_low_eq.
      assert (size l h1 = size l h2) by eauto.
      assert (size l h2 = size l h3) by eauto.
      congruence.
    - intros.
      _apply left_compose in *.
      super_destruct; subst.
      destruct (left φ loc) eqn:H_loc.
      + assert (left ψ l0 = Some loc') by eauto 2.
        assert (exists σ, heap_lookup l0 h2 = Some (l, σ)).
        {
          do 2 invert_state_low_eq.
          eauto.
        }
        super_destruct'; subst.
        assert (length_of loc h1 = length_of l0 h2)
          by (do 2 invert_state_low_eq; eauto 2).
        assert (length_of l0 h2 = length_of loc' h3)
          by (do 2 invert_state_low_eq; eauto).
        congruence.
      + repeat specialize_gen.
        discriminate.
  Qed.

End LowEquivalence.