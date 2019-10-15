Require Import id_and_loc augmented mmemory mimperative language mlattice bridge types bijection Coq.Program.Tactics Arith Omega tactics low_equivalence nibridge_helper nibridge decision preservation List.
Require Import LibTactics InductionPrinciple Coq.Program.Equality Coq.Program.Basics.
Import FunctionalExtensionality.
Set Implicit Arguments.

Module NI (L : Lattice) (M: Memory L).
  Module NIBridge := NIBridge L M.
  Import NIBridge NIBridgeHelper Preserve LowEq B Aug Imp TDefs M T MemProp LatProp Lang L.

  Ltac invert_step_many_num :=
    match goal with
      [H: _ ⇒ (_, _, _, _) _ |- _] =>
      inverts H
    end.

  Lemma low_event_dec:
    forall ℓ_adv ev, { low_event ℓ_adv ev } + { high_event ℓ_adv ev }.
  Proof.
    intros.
    destruct ev.
    - eauto.
    - destruct (flowsto_dec l ℓ_adv); eauto 3.
      right.
      intro; invert_low_event; contradiction.
    - destruct (flowsto_dec l ℓ_adv); eauto 3.
      right.
      intro; invert_low_event; contradiction.
    - destruct (flowsto_dec l ℓ_adv); eauto 3.
      right.
      intro; invert_low_event; contradiction.
    - destruct (flowsto_dec l ℓ_adv).
      + destruct (flowsto_dec l0 ℓ_adv); eauto 3.
        right.
        intro; invert_low_event; contradiction.
      + right.
        intro; invert_low_event; contradiction.
    - destruct (flowsto_dec l ℓ_adv); eauto 3.
      right.
      intro; invert_low_event; contradiction.
    - destruct (flowsto_dec l ℓ_adv); eauto 3.
      right.
      intro; invert_low_event; contradiction.
  Qed.

  Lemma bridge_step_num_implies_step_many_num:
    forall ℓ_adv Γ Σ Σ' ev n c pc m h t c' pc' m' h' t',
      ⟨c, pc, m, h, t⟩ ↷ [ℓ_adv, Γ, Σ, Σ', ev, n] ⟨c', pc', m', h', t'⟩ ->
      ⟨c, pc, m, h, t⟩ ⇒ (Γ, Σ, Σ', n + 1) ⟨c', pc', m', h', t'⟩.
  Proof.
    intros.
    dependent induction H.
    - invert_low_event_step.
      replace (0 + 1) with 1 by omega.
      constructors; eauto 2.
    - invert_high_event_step.
      replace (0 + 1) with 1 by omega.
      constructors; eauto 2.
    - destruct cfg2.
      remember_simple (IHbridge_step_num _ _ _ _ _ _ _ _ _ _ eq_refl eq_refl).
      replace (S n + 1) with (S (n + 1)) by omega.
      invert_high_event_step.
      constructors; eauto 2.
  Qed.
  Hint Resolve bridge_step_num_implies_step_many_num.

  Lemma concat_step_many_num:
    forall n1 Γ n2 c c' c'' pc pc' pc'' m m' m'' h h' h'' t t' t'' Σ Σ' Σ'',
      ⟨c, pc, m, h, t⟩ ⇒ (Γ, Σ, Σ', n1) ⟨c', pc', m', h', t'⟩ ->
      ⟨c', pc', m', h', t'⟩ ⇒ (Γ, Σ', Σ'', n2) ⟨c'', pc'', m'', h'', t''⟩ ->
      ⟨c, pc, m, h, t⟩ ⇒ (Γ, Σ, Σ'', n1 + n2) ⟨c'', pc'', m'', h'', t''⟩.
  Proof.
    intro n1.
    induction n1; intros.
    - replace (0 + n2) with n2 by omega.
      inverts H.
      eauto 2.
    - replace (S n1 + n2) with (S (n1 + n2)) by omega.
      inverts H.
      eauto 3.
  Qed.
  Hint Resolve concat_step_many_num.
  
  Theorem bridge_adequacy:
    forall Γ n ℓ_adv Σ Σ'' c pc pc'' m m'' h h'' t t'' pc_end,
      wellformed_aux Γ Σ ⟨c, pc, m, h, t⟩ pc_end ->
      ⟨c, pc, m, h, t⟩ ⇒ (Γ, Σ, Σ'', n) ⟨Stop, pc'', m'', h'', t''⟩ ->
      (c = Stop \/
       (c <> Stop /\
        exists ev c' pc' m' h' t' k Σ',
          n > k /\
          ⟨c, pc, m, h, t⟩ ↷ [ℓ_adv, Γ, Σ, Σ', ev, k] ⟨c', pc', m', h', t'⟩ /\
          ⟨c', pc', m', h', t'⟩ ⇒ (Γ, Σ', Σ'', n - k - 1) ⟨Stop, pc'', m'', h'', t''⟩)).
  Proof.
    intros Γ n ℓ_adv.
    induction n; intros.
    - inverts H0.
      left; eauto 2.
    - right.
      
      revert pc m h t H H0.
      induction c; intros.
      + invert_step_many_num.
        assert (wellformed_aux Γ Σ' ⟨c', pc', m', h', t'⟩ pc_end).
        {
          eapply preservation; eauto 2.
        }
        remember_simple (IHn _ _ _ _ _ _ _ _ _ _ _ _ H0 H16).
        super_destruct; subst.
        * invert_step_many_num; try solve[invert_step; exfalso; eauto 2].
          splits; try congruence.
          invert_step.
          do 8 eexists.
          splits*.
        * invert_step.
          {
            exfalso; eauto 2.
          }
          {
            splits; try congruence.
            exists ev c'0 pc'0 m'0 h'0; exists t'0 (S k) Σ'0.
            splits*; try omega.
            constructors; eauto 2.
            - splits*.
            - intro; discriminate.
            - intro; discriminate.
          }
      + invert_step_many_num; solve[invert_step; exfalso; eauto 2] || omega.
      + invert_step_many_num; try solve[invert_step; exfalso; eauto 2].
        assert (wellformed_aux Γ Σ' ⟨c', pc', m', h', t'⟩ pc_end).
        {
          eapply preservation; eauto 2.
        }
        remember_simple (IHn _ _ _ _ _ _ _ _ _ _ _ _ H0 H16).
        super_destruct; subst.
        * invert_step.
          {
            invert_step_many_num; try solve[invert_step; exfalso; eauto 2].
            invert_wf_aux.
            repeat specialize_gen.
            invert_wt_cmd.
            invert_lifted.
            rewrite_inj.
            splits; try congruence.
            destruct l2 as [ℓ ι].
            exists (AssignEvent ℓ i v) Stop pc_end (m [i → v]) h'';
              exists (S t) 0 Σ''.
            splits*; try omega.
            destruct (flowsto_dec ℓ ℓ_adv).
            - constructor; splits*.
            - eapply bridge_stop_num.
              + splits*.
                intro; invert_low_event; contradiction.
              + reflexivity.
          }
        * splits; try congruence. 
          invert_step; try solve[exfalso; eauto 2].
          exists ev (c'0) pc'0 m'0 h'0; exists (t'0) (S k) Σ'0.
          splits*; try omega.
          eapply bridge_trans_num.
          { splits*. }
          { intro; discriminate. }
          { intro; discriminate. }
          { eauto 2. }
      + splits; try congruence.
        invert_step_many_num.
        assert (wellformed_aux Γ Σ' ⟨c', pc', m', h', t'⟩ pc_end).
        {
          eapply preservation; eauto 2.
        }
        remember_simple (IHn _ _ _ _ _ _ _ _ _ _ _ _ H0 H16).
        super_destruct; subst.
        * invert_step_many_num; try solve[invert_step; exfalso; eauto 2].
          invert_step;
            invert_wf_aux;
            repeat specialize_gen;
            invert_wt_cmd;
            invert_wt_stop.
        * exists ev c'0 pc'0 m'0 h'0; exists (t'0) (S k) Σ'0.
          splits*; try omega.
          invert_step.
          {
            constructors.
            - splits*.
            - intro; unfold is_stop_config, cmd_of in *; subst.
              invert_wf_aux;
                repeat specialize_gen;
                invert_wt_cmd;
                invert_wt_stop.
            - intro; unfold is_timeout_config, cmd_of in *; subst.
              invert_wf_aux;
                repeat specialize_gen;
                invert_wt_cmd;
                invert_wt_timeout.
            - eauto 2.
          }
          {
            constructors.
            - splits*.
            - intro; unfold is_stop_config, cmd_of in *; subst.
              invert_wf_aux;
                repeat specialize_gen;
                invert_wt_cmd;
                invert_wt_stop.
            - intro; unfold is_timeout_config, cmd_of in *; subst.
              invert_wf_aux;
                repeat specialize_gen;
                invert_wt_cmd;
                invert_wt_timeout.
            - eauto 2.
          }
          {
            eapply bridge_trans_num.
            { splits*. }
            { intro; discriminate. }
            { intro; discriminate. }
            { eauto 2. }
          }
      + splits; try congruence.
        invert_step_many_num.
        assert (wellformed_aux Γ Σ' ⟨c', pc', m', h', t'⟩ pc_end).
        {
          eapply preservation; eauto 2.
        }
        remember_simple (IHn _ _ _ _ _ _ _ _ _ _ _ _ H0 H16).
        super_destruct; subst.
        * invert_step_many_num; try solve[invert_step; exfalso; eauto 2].
          invert_step.
          do 8 eexists.
          splits*.
        * exists ev c'0 pc'0 m'0 h'0; exists (t'0) (S k) Σ'0.
          invert_step; try solve[exfalso; eauto 2].
          {
            splits*; try omega.
            eapply bridge_trans_num.
            { splits*. }
            { intro; discriminate. }
            { intro; discriminate. }
            { eauto 2. }
          }
          {
            splits*; try omega.
            eapply bridge_trans_num.
            { splits*. }
            { intro; discriminate. }
            { intro; discriminate. }
            { eauto 2. }
          }
      + splits; try congruence.
        invert_step_many_num.
        assert (wellformed_aux Γ Σ' ⟨c', pc', m', h', t'⟩ pc_end).
        {
          eapply preservation; eauto 2.
        }
        remember_simple (IHn _ _ _ _ _ _ _ _ _ _ _ _ H0 H16).
        super_destruct; subst.
        * invert_step_many_num; try solve[invert_step; exfalso; eauto 2].
          invert_step.
          invert_wf_aux;
            repeat specialize_gen;
            invert_wt_cmd;
            invert_wt_stop.
        * remember_simple (event_step_adequacy _ _ _ _ _ _ _ _ _ _ _ _ _ _ H H6).
          clear H6.
          super_destruct; subst.
          destruct (low_event_dec ℓ_adv ev0).
          {
            exists ev0 c' pc' m' h'; exists t' 0 Σ'.
            splits*; try omega.
            replace (S n - 0 - 1) with n by omega.
            remember_simple (bridge_step_num_implies_step_many_num H3).
            replace n with ((k + 1) + (n - k - 1)) by omega.
            eauto 2.
          }
          {
            exists ev c'0 pc'0 m'0 h'0; exists (t'0) (S k) Σ'0.
            splits*; try omega.
            eapply bridge_trans_num.
            - splits*.
            - eauto 2.
            - intro; unfold is_timeout_config, cmd_of in *; subst.
              invert_step_many_num.
              invert_step; exfalso; eauto 2.
            - eauto 2.
          }
      + invert_step_many_num; try solve[invert_step; exfalso; eauto 2].
        assert (wellformed_aux Γ Σ' ⟨c', pc', m', h', t'⟩ pc_end).
        {
          eapply preservation; eauto 2.
        }
        remember_simple (IHn _ _ _ _ _ _ _ _ _ _ _ _ H0 H16).
        splits; try congruence.
        super_destruct; subst.
        * invert_step_many_num; try solve[invert_step; exfalso; eauto 2].
        * exists ev c'0 pc'0 m'0 h'0; exists (t'0) (S k) Σ'0.
          splits*; try omega.
          invert_step.
          {
            eapply bridge_trans_num.
            { splits*. }
            { intro; discriminate. }
            { intro; discriminate. }
            { eauto 2. }
          }
          {
            eapply bridge_trans_num.
            { splits*. }
            { intro; discriminate. }
            { intro; discriminate. }
            { eauto 2. }
          }
      + invert_step_many_num; try solve[invert_step; exfalso; eauto 2].
        assert (wellformed_aux Γ Σ' ⟨c', pc', m', h', t'⟩ pc_end).
        {
          eapply preservation; eauto 2.
        }
        remember_simple (IHn _ _ _ _ _ _ _ _ _ _ _ _ H0 H16).
        splits; try congruence.
        super_destruct; subst.
        * invert_step_many_num; try solve[invert_step; exfalso; eauto 2].
          invert_step.
          destruct (flowsto_dec pc'' ℓ_adv).
          {
            do 8 eexists.
            splits*.
            constructor.
            splits*. }
          {
            do 8 eexists.
            splits*.
            eapply bridge_stop_num; eauto 2.
            splits*.
            intro; invert_low_event; contradiction.
          }
        * exists ev c'0 pc'0 m'0 h'0; exists (t'0) (S k) Σ'0.
          splits*; try omega.
          invert_step.
          {
            eapply bridge_trans_num.
            { splits*. }
            { intro; discriminate. }
            { intro; discriminate. }
            { eauto 2. }
          }
          {
            congruence.
          }
          {
            invert_step_many_num; try solve[invert_step; exfalso; eauto 2].
          }
          {
            eapply bridge_trans_num.
            { splits*. }
            { intro; discriminate. }
            { intro; discriminate. }
            { eauto 2. }
          }
      + invert_step_many_num; try solve[invert_step; exfalso; eauto 2].
        assert (wellformed_aux Γ Σ' ⟨c', pc', m', h', t'⟩ pc_end).
        {
          eapply preservation; eauto 2.
        }
        remember_simple (IHn _ _ _ _ _ _ _ _ _ _ _ _ H0 H16).
        super_destruct; subst.
        * invert_step.
          {
            invert_step_many_num; try solve[invert_step; exfalso; eauto 2].
            destruct ℓ as [ℓ ι].
            splits; try congruence.
            exists (NewEvent ℓ i l1) Stop pc''
              (m [i → ValLoc l1]) (extend_heap v l1 l n0 h H1 H2);
            exists (S t) 0 (extend_stenv l1 τ Σ).
            splits*; try omega.
            destruct (flowsto_dec ℓ ℓ_adv).
            - constructor; splits*.
            - eapply bridge_stop_num.
              + splits*.
                intro; invert_low_event; contradiction.
              + reflexivity.
          }
        * splits; try congruence. 
          invert_step; try solve[exfalso; eauto 2].
          exists ev (c'0) pc'0 m'0 h'0; exists (t'0) (S k) Σ'0.
          splits*; try omega.
          eapply bridge_trans_num.
          { splits*. }
          { intro; discriminate. }
          { intro; discriminate. }
          { eauto 2. }
      + invert_step_many_num; try solve[invert_step; exfalso; eauto 2].
        assert (wellformed_aux Γ Σ' ⟨c', pc', m', h', t'⟩ pc_end).
        {
          eapply preservation; eauto 2.
        }
        remember_simple (IHn _ _ _ _ _ _ _ _ _ _ _ _ H0 H16).
        super_destruct; subst.
        * invert_step.
          {
            invert_step_many_num; try solve[invert_step; exfalso; eauto 2].
            invert_wf_aux.
            clear IHn.
            repeat specialize_gen.
            invert_wt_cmd.
            invert_lifted.
            destruct l2 as [ℓ' ι'].
            destruct ε_x as [ℓ_x ι_x].
            splits; try congruence.
            destruct_prod_join_flowsto.
            exists (SetEvent ℓ' ℓ_x i n0 v) Stop pc_end m'' (update_heap l0 n0 v h);
            exists (S t) 0 Σ''.
            splits*; try omega.
            destruct (flowsto_dec ℓ' ℓ_adv).
            - assert (ℓ_x ⊑ ℓ_adv) by eauto 3.
              constructor; splits*.
            - eapply bridge_stop_num.
              + splits*.
                intro; invert_low_event; contradiction.
              + reflexivity.
          }
        * splits; try congruence. 
          invert_step; try solve[exfalso; eauto 2].
          exists ev (c'0) pc'0 m'0 h'0; exists (t'0) (S k) Σ'0.
          splits*; try omega.
          eapply bridge_trans_num.
          { splits*. }
          { intro; discriminate. }
          { intro; discriminate. }
          { eauto 2. }
      + invert_step_many_num; try solve[invert_step; exfalso; eauto 2].
        assert (wellformed_aux Γ Σ' ⟨c', pc', m', h', t'⟩ pc_end).
        {
          eapply preservation; eauto 2.
        }
        remember_simple (IHn _ _ _ _ _ _ _ _ _ _ _ _ H0 H16).
        super_destruct; subst.
        * invert_step.
          {
            invert_step_many_num; try solve[invert_step; exfalso; eauto 2].
            destruct t0 as [σ [ℓ0 ι]].
            splits; try congruence.
            exists (GetEvent ℓ0 i i0 v) Stop pc'' (m [i → v]) h'';
              exists (S t) 0 Σ''.
            splits*; try omega.
            destruct (flowsto_dec ℓ0 ℓ_adv).
            - constructor; splits*.
              invert_wf_aux.
              clear IHn.
              repeat specialize_gen.
              invert_wt_cmd.
              invert_lifted.
              rewrite_inj.
              constructor.
              constructors; eauto 2.
            - eapply bridge_stop_num.
              + splits*.
                * invert_wf_aux.
                  clear IHn.
                  repeat specialize_gen.
                  invert_wt_cmd.
                  invert_lifted.
                  rewrite_inj.
                  constructor.
                  constructors; eauto 2.
                * intro; invert_low_event; contradiction.
              + reflexivity.
          }
        * splits; try congruence. 
          invert_step; try solve[exfalso; eauto 2].
          exists ev (c'0) pc'0 m'0 h'0; exists (t'0) (S k) Σ'0.
          splits*; try omega.
          eapply bridge_trans_num.
          { splits*. }
          { intro; discriminate. }
          { intro; discriminate. }
          { eauto 2. }
      + invert_step_many_num; try solve[invert_step; exfalso; eauto 2].
        assert (wellformed_aux Γ Σ' ⟨c', pc', m', h', t'⟩ pc_end).
        {
          eapply preservation; eauto 2.
        }
        remember_simple (IHn _ _ _ _ _ _ _ _ _ _ _ _ H0 H16).
        super_destruct; subst.
        * invert_step.
          {
            invert_step_many_num; try solve[invert_step; exfalso; eauto 2].
            invert_wf_aux.
            repeat specialize_gen.
            invert_wt_cmd.
            splits; try congruence.
            exists (TimeEvent ℓ i t) Stop pc_end (m [i → ValNum t]) h'';
              exists (S t) 0 Σ''.
            splits*; try omega.
            destruct (flowsto_dec ℓ ℓ_adv).
            - constructor; splits*.
            - eapply bridge_stop_num.
              + splits*.
                intro; invert_low_event; contradiction.
              + reflexivity.
          }
        * splits; try congruence. 
          invert_step; try solve[exfalso; eauto 2].
          exists ev (c'0) pc'0 m'0 h'0; exists (t'0) (S k) Σ'0.
          splits*; try omega.
          eapply bridge_trans_num.
          { splits*. }
          { intro; discriminate. }
          { intro; discriminate. }
          { eauto 2. }
      + invert_step_many_num.
        invert_step; exfalso; eauto 2.
  Qed.

  Definition TINI_idx (n1: nat) (ℓ: level_proj1): Prop :=
    forall Γ Σ1 Σ2 Σ3 Σ1' Σ3' φ Φ pc pc1' pc2'' c c' m1 m2 s1 s2'' h1 h2
      w1 w2'' t t2 g2'' s1' w1' pc_end n2 t',
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
      ⟨c, pc, m1, h1, t⟩ ⇒ (Γ, Σ1, Σ1', n1) ⟨Stop, pc1', m2, h2, t2⟩ ->
      ⟨c', pc, s1', w1', t'⟩ ⇒ (Γ, Σ3, Σ3', n2) ⟨Stop, pc2'', s2'', w2'', g2''⟩ ->
      exists n1' ψ Ψ s2' w2' Σ2',
        ⟨c, pc, s1, w1, t⟩ ⇒ (Γ, Σ2, Σ2', n1') ⟨Stop, pc1', s2', w2', t2⟩ /\
        pc1' ⊑ ℓ /\
        pc2'' = pc1' /\
        state_low_eq ℓ ψ m2 h2 s2' w2' Γ Σ1' Σ2'/\
        wf_bijection ℓ ψ Γ Σ1' m2 h2 /\
        wf_bijection ℓ (inverse ψ) Γ Σ2' s2' w2' /\
        wf_taint_bijection ℓ Ψ s2' w2' /\
        wf_taint_bijection ℓ (inverse Ψ) s2'' w2'' /\
        taint_eq ℓ Ψ Γ Σ2' Σ3' Stop Stop s2' w2' s2'' w2''.

  Lemma tini_idx:
    forall n ℓ, TINI_idx n ℓ.
  Proof.
    intros.
    induction n using strongind.
    - unfolds.
      intros.
      inverts H9.
      invert_taint_eq; invert_taint_eq_cmd; subst.
      inverts H10.
      + exists 0 φ Φ s1 w1 Σ2.
        unfold taint_eq in*; super_destruct'; subst.
        splits*.
      + invert_step; exfalso; eauto 2.
    - unfolds.
      intros.
      remember_simple (bridge_adequacy ℓ H4 H10).
      super_destruct; subst.
      + invert_taint_eq; invert_taint_eq_cmd.
        assert (n2 = 0).
        {
          inverts H11; try reflexivity.
          invert_step; exfalso; eauto 2.
        }
        subst.
        inverts H10.
        invert_step; exfalso; eauto 2.
      + replace (S n - k - 1) with (n - k) in * by omega.
        remember_simple (bridge_adequacy ℓ H6 H11).
        super_destruct; subst.
        * assert (n2 = 0).
          {
            invert_step_many_num; try reflexivity.
            invert_step; exfalso; eauto 2.
          }
          subst.
          invert_taint_eq; invert_taint_eq_cmd.
          exfalso; eauto 2.
        * assert (c'0 <> TIMEOUT).
          {
            intro; subst.
            invert_step_many_num.
            invert_step; exfalso; eauto 2.
          }
          assert (c'1 <> TIMEOUT).
          {
            intro; subst.
            invert_step_many_num.
            invert_step; exfalso; eauto 2.
          }
          remember_simple (ni_bridge_num H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H14 H18 H20 H21).
          super_destruct; subst.
          assert (n - k <= n) by omega.
          assert (wellformed_aux Γ Σ' ⟨c'0, pc', m', h', t'0⟩ pc_end) by eauto 2.
          assert (wellformed_aux Γ Σ2' ⟨c'0, pc', s2', w2', t'0 ⟩ pc_end) by eauto 2.
          assert (wellformed_aux Γ Σ'0 ⟨c'1, pc', m'0, h'0, t'1⟩ pc_end) by eauto 2.
          remember_simple (
              H (n - k) H24 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                H28 H29 H30 H31 H33 H34 H35 H25 H23 H32 H15 H19).
          super_destruct; subst.
          exists (n1' + 1 + n1'0) ψ0 Ψ0 s2'0 w2'0 Σ2'0.
          splits*.
  Qed.

  Lemma empty_bijection_left_inverse:
    forall A B : Type,
      @left_inverse A B (const None) (const None).
  Proof.
    intros.
    unfolds.
    intros.
    discriminate.
  Qed.

  Lemma empty_bijection_right_inverse:
    forall A B : Type,
      @right_inverse A B (const None) (const None).
  Proof.
    intros.
    unfolds.
    intros.
    discriminate.
  Qed.
  
  Lemma empty_bijection {A B : Type}:
    bijection A B.
  Proof.
    eapply (Bijection A B (const None) (const None)
                      (@empty_bijection_left_inverse A B)
                      (@empty_bijection_right_inverse A B)).
  Defined.

  Definition initial_memory (m : Memory) : Prop :=
    forall x v,
      memory_lookup m x = Some v ->
      exists n, v = ValNum n.
  Hint Unfold initial_memory.

  Lemma step_many_num_implies_step_many:
    forall c pc m h t Γ Σ Σ' c' pc' m' h' t' n,
      ⟨c, pc, m, h, t⟩ ⇒ (Γ, Σ, Σ', n) ⟨c', pc', m', h', t'⟩ ->
      ⟨c, pc, m, h, t⟩ ⇒ * (Γ, Σ, Σ') ⟨c', pc', m', h', t'⟩.
  Proof.
    intros.
    dependent induction H; eauto 2.
  Qed.
  Hint Resolve step_many_num_implies_step_many.

  Definition memory_low_eq φ ℓ_adv (Γ : tenv) m1 m2 :=
    (forall x σ ℓ ι,
        Γ x = Some (SecType σ (ℓ, ι)) ->
        ℓ ⊑ ℓ_adv ->
        (exists v, memory_lookup m1 x = Some v) <->
        (exists u, memory_lookup m2 x = Some u))
    /\
    (forall x τ v u,
        Γ x = Some τ ->
        memory_lookup m1 x = Some v ->
        memory_lookup m2 x = Some u ->
        val_low_eq ℓ_adv τ v u φ).

  Inductive std_gc_step: config -> config -> Prop :=
  | std_step_gc:
      forall pc m h1 h2 h1_pc h1_not_pc t c δ H1 H2 H3,
        c <> Stop ->
        c <> TimeOut ->
        (forall loc ℓ μ, heap_lookup loc h2 = Some (ℓ, μ) ->
                    ~ reach m ([h1 ⊎ h2, H1]) loc) ->
        levels_satisfy h2 (eq pc) ->
        h1 = [h1_pc ⊎ h1_not_pc, H2] ->
        levels_satisfy h1_pc (eq pc) ->
        levels_satisfy h1_not_pc (compose not (eq pc)) ->
        gc m ([h1_pc ⊎ h2, H3]) δ h1_pc ->
        std_gc_step (Config c pc m ([h1 ⊎ h2, H1]) t) (Config c pc m h1 (t + δ)).
  
  Inductive std_sem_step: config -> config -> Prop :=
  | std_step_skip:
      forall pc m h t,
        std_sem_step (Config Skip pc m h t) (Config Stop pc m h (S t))
  | std_step_assign:
      forall pc m h x e v t,
        eval m e = Some v ->
        std_sem_step (Config (Assign x e) pc m h t)
                     (Config Stop pc (extend_memory x v m) h (S t))
  | std_step_if_false:
      forall pc m h e c1 c2 n t,
        eval m e = Some (ValNum n) ->
        n = 0 ->
        std_sem_step (Config (If e c1 c2) pc m h t)
                     (Config c2 pc m h (S t))
  | std_step_if_true:
      forall pc m h e c1 c2 n t,
        eval m e = Some (ValNum n) ->
        n <> 0 ->
        std_sem_step (Config (If e c1 c2) pc m h t)
                     (Config c1 pc m h (S t))
  | std_step_while_false:
      forall pc m h e c n t,
        eval m e = Some (ValNum n) ->
        n = 0 ->
        std_sem_step (Config (While e c) pc m h t)
                     (Config Stop pc m h (S t))
  | std_step_while_true:
      forall pc m h e c n t,
        eval m e = Some (ValNum n) ->
        n <> 0 ->
        std_sem_step (Config (While e c) pc m h t)
                     (Config (Seq c (While e c)) pc m h (S t))
  | std_step_seq_stop:
      forall pc pc' m m' h h' c1 c2 t t',
        std_step (Config c1 pc m h t)
                 (Config Stop pc' m' h' t') ->
        std_sem_step (Config (Seq c1 c2) pc m h t)
                     (Config c2 pc' m' h' t')
  | std_step_seq_nonstop:
      forall pc pc' m m' h h' c1 c1' c2 t t',
        std_step (Config c1 pc m h t)
             (Config c1' pc' m' h' t') ->
        c1' <> Stop ->
        c1' <> TimeOut ->
        std_sem_step (Config (Seq c1 c2) pc m h t)
                     (Config (Seq c1' c2) pc' m' h' t')
  | std_step_time:
      forall pc m h t x,
        std_sem_step (Config (Time x) pc m h t)
                 (Config Stop pc (extend_memory x (ValNum t) m) h
                         (S t))
  | std_step_new:
      forall pc m h t e e_init ℓ_p x n v l
        (H1: heap_lookup l h = None) (H2: size ℓ_p h + n <= maxsize ℓ_p h),
        eval m e = Some (ValNum n) ->
        eval m e_init = Some v ->
        std_sem_step (Config (NewArr x ℓ_p e e_init) pc m h t)
                     (Config Stop pc
                             (extend_memory x (ValLoc l) m)
                             (extend_heap v l ℓ_p n h H1 H2) (S t))
  | std_step_get:
      forall pc m h x y e l n v length t ℓ μ,
        memory_lookup m y = Some (ValLoc l) ->
        eval m e = Some (ValNum n) ->
        length_of l h = Some length ->
        0 <= n ->
        n < length ->
        heap_lookup l h = Some (ℓ, μ) ->
        lookup μ n = Some v ->
        std_sem_step (Config (GetArr x y e) pc m h t)
                     (Config Stop pc (extend_memory x v m) h (S t))
  | std_step_set:
      forall pc m h t x e1 e2 l n v length,
        memory_lookup m x = Some (ValLoc l) ->
        eval m e1 = Some (ValNum n) ->
        length_of l h = Some length ->
        0 <= n ->
        n < length ->
        eval m e2 = Some v ->
        std_sem_step (Config (SetArr x e1 e2) pc m h t)
                     (Config Stop pc m (update_heap l n v h) (S t))
  | std_step_at:
      forall pc m h t l c e n,
        eval m e = Some (ValNum n) ->
        std_sem_step (Config (At l e c) pc m h t)
                     (Config (Seq c (BackAt pc (n + t))) l m h (S t))
  | step_backat_wait:
      forall pc m h t l n,
        t < n ->
        std_sem_step (Config (BackAt l n) pc m h t)
                     (Config (BackAt l n) pc m h (S t))
  | step_backat_progress:
      forall pc m h t l,
        std_sem_step (Config (BackAt l t) pc m h t)
                     (Config Stop l m h (S t))
  | step_timeout:
      forall pc m h t l n,
        t > n ->
        std_sem_step (Config (BackAt l n) pc m h t)
                     (Config TimeOut l m h (S t))
  with std_step : config -> config -> Prop :=
       | StdSemStep:
           forall c c' pc pc' m m' h h' t t',
             std_sem_step (Config c pc m h t) (Config c' pc' m' h' t') ->
             std_step (Config c pc m h t) (Config c' pc' m' h' t')
       | StdGCStep:
           forall c c' pc pc' m m' h h' t t',
             std_gc_step (Config c pc m h t) (Config c' pc' m' h' t') ->
             std_step (Config c pc m h t) (Config c' pc' m' h' t').
  Hint Constructors std_gc_step.
  Hint Constructors std_sem_step.
  Hint Constructors std_step.

  Notation "cfg1 '⇒' cfg2" := (std_step cfg1 cfg2)
                                (at level 10, no associativity).

   Inductive std_step_many: config -> config -> Prop :=
  | StepMany0: forall cfg1 cfg2, cfg1 = cfg2 -> std_step_many cfg1 cfg2
  | StepManyN:
      forall cfg1 cfg cfg2,
        std_step cfg1 cfg -> std_step_many cfg cfg2 ->
        std_step_many cfg1 cfg2.
  Hint Constructors std_step_many.
  
  Notation "cfg1 '⇒' '*' cfg2" := (std_step_many cfg1 cfg2)
                                    (at level 10, no associativity).

  Ltac invert_std_sem_step :=
    match goal with [ H : std_sem_step _ _ |-  _ ] => inverts H end.

  Ltac invert_std_gc_step :=
    match goal with [ H : std_gc_step _ _ |-  _ ] => inverts H end.
  
  Ltac invert_std_step :=
    match goal with [ H : _ ⇒ _ |-  _ ] => inverts H; [> invert_std_sem_step | invert_std_gc_step] end.
  
  Lemma std_step_implies_step:
    forall c Γ pc m h t c' pc' m' h' t' Σ pc_end,
      wellformed_aux Γ Σ ⟨c, pc, m, h, t⟩ pc_end ->
      ⟨c, pc, m, h, t⟩ ⇒ ⟨c', pc', m', h', t'⟩ ->
      exists Σ',
        ⟨c, pc, m, h, t⟩ ⇒ (Γ, Σ, Σ') ⟨c', pc', m', h', t'⟩.
  Proof.
    intros c Γ.
    induction c; intros; try solve[eexists; invert_std_step; eauto].
    - invert_std_step; eauto.
      + _apply wf_seq1 in *.
        super_destruct; subst.
        remember_simple (IHc1 _ _ _ _ _ _ _ _ _ _ _ H H1).
        super_destruct; subst.
        exists Σ'.
        eauto.
      + _apply wf_seq1 in *.
        super_destruct; subst.
        remember_simple (IHc1 _ _ _ _ _ _ _ _ _ _ _ H H4).
        super_destruct; subst.
        exists Σ'.
        eauto.
    - invert_std_step; eauto.
      invert_wf_aux.
      repeat specialize_gen.
      invert_wt_cmd.
      exists (extend_stenv l1 τ Σ).
      eauto.
    - invert_std_step; eauto.
      invert_wf_aux.
      repeat specialize_gen.
      invert_wt_cmd; eauto.
  Qed.
  Hint Resolve std_step_implies_step.

  Lemma std_step_implies_step_many:
    forall c Γ pc m h t c' pc' m' h' t' Σ pc_end,
      wellformed_aux Γ Σ ⟨c, pc, m, h, t⟩ pc_end ->
      ⟨c, pc, m, h, t⟩ ⇒ * ⟨c', pc', m', h', t'⟩ ->
      exists Σ',
        ⟨c, pc, m, h, t⟩ ⇒ * (Γ, Σ, Σ') ⟨c', pc', m', h', t'⟩.
  Proof.
    intros.
    revert Σ H.
    dependent induction H0; intros; eauto 3.
    destruct cfg.
    remember_simple (std_step_implies_step H1 H).
    super_destruct; subst.
    assert (wellformed_aux Γ Σ' ⟨c0, pc0, memory, heap, time⟩ pc_end).
    {
      eapply preservation; eauto.
    }
    remember_simple (IHstd_step_many _ _ _ _ _ _ _ _ _ _ eq_refl eq_refl _ H3).
    super_destruct; subst.
    exists Σ'0.
    eauto.
  Qed.
  Hint Resolve std_step_implies_step_many.

  Lemma step_implies_std_step:
    forall c Γ pc m h t c' pc' m' h' t' Σ Σ' pc_end,
      wellformed_aux Γ Σ ⟨c, pc, m, h, t⟩ pc_end ->
      ⟨c, pc, m, h, t⟩ ⇒ (Γ, Σ, Σ') ⟨c', pc', m', h', t'⟩ ->
      ⟨c, pc, m, h, t⟩ ⇒ ⟨c', pc', m', h', t'⟩.
  Proof.
    intros c Γ.
    induction c; intros; try solve[invert_step; eauto].
    - invert_step; eauto 3.
      + _apply wf_seq1 in *.
        super_destruct.
        eauto using IHc1.
      + _apply wf_seq1 in *.
        super_destruct.
        eauto using IHc1.
  Qed.
  Hint Resolve step_implies_std_step.

  Lemma step_implies_std_step_many:
    forall c Γ pc m h t c' pc' m' h' t' Σ Σ' pc_end,
      wellformed_aux Γ Σ ⟨c, pc, m, h, t⟩ pc_end ->
      ⟨c, pc, m, h, t⟩ ⇒ * (Γ, Σ, Σ') ⟨c', pc', m', h', t'⟩ ->
      ⟨c, pc, m, h, t⟩ ⇒ * ⟨c', pc', m', h', t'⟩.
  Proof.
    intros.
    dependent induction H0; eauto 2.
    destruct cfg.
    remember_simple (step_implies_std_step H H1).
    assert (wellformed_aux Γ Σ' ⟨ c0, pc0, memory, heap, time ⟩ pc_end).
    {
      eapply preservation; eauto 2.
    }
    eauto.
  Qed.
  Hint Resolve step_implies_std_step_many.

  Lemma wt_implies_wt_aux:
    forall Γ pc c,
      ~ contains_backat c ->
      wt Γ pc c ->
      exists pc_end,
        wt_aux Γ pc c pc_end.
  Proof.
    intros.
    dependent induction H0; eauto.
    - super_destruct; subst.
      intuition.
      super_destruct.
      assert (~ contains_backat c1) by intuition.
      assert (~ contains_backat c2) by intuition.
      assert (pc = pc_end0) by eauto 2.
      assert (pc = pc_end) by eauto 2.
      repeat subst.
      eauto.
    - super_destruct; subst.
      intuition.
      super_destruct.
      assert (~ contains_backat c) by intuition.
      assert (pc = pc_end) by eauto 2.
      subst.
      eauto.
    - intuition.
      super_destruct.
      assert (pc = pc_end0) by eauto.
      assert (pc = pc_end) by eauto.
      repeat subst.
      eauto.
    - intuition.
      super_destruct; subst.
      assert (~ contains_backat c) by intuition.
      assert (ℓ = pc_end) by eauto 2.
      subst.
      eauto.
  Qed.
  Hint Resolve wt_implies_wt_aux.

  Ltac invert_contains_backat :=
    match goal with
      [H: contains_backat _ |- _] => inverts H
    end.
  
  Lemma wt_program_has_no_backat:
    forall Γ pc c,
      wt Γ pc c ->
      ~ contains_backat c.
  Proof.
    intros.
    dependent induction H; intro; invert_contains_backat; eauto 2.
  Qed.
  Hint Resolve wt_program_has_no_backat.
    
  Theorem TINI:
    forall ℓ_adv Γ c m1 m2 m1' m2' h2' h1' t pc1_end pc2_end t1' t2',
      wt Γ bot c ->
      wf_tenv Γ m1 ->
      wf_tenv Γ m2 ->
      initial_memory m1 ->
      initial_memory m2 ->
      memory_low_eq empty_bijection ℓ_adv Γ m1 m2 ->
      ⟨c, bot, m1, emptyHeap, t⟩ ⇒ * ⟨Stop, pc1_end, m1', h1', t1'⟩ ->
      ⟨c, bot, m2, emptyHeap, t⟩ ⇒ * ⟨Stop, pc2_end, m2', h2', t2'⟩ ->
      exists ψ s' w',
        ⟨c, bot, m2, emptyHeap, t⟩ ⇒ * ⟨Stop, pc2_end, s', w', t1'⟩
        /\ memory_low_eq ψ ℓ_adv Γ m1' s'.
  Proof.
    intros.
    assert (~ contains_backat c) by eauto 2.
    assert (exists pc_end, wt_aux Γ bot c pc_end) by eauto 2.
    clear H.
    super_destruct.

    assert (wellformed_aux Γ emptyStenv ⟨c, bot, m1, emptyHeap, t⟩ pc_end).
    {
      constructor; eauto 2.
      - unfolds.
        intros.
        splits.
        + intros.
          discriminate.
        + intros.
          discriminate.
        + intros.
          discriminate.
        + intros.
          assert (heap_lookup loc emptyHeap = None) by eauto 2.
          congruence.
      - unfolds.
        splits.
        + intros.
          assert (exists n, ValLoc loc = ValNum n) by eauto 2.
          super_destruct; discriminate.
        + intros.
          discriminate.
      - unfolds.
        intros.
        invert_reach.
        * assert (exists n, ValLoc loc = ValNum n) by eauto 2.
          super_destruct; discriminate.
        * assert (heap_lookup loc0 emptyHeap = None) by eauto 2.
          congruence.
      - unfolds.
        intros.
        invert_reach.
        + assert (exists n, ValLoc loc = ValNum n) by eauto 2.
          super_destruct; discriminate.
        + assert (heap_lookup loc0 emptyHeap = None) by eauto 2.
          congruence.
      - unfolds.
        splits.
        + intros.
          assert (exists n, ValLoc loc = ValNum n) by eauto 2.
          super_destruct; discriminate.
        + intros.
          discriminate.
        + intros.
          invert_reach.
          * assert (exists n, ValLoc loc1 = ValNum n) by eauto 2.
            super_destruct; discriminate.
          * assert (heap_lookup loc1 emptyHeap = None) by eauto 2.
            congruence.
    }

    assert (wellformed_aux Γ emptyStenv ⟨c, bot, m2, emptyHeap, t⟩ pc_end).
    {
      constructor; eauto 2.
      - unfolds.
        intros.
        splits.
        + intros.
          discriminate.
        + intros.
          discriminate.
        + intros.
          discriminate.
        + intros.
          assert (heap_lookup loc emptyHeap = None) by eauto 2.
          congruence.
      - unfolds.
        splits.
        + intros.
          assert (exists n, ValLoc loc = ValNum n) by eauto 2.
          super_destruct; discriminate.
        + intros.
          discriminate.
      - unfolds.
        intros.
        invert_reach.
        * assert (exists n, ValLoc loc = ValNum n) by eauto 2.
          super_destruct; discriminate.
        * assert (heap_lookup loc0 emptyHeap = None) by eauto 2.
          congruence.
      - unfolds.
        intros.
        invert_reach.
        + assert (exists n, ValLoc loc = ValNum n) by eauto 2.
          super_destruct; discriminate.
        + assert (heap_lookup loc0 emptyHeap = None) by eauto 2.
          congruence.
      - unfolds.
        splits.
        + intros.
          assert (exists n, ValLoc loc = ValNum n) by eauto 2.
          super_destruct; discriminate.
        + intros.
          discriminate.
        + intros.
          invert_reach.
          * assert (exists n, ValLoc loc1 = ValNum n) by eauto 2.
            super_destruct; discriminate.
          * assert (heap_lookup loc1 emptyHeap = None) by eauto 2.
            congruence.
    }
    remember_simple (std_step_implies_step_many H H5).
    clear H5.
    remember_simple (std_step_implies_step_many H9 H6).
    clear H6.
    super_destruct; subst.
    _apply step_many_implies_step_many_num in *.
    super_destruct; subst.

    assert (wf_bijection ℓ_adv empty_bijection Γ emptyStenv m1 emptyHeap).
    {
      unfolds.
      intros.
      splits; intros.
      - super_destruct; subst.
        discriminate.
      - destruct_low.
        + invert_low_reach.
          * assert (exists n, ValLoc loc = ValNum n) by eauto 2.
            super_destruct; discriminate.
          * discriminate.
        + assert (heap_lookup loc emptyHeap = None) by eauto 2.
          congruence.
    }

    assert (wf_bijection ℓ_adv (inverse empty_bijection) Γ emptyStenv m2 emptyHeap).
    {
      unfolds.
      intros.
      splits; intros.
      - super_destruct; subst.
        discriminate.
      - destruct_low.
        + invert_low_reach.
          * assert (exists n, ValLoc loc = ValNum n) by eauto 2.
            super_destruct; discriminate.
          * discriminate.
        + assert (heap_lookup loc emptyHeap = None) by eauto 2.
          congruence.
    }

    assert (wf_taint_bijection ℓ_adv empty_bijection m2 emptyHeap).
    {
      unfolds.
      intros.
      splits; intros.
      - super_destruct; discriminate.
      - destruct_high.
        + invert_reach.
          * assert (exists n, ValLoc loc = ValNum n) by eauto 2.
            super_destruct; discriminate.
          * assert (heap_lookup loc0 emptyHeap = None) by eauto 2.
            congruence.
        + assert (heap_lookup loc emptyHeap = None) by eauto 2.
          congruence.
    }

    assert (wf_taint_bijection ℓ_adv (inverse empty_bijection) m2 emptyHeap).
    {
      unfolds.
      intros.
      splits; intros.
      - super_destruct; discriminate.
      - destruct_high.
        + invert_reach.
          * assert (exists n, ValLoc loc = ValNum n) by eauto 2.
            super_destruct; discriminate.
          * assert (heap_lookup loc0 emptyHeap = None) by eauto 2.
            congruence.
        + assert (heap_lookup loc emptyHeap = None) by eauto 2.
          congruence.
    }
    
    assert (bot ⊑ ℓ_adv).
    {
      eapply join_flowsto; eauto 2.
    }

    assert (taint_eq ℓ_adv empty_bijection Γ emptyStenv emptyStenv c c m2 emptyHeap m2
                     emptyHeap).
    {
      unfolds.
      splits~.
      - unfolds.
        intros.
        splits*.
        intros.
        rewrite_inj.
        destruct τ as [σ ε].
        destruct σ.
        + assert (exists n, v2 = ValNum n) by eauto 2.
          super_destruct; subst.
          eauto 2.
        + assert (exists n, v2 = ValNum n) by eauto 2.
          super_destruct; subst.
          assert (exists loc, ValNum n1 = ValLoc loc).
          {
            repeat invert_wf_aux; eauto 2.
          }
          super_destruct; discriminate.
      - unfolds.
        intros.
        discriminate.
      - unfolds.
        intros.
        discriminate.
      - unfolds.
        intros.
        discriminate.
      - unfolds.
        intros.
        discriminate.
    }

    assert (state_low_eq ℓ_adv empty_bijection m1 emptyHeap m2 emptyHeap Γ emptyStenv emptyStenv).
    {
      constructors; eauto 2.
      - unfolds.
        intros.
        discriminate.
      - unfolds.
        intros.
        eapply H4; eauto 2.
      - unfolds.
        intros.
        discriminate.
      - unfolds.
        eapply H4; eauto 2.
      - unfolds.
        intros.
        discriminate.
      - unfolds.
        intros.
        discriminate.
      - intros.
        discriminate.
    }
    match goal with
      [H1: wf_bijection _ _ _ _ ?m1 _,
       H2: wf_bijection _ _ _ _ ?m2 _,
       H3: wf_taint_bijection _ _ ?m2 _,
       H4: wf_taint_bijection _ (inverse _) ?m2 _,
       H5: wellformed_aux _ _ ⟨_, _, ?m1, _, _⟩ _,
       H6: wellformed_aux _ _ ⟨_, _, ?m2, _, _⟩ _,
       H7: context[state_low_eq],
       H8: bot ⊑ _,
       H9: context[taint_eq],
       H10: ⟨_, _, ?m1, _, _⟩ ⇒ (_, _, _, _) ⟨_, _, _, _, _⟩,
       H11: ⟨_, _, ?m2, _, _⟩ ⇒ (_, _, _, _) ⟨_, _, _, _, _⟩ |- _] =>
      remember_simple (tini_idx H1 H2 H3 H4 H5 H6 H6 H7 H8 H9 H10 H11)
    end.
    super_destruct; subst.
    exists ψ s2' w2'.
    splits*.
    unfolds.
    splits.
    - intros.
      invert_state_low_eq.
      eapply H28; eauto 2.
    - intros.
      invert_state_low_eq.
      eapply H31; eauto 2.
  Qed.
  
End NI.