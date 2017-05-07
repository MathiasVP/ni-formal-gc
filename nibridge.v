Require Import id_and_loc augmented mmemory mimperative language mlattice bridge types bijection Coq.Program.Tactics Arith Omega tactics low_equivalence nibridge_helper decision preservation List.
Require Import LibTactics InductionPrinciple Coq.Program.Equality Coq.Program.Basics.
Import FunctionalExtensionality.
Set Implicit Arguments.

Module NIBridge (L : Lattice) (M: Memory L).
  Module NIBridgeHelper := NIBridgeHelper L M.
  Import NIBridgeHelper Preserve LowEq B Aug Imp TDefs M T MemProp LatProp Lang L.
  
Theorem ni_bridge_num:
  forall n ℓ, ni_bridge n ℓ.
Proof.
  intros.
  induction n using strongind.
  {
    (* n = 0 *)
    unfold ni_bridge.
    intros.
    revert Σ1 Σ2 Σ1' Σ3 Σ3' H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
    revert pc pc1' pc2'' pc_end.
    revert φ Φ.
    revert c' c2 c2' H11 H12.
    revert m1 m2 s1 s2'' s1' w1' h1 h2 w1 w2''.
    revert t t' t2 g2''.
    revert ev1 ev2.
    revert n2.
    induction c; intros; subst.
    (* Skip *)
    {
      invert_bridge_step_with_steps 0.
      - invert_low_event_step.
        invert_event_step.
        + invert_low_event.
        + invert_low_event.
      - unfold is_stop_config, cmd_of in *; subst.
        invert_high_event_step.
        invert_event_step.
        + super_destruct; subst.
          * invert_sem_step.            
            invert_taint_eq.
            invert_taint_eq_cmd.
            exists EmptyEvent 0 φ Φ s1 w1; exists Σ2.
            _apply skip_bridge_properties in *.
            super_destruct; subst.            
            splits*.
            { unfolds.
              splits*. }
            { splits; eauto 2.
              - unfolds.
                intros.
                splits.
                + intros.
                  eapply low_gc_trans_preserves_high; eauto 2.
                  eapply H2; eauto.
                + intros.
                  assert (high ℓ s2'' w1' loc).
                  {
                    eapply high_iff; reflexivity || eauto 2.
                  }
                  eapply H2; eauto.
              - remember_simple (low_gc_trans_preserves_taint_eq H5 H7 H22).
                rewrite <- (compose_id_right Φ).
                eapply taint_eq_trans with (m' := s2'') (h' := w1').
                + repeat invert_wf_aux; eauto 2.
                + unfolds.
                  splits*.
                + unfold taint_eq in *; super_destruct'; subst.
                  splits*.
            }
    }
    
    (* Stop *)
    {
      invert_bridge_step_with_steps 0.
      - exfalso; eauto 2.
      - unfold high_event_step in *.
        super_destruct;
          subst;
          invert_event_step; exfalso; eauto using stop_takes_no_step.
    }

    (* Assign *)
    {
      invert_bridge_step_with_steps 0.
      - invert_low_event_step.
        invert_event_step.
        + assert (wellformed_aux Γ Σ1' ⟨ Stop, pc1', m2, h2, t2 ⟩ pc_end).
          {
            eapply preservation; eauto.
          }
          assert (wellformed_aux Γ Σ3' ⟨c2', pc2'', s2'', w2'', g2''⟩ pc_end) by eauto 2.
          invert_taint_eq.
          invert_taint_eq_cmd.
          _apply assign_bridge_properties in *.
          super_destruct; subst.
          assert (wellformed_aux Γ Σ3' ⟨i ::= e, pc2'', s1', w2'', g2'' - 1⟩ pc_end) by eauto 2.
          invert_sem_step.
          rewrite_inj.
          repeat invert_wf_aux.
          assert ((i ::= e) <> Stop) by congruence.
          assert ((i ::= e) <> TimeOut) by congruence.
          do 4 specialize_gen.
          do 2 invert_wt_cmd.
          invert_lifted.
          rewrite_inj.
          invert_bridge_step_with_steps 0.
          * invert_low_event_step.
            invert_event_step.
            invert_sem_step.
            rewrite_inj.
            match goal with
              [H: S (?X - 1) = ?X |- _] => clear H
            end.
           
            destruct_prod_join_flowsto.
            destruct ε as [ℓ' ι'].
            invert_low_event.
            assert (taint_eq_mem (inverse Φ) Γ s1' s1) by eauto 2 using taint_eq_mem_sym.
            assert (exists v2, eval s1 e = Some v2 /\ val_taint_eq (inverse Φ) (SecType τ (ℓ', ι')) v1 v2) by eauto 2.
            super_destruct; subst.
            rename v2 into u.
            destruct_prod_join_flowsto.
            assert (val_low_eq ℓ (SecType τ (ℓ1, ι0)) v0 u φ)
              by (invert_state_low_eq; eauto 3).            
            remember_simple (filter_bijection (low ℓ Γ Σ1' (extend_memory i v0 m1) h2) (low_dec ℓ Γ Σ1' (extend_memory i v0 m1) h2) φ).
            remember_simple (filter_bijection
                               (high ℓ (extend_memory i u s1) w1)
                               (high_dec ℓ (extend_memory i u s1) w1) Φ).
            super_destruct; subst.
            rename ψ into Ψ.
            rename ψ0 into ψ.
            exists (AssignEvent ℓ1 i u).
            exists 0.
            exists ψ.
            exists Ψ.
            exists (extend_memory i u s1).
            exists w1.
            exists Σ2.
            assert (state_low_eq ℓ ψ (m1 [i → v0]) h2
                                 (s1 [i → u]) w1 Γ Σ1' Σ2).
            {
              eapply state_low_eq_extend_memory; intros; subst; eauto 2.
              - intros; subst.
                assert (exists loc, v0 = ValLoc loc) by eauto 2.
                super_destruct; subst.
                exists loc.
                splits~.
                intros.
                eapply eval_low_implies_low_reach; eauto 3.
              - intros; subst.
                assert (exists loc, u = ValLoc loc) by eauto 2.
                super_destruct; subst.
                exists loc.
                splits~.
                intros.
                eapply eval_low_implies_low_reach; eauto.
              - subst; eauto 2.
              - subst; eauto 2.
              - eapply wf_tenv_extend.
                + eauto.
                + eauto.
                + intros; subst.
                  eauto 2.
                + intros; subst.
                  eauto 2.
            }
            assert (wf_bijection ℓ ψ Γ Σ1' (m1 [i → v0]) h2).
            {
              invert_low_event.
              destruct ε0 as [ℓ_e ι_e].            
              eapply wf_bijection_extend_mem1; eauto 2.
              - intros; subst; eauto 2.
              - intros; subst.
                assert (exists loc, v0 = ValLoc loc) by eauto 2.
                super_destruct; subst.
                exists loc.
                splits~.
                intros.
                assert (wf_type bot (SecType (Array τ0 ℓ'0) (ℓ', ι'))) by eauto 2.
                invert_wf_type.
                assert (exists x, memory_lookup m1 x = Some (ValLoc loc) /\ e = Var x)
                  by eauto 2.
                super_destruct; subst.
                rewrite_inj.
                do 2 invert_var_typing.
                rewrite_inj.
                assert (ℓ_e ⊑ ℓ1) by eauto 2.
                eauto 3.
            }
            splits~.
            {
              eapply bridge_low_num.
              splits~.
              eauto.
            }
            { invert_low_event.
              constructor.
              - splits*.
              - intros _.
                constructor.
                repeat destruct_prod_join_flowsto.
                repeat invert_state_low_eq.
                invert_val_low_eq.
                + exfalso; eauto.
                + exfalso; eauto.
                + eauto.
                + assert (wf_type bot (SecType (Array τ0 ℓ_p) (ℓ1, ι0))) by eauto 2.
                  invert_wf_type.
                  assert (low ℓ Γ Σ1' (m1 [i → ValLoc l1]) h2 l1).
                  {
                    eapply LowReachable.
                    eauto 3.
                  }
                  eauto 3.
            }
            {
              eapply TaintEqEventAssign.
              - eauto.
              - invert_val_taint_eq; eauto 3.
                assert (left Φ loc' = Some loc) by (destruct Φ; eauto).
                assert (high ℓ (s1 [i → ValLoc loc'])
                             w1 loc') by eauto 3.
                assert (left Ψ loc' = Some loc) by eauto 2.
                eauto.
            }
            
            assert (taint_eq ℓ Ψ Γ Σ2 Σ3' Stop Stop (s1 [i → u]) w1
                             (s1' [i → v1]) w2'').
            {
              assert (taint_eq ℓ (identity_bijection loc) Γ Σ3' Σ3' (i ::= e) (i ::= e) s1' w1' s1' w2'').
              {
                eauto 3 using low_gc_trans_preserves_taint_eq.
              }
              unfold taint_eq in *; super_destruct'; subst.
              splits~.
              - eapply taint_eq_mem_extend; eauto 4.
              - eapply taint_eq_reach_extend_mem; eauto 2.
                + assert (taint_eq_reach (identity_bijection loc) s1' w1' s1' w2'')
                    by eauto 2.
                  rewrite <- (compose_id_right Φ).
                  eapply taint_eq_reach_trans; eauto.
                + rewrite <- (compose_id_right Φ).
                  eapply taint_eq_heap_trans; eauto 2.
                + eapply low_gc_trans_preserves_wf_taint_bijection with (pc := pc_end); eauto.
                + eauto 4.
                + intros; subst; eauto 2.
                + intros; subst; eauto 2.
              - eapply taint_eq_heap_extend_mem.
                + eapply taint_eq_heap_trans; eauto 2.
                + eauto.
                + intros; subst; eauto 2.
                + intros; subst; eauto 2.
                + intros; subst.
                  assert (exists loc, u = ValLoc loc) by eauto 2.
                  super_destruct; subst.
                  exists loc.
                  splits; eauto 3.
                + intros; subst.
                  assert (exists loc, v1 = ValLoc loc) by eauto 2.
                  super_destruct; subst.
                  exists loc.
                  splits; eauto 3.
                + rewrite -> compose_id_right.
                  eauto.
                + rewrite -> compose_id_right.
                  eapply low_gc_trans_preserves_wf_taint_bijection with (pc := pc_end); eauto 2.
                + rewrite -> compose_id_right.
                  eauto.
              - eapply taint_eq_heap_size_trans; eauto 2.
              - repeat invert_wf_aux.
                eapply taint_eq_heap_domain_eq_extend_mem with (Φ := bijection.bijection_compose Φ (identity_bijection loc)); eauto 2.
                + eapply taint_eq_heap_domain_eq_trans; eauto 2.
                + rewrite -> compose_id_right.
                  eauto.
                + rewrite -> compose_id_right.
                  eapply low_gc_trans_preserves_wf_taint_bijection
                  with (pc := pc_end); eauto.
                + eapply taint_eq_mem_trans; eauto 2.
                + eapply taint_eq_heap_trans; eauto 2.
                + eapply taint_eq_reach_trans; eauto 2.
                + rewrite -> compose_id_right.
                  eauto.
                + rewrite -> compose_id_right.
                  eauto.
                + rewrite -> compose_id_right.
                  eauto.
                + rewrite -> compose_id_right.
                  eapply low_gc_trans_preserves_wf_taint_bijection
                  with (pc := pc_end); eauto.
                + intros; subst.
                  assert (exists loc, u = ValLoc loc) by eauto 2.
                  super_destruct; subst.
                  exists loc.
                  splits; eauto 3.
                + intros; subst; eauto 3.
                + intros; subst.
                  assert (exists loc, v1 = ValLoc loc) by eauto 2.
                  super_destruct; subst.
                  exists loc.
                  splits; eauto 3.
                + intros; subst; eauto 3.
                + rewrite -> compose_id_right.
                  eauto.
              - eapply taint_eq_stenv_extend_mem; eauto 2.
            }
            splits.
            {
              eapply wf_bijection_extend_mem2; eauto 3.
              - intros; subst.
                eauto 2.
              - intros; subst.
                assert (exists loc, u = ValLoc loc) by eauto 2.
                super_destruct; subst.
                exists loc.
                splits~.
                destruct ε0 as [ℓ_e ι_e].
                intros.
                assert (wf_type bot (SecType (Array τ0 ℓ'0) (ℓ', ι'))) by eauto 2.
                invert_wf_type.
                assert (exists x, memory_lookup s1 x = Some (ValLoc loc) /\ e = Var x)
                  by eauto 2.
                super_destruct; subst.
                rewrite_inj.
                do 2 invert_var_typing.
                rewrite_inj.
                assert (ℓ_e ⊑ ℓ1) by eauto 2.
                eauto 3.
            }
            {
              eapply wf_taint_bijection_extend_mem1; intros; subst; eauto 2.
            }
            {
              invert_taint_eq.
              eapply wf_taint_bijection_extend_mem2 with (m := s1) (h := w1) (Φ := Φ); eauto 2.
              - rewrite <- (compose_id_right Φ).
                eapply taint_eq_reach_trans.
                + eauto.
                + eapply gc_trans_preserves_taint_eq_reach; eauto.
              - rewrite <- (compose_id_right Φ).
                eapply taint_eq_heap_trans.
                + eapply gc_trans_preserves_taint_eq_reach; eauto 2.
                + eauto.
                + eauto.
                + eauto.
                + eapply low_gc_trans_preserves_taint_eq_heap; eauto 2.
                + eapply low_gc_trans_preserves_taint_eq_heap_domain_eq with (pc := pc_end); eauto 2.
              - rewrite <- (compose_id_right Φ).
                eapply taint_eq_heap_domain_eq_trans; eauto 2.
              - eapply low_gc_trans_preserves_wf_taint_bijection with (pc := pc_end); eauto 2.
              - intros; subst; eauto 3.
              - intros; subst; eauto 3.
              - eauto 4.
              - intros; subst.
                assert (exists loc, v1 = ValLoc loc) by eauto 3.
                super_destruct'; subst.
                eexists; splits; eauto 2.
            }
            { eauto. }
          * invert_high_event_step.
            invert_event_step.
            rewrite_inj.
            invert_low_event.
            assert (~ ℓ1 ⊑ ℓ) by eauto.
            contradiction.
        + invert_low_event.
      - invert_high_event_step.
        unfold is_stop_config, cmd_of in *; subst.
        invert_event_step.
        + assert (wellformed_aux Γ Σ1' ⟨ Stop, pc1', m2, h2, t2 ⟩ pc_end).
          {
            eapply preservation; eauto.
          }
          assert (wellformed_aux Γ Σ3' ⟨c2', pc2'', s2'', w2'', g2''⟩ pc_end) by eauto 2.
          invert_taint_eq.
          invert_taint_eq_cmd.
          _apply assign_bridge_properties in *.
          super_destruct; subst.
          assert (wellformed_aux Γ Σ3' ⟨i ::= e, pc2'', s1', w2'', g2'' - 1⟩ pc_end) by eauto 2.
          invert_sem_step.
          rewrite_inj.
          repeat invert_wf_aux.
          assert ((i ::= e) <> Stop) by congruence.
          assert ((i ::= e) <> TimeOut) by congruence.
          do 4 specialize_gen.
          do 2 invert_wt_cmd.
          invert_lifted.
          rewrite_inj.
          invert_bridge_step_with_steps 0.
          * invert_low_event_step.
            invert_event_step.
            rewrite_inj.
            invert_low_event.
            assert (~ ℓ1 ⊑ ℓ) by eauto.
            contradiction.
          * invert_high_event_step.
            invert_event_step.
            rewrite_inj.
            assert (~ ℓ1 ⊑ ℓ) by eauto.
            invert_sem_step.
            rewrite_inj.
            match goal with
              [H: S (?X - 1) = ?X |- _] => clear H
            end.
           
            destruct_prod_join_flowsto.
            destruct ε as [ℓ' ι'].
            assert (taint_eq_mem (inverse Φ) Γ s1' s1) by eauto 2 using taint_eq_mem_sym.
            assert (exists v2, eval s1 e = Some v2 /\ val_taint_eq (inverse Φ) (SecType τ (ℓ', ι')) v1 v2) by eauto 2.
            super_destruct; subst.
            rename v2 into u.
            destruct_prod_join_flowsto.
            assert (val_low_eq ℓ (SecType τ (ℓ1, ι0)) v0 u φ)
              by (invert_state_low_eq; eauto 3).            
            remember_simple (filter_bijection (low ℓ Γ Σ1' (extend_memory i v0 m1) h2) (low_dec ℓ Γ Σ1' (extend_memory i v0 m1) h2) φ).
            remember_simple (filter_bijection
                               (high ℓ (extend_memory i u s1) w1)
                               (high_dec ℓ (extend_memory i u s1) w1) Φ).
            super_destruct; subst.
            rename ψ into Ψ.
            rename ψ0 into ψ.
            exists (AssignEvent ℓ1 i u).
            exists 0.
            exists ψ.
            exists Ψ.
            exists (extend_memory i u s1).
            exists w1.
            exists Σ2.
            assert (state_low_eq ℓ ψ (m1 [i → v0]) h2
                                 (s1 [i → u]) w1 Γ Σ1' Σ2).
            {
              eapply state_low_eq_extend_memory; eauto 2.
              - intros; subst.
                assert (exists loc, v0 = ValLoc loc) by eauto.
                super_destruct; subst.
                exists loc.
                splits~.
                intros.
                assert (~ ℓ1 ⊑ ℓ) by eauto.
                contradiction.
              - intros; subst.
                assert (exists loc, u = ValLoc loc) by eauto.
                super_destruct; subst.
                exists loc.
                splits~.
                intros.
                assert (~ ℓ1 ⊑ ℓ) by eauto.
                contradiction.
              - intros; subst; eauto 2.
              - intros; subst; eauto 2.
              - eapply wf_tenv_extend.
                + eauto.
                + eauto.
                + intros; subst.
                  eauto 2.
                + intros; subst.
                  eauto 2.
            }
            assert (wf_bijection ℓ ψ Γ Σ1' (m1 [i → v0]) h2).
            {
              eapply wf_bijection_extend_mem1; eauto 2.
              - intros; subst; eauto 2.
              - intros; subst.
                assert (exists loc, v0 = ValLoc loc) by eauto 2.
                super_destruct; subst.
                exists loc.
                splits~.
                intro.
                exfalso; eauto 3.
            }
            splits~.
            {
              eapply bridge_stop_num; eauto.
              constructor.
              - eapply EventSemStep; eauto.
              - unfolds.
                intro.
                invert_low_event.
                eauto.
            }
            { unfolds.
              splits~.
              - invert_high_event.
                splits; intros; invert_low_event; exfalso; eauto.
              - intros; invert_low_event; exfalso; eauto.
            }
            {
              eapply TaintEqEventAssign.
              - eauto.
              - invert_val_taint_eq; eauto 3.
                assert (left Φ loc' = Some loc) by (destruct Φ; eauto).
                assert (high ℓ (s1 [i → ValLoc loc'])
                              w1 loc') by eauto 3.
                assert (left Ψ loc' = Some loc) by eauto 2.
                eauto.
            }
            {
              
              assert (taint_eq ℓ Ψ Γ Σ2 Σ3' Stop Stop (s1 [i → u]) w1
                               (s1' [i → v1]) w2'').
              {
                assert (taint_eq ℓ (identity_bijection loc) Γ Σ3' Σ3' (i ::= e) (i ::= e) s1' w1' s1' w2'').
                {
                  eauto 3 using low_gc_trans_preserves_taint_eq.
                }
                unfold taint_eq in *; super_destruct'; subst.
                splits~.
                - eapply taint_eq_mem_extend; eauto 4.
                - eapply taint_eq_reach_extend_mem; eauto 2.
                  + assert (taint_eq_reach (identity_bijection loc) s1' w1' s1' w2'')
                      by eauto 2.
                    rewrite <- (compose_id_right Φ).
                    eapply taint_eq_reach_trans; eauto.
                  + rewrite <- (compose_id_right Φ).
                    eapply taint_eq_heap_trans; eauto 2.
                  + eapply low_gc_trans_preserves_wf_taint_bijection with (pc := pc_end); eauto.
                  + eauto 4.
                  + intros; subst; eauto 2.
                  + intros; subst; eauto 2.
                - eapply taint_eq_heap_extend_mem.
                  + eapply taint_eq_heap_trans; eauto 2.
                  + eauto.
                  + intros; subst; eauto 2.
                  + intros; subst; eauto 2.
                  + intros; subst.
                    assert (exists loc, u = ValLoc loc) by eauto 2.
                    super_destruct; subst.
                    exists loc.
                    splits; eauto 3.
                  + intros; subst.
                    assert (exists loc, v1 = ValLoc loc) by eauto 2.
                    super_destruct; subst.
                    exists loc.
                    splits; eauto 3.
                  + rewrite -> compose_id_right.
                    eauto.
                  + rewrite -> compose_id_right.
                    eapply low_gc_trans_preserves_wf_taint_bijection with (pc := pc_end); eauto 2.
                  + rewrite -> compose_id_right.
                    eauto.
                - eapply taint_eq_heap_size_trans; eauto 2.
                - repeat invert_wf_aux.
                  eapply taint_eq_heap_domain_eq_extend_mem with (Φ := bijection.bijection_compose Φ (identity_bijection loc)); eauto 2.
                  + eapply taint_eq_heap_domain_eq_trans; eauto 2.
                  + rewrite -> compose_id_right.
                    eauto.
                  + rewrite -> compose_id_right.
                    eapply low_gc_trans_preserves_wf_taint_bijection
                    with (pc := pc_end); eauto.
                  + eapply taint_eq_mem_trans; eauto 2.
                  + eapply taint_eq_heap_trans; eauto 2.
                  + eapply taint_eq_reach_trans; eauto 2.
                  + rewrite -> compose_id_right.
                    eauto.
                  + rewrite -> compose_id_right.
                    eauto.
                  + rewrite -> compose_id_right.
                    eauto.
                  + rewrite -> compose_id_right.
                    eapply low_gc_trans_preserves_wf_taint_bijection
                    with (pc := pc_end); eauto.
                  + intros; subst.
                    assert (exists loc, u = ValLoc loc) by eauto 2.
                    super_destruct; subst.
                    exists loc.
                    splits; eauto 3.
                  + intros; subst; eauto 3.
                  + intros; subst.
                    assert (exists loc, v1 = ValLoc loc) by eauto 2.
                    super_destruct; subst.
                    exists loc.
                    splits; eauto 3.
                  + intros; subst; eauto 3.
                  + rewrite -> compose_id_right.
                    eauto.
                - eapply taint_eq_stenv_extend_mem; eauto 2.
              }
              splits.
              {
                eapply wf_bijection_extend_mem2; eauto 3.
              - intros; subst; eauto 2.
              - intros; subst.
                assert (exists loc, u = ValLoc loc) by eauto 2.
                super_destruct; subst.
                exists loc.
                splits~.
                intro; exfalso; eauto 3.
              }
              {
                eapply wf_taint_bijection_extend_mem1; intros; subst; eauto 2.
              }
              {
                invert_taint_eq.
                eapply wf_taint_bijection_extend_mem2 with (m := s1) (h := w1) (Φ := Φ); eauto 2.
                - rewrite <- (compose_id_right Φ).
                  eapply taint_eq_reach_trans.
                  + eauto.
                  + eapply gc_trans_preserves_taint_eq_reach; eauto.
                - rewrite <- (compose_id_right Φ).
                  eapply taint_eq_heap_trans.
                  + eapply gc_trans_preserves_taint_eq_reach; eauto 2.
                  + eauto.
                  + eauto.
                  + eauto.
                  + eapply low_gc_trans_preserves_taint_eq_heap; eauto 2.
                  + eapply low_gc_trans_preserves_taint_eq_heap_domain_eq with (pc := pc_end); eauto 2.
                - rewrite <- (compose_id_right Φ).
                  eapply taint_eq_heap_domain_eq_trans; eauto 2.
                - eapply low_gc_trans_preserves_wf_taint_bijection with (pc := pc_end); eauto 2.
                - intros; subst; eauto 3.
                - intros; subst; eauto 3.
                - eauto 4.
                - intros; subst.
                  assert (exists loc, v1 = ValLoc loc) by eauto 3.
                  super_destruct'; subst.
                  eexists; splits; eauto 2.
              }
              { eauto. }
            }
    }
    (* If *)
    {
      invert_bridge_step_with_steps 0.
      - invert_low_event_step.
        invert_event_step; invert_low_event.
      - invert_high_event_step.
        exfalso.
        eauto 2.
    }
    (* While *)
    {
      invert_bridge_step_with_steps 0.
      - invert_low_event_step.
        invert_event_step; invert_low_event.
      - invert_high_event_step.
        unfold is_stop_config, cmd_of in *; subst.
        invert_event_step.
        * super_destruct; try invert_ends_with_backat.
          subst.
          invert_sem_step.
          exists EmptyEvent 0 φ Φ s1 w1; exists Σ2.
          assert (eval s1 e = Some (ValNum 0)).
          {
            repeat invert_wf_aux.
            repeat specialize_gen.
            invert_wt_cmd.
            assert (ℓ0 ⊑ ℓ) by eauto 2.
            assert (exists u, onvals (left φ) (ValNum 0) = Some u /\ eval s1 e = Some u)
              by eauto 2.
            super_destruct'; subst.
            unfold onvals in *.
            injects.
            eauto.
          }
          invert_taint_eq.
          invert_taint_eq_cmd.
          assert (eval s1' e = Some (ValNum 0)).
          {
            repeat invert_wf_aux.
            repeat specialize_gen.
            invert_wt_cmd.
            assert (exists v2,
                       eval s1' e = Some v2 /\ val_taint_eq Φ (SecType Int (ℓ0, ∘)) (ValNum 0) v2) by eauto 2.
            super_destruct'; subst.
            invert_val_taint_eq.
            eauto.
          }
          splits; eauto 2.
          {
            _apply while_bridge_properties in *.
            super_destruct; subst.
            - eauto.
            - congruence.
          }
          {
            _apply while_bridge_properties in *.
            super_destruct; subst.
            - eauto.
            - congruence.
          }
          {
            splits*.
          }
          {
            _apply while_bridge_properties in *.
            super_destruct; subst.
            - eauto.
            - congruence.
          }
          splits; eauto 2.
          {
            _apply while_bridge_properties in *.
            super_destruct; subst.
            - eapply low_gc_trans_preserves_wf_taint_bijection; eauto.
            - congruence.
          }
          {
            _apply while_bridge_properties in *.
            super_destruct; subst.
            - remember_simple (low_gc_trans_preserves_taint_eq H5 H7 H26).
              unfold taint_eq in *; super_destruct.
              splits.
              + eauto.
              + eauto.
              + rewrite <- (compose_id_right Φ).
                eapply taint_eq_reach_trans; eauto.
              + rewrite <- (compose_id_right Φ).
                eapply taint_eq_heap_trans; eauto.
                * repeat invert_wf_aux; eauto.
              + eapply taint_eq_heap_size_trans; eauto.
              + rewrite <- (compose_id_right Φ).
                eapply taint_eq_heap_domain_eq_trans; eauto.
              + rewrite <- (compose_id_right Φ).
                eapply taint_eq_stenv_trans; eauto. 
            - congruence.
          }
    }
    (* Sequential composition *)
    {
      assert (H8' := H8).
      match goal with
        [H: context[bridge_step_num] |- _] => assert (H' := H); eapply about_seq_bridge_step in H; eauto 2
      end.
      match goal with
        [H: (exists _, _ ) \/ (exists _, _ ) |- _] =>
        destruct H; super_destruct'; try omega
      end.
      subst.
      assert (c1 <> Stop).
      {
        intro; subst.
        invert_wf_aux.
        repeat specialize_gen.
        invert_wt_cmd.
        match goal with
          [H: wt_aux _ _ Stop _ |- _] =>
          inverts H
        end.
      }
      assert (c2 <> Stop).
      {
        intro; subst.
        invert_wf_aux.
        repeat specialize_gen.
        invert_wt_cmd.
        match goal with
          [H: wt_aux _ _ Stop _ |- _] =>
          inverts H
        end.
      }
      invert_taint_eq.
      invert_taint_eq_cmd.
      assert (exists pc'',
                 wellformed_aux Γ Σ1 ⟨ c1, pc, m1, h1, t ⟩ pc'') by eauto 2.
      assert (exists pc'',
                 wellformed_aux Γ Σ2 ⟨ c1, pc, s1, w1, t ⟩ pc'') by eauto 2.
      assert (exists pc'',
                 wellformed_aux Γ Σ3 ⟨ c1'0, pc, s1', w1', t' ⟩ pc'') by eauto 2.
      super_destruct'; subst.
      assert (taint_eq ℓ Φ Γ Σ2 Σ3 c1 c1'0 s1 w1 s1' w1').
      {
        unfolds.
        splits*.
      }
      assert (wellformed_aux Γ Σ3' ⟨c2', pc2'', s2'', w2'', g2''⟩ pc_end) by eauto 2.
      match goal with
        [H: context[bridge_step_num] |- _] =>
        eapply about_seq_bridge_step in H; eauto 2
      end.
      
      super_destruct; subst.
      - assert (c1 <> TimeOut).
        {
          intro; subst.
          repeat invert_wf_aux.
          repeat specialize_gen.
          match goal with
            [H: wt_aux _ _ (TimeOut ;; _) _ |- _] =>
            inverts H
          end.
          invert_wt_timeout.
        }
        assert (pc''1 = pc''0).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          eapply deterministic_typing; eauto 2.
        }
        subst.
        assert (c1' <> TimeOut).
        {
          intro; subst.
          repeat specialize_gen.
          subst.
          assert (wellformed_aux Γ Σ1' ⟨TIMEOUT;; c2, pc1', m2, h2, t2⟩ pc_end) by eauto 2.
          invert_wf_aux.
          repeat specialize_gen.
          invert_wt_cmd.
          invert_wt_timeout.
        }
        assert (c1'0 <> Stop).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          intro; subst.
          invert_wt_cmd; invert_wt_stop.
        }
        assert (c1'0 <> TimeOut).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          intro; subst.
          invert_wt_cmd; invert_wt_timeout.
        }
        assert (c1'1 <> TimeOut).
        {
          intro; subst.
          assert (TimeOut <> Stop) by congruence.
          specialize_gen.
          subst.
          invert_wf_aux.
          repeat specialize_gen.
          invert_wt_cmd.
          invert_wt_timeout.
        }
        assert (pc'' = pc''0).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          remember_simple (taint_eq_cmd_implies_same_type H27 H50).
          eauto 2.
        }
        subst.
        remember_simple (IHc1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H35 H38 _ _ _ _ _ _ _ _ _ _ _ H H0 H1 H2 H18 H25 H26 H6 H7 H28 H9 H10).
        super_destruct'; rewrite_inj; subst.
        exists ev1' n1' ψ Ψ s2' w2'; exists Σ2'.
        splits~.
        + destruct (eq_cmd_dec c1' Stop).
          * subst.
            match goal with
              [H: _ = _ -> _ |- _] =>
              specialize (H eq_refl); subst
            end.
            eapply bridge_step_seq_low_event_in_left_stop; eauto 2.
          * match goal with
              [H1: ?P -> _, H2: ?P |- _] =>
              specialize (H1 H2); subst
            end.
            destruct (eq_cmd_dec c1' TimeOut).
            {
              subst.
              assert (wellformed_aux Γ Σ1' ⟨TIMEOUT;; c2, pc1', m2, h2, t2⟩ pc_end).
              {
                eauto 2.
              }
              invert_wf_aux.
              repeat specialize_gen.
              invert_wt_cmd.
              invert_wt_timeout.
            }
            {
              eapply bridge_step_seq_low_event_in_left_nonstop; eauto 2.
            }
        + splits; eauto 2.
          invert_taint_eq.
          unfolds.
          splits; eauto 2.
          destruct (eq_cmd_dec c1' Stop).
          * subst.
            repeat specialize_gen.
            subst.
            assert (c1'1 = Stop).
            {
              invert_taint_eq_cmd; eauto 2.
            }
            subst.
            repeat specialize_gen.
            subst.
            eauto 2.
          * assert (c1'1 <> Stop).
            {
              intro; subst.
              invert_taint_eq_cmd.
              eauto 2.
            }
            repeat specialize_gen.
            subst.
            eauto 2.
      - assert (pc''2 = pc'') by (eapply wt_aux_soundness_bridge; eauto 2).
        subst.
        assert (c1 <> TimeOut).
        {
          intro; subst.
          inverts H3.
          repeat specialize_gen.
          invert_wt_cmd.
          invert_wt_timeout.
        }
        assert (pc''1 = pc''0).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          eauto 2.
        }
        subst.
        assert (c1'0 <> Stop).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          intro; subst.
          invert_wt_cmd.
          invert_wt_stop.
        }
        assert (c1'0 <> TIMEOUT).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          intro; subst.
          invert_wt_cmd.
          invert_wt_timeout.
        }
        assert (c1'0 <> TimeOut).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          intro; subst.
          invert_wt_cmd; invert_wt_timeout.
        }
        assert (pc'' = pc''0).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          remember_simple (taint_eq_cmd_implies_same_type H27 H50).
          eauto 2.
        }
        subst.
        assert (c1' <> TimeOut).
        {
          intro; subst.
          repeat specialize_gen.
          subst.
          assert (wellformed_aux Γ Σ1' ⟨TIMEOUT;; c2, pc1', m2, h2, t2⟩ pc_end) by eauto 2.
          invert_wf_aux.
          repeat specialize_gen.
          invert_wt_cmd.
          invert_wt_timeout.
        }
        assert (Stop <> TimeOut) by congruence.
        remember_simple (IHc1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H39 H40 _ _ _ _ _ _ _ _ _ _ _ H H0 H1 H2 H18 H25 H26 H6 H7 H28 H9 H33).
        super_destruct'; rewrite_inj; subst.
        assert (low_event ℓ ev1') by eauto 2.
        assert (low_event ℓ ev').
        {
          eapply taint_eq_event_low_implies_low.
          - eapply taint_eq_events_sym.
            eauto.
          - eauto.
        }
        contradiction.
    }
    (* At *)
    {
      invert_bridge_step_with_steps 0.
      - invert_low_event_step.
        invert_event_step; invert_low_event.
      - unfold is_stop_config, cmd_of in *; subst.
        invert_high_event_step.
        invert_event_step.
        + invert_sem_step.
    }
    (* Back at *)
    {
      invert_taint_eq; invert_taint_eq_cmd.
      assert (Σ3 = Σ3' /\
              (exists t'', ev2 = RestoreEvent l t'') /\
              taint_eq_mem (identity_bijection loc) Γ s1' s2'' /\
              taint_eq_heap ℓ (identity_bijection loc) Σ3 Σ3' s1' w1' s2'' w2'' /\
              taint_eq_reach (identity_bijection loc) s1' w1' s2'' w2'' /\
              taint_eq_heap_size ℓ w1' w2'' /\
              taint_eq_heap_domain_eq ℓ (identity_bijection loc) s1' s2'' w1' w2'' /\
              wf_taint_bijection ℓ (inverse Φ) s2'' w2'').
      {
        remember_simple (backat_bridge_properties H5 H10).
        super_destruct; subst.
        - congruence.
        - splits*.
          + repeat invert_wf_aux.
            eapply taint_eq_mem_refl; eauto.
          + remember_simple (low_gc_or_inc_many_preserves_taint_eq H5 H7 H8).
            unfold taint_eq in *; super_destruct'; subst.
            eauto.
          + remember_simple (low_gc_or_inc_many_preserves_taint_eq H5 H7 H8).
            unfold taint_eq in *; super_destruct'; subst.
            eauto.
          + remember_simple (low_gc_or_inc_many_preserves_taint_eq H5 H7 H8).
            unfold taint_eq in *; super_destruct'; subst.
            eauto.
          + remember_simple (low_gc_or_inc_many_preserves_taint_eq H5 H7 H8).
            unfold taint_eq in *; super_destruct'; subst.
            eauto.
      }
      super_destruct'; subst.
      subst.
      invert_bridge_step_with_steps 0.
      - invert_low_event_step.
        invert_event_step.
        + invert_low_event.
        + invert_sem_step.
          * omega.
          * invert_low_event.
            do 7 eexists.
            splits.
            { constructor.
              splits*. }
            { eauto. }
            { remember_simple (backat_bridge_properties H5 H10).
              super_destruct; congruence. }
            { eapply H6; eauto 2. }
            { splits*. }
            { eauto. }
            { eauto 2. }
            splits.
            { eauto. }
            { eauto. }
            { eauto 2. }
            { unfolds.
              splits.
              - remember_simple (backat_bridge_properties H5 H10).
                super_destruct; try congruence.
                subst.
                eauto 2.
              - rewrite <- (compose_id_right Φ).
                eapply taint_eq_mem_trans; eauto 2.
              - rewrite <- (compose_id_right Φ).
                eauto 2 using taint_eq_reach_trans.
              - rewrite <- (compose_id_right Φ).
                eapply taint_eq_heap_trans.
                + eauto.
                + eauto.
                + repeat invert_wf_aux.
                  eauto.
                + eauto.
                + eauto.
                + eauto.
              - eauto 2 using taint_eq_heap_size_trans.
              - rewrite <- (compose_id_right Φ).
                eauto 2 using taint_eq_heap_domain_eq_trans.
              - eauto 2 using taint_eq_stenv_trans.
            }
          * omega.
        + invert_sem_step.
          * omega.
          * omega.
          * congruence.
        + invert_low_event.
      - unfold is_stop_config, cmd_of in *; subst.
        invert_high_event_step.
        invert_event_step.
        + invert_sem_step.
          omega.
        + invert_sem_step.
          assert (~ pc1' ⊑ ℓ) by eauto.
          invert_wf_aux.
          do 2 specialize_gen.
          invert_wt_cmd.
          exfalso; eauto 3.
        + invert_sem_step.
          assert (~ pc1' ⊑ ℓ) by eauto.
          invert_wf_aux.
          do 2 specialize_gen.
          invert_wt_cmd.
          exfalso; eauto 3.
    }
  
    (* New *)
    {
      invert_taint_eq; invert_taint_eq_cmd.
      invert_bridge_step_with_steps 0.
      - invert_low_event_step.
        assert (wellformed_aux Γ Σ1' ⟨c2, pc1', m2, h2, t2⟩
                               pc_end) by eauto 2 using preservation_event_step.
        assert (wellformed_aux Γ Σ3' ⟨c2', pc2'', s2'', w2'', g2''⟩ pc_end).
        {
          eauto 2 using preservation_bridge_step.
        }
        invert_event_step.
        + super_destruct; subst; try invert_ends_with_backat.
          invert_sem_step.
          rewrite_inj.
          _apply same_extend_implies_same_loc in *; subst.
          invert_low_event.
          assert (wf_type bot (SecType (Array τ0 l) (ℓ0, ι))).
          {
            repeat invert_wf_aux.
            eauto.
          }
          _apply new_bridge_properties in *.
          super_destruct'; subst.
          invert_bridge_step; try solve[invert_high_event_step; invert_event_step; rewrite_inj; assert (~ ℓ1 ⊑ ℓ) by eauto; contradiction].
          invert_low_event_step.
          invert_event_step.
          rewrite_inj.
          invert_sem_step.
          match goal with
            [H: S (_ - 1) = _ |- _] =>
            clear H
          end.
          _apply same_extend_implies_same_loc in *; subst.
          rewrite_inj.
          inverts H4.
          do 2 specialize_gen.
          invert_wt_cmd.
          rewrite_inj.
          assert (exists v2,
                     eval s1 e = Some v2 /\ val_taint_eq Φ (SecType Int (ℓ_size, ∘)) v2 (ValNum n0)).
          {
            repeat invert_wf_aux.
            repeat specialize_gen.
            invert_wt_cmd.
            repeat destruct_join_flowsto.
            assert (exists v2,
                       eval s1 e = Some v2 /\ val_taint_eq (inverse Φ) (SecType Int (ℓ_size, ∘))  (ValNum n0) v2).
            {
              assert (taint_eq_mem (inverse Φ) Γ s1' s1) by (eapply taint_eq_mem_sym; eauto 2).
              eapply eval_taint_eq_possibilistic with (m1 := s1') (m2 := s1); eauto 2.
            }
            super_destruct'; subst.
            eauto 4.
          }
          super_destruct'; subst.
          invert_val_taint_eq.
          assert (n = n0).
          {
            repeat invert_wf_aux.
            repeat specialize_gen.
            invert_wt_cmd.
            repeat destruct_join_flowsto.
            assert (val_low_eq ℓ (SecType Int (ℓ_size, ∘)) (ValNum n) (ValNum n0) φ).
            {
              invert_state_low_eq.
              eauto 2 using eval_low_eq.
            }
            rewrite_inj.
            invert_val_low_eq.
            - exfalso; eauto.
            - reflexivity.
          }
          subst.
          assert (size l w1 + n0 <= maxsize l w1).
          {
            destruct (flowsto_dec l ℓ).
            - assert (size l h1 = size l w1).
              {
                invert_state_low_eq.
                eauto.
              }
              subst.
              match goal with
                [H: size _ _ = size _ _ |- _] =>
                rewrite <- H
              end.
              erewrite -> constant_maxsize; eauto.
            - assert (l <> pc_end).
              {
                intro; subst.
                contradiction.
              }
              assert (size l w1' = size l h')
                by eauto using gc_trans_preserves_heap_size_neq_pc.
              assert (size l w1 = size l w1') by eauto 2.
              rewrite <- (constant_maxsize h' w1 l).
              congruence.
          }
          
          match goal with
            [H: size _ _ + _ <= maxsize _ _ |- _] =>
            remember_simple (fresh_location w1 l n0 v H)
          end.
          super_destruct; subst.
          
          assert (left φ l1 = None).
          {
            destruct (left φ l1) eqn:H_l1; try reflexivity.
            assert (exists ℓ μ, heap_lookup l1 h1 = Some (ℓ, μ)).
            {
              repeat invert_wf_aux.
              eapply bijection_implies_in_heap; eauto 2.
            }
            super_destruct'; subst.
            congruence.
          }
          assert (right φ loc = None).
          {
            destruct (right φ loc) eqn:H_loc; try reflexivity.
            assert (exists ℓ μ, heap_lookup loc w1 = Some (ℓ, μ)).
            {
              repeat invert_wf_aux.
              eapply bijection_implies_in_heap; destruct φ; eauto 2.
            }
            super_destruct'; subst.
            congruence.
          }            
          
          remember_simple (filter_bijection
                             (low ℓ Γ (extend_stenv l1 τ0 Σ1)
                                  (m1 [i → ValLoc l1])
                                  (extend_heap v l1 l n0 h1 H9 H21))
                             (low_dec ℓ Γ (extend_stenv l1 τ0 Σ1)
                                      (m1 [i → ValLoc l1])
                                      (extend_heap v l1 l n0 h1 H9 H21)) φ).
          super_destruct; subst.
          assert (left ψ l1 = None) by eauto 2.
          assert (right ψ loc = None).
          {
            destruct (right ψ loc) eqn:H_loc; try reflexivity.
            rename l0 into loc'.
            assert (left ψ loc' = Some loc) by (destruct ψ; eauto 2).
            assert (low ℓ Γ (extend_stenv l1 τ0 Σ1)
                        (m1 [i → ValLoc l1])
                        (extend_heap v l1 l n0 h1 H9 H21) loc').
            {
              eapply filtered_bijection_some_implies_predicate; eauto 2.
            }
            destruct_low.
            - destruct (decide (loc0 = l1)); subst.
              + congruence.
              + assert (low_reach ℓ_adv Γ Σ1 m1 h1 loc0).
                {
                  inverts H3.
                  assert (NewArr i l e e0 <> Stop) as H' by congruence.
                  assert (NewArr i l e e0 <> TimeOut) as H'' by congruence.
                  do 2 specialize_gen.
                  clear H' H''.
                  invert_wt_cmd.
                  rewrite_inj.
                  destruct τ as [τ [ℓ ι]].
                  eapply low_reach_extend_implies_low_reach_if
                  with (σ := τ) (v := v) (ℓ := ℓ).
                  - intros; subst.
                    assert (exists loc, v = ValLoc loc) by eauto 2.
                    super_destruct; subst.
                    exists loc1.
                    splits~.
                    intros.
                    assert (exists x, memory_lookup m1 x = Some (ValLoc loc1) /\ e0 = Var x) by eauto 2.
                    super_destruct; subst.
                    assert (ι = ∘).
                    {
                      assert_wf_type.
                      do 2 invert_wf_type.
                      reflexivity.
                    }
                    subst.
                    invert_var_typing.
                    eauto 2.
                  - intros; subst.
                    eauto 2.
                  - eauto.
                  - eauto.
                }
                assert (low_reach ℓ_adv Γ Σ2 s1 w1 loc).
                {
                  invert_state_low_eq.
                  match goal with
                    [H: context[low_reach_NI] |- _] =>
                    solve[eapply H; eauto]
                  end.
                }
                repeat invert_wf_aux.
                assert (exists ℓ μ, heap_lookup loc w1 = Some (ℓ, μ)) by eauto 3.
                super_destruct.
                congruence.
            - destruct (decide (loc0 = l1)); subst.
              + congruence.
              + rewrite -> heap_lookup_extend_neq in * by solve[eauto 2].
                assert (low ℓ_adv Γ Σ1 m1 h1 loc0) by eauto 2.
                assert (exists ν, heap_lookup loc w1 = Some (ℓ, ν)).
                {
                  invert_state_low_eq.
                  match goal with
                    [H: context[low_heap_domain_eq] |- _] =>
                    solve[eapply H; eauto]
                  end.
                }
                super_destruct; subst.
                congruence.
          }

          exists (NewEvent ℓ_x i loc).
          exists 0.
          match goal with
            [H1: left ψ ?loc1 = None,
                 H2: right ψ ?loc2 = None |- _] =>
            exists (extend_bijection ψ loc1 loc2 H1 H2)
          end.

          assert (exists v2, eval s1 e0 = Some v2 /\ val_taint_eq Φ τ0 v2 v1).
          {
            destruct τ0 as [σ [ℓ' ι']].
            repeat invert_wf_aux.
            assert (taint_eq_mem (inverse Φ) Γ s1' s1) by eauto 2.
            assert (exists v2,
                       eval s1 e0 = Some v2 /\
                       val_taint_eq (inverse Φ) (SecType σ (ℓ', ι')) v1 v2) by eauto 2.
            super_destruct'; subst.
            eauto 4.
          }
          super_destruct'; subst.
          
          remember_simple (filter_bijection
                             (high ℓ (s1 [i → ValLoc loc])
                                    (extend_heap v2 loc l n0 w1 H30 H28))
                             (high_dec ℓ (s1 [i → ValLoc loc])
                                        (extend_heap v2 loc l n0 w1 H30 H28)) Φ).
          super_destruct'; subst.
          rename ψ0 into Ψ.
          assert (left Ψ loc = None).
          {
            assert (left Φ loc = None).
            {
              destruct (left Φ loc) eqn:H_loc; try reflexivity.
              rename l0 into loc'.
              assert (high ℓ s1 w1 loc).
              {
                eapply H1; eauto.
              }
              assert (exists ℓ μ, heap_lookup loc w1 = Some (ℓ, μ)).
              {
                destruct_high; eauto 3.
              }
              super_destruct'; subst.
              congruence.
            }
            eapply filtered_bijection_is_subset_transpose_left.
            - eapply high_dec.
            - eauto.
            - eauto.
          }
          assert (right Ψ l2 = None).
          {
            destruct (right Ψ l2) eqn:H_loc; try reflexivity.
            rename l0 into l2'.
            assert (left Ψ l2' = Some l2) by (destruct Ψ; eauto 2).
            assert (high ℓ (s1 [i → ValLoc loc])
                          (extend_heap v2 loc l n0 w1 H30 H28) l2').
            {
              eapply filtered_bijection_some_implies_predicate.
              - eapply high_dec; eauto.
              - eauto.
              - eauto.
            }
            destruct (decide (loc = l2')); subst.
            + congruence.
            + assert (high ℓ s1 w1 l2').
              {
                destruct_high.
                - eapply HighReachable.
                  eapply reach_extend_implies_reach_if with (v := v2).
                  + intros; subst.
                    eauto 3.
                  + eauto.
                  + eauto.
                - rewrite -> heap_lookup_extend_neq in * by solve[eauto 2].
                  eauto 3.
              }
              assert (left Φ l2' = Some l2).
              {
                eapply filtered_bijection_is_subset.
                - eapply high_dec.
                - eauto.
                - eauto.
              }
              assert (high ℓ s1' w1' l2).
              {
                rewrite <- high_iff; eauto 2.
              }
              assert (high ℓ s1' h' l2).
              {
                eapply low_gc_trans_preserves_high; eauto 2.
              }
              assert (wellformed_aux Γ Σ3 ⟨NewArr i l e e0, pc_end, s1', h', g2'' - 1 ⟩ pc_end) by eauto 2.
              repeat invert_wf_aux.
              assert (exists ℓ μ, heap_lookup l2 h' = Some (ℓ, μ)).
              {
                destruct_high; eauto 3.
              }
              super_destruct'.
              congruence.
          }
          match goal with
            [H1: left Ψ ?loc1 = None,
                 H2: right Ψ ?loc2 = None |- _] =>
            exists (extend_bijection Ψ loc1 loc2 H1 H2)
          end.
          exists (s1 [i → ValLoc loc]).
          exists (extend_heap v2 loc l n0 w1 H30 H28).
          exists (extend_stenv loc τ0 Σ2).
          
          assert (state_low_eq ℓ (extend_bijection ψ l1 loc H46 H48)
                               (m1 [i → ValLoc l1]) 
                               (extend_heap v l1 l n0 h1 H9 H21)
                               (s1 [i → ValLoc loc])
                               (extend_heap v2 loc l n0 w1 H30 H28) Γ (extend_stenv l1 τ0 Σ1)
                               (extend_stenv loc τ0 Σ2)).
          {
            destruct τ0 as [σ [ℓ' ι']].
            repeat invert_wf_aux.
            repeat specialize_gen.
            repeat invert_wt_cmd.
            rewrite_inj.
            eapply state_low_eq_extend_EVERYTHING; try solve[intros; subst; eauto 3].
            - intros; subst.
              assert (exists loc, v = ValLoc loc) by eauto 2.
              super_destruct; subst.
              exists loc0.
              assert (exists x, memory_lookup m1 x = Some (ValLoc loc0) /\ e0 = Var x) by eauto 2.
              super_destruct; subst.
              invert_var_typing.
              assert_wf_type.
              invert_wf_type.
              splits~.
              + intros; eauto 3.
              + intros; eauto 3.
            - intros; subst.
              assert (exists loc, v2 = ValLoc loc) by eauto 3.
              super_destruct; subst.
              exists loc0.
              assert (exists x, memory_lookup s1 x = Some (ValLoc loc0) /\ e0 = Var x) by eauto 3.
              super_destruct; subst.
              invert_var_typing.
              assert_wf_type.
              invert_wf_type.
              splits~.
              + intros; eauto 3.
              + intros; eauto 3.
            - intros.
              assert (val_low_eq ℓ (SecType σ (ℓ', ι')) v v2 φ).
              {
                invert_state_low_eq.
                eauto 3 using eval_low_eq.
              }
              invert_val_low_eq; contradiction || eauto.
          }

          assert (wf_bijection ℓ (extend_bijection ψ l1 loc H46 H48) Γ
                               (extend_stenv l1 τ0 Σ1)
                               (m1 [i → ValLoc l1])
                               (extend_heap v l1 l n0 h1 H9 H21)).
          {
            destruct τ0 as [τ0 [ℓ' ι']].
            eapply wf_bijection_extend_mem_and_heap1; eauto 3.
            - repeat invert_wf_aux; eauto.
            - intros; subst.
              repeat invert_wf_aux.
              assert (exists loc, v = ValLoc loc) by eauto 3.
              super_destruct; subst.
              exists loc0.
              splits~.
              intros.
              assert (NewArr i l e e0 <> Stop) by congruence.
              assert (NewArr i l e e0 <> TimeOut) by congruence.
              do 2 specialize_gen.
              invert_wt_cmd.
              rewrite_inj.
              assert (exists x, memory_lookup m1 x = Some (ValLoc loc0) /\ e0 = Var x) by eauto 2.
              super_destruct; subst.
              invert_var_typing.
              assert_wf_type.
              invert_wf_type.
              eauto 2.
            - intros; subst.
              repeat invert_wf_aux.
              eauto 3.
          }

          assert (wellformed_aux Γ Σ3 ⟨NewArr i l e e0, pc_end, s1', h', g2'' - 1⟩ pc_end) by eauto 2.
          splits~.
          { eapply bridge_low_num.
            splits*.
          }
          { unfolds.
            splits*.
          }
          
          assert (wf_taint_bijection ℓ (extend_bijection Ψ loc l2 H52 H53)
                                     (s1 [i → ValLoc loc]) (extend_heap v2 loc l n0 w1 H30 H28)).
          {
            eapply wf_taint_bijection_extend_mem_and_heap1; eauto 2.
            intros; subst; eauto 2.
          }
          splits.
          {
            repeat invert_wf_aux.
            assert (NewArr i l e e0 <> Stop) as H' by congruence.
            repeat match goal with
                     [H: _ <> _ -> _ |- _] =>
                     specialize (H H')
                   end.
            clear H'.
            repeat invert_wt_cmd.
            rewrite_inj.
            destruct τ0 as [τ [ℓ' ι]].
            eapply wf_bijection_extend_mem_and_heap2; eauto 3.
            - intros; subst; eauto 3.
            - intros; subst; eauto 3.
            - intros; subst.
              assert (exists loc, v = ValLoc loc) by eauto 3.
              super_destruct; subst.
              exists loc0.
              assert (exists x, memory_lookup m1 x = Some (ValLoc loc0) /\ e0 = Var x) by eauto.
              super_destruct; subst.
              rewrite_inj.
              invert_var_typing.
              invert_wf_type.
              invert_wf_type.
              splits~.
              + intros; eauto 3.
              + intros; eauto 3.
            - intros; subst.
              assert (exists loc, v2 = ValLoc loc) by eauto 3.
              super_destruct; subst.
              exists loc0.
              assert (exists x, memory_lookup s1 x = Some (ValLoc loc0) /\ e0 = Var x) by eauto.
              super_destruct; subst.
              rewrite_inj.
              invert_var_typing.
              invert_wf_type.
              invert_wf_type.
              splits~.
              + intros; eauto 3.
              + intros; eauto 3.
            - repeat invert_state_low_eq.
              assert (val_low_eq ℓ (SecType τ (ℓ', ι)) v v2 φ) by eauto 3.
              invert_val_low_eq; contradiction || eauto 3.
          }
          {
            eauto 2.
          }
          {
            remember_simple (low_gc_trans_preserves_taint_eq H5 H7 H26).
            unfold taint_eq in *; super_destruct'; subst.
            destruct τ0 as [σ [ℓ' ι']].
            repeat invert_wf_aux.
            eapply wf_taint_bijection_extend_mem_and_heap2 with (Φ := Φ) (m1 := s1) (h1 := w1) (v1 := v2); intros; subst; eauto 3.
            - rewrite <- (compose_id_right Φ).
              eapply taint_eq_reach_trans; eauto.
            - rewrite <- (compose_id_right Φ).
              eapply taint_eq_heap_trans; eauto.
            - rewrite <- (compose_id_right Φ).
              eapply taint_eq_heap_domain_eq_trans; eauto.
            - eapply low_gc_trans_preserves_wf_taint_bijection with (pc := pc_end); eauto.
            - subst; eauto 2.
            - subst; eauto 2.
            - subst.
              assert (exists loc, v2 = ValLoc loc) by eauto 3.
              super_destruct'; subst.
              eexists; splits; eauto 2.
            - subst.
              assert (exists loc, v1 = ValLoc loc) by eauto 3.
              super_destruct'; subst.
              eexists; splits; eauto 2.
          }
          {
            unfolds.
            splits.
            - eauto 2.
            - eapply taint_eq_mem_extend_mem_and_bijection; eauto.
            - destruct τ0 as [σ [ℓ' ι']].
              remember_simple (low_gc_trans_preserves_taint_eq H5 H7 H26).
              unfold taint_eq in *; super_destruct'; subst.
              eapply taint_eq_reach_extend_mem_and_heap;
                (intros; subst; eauto 3) || (try solve [repeat invert_wf_aux; eauto 2]).
              + rewrite <- (compose_id_right Φ).
                eapply taint_eq_reach_trans; eauto 2.
              + eapply low_gc_trans_preserves_wf_taint_bijection with (pc := pc_end); eauto 2.
              + rewrite <- (compose_id_right Φ).
                eapply taint_eq_heap_trans; eauto 2.
                repeat invert_wf_aux; eauto 2.
              + intros; subst.
                assert (exists loc, v2 = ValLoc loc) by eauto 2.
                super_destruct'; subst; eexists; splits; eauto 2.
              + intros; subst.
                repeat invert_wf_aux.
                assert (exists loc, v1 = ValLoc loc) by eauto 2.
                super_destruct'; subst; eexists; splits; eauto 2.
              + subst; eauto 2.
              + subst.
                repeat invert_wf_aux; eauto 3.                
            - remember_simple (low_gc_trans_preserves_taint_eq H5 H7 H26).
              unfold taint_eq in *; super_destruct'; subst.
              eapply taint_eq_heap_extend_mem_and_heap with (Φ := Φ).
              + rewrite <- (compose_id_right Φ).
                eapply taint_eq_heap_trans.
                * eauto.
                * eauto.
                * repeat invert_wf_aux; eauto 2.
                * eauto.
                * eauto.
                * eauto.
              + eauto.
              + intros; subst; eauto 2.
              + intros; subst; repeat invert_wf_aux; eauto 2.
              + eauto.
            - remember_simple (low_gc_trans_preserves_taint_eq H5 H7 H26).
              unfold taint_eq in *; super_destruct'; subst.
              unfolds.
              intros.
              destruct (T_dec l0 l); subst.
              + repeat rewrite -> size_extend_heap_eq_level by solve[eauto 2].
                assert (size l w1' = size l h') by eauto 2.
                assert (size l w1 = size l w1') by eauto 2.
                omega.
              + repeat rewrite -> size_extend_heap_neq_level by solve[eauto 2].
                assert (size l0 w1' = size l0 h') by eauto 2.
                assert (size l0 w1 = size l0 w1') by eauto 2.
                omega.
            - destruct τ0 as [σ ε].
              remember_simple (low_gc_trans_preserves_taint_eq H5 H7 H26).
              unfold taint_eq in *; super_destruct'; subst.
              repeat invert_wf_aux.
              eapply taint_eq_heap_domain_eq_extend_mem_and_heap with (Φ := Φ); eauto 2.
              + eapply low_gc_trans_preserves_wf_taint_bijection with (pc := pc_end); eauto 2.
              + intros; subst.
                assert (exists loc, v2 = ValLoc loc) by eauto 2.
                super_destruct'; subst; eexists; splits; eauto 2.
              + intros; subst.
                assert (exists loc, v1 = ValLoc loc) by eauto 2.
                super_destruct'; subst; eexists; splits; eauto 2.
              + rewrite <- (compose_id_right Φ).
                eapply taint_eq_reach_trans; eauto 2.
              + rewrite <- (compose_id_right Φ).
                eapply taint_eq_heap_trans; eauto 2.
              + rewrite <- (compose_id_right Φ).
                eapply taint_eq_heap_domain_eq_trans; eauto.
              + intros; subst; eauto 3.
              + intros; subst; eauto 3.
            - unfolds.
              intros.
              destruct (decide (loc = loc1)); subst.
              + _rewrite -> left_extend_bijection_eq in *.
                rewrite_inj.
                repeat rewrite -> extend_stenv_lookup_eq.
                splits*.
              + _rewrite -> left_extend_bijection_neq in * by solve[eauto 2].
                assert (l2 <> loc2).
                {
                  intro; subst.
                  assert (right Ψ loc2 = Some loc1) by (destruct Ψ; eauto 2).
                  congruence.
                }
                repeat rewrite -> extend_stenv_lookup_neq by solve[eauto 2].
                assert (left Φ loc1 = Some loc2).
                {
                  eapply filtered_bijection_is_subset.
                  - eapply high_dec.
                  - eauto 2.
                  - eauto 2.
                }
                eapply H18; eauto 2.
          }
        + invert_low_event.
      - unfold is_stop_config, cmd_of in *; subst.
        invert_high_event_step.
        assert (wellformed_aux Γ Σ1' ⟨Stop, pc1', m2, h2, t2⟩
                               pc_end) by eauto 2 using preservation_event_step.
        assert (wellformed_aux Γ Σ3' ⟨c2', pc2'', s2'', w2'', g2''⟩ pc_end).
        {
          eauto 2 using preservation_bridge_step.
        }
        invert_event_step.
        invert_sem_step.
        assert (~ ℓ0 ⊑ ℓ) by eauto.
        rewrite_inj.
        _apply same_extend_implies_same_loc in *; subst.
        assert (wf_type bot (SecType (Array τ0 l) (ℓ0, ι))).
        {
          repeat invert_wf_aux.
          eauto.
        }
        _apply new_bridge_properties in *.
        super_destruct'; subst.
        invert_bridge_step; try solve[invert_low_event_step; invert_event_step; invert_low_event; rewrite_inj; contradiction].
        invert_high_event_step.
        invert_event_step.
        rewrite_inj.
        invert_sem_step.
        match goal with
          [H: S (_ - 1) = _ |- _] =>
          clear H
        end.
        _apply same_extend_implies_same_loc in *; subst.
        rewrite_inj.
        inverts H4.
        do 2 specialize_gen.
        invert_wt_cmd.
        rewrite_inj.
        assert (exists v2,
                   eval s1 e = Some v2 /\ val_taint_eq Φ (SecType Int (ℓ_size, ∘)) v2 (ValNum n0)).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          invert_wt_cmd.
          repeat destruct_join_flowsto.
          assert (exists v2,
                       eval s1 e = Some v2 /\ val_taint_eq (inverse Φ) (SecType Int (ℓ_size, ∘))  (ValNum n0) v2).
            {
              assert (taint_eq_mem (inverse Φ) Γ s1' s1) by (eapply taint_eq_mem_sym; eauto 2).
              eapply eval_taint_eq_possibilistic with (m1 := s1') (m2 := s1); eauto 2.
            }
            super_destruct'; subst.
            eauto 4.
          }
          super_destruct'; subst.
        invert_val_taint_eq.
        assert (wf_type bot (SecType (Array τ0 l) (ℓ_x, ∘))) by eauto.
        invert_wf_type.
        assert (~ l ⊑ ℓ) by eauto.
        assert (size l w1' = size l h').
        {
          eapply gc_trans_preserves_heap_size_neq_pc.
          - eauto 2.
          - intro; subst.
            eauto 3.
        }
        assert (size l w1 = size l w1').
        {
          eapply H16; eauto 3.
        }
        let H' := fresh in
        assert (size l w1 + n0 <= maxsize l w1) as H' by
              (rewrite <- (constant_maxsize h' w1 l); omega);
          remember_simple (fresh_location w1 l n0 v H').
        super_destruct; subst.        
        
        assert (left φ l1 = None).
        {
          destruct (left φ l1) eqn:H_l1; try reflexivity.
          assert (exists ℓ μ, heap_lookup l1 h1 = Some (ℓ, μ)).
          {
            repeat invert_wf_aux.
            eapply bijection_implies_in_heap; eauto 2.
          }
          super_destruct'; subst.
          congruence.
        }
        assert (right φ loc = None).
        {
          destruct (right φ loc) eqn:H_loc; try reflexivity.
          assert (exists ℓ μ, heap_lookup loc w1 = Some (ℓ, μ)).
          {
            repeat invert_wf_aux.
            eapply bijection_implies_in_heap; destruct φ; eauto 2.
          }
          super_destruct'; subst.
          congruence.
        }            
        
        remember_simple (filter_bijection
                           (low ℓ Γ (extend_stenv l1 τ0 Σ1)
                                (m1 [i → ValLoc l1])
                                (extend_heap v l1 l n h1 H9 H21))
                           (low_dec ℓ Γ (extend_stenv l1 τ0 Σ1)
                                    (m1 [i → ValLoc l1])
                                    (extend_heap v l1 l n h1 H9 H21)) φ).
          super_destruct; subst.
          exists (NewEvent ℓ_x i loc).
          exists 0.
          exists ψ.

          assert (exists v2, eval s1 e0 = Some v2 /\ val_taint_eq Φ τ0 v2 v1).
          {
            destruct τ0 as [σ [ℓ' ι']].
            repeat invert_wf_aux.
            assert (taint_eq_mem (inverse Φ) Γ s1' s1) by eauto 2.
            assert (exists v2,
                       eval s1 e0 = Some v2 /\
                       val_taint_eq (inverse Φ) (SecType σ (ℓ', ι')) v1 v2) by eauto 2.
            super_destruct'; subst.
            eauto 4.
          }
          super_destruct'; subst.
          
          remember_simple (filter_bijection
                             (high ℓ (s1 [i → ValLoc loc])
                                    (extend_heap v2 loc l n0 w1 H50 H33))
                             (high_dec ℓ (s1 [i → ValLoc loc])
                                        (extend_heap v2 loc l n0 w1 H50 H33)) Φ).
          super_destruct'; subst.
          rename ψ0 into Ψ.
          assert (left Ψ loc = None).
          {
            assert (left Φ loc = None).
            {
              destruct (left Φ loc) eqn:H_loc; try reflexivity.
              rename l0 into loc'.
              assert (high ℓ s1 w1 loc).
              {
                eapply H1; eauto.
              }
              assert (exists ℓ μ, heap_lookup loc w1 = Some (ℓ, μ)).
              {
                destruct_high; eauto 3.
              }
              super_destruct'; subst.
              congruence.
            }
            eapply filtered_bijection_is_subset_transpose_left.
            - eapply high_dec.
            - eauto.
            - eauto.
          }
          assert (right Ψ l2 = None).
          {
            destruct (right Ψ l2) eqn:H_loc; try reflexivity.
            rename l0 into l2'.
            assert (left Ψ l2' = Some l2) by (destruct Ψ; eauto 2).
            assert (high ℓ (s1 [i → ValLoc loc])
                          (extend_heap v2 loc l n0 w1 H50 H33) l2').
            {
              eapply filtered_bijection_some_implies_predicate.
              - eapply high_dec; eauto.
              - eauto.
              - eauto.
            }
            destruct (decide (loc = l2')); subst.
            + congruence.
            + assert (high ℓ s1 w1 l2').
              {
                destruct_high.
                - eapply HighReachable.
                  eapply reach_extend_implies_reach_if with (v := v2).
                  + intros; subst.
                    eauto 3.
                  + eauto.
                  + eauto.
                - rewrite -> heap_lookup_extend_neq in * by solve[eauto 2].
                  eapply HighHeapLevel; eauto 3.
              }
              assert (left Φ l2' = Some l2).
              {
                eapply filtered_bijection_is_subset.
                - eapply high_dec.
                - eauto.
                - eauto.
              }
              assert (high ℓ s1' w1' l2).
              {
                rewrite -> high_iff; eauto 2.
                destruct Φ; eauto 2.
              }
              assert (high ℓ s1' h' l2).
              {
                eapply low_gc_trans_preserves_high; eauto 2.
              }
              assert (wellformed_aux Γ Σ3 ⟨NewArr i l e e0, pc_end, s1', h', g2'' - 1 ⟩ pc_end) by eauto 2.
              repeat invert_wf_aux.
              assert (exists ℓ μ, heap_lookup l2 h' = Some (ℓ, μ)).
              {
                destruct_high; eauto 3.
              }
              super_destruct'.
              congruence.
          }
          match goal with
            [H1: left Ψ ?loc1 = None,
                 H2: right Ψ ?loc2 = None |- _] =>
            exists (extend_bijection Ψ loc1 loc2 H1 H2)
          end.
          exists (s1 [i → ValLoc loc]).
          exists (extend_heap v2 loc l n0 w1 H50 H33).
          exists (extend_stenv loc τ0 Σ2).
          
          assert (state_low_eq ℓ ψ
                               (m1 [i → ValLoc l1]) 
                               (extend_heap v l1 l n h1 H9 H21)
                               (s1 [i → ValLoc loc])
                               (extend_heap v2 loc l n0 w1 H50 H33) Γ (extend_stenv l1 τ0 Σ1)
                               (extend_stenv loc τ0 Σ2)).
          {
            destruct τ0 as [τ [ℓ' ι']].
            eapply state_low_eq_extend_EVERYTHING_high; try solve[intros; subst; eauto 3].
            - repeat invert_wf_aux; eauto 2.
            - repeat invert_wf_aux; eauto 2.
            - repeat invert_wf_aux; eauto 2.
            - repeat invert_wf_aux; eauto 2.
            - intros; subst; repeat invert_wf_aux; eauto 2.
            - intros; subst.
              repeat invert_wf_aux.
              assert (exists loc, v = ValLoc loc) by eauto 3.
              super_destruct; subst.
              exists loc0.
              assert (exists x, memory_lookup m1 x = Some (ValLoc loc0) /\ e0 = Var x) by eauto 2.
              super_destruct; subst.
              invert_var_typing.
              assert_wf_type.
              invert_wf_type.
              splits~.
              + intros; eauto 3.
              + intros; eauto 3.
            - intros; subst.
              repeat invert_wf_aux.
              assert (exists loc, v2 = ValLoc loc) by eauto 3.
              super_destruct; subst.
              exists loc0.
              assert (exists x, memory_lookup s1 x = Some (ValLoc loc0) /\ e0 = Var x) by eauto 2.
              super_destruct; subst.
              invert_var_typing.
              assert_wf_type.
              invert_wf_type.
              splits~.
              + intros; eauto 3.
              + intros; eauto 3.
            - intros; contradiction.
          }
          assert (wf_bijection ℓ ψ Γ
                               (extend_stenv l1 τ0 Σ1)
                               (m1 [i → ValLoc l1])
                               (extend_heap v l1 l n h1 H9 H21)).
          {
            destruct τ0 as [τ0 [ℓ' ι']].
            eapply wf_bijection_extend_mem_and_heap_high1; eauto 3.
            - repeat invert_wf_aux; eauto.
            - repeat invert_wf_aux; eauto.
          }

          assert (wellformed_aux Γ Σ3 ⟨NewArr i l e e0, pc_end, s1', h', g2'' - 1⟩ pc_end) by eauto 2.
          splits~.
          { eapply bridge_stop_num.
            splits; eauto 2.
            - constructor.
              constructors; eauto 2.
            - intro.
              invert_low_event; contradiction.
            - reflexivity.
          }
          { unfolds.
            splits.
            - splits; intros; invert_low_event; contradiction.
            - intros; invert_low_event; contradiction.
          }

          assert (wf_taint_bijection ℓ (extend_bijection Ψ loc l2 H58 H59)
                                     (s1 [i → ValLoc loc]) (extend_heap v2 loc l n0 w1 H50 H33)).
          {
            eapply wf_taint_bijection_extend_mem_and_heap1; eauto 2.
            intros; subst; eauto 2.
          }
          splits.
          {
            eapply wf_bijection_extend_mem_and_heap_high2; eauto 2.
          }
          {
            eauto 2.
          }
          {
            remember_simple (low_gc_trans_preserves_taint_eq H5 H7 H27).
            unfold taint_eq in *; super_destruct'; subst.
            destruct τ0 as [σ [ℓ' ι']].
            repeat invert_wf_aux.
            eapply wf_taint_bijection_extend_mem_and_heap2 with (Φ := Φ) (m1 := s1) (h1 := w1) (v1 := v2); intros; subst; eauto 3.
            - rewrite <- (compose_id_right Φ).
              eapply taint_eq_reach_trans; eauto.
            - rewrite <- (compose_id_right Φ).
              eapply taint_eq_heap_trans; eauto.
            - rewrite <- (compose_id_right Φ).
              eapply taint_eq_heap_domain_eq_trans; eauto.
            - eapply low_gc_trans_preserves_wf_taint_bijection with (pc := pc_end); eauto.
            - subst; eauto 2.
            - subst; eauto 2.
            - subst.
              assert (exists loc, v2 = ValLoc loc) by eauto 3.
              super_destruct'; subst.
              eexists; splits; eauto 2.
            - subst.
              assert (exists loc, v1 = ValLoc loc) by eauto 3.
              super_destruct'; subst.
              eexists; splits; eauto 2.
          }
          {
            unfolds.
            splits.
            - eauto 2.
            - eapply taint_eq_mem_extend_mem_and_bijection; eauto.
            - destruct τ0 as [σ [ℓ' ι']].
              remember_simple (low_gc_trans_preserves_taint_eq H5 H7 H27).
              unfold taint_eq in *; super_destruct'; subst.
              eapply taint_eq_reach_extend_mem_and_heap;
                (intros; subst; eauto 3) || (try solve [repeat invert_wf_aux; eauto 2]).
              + rewrite <- (compose_id_right Φ).
                eapply taint_eq_reach_trans; eauto 2.
              + eapply low_gc_trans_preserves_wf_taint_bijection with (pc := pc_end); eauto 2.
              + rewrite <- (compose_id_right Φ).
                eapply taint_eq_heap_trans; eauto 2.
                repeat invert_wf_aux; eauto 2.
              + intros; subst.
                assert (exists loc, v2 = ValLoc loc) by eauto 2.
                super_destruct'; subst; eexists; splits; eauto 2.
              + intros; subst.
                repeat invert_wf_aux.
                assert (exists loc, v1 = ValLoc loc) by eauto 2.
                super_destruct'; subst; eexists; splits; eauto 2.
              + subst.
                repeat invert_wf_aux; eauto 3.
              + subst.
                repeat invert_wf_aux; eauto 3.                
            - remember_simple (low_gc_trans_preserves_taint_eq H5 H7 H27).
              unfold taint_eq in *; super_destruct'; subst.
              eapply taint_eq_heap_extend_mem_and_heap with (Φ := Φ).
              + rewrite <- (compose_id_right Φ).
                eapply taint_eq_heap_trans.
                * eauto.
                * eauto.
                * repeat invert_wf_aux; eauto 2.
                * eauto.
                * eauto.
                * eauto.
              + eauto.
              + intros; subst; eauto 2.
              + intros; subst; repeat invert_wf_aux; eauto 2.
              + eauto.
            - remember_simple (low_gc_trans_preserves_taint_eq H5 H7 H27).
              unfold taint_eq in *; super_destruct'; subst.
              unfolds.
              intros.
              destruct (T_dec l0 l); subst.
              + repeat rewrite -> size_extend_heap_eq_level by solve[eauto 2].
                assert (size l w1' = size l h') by eauto 2.
                assert (size l w1 = size l w1') by eauto 2.
                omega.
              + repeat rewrite -> size_extend_heap_neq_level by solve[eauto 2].
                assert (size l0 w1' = size l0 h') by eauto 2.
                assert (size l0 w1 = size l0 w1') by eauto 2.
                omega.
            - destruct τ0 as [σ ε].
              remember_simple (low_gc_trans_preserves_taint_eq H5 H7 H27).
              unfold taint_eq in *; super_destruct'; subst.
              repeat invert_wf_aux.
              eapply taint_eq_heap_domain_eq_extend_mem_and_heap with (Φ := Φ); eauto 2.
              + eapply low_gc_trans_preserves_wf_taint_bijection with (pc := pc_end); eauto 2.
              + intros; subst.
                assert (exists loc, v2 = ValLoc loc) by eauto 2.
                super_destruct'; subst; eexists; splits; eauto 2.
              + intros; subst.
                assert (exists loc, v1 = ValLoc loc) by eauto 2.
                super_destruct'; subst; eexists; splits; eauto 2.
              + rewrite <- (compose_id_right Φ).
                eapply taint_eq_reach_trans; eauto 2.
              + rewrite <- (compose_id_right Φ).
                eapply taint_eq_heap_trans; eauto 2.
              + rewrite <- (compose_id_right Φ).
                eapply taint_eq_heap_domain_eq_trans; eauto.
              + intros; subst; eauto 3.
              + intros; subst; eauto 3.
            - unfolds.
              intros.
              destruct (decide (loc = loc1)); subst.
              + _rewrite -> left_extend_bijection_eq in *.
                rewrite_inj.
                repeat rewrite -> extend_stenv_lookup_eq.
                splits*.
              + _rewrite -> left_extend_bijection_neq in * by solve[eauto 2].
                assert (l2 <> loc2).
                {
                  intro; subst.
                  assert (right Ψ loc2 = Some loc1) by (destruct Ψ; eauto 2).
                  congruence.
                }
                repeat rewrite -> extend_stenv_lookup_neq by solve[eauto 2].
                assert (left Φ loc1 = Some loc2).
                {
                  eapply filtered_bijection_is_subset.
                  - eapply high_dec.
                  - eauto 2.
                  - eauto 2.
                }
                eapply H18; eauto 2.
          }
    }
    (* Set *)
    {
      invert_bridge_step_with_steps 0.
      + invert_low_event_step.
        assert (wellformed_aux Γ Σ1' ⟨c2, pc1', m2, h2, t2⟩ pc_end) by eauto 2.
        invert_taint_eq; invert_taint_eq_cmd.
        invert_event_step; try solve[invert_low_event].
        assert (lookup_in_bounds m2 h2).
        {
          repeat invert_wf_aux; eauto.
        }
        invert_sem_step.
        invert_low_event.
        _apply set_bridge_properties in *.
        super_destruct'; subst.
        invert_bridge_step.
        * invert_low_event_step.
          invert_event_step; invert_low_event.
          invert_sem_step.
          rewrite_inj.
          clear H40.
          
          assert (eval s1 e = Some (ValNum n0)).
          {
            repeat invert_wf_aux.
            repeat specialize_gen.
            invert_wt_cmd.
            rewrite_inj.
            destruct ε as [ℓ' ι'].
            repeat invert_lifted.
            rewrite_inj.
            destruct ε_idx as [ℓ_idx ι_idx].
            rewrite -> ProdL.join_is_pairwise in *.
            assert (ℓ_idx ⊔ pc_end ⊑ ℓ_x0) by eauto 2.
            destruct_join_flowsto.
            assert (ℓ_idx ⊑ ℓ) by eauto 2.
            assert (exists u, onvals (left φ) (ValNum n0) = Some u /\ eval s1 e = Some u) by eauto 2 using eval_low_eq_possibilistic.
            super_destruct'; subst.
            unfold onvals in *.
            rewrite_inj.
            eauto.
          }
          assert (n0 = n3).
          {
            repeat invert_wf_aux.
            repeat specialize_gen.
            invert_wt_cmd.
            rewrite_inj.
            destruct ε as [ℓ' ι'].
            repeat invert_lifted.
            rewrite_inj.
            destruct ε_idx as [ℓ_idx ι_idx].
            assert_wf_type.
            invert_wf_type.
            repeat rewrite -> ProdL.join_is_pairwise in *.
            assert (LH.flowsto (LH.join ι_idx ∘) ∘) by eauto 2.
            assert (val_taint_eq Φ (SecType Int (ℓ_idx, ι_idx)) (ValNum n0) (ValNum n3))
              by eauto 2.
            invert_val_taint_eq.
            - reflexivity.
            - inverts H3.
          }
          subst.
          assert (exists u, onvals (left φ) v0 = Some u /\ eval s1 e0 = Some u).
          {
            repeat invert_wf_aux.
            repeat specialize_gen.
            invert_wt_cmd.
            rewrite_inj.
            destruct ε as [ℓ' ι'].
            repeat invert_lifted.
            rewrite_inj.
            assert (ℓ_x0 ⊔ ℓ' ⊑ ℓ1) by eauto 2.
            destruct_join_flowsto.
            assert_wf_type.
            invert_wf_type.
            assert (ℓ' ⊑ ℓ) by eauto 2.
            eauto 2 using eval_low_eq_possibilistic.
          }
          super_destruct'; subst.
          rewrite_inj.
          exists (SetEvent ℓ1 ℓ_x0 i n3 u) 0.

          remember_simple (filter_bijection (low ℓ Γ Σ1' m2 (update_heap l1 n3 v0 h1))
                                            (low_dec ℓ Γ Σ1' m2 (update_heap l1 n3 v0 h1)) φ).
          super_destruct; subst.          
          exists ψ.
          assert (eval m2 (Var i) = Some (ValLoc l1)) by eauto 2.
          assert (exists u, onvals (left φ) (ValLoc l1) = Some u /\ eval s1 (Var i) = Some u).
          {
            repeat invert_wf_aux.
            repeat specialize_gen.
            invert_wt_cmd.
            rewrite_inj.
            assert (expr_has_type Γ (Var i) (SecType (Array (SecType τ0 (ℓ1, ι0)) ℓ0) (ℓ_x0, ι_x0))) by eauto 2.
            eauto 2 using eval_low_eq_possibilistic.
          }
          super_destruct'; subst; unfold onvals in *.
          break_match; try discriminate.
          rewrite_inj.
          remember_simple (filter_bijection (high ℓ s1 (update_heap l n3 u w1)) (high_dec ℓ s1 (update_heap l n3 u w1)) Φ).
          super_destruct'; subst.
          rename ψ0 into Ψ.
          exists Ψ s1 (update_heap l n3 u w1) Σ2.

          assert (left Φ l = Some l3).
          {
            repeat invert_wf_aux.
            repeat specialize_gen.
            invert_wt_cmd.
            invert_lifted.
            rewrite_inj.
            assert (expr_has_type Γ (Var i) (SecType (Array (SecType σ (ℓ1, ι0)) ℓ0) (ℓ_x0, ι_x0))) by eauto 2.
            assert (eval s2'' (Var i) = Some (ValLoc l3)) by eauto 2.
            assert (val_taint_eq Φ (SecType (Array (SecType σ (ℓ1, ι0)) ℓ0) (ℓ_x0, ι_x0)) (ValLoc l) (ValLoc l3)) by eauto 2 using eval_taint_eq.
            invert_val_taint_eq; eauto 2.
            assert_wf_type.
            invert_wf_type.
          }
          assert (wellformed_aux Γ Σ3' ⟨SetArr i e e0, pc2'', s2'', h', g2'' - 1⟩ pc_end).
          {
            eauto 2 using gc_trans_preservation.
          }
          assert (taint_eq ℓ (identity_bijection loc) Γ Σ3' Σ3' (SetArr i e e0) (SetArr i e e0) s2'' w1' s2'' h').
          {
            eauto 2.
          }
          unfold taint_eq in *; super_destruct'.
          assert (taint_eq_heap ℓ Φ Σ2 Σ3' s1 w1 s2'' h').
          {
            rewrite <- (compose_id_right Φ).
            repeat invert_wf_aux.
            eapply taint_eq_heap_trans; eauto 2.
          }
          assert (high ℓ s1 w1 l) by eauto 3.
          assert (exists ℓ μ, heap_lookup l w1 = Some (ℓ, μ)).
          {
            repeat invert_wf_aux.
            destruct_high; eauto 3.
          }
          assert (high ℓ s2'' h' l3) by eauto 3.
          assert (exists ℓ μ, heap_lookup l3 h' = Some (ℓ, μ)).
          {
            repeat invert_wf_aux.
            destruct_high; eauto 3.
          }
          super_destruct'; subst.
          assert (exists s, Σ2 l = Some s) by (repeat invert_wf_aux; eauto 2).
          super_destruct'; subst.
          assert (Σ3' l3 = Some s).
          {
            eapply H20; eauto 2.
          }
          assert (ℓ2 = ℓ0 /\
                  length_of l w1 = length_of l3 h' /\
                  (forall n,
                      (exists v, lookup μ0 n = Some v) <-> (exists v, lookup μ n = Some v)) /\
                  (forall n v1 v2,
                      reach s1 w1 l ->
                      reach s2'' h' l3 ->
                      lookup μ0 n = Some v1 -> lookup μ n = Some v2 -> val_taint_eq Φ s v1 v2)).
          {
            eapply H46; eauto.
          }
          super_destruct'; subst.
          assert (state_low_eq ℓ ψ m2 (update_heap l1 n3 v0 h1) s1 (update_heap l n3 u w1) Γ Σ1' Σ2).
          {
            repeat invert_wf_aux.
            repeat specialize_gen.
            invert_wt_cmd.
            invert_lifted.
            rewrite_inj.
            eapply state_low_eq_update_heap with (length1 := length) (length2 := length0); try solve[intros; subst; eauto 3].
            - intros; subst.
              assert (exists loc, v0 = ValLoc loc) by eauto 3.
              super_destruct; subst.
              exists loc.
              assert (exists x, memory_lookup m2 x = Some (ValLoc loc) /\ e0 = Var x)
                by eauto 2.
              super_destruct; subst.
              rewrite_inj.
              invert_var_typing.
              assert (wf_type bot (SecType (Array (SecType (Array s0 ℓ3) (ℓ1, ι0)) ℓ2) (ℓ_x0, ι_x0))) by eauto 2.
              do 2 invert_wf_type.
              splits~; eauto 3.
              intros.
              assert (wf_type bot (SecType (Array s0 ℓ3) ε)) by eauto 2.
              invert_wf_type.
              destruct_prod_join_flowsto.
              assert (l_ref ⊑ ℓ1) by eauto 2.
              eauto 3.
            - intros; subst.
              assert (exists loc, u = ValLoc loc) by eauto 3.
              super_destruct; subst.
              exists loc.
              assert (exists x, memory_lookup s1 x = Some (ValLoc loc) /\ e0 = Var x)
                by eauto 2.
              super_destruct; subst.
              rewrite_inj.
              invert_var_typing.
              assert (wf_type bot (SecType (Array (SecType (Array s0 ℓ3) (ℓ1, ι0)) ℓ2) (ℓ_x0, ι_x0))) by eauto 2.
              do 2 invert_wf_type.
              splits~; eauto 3.
              intros.
              assert (wf_type bot (SecType (Array s0 ℓ3) ε)) by eauto 2.
              invert_wf_type.
              destruct_prod_join_flowsto.
              assert (l_ref ⊑ ℓ1) by eauto 2.
              eauto 3.
            - destruct ε as [ℓ' ι'].
              destruct_prod_join_flowsto.
              assert (ℓ' ⊑ ℓ1) by eauto 2.
              assert (ℓ' ⊑ ℓ) by eauto 2.
              eapply val_low_eq_mon.
              + invert_state_low_eq.
                eapply eval_low_eq with (m1 := m2); eauto 3.
              + eauto 2.
            - congruence.
          }
          
          assert (wf_bijection ℓ ψ Γ Σ1' m2 (update_heap l1 n3 v0 h1)).
          {
            repeat invert_wf_aux.
            repeat specialize_gen.
            invert_wt_cmd.
            invert_lifted.
            rewrite_inj.
            assert_wf_type.
            invert_wf_type.
            eapply wf_bijection_update_heap1.
            - eauto 3.
            - eauto.
            - intros; subst.
              destruct σ.
              + assert (exists n, ValLoc loc' = ValNum n) by eauto 2.
                super_destruct; discriminate.
              + assert (exists x, memory_lookup m2 x = Some (ValLoc loc') /\ e0 = Var x)
                  by eauto 2.
                super_destruct; subst.
                destruct ε as [ℓ' ι'].
                destruct_prod_join_flowsto.
                assert (ℓ' ⊑ ℓ1) by eauto 2.
                assert (ℓ' ⊑ ℓ) by eauto 2.
                invert_var_typing.
                assert_wf_type.
                invert_wf_type.
                eauto 3.
            - eauto.
          }
          
          splits.
          {
            constructor.
            splits; eauto 2.
            constructor.
            eapply event_sem_step_set; eauto 2.
            eapply step_set with (length := length0); eauto 2.
            congruence.
          }
          {
            eauto 2.
          }
          {
            eauto 2.
          }
          {
            eauto 2.
          }
          {
            splits*.
            intros.
            constructor.
            break_match; rewrite_inj.
            - eauto 2.
            - break_match; try discriminate.
              subst.
              rewrite_inj.
              assert (low ℓ Γ Σ1' m2 (update_heap l1 n3 (ValLoc l0) h1) l0).
              {
                assert (low ℓ Γ Σ1' m2 h1 l0) by eauto 2.
                destruct_low.
                - repeat invert_wf_aux.
                  assert_wf_type.
                  invert_wf_type.
                  repeat specialize_gen.
                  invert_wt_cmd.
                  invert_lifted.
                  rewrite_inj.
                  assert (exists τ ℓ, σ = Array τ ℓ).
                  {
                    destruct σ.
                    - assert (exists n, ValLoc loc = ValNum n) by eauto 3.
                      super_destruct'; congruence.
                    - do 2 eexists; reflexivity.
                  }
                  super_destruct'; subst.
                  rewrite_inj.
                  invert_wf_type.
                  assert (reach m h l1) by eauto 2.
                  assert (exists ℓ μ, heap_lookup l1 h = Some (ℓ, μ)) by eauto 2.
                  super_destruct'.
                  eapply LowReachable.
                  eapply LowReachHeap.
                  + eapply LowReachMem.
                    * eauto 2.
                    * eauto.
                    * eauto.
                  + eauto 3.
                  + eapply heap_lookup_update_eq; eauto 2.
                  + eauto 2.
                  + eauto 2.
                - destruct (decide (l1 = loc)); subst.
                  + eapply LowHeapLevel.
                    * eapply heap_lookup_update_eq; eauto 2.
                    * eauto 2.
                  + eapply LowHeapLevel.
                    * rewrite -> heap_lookup_update_neq by solve[eauto 2].
                      eauto 2.
                    * eauto 2.
              }
              assert (left ψ l0 = Some l2) by eauto 2.
              eauto 2.
          }
          {
            repeat invert_wf_aux.
            assert_wf_type.
            invert_wf_type.
            repeat specialize_gen.
            invert_wt_cmd.
            invert_lifted.
            rewrite_inj.
            eapply TaintEqEventSet.
            - eauto 2.
            - destruct ε as [ℓ' ι'].
              destruct_prod_join_flowsto.
              eapply val_taint_eq_mon with (ℓ1 := ℓ') (ι1 := ι'); eauto 2.
              assert (val_taint_eq Φ (SecType σ (ℓ', ι')) u v2) by eauto 2 using eval_taint_eq.
              invert_val_taint_eq; eauto 2.
              assert (left Ψ loc = Some loc').
              {
                assert (high ℓ s1 (update_heap l n3 (ValLoc loc) w1) loc).
                {
                  eauto 3.
                }
                eapply filter_true; eauto 2.
              }
              eauto 2.
          }
          {
            eauto 2.
          }

          assert (wf_taint_bijection ℓ Ψ s1 (update_heap l n3 u w1)).
          {
            eapply taint_eq_update_bijection1; eauto 2.
            intros; subst.
            repeat invert_wf_aux.
            repeat specialize_gen.
            invert_wt_cmd.
            eapply eval_implies_reach; eauto 2.
          }

          repeat invert_wf_aux.
          repeat specialize_gen.
          invert_wt_cmd.
          invert_lifted.
          rewrite_inj.
          assert (val_taint_eq Φ (SecType σ (ℓ1, ι0)) u v2).
          {
            destruct ε as [ℓ'' ι''].
            destruct_prod_join_flowsto.
            eapply val_taint_eq_mon; eauto.
            eapply LHLatProp.flowsto_refl.
          }

          repeat invert_wf_aux.
          repeat specialize_gen.
          invert_wt_cmd.
          invert_lifted.
          rewrite_inj.
          splits~.

          {
            repeat invert_wf_aux.
            repeat specialize_gen.
            invert_wt_cmd.
            invert_lifted.
            rewrite_inj.
            eapply wf_bijection_update_heap2; try solve[intros; subst; eauto 3].
            - eapply val_low_eq_mon.
              + repeat invert_state_low_eq.
                eauto 3.
              + repeat destruct_prod_join_flowsto.
                eauto.                
            - intros; subst.
              assert (exists loc, v0 = ValLoc loc) by eauto 2.
              super_destruct'; subst.
              eexists; splits~.
              intros.
              destruct ε as [ℓ'' ι''].
              repeat destruct_join_flowsto.
              assert (ℓ_x0 ⊔ ℓ'' ⊑ ℓ1) by eauto 2.
              destruct_join_flowsto.
              assert (ℓ'' ⊑ ℓ) by eauto 3.
              assert_wf_type.
              invert_wf_type.
              invert_wf_type.
              assert (exists x, memory_lookup m2 x = Some (ValLoc loc) /\ e0 = Var x) by eauto 2.
              super_destruct'; subst.
              invert_var_typing.
              assert_wf_type.
              invert_wf_type.
              eauto 2.
            - intros; subst.
              assert (exists loc, u = ValLoc loc) by eauto 2.
              super_destruct'; subst.
              eexists; splits~.
              intros.
              destruct ε as [ℓ'' ι''].
              repeat destruct_join_flowsto.
              assert (ℓ_x0 ⊔ ℓ'' ⊑ ℓ1) by eauto 2.
              destruct_join_flowsto.
              assert (ℓ'' ⊑ ℓ) by eauto 3.
              assert_wf_type.
              invert_wf_type.
              invert_wf_type.
              assert (exists x, memory_lookup s1 x = Some (ValLoc loc) /\ e0 = Var x) by eauto 2.
              super_destruct'; subst.
              invert_var_typing.
              assert_wf_type.
              invert_wf_type.
              eauto 2.
          }
          
          {
            eapply wf_taint_bijection_update_heap2 with (Φ := Φ) (m1 := s1) (m2 := s2'')
            ; eauto 2.
            - eapply low_gc_trans_preserves_wf_taint_bijection; eauto 2.
            - rewrite <- (compose_id_right Φ).
              eapply taint_eq_heap_domain_eq_trans; eauto 2.
            - rewrite <- (compose_id_right Φ).
              eapply taint_eq_reach_trans; eauto 2.
            - intros; subst.
              assert (exists loc, u = ValLoc loc) by eauto 2.
              super_destruct'; subst.
              eexists; splits; eauto 2.
            - intros; subst.
              assert (exists loc, v2 = ValLoc loc) by eauto 2.
              super_destruct'; subst.
              eexists; splits; eauto 2.
            - intros; subst.
              eauto 2.
            - intros; subst.
              eauto 2.
          }
          { eapply taint_eq_mem_update_heap; eauto 2. }
          { eapply taint_eq_reach_update_heap; eauto 2.
            - rewrite <- (compose_id_right Φ).
              eapply taint_eq_reach_trans; eauto 2.
            - rewrite <- (compose_id_right Φ).
              eapply taint_eq_heap_domain_eq_trans; eauto 2.
            - intros; subst.
              assert (exists loc, u = ValLoc loc) by eauto 2.
              super_destruct'; subst.
              eexists; splits; eauto 2.
            - intros; subst.
              assert (exists loc, v2 = ValLoc loc) by eauto 2.
              super_destruct'; subst.
              eexists; splits; eauto 2.
            - intros; subst.
              eauto 2.
            - intros; subst.
              eauto 2.
            - eapply low_gc_trans_preserves_wf_taint_bijection; eauto 2.
            - rewrite <- (compose_id_right Φ).
              eapply taint_eq_reach_trans; eauto 2.
          }
          { assert (Σ2 l = Some (SecType σ0 (ℓ1, ι0))) by eauto 2.
            rewrite_inj.
            eapply taint_eq_heap_update_heap; eauto 2.
            + intros; subst.
              eauto 2.
            + intros; subst.
              eauto 2. }
          { splits.
            - unfolds.
              intros.
              repeat rewrite -> size_update_heap.
              rewrite -> H18 by eauto 2.
              eauto 2.
            - repeat invert_wf_aux.
              eapply taint_eq_heap_update_domain_eq_update_heap with (Φ := Φ) (Σ1 := Σ2) (Σ2 := Σ3'); eauto 2.
              + rewrite <- (compose_id_right Φ).
                eapply taint_eq_heap_domain_eq_trans; eauto 2.
              + eapply low_gc_trans_preserves_wf_taint_bijection; eauto 2.
              + rewrite <- (compose_id_right Φ).
                eapply taint_eq_heap_domain_eq_trans; eauto 2.
              + rewrite <- (compose_id_right Φ).
                eapply taint_eq_reach_trans; eauto 2.
              + intros; subst.
                assert (exists loc, u = ValLoc loc) by eauto 3.
                super_destruct'; subst.
                eexists; eauto 3.
              + intros; subst.
                assert (exists loc, v2 = ValLoc loc) by eauto 3.
                super_destruct'; subst.
                eexists; eauto 3.
              + intros; subst; eauto 2.
              + intros; subst; eauto 3.
            - unfolds.
              intros.
              assert (left Φ loc1 = Some loc2).
              {
                eapply filtered_bijection_is_subset.
                - eapply high_dec.
                - eauto 2.
                - eauto 2.
              }
              eauto. }
        * unfold is_stop_config, cmd_of in *; subst.
          invert_high_event_step.
          invert_event_step.
          invert_sem_step.
          rewrite_inj.
          assert (low_event ℓ (SetEvent ℓ1 ℓ_x0 i n3 v2)) by eauto 2.
          contradiction.
      + invert_high_event_step.
        unfold is_stop_config, cmd_of in *; subst.
        assert (wellformed_aux Γ Σ1' ⟨Stop, pc1', m2, h2, t2⟩ pc_end) by eauto 2.
        invert_taint_eq; invert_taint_eq_cmd.
        invert_event_step; try solve[invert_low_event].
        assert (lookup_in_bounds m2 h2).
        {
          repeat invert_wf_aux; eauto.
        }
        invert_sem_step.
        invert_high_event.
        _apply set_bridge_properties in *.
        super_destruct'; subst.
        invert_bridge_step.
        * invert_low_event_step.
          invert_event_step; try solve[invert_low_event].
          rewrite_inj.
          invert_low_event.
          assert (low_event ℓ (SetEvent ℓ1 ℓ_x0 i n0 v0)) by eauto 2.
          contradiction.
        * invert_high_event_step.
          invert_event_step.
          invert_sem_step.
          rewrite_inj.
          clear H31.
          
         assert (eval s1 e = Some (ValNum n3)).
          {
            repeat invert_wf_aux.
            repeat specialize_gen.
            invert_wt_cmd.
            rewrite_inj.
            destruct ε as [ℓ' ι'].
            repeat invert_lifted.
            rewrite_inj.
            destruct ε_idx as [ℓ_idx ι_idx].
            assert (taint_eq_mem (inverse Φ) Γ s2'' s1) by eauto 2.
            remember_simple (eval_taint_eq_possibilistic H9 H27 H24 H3 H50).
            super_destruct'; subst.
            invert_val_taint_eq.
            - eauto.
            - assert_wf_type.
              invert_wf_type.
              assert (LH.flowsto (LH.join • ∘) ∘) as H' by eauto 2.
              inverts H'.
          }
   
          assert (exists u,
                     eval s1 e0 = Some u /\ val_taint_eq Φ (SecType τ0 (ℓ1, ι0)) u v2).
          {
            repeat invert_wf_aux.
            repeat specialize_gen.
            invert_wt_cmd.
            rewrite_inj.
            destruct ε as [ℓ' ι'].
            repeat invert_lifted.
            rewrite_inj.
            assert_wf_type.
            invert_wf_type.
            assert (taint_eq_mem (inverse Φ) Γ s2'' s1) by eauto 2.
            remember_simple (eval_taint_eq_possibilistic H21 H28 H25 H3 H51).
            super_destruct'; subst.
            exists v1.
            splits*.
          }
          super_destruct'; subst.
          rewrite_inj.
          exists (SetEvent ℓ1 ℓ_x0 i n3 u) 0.

          remember_simple (filter_bijection (low ℓ Γ Σ1' m2 (update_heap l1 n0 v0 h1))
                                            (low_dec ℓ Γ Σ1' m2 (update_heap l1 n0 v0 h1)) φ).
          super_destruct; subst.          
          exists ψ.
          assert (eval m2 (Var i) = Some (ValLoc l1)) by eauto 2.
          assert (exists l, right Φ l3 = Some l /\ eval s1 (Var i) = Some (ValLoc l)).
          {
            repeat invert_wf_aux.
            repeat specialize_gen.
            invert_wt_cmd.
            rewrite_inj.
            assert (expr_has_type Γ (Var i) (SecType (Array (SecType τ0 (ℓ1, ι0)) ℓ0) (ℓ_x0, ι_x0))) by eauto 2.
            invert_lifted.
            assert (taint_eq_mem (inverse Φ) Γ s2'' s1) by eauto 2.
            assert (eval s2'' (Var i) = Some (ValLoc l3)) by eauto 2.
            remember_simple (eval_taint_eq_possibilistic H3 H32 H29 H4 H28).
            super_destruct'; subst.
            invert_val_taint_eq.
            - destruct Φ; eexists; splits*.
            - assert_wf_type.
              invert_wf_type.
          }
          super_destruct'; subst; unfold onvals in *.
          remember_simple (filter_bijection (high ℓ s1 (update_heap l n3 u w1))
                                            (high_dec ℓ s1 (update_heap l n3 u w1)) Φ).
          super_destruct'; subst.
          rename ψ0 into Ψ.
          exists Ψ s1 (update_heap l n3 u w1) Σ2.

          assert (left Φ l = Some l3).
          {
            repeat invert_wf_aux.
            repeat specialize_gen.
            invert_wt_cmd.
            invert_lifted.
            rewrite_inj.
            assert (expr_has_type Γ (Var i) (SecType (Array (SecType σ (ℓ1, ι0)) ℓ0) (ℓ_x0, ι_x0))) by eauto 2.
            assert (eval s2'' (Var i) = Some (ValLoc l3)) by eauto 2.
            assert (val_taint_eq Φ (SecType (Array (SecType σ (ℓ1, ι0)) ℓ0) (ℓ_x0, ι_x0)) (ValLoc l) (ValLoc l3)) by eauto 2 using eval_taint_eq.
            invert_val_taint_eq; eauto 2.
            assert_wf_type.
            invert_wf_type.
          }
          assert (wellformed_aux Γ Σ3' ⟨SetArr i e e0, pc2'', s2'', h', g2'' - 1⟩ pc_end).
          {
            eauto 2 using gc_trans_preservation.
          }
          assert (taint_eq ℓ (identity_bijection loc) Γ Σ3' Σ3' (SetArr i e e0) (SetArr i e e0) s2'' w1' s2'' h').
          {
            eauto 2.
          }
          unfold taint_eq in *; super_destruct'.
          assert (taint_eq_heap ℓ Φ Σ2 Σ3' s1 w1 s2'' h').
          {
            rewrite <- (compose_id_right Φ).
            repeat invert_wf_aux.
            eapply taint_eq_heap_trans; eauto 2.
          }
          assert (high ℓ s1 w1 l) by eauto 3.
          assert (exists ℓ μ, heap_lookup l w1 = Some (ℓ, μ)).
          {
            repeat invert_wf_aux.
            destruct_high; eauto 3.
          }
          assert (high ℓ s2'' h' l3) by eauto 3.
          assert (exists ℓ μ, heap_lookup l3 h' = Some (ℓ, μ)).
          {
            repeat invert_wf_aux.
            destruct_high; eauto 3.
          }
          super_destruct'; subst.
          assert (exists s, Σ2 l = Some s) by (repeat invert_wf_aux; eauto 2).
          super_destruct'; subst.
          assert (Σ3' l3 = Some s).
          {
            eapply H20; eauto 2.
          }
          assert (ℓ2 = ℓ0 /\
                  length_of l w1 = length_of l3 h' /\
                  (forall n,
                      (exists v, lookup μ0 n = Some v) <-> (exists v, lookup μ n = Some v)) /\
                  (forall n v1 v2,
                      reach s1 w1 l ->
                      reach s2'' h' l3 ->
                      lookup μ0 n = Some v1 -> lookup μ n = Some v2 -> val_taint_eq Φ s v1 v2)).
          {
            eapply H49; eauto.
          }
          super_destruct'; subst.
          assert (~ ℓ1 ⊑ ℓ).
          {
            intro.
            repeat invert_wf_aux.
            repeat specialize_gen.
            invert_wt_cmd.
            invert_lifted.
            rewrite_inj.
            assert_wf_type.
            invert_wf_type.
            destruct ε as [ℓ' ι'].
            assert (ℓ_x0 ⊔ ℓ' ⊑ ℓ1) by eauto 2.
            destruct_join_flowsto.
            assert (ℓ_x0 ⊑ ℓ) by eauto.
            assert (low_event ℓ (SetEvent ℓ1 ℓ_x0 i n3 v2)) by eauto 2.
            contradiction.
          }
          assert (state_low_eq ℓ ψ m2 (update_heap l1 n0 v0 h1) s1 (update_heap l n3 u w1) Γ Σ1' Σ2).
          {
            repeat invert_wf_aux.
            repeat specialize_gen.
            invert_wt_cmd.
            invert_lifted.
            rewrite_inj.
            eapply state_low_eq_update_heap with (length1 := length) (length2 := length0); try solve[intros; subst; eauto 3].
            - intros; subst.
              assert (exists loc, v0 = ValLoc loc) by eauto 3.
              super_destruct; subst.
              exists loc.
              assert (exists x, memory_lookup m2 x = Some (ValLoc loc) /\ e0 = Var x)
                by eauto 2.
              super_destruct; subst.
              rewrite_inj.
              invert_var_typing.
              assert (wf_type bot (SecType (Array (SecType (Array s0 ℓ3) (ℓ1, ι0)) ℓ2) (ℓ_x0, ι_x0))) by eauto 2.
              do 2 invert_wf_type.
              splits~; eauto 3.
              intros.
              assert (wf_type bot (SecType (Array s0 ℓ3) ε)) by eauto 2.
              invert_wf_type.
              destruct_prod_join_flowsto.
              assert (l_ref ⊑ ℓ1) by eauto 2.
              eauto 3.
            - intros; subst.
              assert (exists loc, u = ValLoc loc) by eauto 3.
              super_destruct; subst.
              exists loc.
              assert (exists x, memory_lookup s1 x = Some (ValLoc loc) /\ e0 = Var x)
                by eauto 2.
              super_destruct; subst.
              rewrite_inj.
              invert_var_typing.
              assert (wf_type bot (SecType (Array (SecType (Array s0 ℓ3) (ℓ1, ι0)) ℓ2) (ℓ_x0, ι_x0))) by eauto 2.
              do 2 invert_wf_type.
              splits~; eauto 3.
              intros.
              assert (wf_type bot (SecType (Array s0 ℓ3) ε)) by eauto 2.
              invert_wf_type.
              destruct_prod_join_flowsto.
              assert (l_ref ⊑ ℓ1) by eauto 2.
              eauto 3.
            - destruct σ.
              + assert (exists n, v0 = ValNum n) by eauto 2.
                assert (exists n, u = ValNum n) by eauto 2.
                super_destruct'; subst; eauto 2.
              + assert (exists loc, v0 = ValLoc loc) by eauto 2.
                assert (exists loc, u = ValLoc loc) by eauto 2.
                super_destruct'; subst; eauto 2.
            - intros; contradiction.
            - congruence.
          }

          assert (wf_bijection ℓ ψ Γ Σ1' m2 (update_heap l1 n0 v0 h1)).
          {
            repeat invert_wf_aux.
            repeat specialize_gen.
            invert_wt_cmd.
            invert_lifted.
            rewrite_inj.
            assert_wf_type.
            invert_wf_type.
            eapply wf_bijection_update_heap1.
            - eauto 3.
            - eauto.
            - intros; subst.
              destruct σ.
              + assert (exists n, ValLoc loc' = ValNum n) by eauto 2.
                super_destruct; discriminate.
              + assert (exists x, memory_lookup m2 x = Some (ValLoc loc') /\ e0 = Var x)
                  by eauto 2.
                super_destruct; subst.
                destruct ε as [ℓ' ι'].
                destruct_prod_join_flowsto.
                assert (ℓ' ⊑ ℓ1) by eauto 2.
                assert (ℓ' ⊑ ℓ) by eauto 2.
                invert_var_typing.
                assert_wf_type.
                invert_wf_type.
                eauto 3.
            - eauto.
          }
          
          splits.
          {
            eapply bridge_stop_num.
            - splits; eauto 2.
              + constructor.
                eapply event_sem_step_set; eauto 2.
                eapply step_set; eauto 2.
                congruence.
              + intro.
                invert_low_event.
                contradiction.
            - reflexivity.
          }
          {
            eauto 2.
          }
          {
            eauto 2.
          }
          {
            eauto 2.
          }
          {
            splits.
            - splits; intro; invert_low_event; contradiction.
            - intro; invert_low_event; contradiction.
          }
          {
            repeat invert_wf_aux.
            assert_wf_type.
            invert_wf_type.
            repeat specialize_gen.
            invert_wt_cmd.
            invert_lifted.
            rewrite_inj.
            eapply TaintEqEventSet.
            - eauto 2.
            - destruct ε as [ℓ' ι'].
              destruct_prod_join_flowsto.
              eapply val_taint_eq_mon with (ℓ1 := ℓ') (ι1 := ι'); eauto 2.
              assert (val_taint_eq Φ (SecType σ (ℓ', ι')) u v2) by eauto 2 using eval_taint_eq.
              invert_val_taint_eq; eauto 2.
              assert (left Ψ loc = Some loc').
              {
                assert (high ℓ s1 (update_heap l n3 (ValLoc loc) w1) loc).
                {
                  eauto 3.
                }
                eapply filter_true; eauto 2.
              }
              eauto 2.
          }
          {
            eauto 2.
          }

          assert (wf_taint_bijection ℓ Ψ s1 (update_heap l n3 u w1)).
          {
            eapply taint_eq_update_bijection1; eauto 2.
            intros; subst.
            repeat invert_wf_aux.
            repeat specialize_gen.
            invert_wt_cmd.
            eapply eval_implies_reach; eauto 2.
          }

          repeat invert_wf_aux.
          repeat specialize_gen.
          invert_wt_cmd.
          invert_lifted.
          rewrite_inj.
          assert (val_taint_eq Φ (SecType σ (ℓ1, ι0)) u v2).
          {
            destruct ε as [ℓ'' ι''].
            destruct_prod_join_flowsto.
            eapply val_taint_eq_mon; eauto.
            eapply LHLatProp.flowsto_refl.
          }

          repeat invert_wf_aux.
          repeat specialize_gen.
          invert_wt_cmd.
          invert_lifted.
          rewrite_inj.
          splits~.

          {
            repeat invert_wf_aux.
            repeat specialize_gen.
            invert_wt_cmd.
            invert_lifted.
            rewrite_inj.
            eapply wf_bijection_update_heap2; try solve[intros; subst; eauto 3].
            - intros; contradiction.
            - eapply val_low_eq_mon.
              + repeat invert_state_low_eq.
                eauto 3.
              + repeat destruct_prod_join_flowsto.
                eauto.
            - intros; subst.
              assert (exists loc, v0 = ValLoc loc) by eauto 2.
              super_destruct'; subst.
              eexists; splits~.
              intros.
              destruct ε as [ℓ'' ι''].
              repeat destruct_join_flowsto.
              assert (ℓ_x0 ⊔ ℓ'' ⊑ ℓ1) by eauto 2.
              destruct_join_flowsto.
              assert (ℓ'' ⊑ ℓ) by eauto 3.
              assert_wf_type.
              invert_wf_type.
              invert_wf_type.
              assert (exists x, memory_lookup m2 x = Some (ValLoc loc) /\ e0 = Var x) by eauto 2.
              super_destruct'; subst.
              invert_var_typing.
              assert_wf_type.
              invert_wf_type.
              eauto 2.
            - intros; subst.
              assert (exists loc, u = ValLoc loc) by eauto 2.
              super_destruct'; subst.
              eexists; splits~.
              intros.
              destruct ε as [ℓ'' ι''].
              repeat destruct_join_flowsto.
              assert (ℓ_x0 ⊔ ℓ'' ⊑ ℓ1) by eauto 2.
              destruct_join_flowsto.
              assert (ℓ'' ⊑ ℓ) by eauto 3.
              assert_wf_type.
              invert_wf_type.
              invert_wf_type.
              assert (exists x, memory_lookup s1 x = Some (ValLoc loc) /\ e0 = Var x) by eauto 2.
              super_destruct'; subst.
              invert_var_typing.
              assert_wf_type.
              invert_wf_type.
              eauto 2.
          }
          {
            eapply wf_taint_bijection_update_heap2 with (Φ := Φ) (m1 := s1) (m2 := s2'')
            ; eauto 2.
            - eapply low_gc_trans_preserves_wf_taint_bijection; eauto 2.
            - rewrite <- (compose_id_right Φ).
              eapply taint_eq_heap_domain_eq_trans; eauto 2.
            - rewrite <- (compose_id_right Φ).
              eapply taint_eq_reach_trans; eauto 2.
            - intros; subst.
              assert (exists loc, u = ValLoc loc) by eauto 2.
              super_destruct'; subst.
              eexists; splits; eauto 2.
            - intros; subst.
              assert (exists loc, v2 = ValLoc loc) by eauto 2.
              super_destruct'; subst.
              eexists; splits; eauto 2.
            - intros; subst.
              eauto 2.
            - intros; subst.
              eauto 2.
          }
          { eapply taint_eq_mem_update_heap; eauto 2. }
          { eapply taint_eq_reach_update_heap; eauto 2.
            - rewrite <- (compose_id_right Φ).
              eapply taint_eq_reach_trans; eauto 2.
            - rewrite <- (compose_id_right Φ).
              eapply taint_eq_heap_domain_eq_trans; eauto 2.
            - intros; subst.
              assert (exists loc, u = ValLoc loc) by eauto 2.
              super_destruct'; subst.
              eexists; splits; eauto 2.
            - intros; subst.
              assert (exists loc, v2 = ValLoc loc) by eauto 2.
              super_destruct'; subst.
              eexists; splits; eauto 2.
            - intros; subst.
              eauto 2.
            - intros; subst.
              eauto 2.
            - eapply low_gc_trans_preserves_wf_taint_bijection; eauto 2.
            - rewrite <- (compose_id_right Φ).
              eapply taint_eq_reach_trans; eauto 2.
          }
          { assert (Σ2 l = Some (SecType σ0 (ℓ1, ι0))) by eauto 2.
            rewrite_inj.
            eapply taint_eq_heap_update_heap; eauto 2.
            + intros; subst.
              eauto 2.
            + intros; subst.
              eauto 2. }
          { splits.
            - unfolds.
              intros.
              repeat rewrite -> size_update_heap.
              rewrite -> H18 by eauto 2.
              eauto 2.
            - repeat invert_wf_aux.
              eapply taint_eq_heap_update_domain_eq_update_heap with (Φ := Φ) (Σ1 := Σ2) (Σ2 := Σ3'); eauto 2.
              + rewrite <- (compose_id_right Φ).
                eapply taint_eq_heap_domain_eq_trans; eauto 2.
              + eapply low_gc_trans_preserves_wf_taint_bijection; eauto 2.
              + rewrite <- (compose_id_right Φ).
                eapply taint_eq_heap_domain_eq_trans; eauto 2.
              + rewrite <- (compose_id_right Φ).
                eapply taint_eq_reach_trans; eauto 2.
              + intros; subst.
                assert (exists loc, u = ValLoc loc) by eauto 3.
                super_destruct'; subst.
                eexists; eauto 3.
              + intros; subst.
                assert (exists loc, v2 = ValLoc loc) by eauto 3.
                super_destruct'; subst.
                eexists; eauto 3.
              + intros; subst; eauto 2.
              + intros; subst; eauto 3.
            - unfolds.
              intros.
              assert (left Φ loc1 = Some loc2).
              {
                eapply filtered_bijection_is_subset.
                - eapply high_dec.
                - eauto 2.
                - eauto 2.
              }
              eauto. }
          }
    (* Get *)
    {
      invert_taint_eq; invert_taint_eq_cmd.
      invert_bridge_step_with_steps 0.
      - invert_low_event_step.
        assert (wellformed_aux Γ Σ1' ⟨c2, pc1', m2, h2, t2⟩ pc_end) by eauto 2.
        assert (wellformed_aux Γ Σ3' ⟨c2', pc2'', s2'', w2'', g2''⟩ pc_end) by eauto 2.
        invert_event_step; try solve[invert_low_event].
        invert_low_event.
        invert_sem_step.
        rewrite_inj.
        _apply get_bridge_properties in *.
        super_destruct'; subst.
        invert_bridge_step_with_steps 0.
        + invert_low_event_step.
          invert_event_step; try solve[invert_low_event].
          invert_sem_step.
          rewrite_inj.
          clear H29.
          rewrite_inj.
          assert (wellformed_aux Γ Σ3' ⟨GetArr i i0 e, pc2'', s1', w2'', g2'' - 1⟩ pc_end) by eauto 2.
          assert (exists l3, right Φ l2 = Some l3 /\ memory_lookup s1 i0 = Some (ValLoc l3)).
          {
            repeat invert_wf_aux.
            repeat specialize_gen.
            invert_wt_cmd.
            invert_lifted.
            rewrite_inj.
            assert (expr_has_type Γ (Var i0) (SecType (Array (SecType σ ε) ℓ2) ε_y)) by eauto 2.
            destruct ε_y as [ℓ_y ι_y].
            assert (ℓ_y ⊑ ℓ_x0).
            {
              destruct ε.
              destruct_prod_join_flowsto.
              eauto 2.
            }
            assert (taint_eq_mem (inverse Φ) Γ s1' s1) by eauto 2.
            assert (eval s1' (Var i0) = Some (ValLoc l2)) by eauto 2.
            remember_simple (eval_taint_eq_possibilistic H3 H27 H20 H5 H66).
            super_destruct'; subst.
            invert_val_taint_eq.
            - destruct Φ; eexists; splits*.
            - assert_wf_type.
              invert_wf_type.
          }
          super_destruct'; subst.
          assert (eval s1 e = Some (ValNum n1)).
          {
            repeat invert_wf_aux.
            repeat specialize_gen.
            invert_wt_cmd.
            invert_lifted.
            rewrite_inj.
            destruct ε_idx as [ℓ_idx ι_idx].
            assert (taint_eq_mem (inverse Φ) Γ s1' s1) by eauto 2.
            remember_simple (eval_taint_eq_possibilistic H8 H29 H24 H3 H49).
            super_destruct'; subst.
            invert_val_taint_eq; eauto 2.
            assert_wf_type.
            invert_wf_type.
            destruct_prod_join_flowsto.
            assert (LH.flowsto • ∘) as H' by eauto 2.
            inverts H'.
          }
          invert_wf_aux; repeat specialize_gen; invert_wt_cmd.
          invert_lifted; rewrite_inj.
          assert (exists u ℓ μ, heap_lookup l3 w1 = Some (ℓ, μ) /\ lookup μ n1 = Some u /\ val_taint_eq Φ (SecType σ (ℓ_x0, ι0)) u v1 /\ length_of l3 w1 = Some length0).
          {
            remember_simple (low_gc_trans_preserves_taint_eq H5 H7 H10).
            unfold taint_eq; super_destruct'; subst.
            assert (taint_eq_heap ℓ Φ Σ2 Σ3' s1 w1 s1' w2'').
            {
              rewrite <- (compose_id_right Φ).
              eapply taint_eq_heap_trans.
              - eapply gc_trans_preserves_taint_eq_reach; eauto 2.
              - eauto 2.
              - repeat invert_wf_aux; eauto 2.
              - eauto 2.
              - eapply low_gc_trans_preserves_taint_eq_heap; eauto 2.
              - eapply low_gc_trans_preserves_taint_eq_heap_domain_eq; eauto 2.
            }
            assert (left Φ l3 = Some l2) by (destruct Φ; eauto 2).
            assert (high ℓ s1 w1 l3) by eauto 3.
            assert (exists ℓ μ, heap_lookup l3 w1 = Some (ℓ, μ)).
            {
              repeat invert_wf_aux.
              destruct_high; eauto 3.
            }
            assert (high ℓ s1' w2'' l2) by eauto 3.
            super_destruct'; subst.
            assert (Σ3' l2 = Some (SecType σ ε)) by (repeat invert_wf_aux; eauto 2).
            assert (Σ2 l3 = Some (SecType σ ε)) by (repeat invert_wf_aux; eauto 2).
            remember_simple (H25 l3 l2 _ _ _ _ _ H26 H32 H46 H33 H54 H56 H47).
            super_destruct'; subst.
            assert (exists v1, lookup μ1 n1 = Some v1) by firstorder 2.
            super_destruct'; subst.
            exists v2.
            assert (val_taint_eq Φ (SecType σ ε) v2 v1) by eauto 4.
            exists ℓ1 μ1.
            splits*.
            - destruct ε, ε_y; destruct_prod_join_flowsto.
              eapply val_taint_eq_mon with (ℓ1 := t0) (ι1 := t1); eauto 2.
            - congruence.
          }
          super_destruct'; subst.
          exists (GetEvent ℓ_x0 i i0 u) 0.
          
          remember_simple (filter_bijection
                             (low ℓ Γ Σ1' (m1 [i → v0]) h2)
                             (low_dec ℓ Γ Σ1' (m1 [i → v0]) h2) φ).
          super_destruct'; subst.
          exists ψ.
          remember_simple (filter_bijection
                             (high ℓ (extend_memory i u s1) w1)
                             (high_dec ℓ (extend_memory i u s1)
                                        w1) Φ).
          super_destruct'; subst.
          rename ψ0 into Ψ.
          exists Ψ.
          exists (extend_memory i u s1).
          exists w1 Σ2.
          
          assert (n0 = n1).
          {
            invert_state_low_eq.
            repeat invert_wf_aux.
            repeat specialize_gen.
            invert_wt_cmd.
            invert_lifted.
            rewrite_inj.
            assert (val_low_eq ℓ (SecType Int ε_idx) (ValNum n0) (ValNum n1) φ)
              by eauto 2.
            invert_val_low_eq.
            - destruct_prod_join_flowsto.
              destruct ε_y0 as [ℓ' ι'].
              assert (ℓ2 ⊑ ℓ') by eauto 2.
              assert (~ ℓ' ⊑ ℓ) by eauto 2.
              destruct_prod_join_flowsto.
              destruct ε0 as [ℓ'' ι''].
              assert (ℓ' ⊑ ℓ_x0) by eauto 2.
              assert (~ ℓ_x0 ⊑ ℓ) by eauto 2.
              contradiction.
            - reflexivity.
          }
          subst.
          assert (val_low_eq ℓ (SecType σ ε) v0 u φ).
          {
            assert (val_low_eq ℓ (SecType (Array (SecType σ ε) ℓ2) ε_y) (ValLoc l1)
                               (ValLoc l3) φ).
            {
              invert_state_low_eq; eauto 2.
            }
            invert_val_low_eq.
            + destruct ε; destruct_prod_join_flowsto.
              assert (ℓ4 ⊑ ℓ_x0) by eauto 2.
              assert (ℓ4 ⊑ ℓ) by eauto 2.
              contradiction.
            + assert (Σ1' l1 = Some (SecType σ ε)) by (repeat invert_wf_aux; eauto 2).
              assert (Σ2 l3 = Some (SecType σ ε)) by (repeat invert_wf_aux; eauto 2).
              assert (low ℓ Γ Σ1' m1 h2 l1) by eauto 2.
              assert (low ℓ Γ Σ2 s1 w1 l3).
              {
                eapply low_iff; destruct φ; eauto 2.
              }
              invert_state_low_eq.
              assert (heapval_low_eq ℓ (SecType σ ε) l1 l3 m1 s1 h2 w1 φ) by eauto 2.
              invert_heapval_low_eq.
              assert (reach m1 h2 l1) by eauto 2.
              assert (reach s1 w1 l3) by eauto 2.
              rewrite_inj.
              eauto 2.
          }
          
          assert (state_low_eq ℓ ψ (m1 [i → v0]) h2
                               (s1 [i → u]) w1 Γ Σ1' Σ2).
          {
            repeat destruct_prod_join_flowsto.
            repeat invert_wf_aux.
            eapply state_low_eq_extend_memory; eauto 2.
            - intros; subst.
              assert (exists loc, v0 = ValLoc loc) by eauto 3.
              super_destruct; subst.
              exists loc.
              splits~.
              intros.
              destruct ε_y as [ℓ_y ι_y].
              assert (ℓ_y ⊑ ℓ_x0) by eauto 2.
              assert (ℓ_y ⊑ ℓ) by eauto 2.
              destruct ε as [ℓ' ι'].
              assert_wf_type.
              invert_wf_type.
              invert_wf_type.
              assert (ℓ' ⊑ ℓ_x0) by eauto 2.
              assert (ℓ' ⊑ ℓ) by eauto 2.
              eapply LowReachHeap; eauto 2.
            - intros; subst.
              assert (exists loc, u = ValLoc loc) by eauto 3.
              super_destruct; subst.
              exists loc.
              splits~.
              intros.
              destruct ε_y as [ℓ_y ι_y].
              assert (ℓ_y ⊑ ℓ_x0) by eauto 2.
              assert (ℓ_y ⊑ ℓ) by eauto 2.
              destruct ε as [ℓ' ι'].
              assert_wf_type.
              invert_wf_type.
              invert_wf_type.
              assert (ℓ' ⊑ ℓ_x0) by eauto 2.
              assert (ℓ' ⊑ ℓ) by eauto 2.
              eapply LowReachHeap; eauto 2.
            - intros; subst; eauto 3.
            - intros; subst; eauto 3.
            - eapply wf_tenv_extend.
              + eauto.
              + eauto.
              + intros; subst; eauto.
              + intros; subst; eauto.
          }

          assert (wf_bijection ℓ ψ Γ Σ1' (m1 [i → v0]) h2).
          {
            repeat invert_wf_aux.
            eapply wf_bijection_extend_mem1; intros; subst; eauto 3.
            - subst.
              eauto 3.
            - subst.
              assert (exists loc, v0 = ValLoc loc) by eauto 3.
              super_destruct; subst.
              exists loc.
              splits~.
              intros.
              assert_wf_type.
              invert_wf_type.
              invert_wf_type.
              assert (l_ref0 ⊔ l_ref ⊑ ℓ_x0) by eauto 2.
              destruct_join_flowsto.
              assert (l_ref ⊑ ℓ) by eauto 2.
              assert (low_reach ℓ Γ Σ1' m1 h2 l1) by eauto 2.
              eapply LowReachHeap; eauto 2.
          }

          assert (wf_taint_bijection ℓ Ψ (s1 [i → u]) w1).
          {
            eapply wf_taint_bijection_extend_mem1; eauto 2.
            intros; subst.
            eapply reach_heap with (loc0 := l3); eauto 2.
          }

          assert (taint_eq ℓ Ψ Γ Σ2 Σ3' Stop Stop
                           (s1 [i → u]) w1
                           (s1' [i → v1]) w2'').
          {
            remember_simple (low_gc_trans_preserves_taint_eq H5 H7 H10).
            unfold taint_eq in *; super_destruct'.
            repeat invert_wf_aux.
            splits~.
            - eapply taint_eq_mem_extend; eauto 2.
            - eapply taint_eq_reach_extend_mem; eauto 2.
              + rewrite <- (compose_id_right Φ).
                eapply taint_eq_reach_trans; eauto 2.
              + rewrite <- (compose_id_right Φ).
                eapply taint_eq_heap_trans; eauto 2.
              + eapply low_gc_trans_preserves_wf_taint_bijection; eauto 2.
              + intros; subst.
                rewrite_inj.
                eapply reach_heap; eauto 2.
              + intros; subst.
                rewrite_inj.
                eapply reach_heap; eauto 2.
            - eapply taint_eq_heap_extend_mem; eauto 2.
              + rewrite <- (compose_id_right Φ).
                eapply taint_eq_heap_trans; eauto 2.
              + intros; subst; eauto.
              + intros; subst; eauto.
              + intros; subst.
                assert (exists loc, u = ValLoc loc) by eauto.
                super_destruct; subst.
                exists loc.
                splits~.
                rewrite_inj.
                eapply reach_heap; eauto 2.
              + intros; subst.
                assert (exists loc, v1 = ValLoc loc) by eauto.
                super_destruct; subst.
                exists loc.
                splits~.
                rewrite_inj.
                eapply reach_heap; eauto 2.
              + eapply low_gc_trans_preserves_wf_taint_bijection; eauto 2.
            - eapply taint_eq_heap_size_trans; eauto 2.
            - eapply taint_eq_heap_domain_eq_extend_mem; eauto 2.
              + rewrite <- (compose_id_right Φ).
                eapply taint_eq_heap_domain_eq_trans; eauto 2.
              + eapply low_gc_trans_preserves_wf_taint_bijection; eauto 2.
              + rewrite <- (compose_id_right Φ).
                eapply taint_eq_heap_trans; eauto 2.
              + rewrite <- (compose_id_right Φ).
                eapply taint_eq_reach_trans; eauto 2.
              + eapply low_gc_trans_preserves_wf_taint_bijection; eauto 2.
              + intros; subst.
                assert (exists loc, u = ValLoc loc) by eauto.
                super_destruct; subst.
                exists loc.
                splits~.
                rewrite_inj.
                eapply reach_heap; eauto 2.
              + intros; subst; eauto 3.
              + intros; subst.
                assert (exists loc, v1 = ValLoc loc) by eauto.
                super_destruct; subst.
                exists loc.
                splits~.
                rewrite_inj.
                eapply reach_heap; eauto 2.
              + intros; subst; eauto 3.
            - eapply taint_eq_stenv_extend_mem; eauto 2.
          }
          
          splits~.
          * constructor.
            splits; eauto 2.
            constructor.
            eapply event_sem_step_get; eauto 2.
          * unfolds.
            splits~.
            { splits*. }
            { intros.
              invert_low_event.
              destruct ε as [ℓ_arr ι_arr].
              destruct ε_y as [ℓ_y ι_y].
              assert (ℓ_arr ⊔ ℓ_y ⊑ ℓ_x0) by eauto 2.
              destruct_join_flowsto.
              assert (ℓ_arr ⊑ ℓ) by eauto 2.
              constructor; eauto 2.
              invert_val_low_eq; contradiction || eauto 2.
              assert (low ℓ Γ Σ1' (m1 [i → ValLoc l0]) h2 l0).
              {
                eauto 2.
                assert (wf_type bot (SecType (Array τ ℓ_p) (ℓ_x0, ι0))) as H' by eauto 2.
                invert_wf_type.
                eapply LowReachable.
                eauto 3.
              }
              eauto 3. }
          * eapply TaintEqEventGet; eauto 2.
            invert_val_taint_eq; eauto 2.
            assert (high ℓ (s1 [i → ValLoc loc]) w1 loc) by eauto 3.
            assert (left Ψ loc = Some loc') by eauto 2.
            eauto 2.
          * splits~.
            {
              repeat invert_wf_aux.
              repeat destruct_prod_join_flowsto.
              eapply wf_bijection_extend_mem2; try solve[intros; subst; eauto 3].
              intros; subst.
              assert (exists loc, u = ValLoc loc) by eauto 3.
              super_destruct; subst.
              exists loc.
              splits~.
              intros.
              assert_wf_type.
              do 2 invert_wf_type.
              assert (l_ref ⊑ ℓ_x0) by eauto 2.
              assert (l_ref ⊑ ℓ) by eauto 2.
              assert (l_ref0 ⊑ ℓ_x0) by eauto 2.
              assert (l_ref0 ⊑ ℓ) by eauto 2.
              rewrite_inj.
              eapply LowReachHeap; eauto 2.
            }
            {
              remember_simple (low_gc_trans_preserves_taint_eq H5 H7 H10).
              repeat invert_wf_aux.
              unfold taint_eq in *; super_destruct'.
              eapply wf_taint_bijection_extend_mem2 with (m := s1) (h := w1) (Φ := Φ); eauto 2.
              - rewrite <- (compose_id_right Φ).
                eapply taint_eq_reach_trans.
                + eauto.
                + eapply gc_trans_preserves_taint_eq_reach; eauto.
              - rewrite <- (compose_id_right Φ).
                eapply taint_eq_heap_trans; eauto 2.
              - rewrite <- (compose_id_right Φ).
                eapply taint_eq_heap_domain_eq_trans; eauto 2.
              - eapply low_gc_trans_preserves_wf_taint_bijection; eauto 2.
              - intros; subst.
                eauto.
              - intros; subst.
                eauto.
              - intros; subst.
                assert (exists loc, v1 = ValLoc loc) by eauto 3.
                super_destruct'; subst.
                exists loc.
                splits~.
                eapply reach_heap; eauto 2.
            }
        + invert_high_event_step.
          invert_event_step.
          invert_sem_step; rewrite_inj.
          assert (low_event ℓ (GetEvent ℓ_x0 i i0 v1)) by eauto 2.
          contradiction.
      - unfold is_stop_config, cmd_of in *; subst.
        invert_high_event_step.
        assert (wellformed_aux Γ Σ1' ⟨Stop, pc1', m2, h2, t2⟩ pc_end) by eauto 2.
        assert (wellformed_aux Γ Σ3' ⟨c2', pc2'', s2'', w2'', g2''⟩ pc_end) by eauto 2.
        invert_event_step.
        assert (~ ℓ_x ⊑ ℓ).
        {
          intro.
          assert (low_event ℓ (GetEvent ℓ_x i i0 v)) by eauto 2.
          contradiction.
        }
        invert_sem_step.
        rewrite_inj.
        _apply get_bridge_properties in *.
        super_destruct'; subst.
        invert_bridge_step_with_steps 0.
        + invert_low_event_step.
          invert_event_step; invert_low_event.
          rewrite_inj.
          contradiction.
        + invert_high_event_step.
          invert_event_step.
          invert_sem_step.
          rewrite_inj.
          clear H31.
          rewrite_inj.
          assert (wellformed_aux Γ Σ3' ⟨GetArr i i0 e, pc2'', s1', w2'', g2'' - 1⟩ pc_end) by eauto 2.
          assert (exists l3, right Φ l2 = Some l3 /\ memory_lookup s1 i0 = Some (ValLoc l3)).
          {
            repeat invert_wf_aux.
            repeat specialize_gen.
            invert_wt_cmd.
            invert_lifted.
            rewrite_inj.
            assert (expr_has_type Γ (Var i0) (SecType (Array (SecType σ ε) ℓ2) ε_y)) by eauto 2.
            destruct ε_y as [ℓ_y ι_y].
            assert (ℓ_y ⊑ ℓ_x0).
            {
              destruct ε.
              destruct_prod_join_flowsto.
              eauto 2.
            }
            assert (taint_eq_mem (inverse Φ) Γ s1' s1) by eauto 2.
            assert (eval s1' (Var i0) = Some (ValLoc l2)) by eauto 2.
            remember_simple (eval_taint_eq_possibilistic H3 H29 H22 H5 H68).
            super_destruct'; subst.
            invert_val_taint_eq.
            - destruct Φ; eexists; splits*.
            - assert_wf_type.
              invert_wf_type.
          }
          super_destruct'; subst.
          assert (eval s1 e = Some (ValNum n1)).
          {
            repeat invert_wf_aux.
            repeat specialize_gen.
            invert_wt_cmd.
            invert_lifted.
            rewrite_inj.
            destruct ε_idx as [ℓ_idx ι_idx].
            assert (taint_eq_mem (inverse Φ) Γ s1' s1) by eauto 2.
            remember_simple (eval_taint_eq_possibilistic H8 H31 H26 H3 H51).
            super_destruct'; subst.
            invert_val_taint_eq; eauto 2.
            assert_wf_type.
            invert_wf_type.
            destruct_prod_join_flowsto.
            assert (LH.flowsto • ∘) as H' by eauto 2.
            inverts H'.
          }
          invert_wf_aux; repeat specialize_gen; invert_wt_cmd.
          invert_lifted; rewrite_inj.
          assert (exists u ℓ μ, heap_lookup l3 w1 = Some (ℓ, μ) /\ lookup μ n1 = Some u /\ val_taint_eq Φ (SecType σ (ℓ_x0, ι0)) u v1 /\ length_of l3 w1 = Some length0).
          {
            remember_simple (low_gc_trans_preserves_taint_eq H5 H7 H21).
            unfold taint_eq; super_destruct'; subst.
            assert (taint_eq_heap ℓ Φ Σ2 Σ3' s1 w1 s1' w2'').
            {
              rewrite <- (compose_id_right Φ).
              eapply taint_eq_heap_trans.
              - eapply gc_trans_preserves_taint_eq_reach; eauto 2.
              - eauto 2.
              - repeat invert_wf_aux; eauto 2.
              - eauto 2.
              - eapply low_gc_trans_preserves_taint_eq_heap; eauto 2.
              - eapply low_gc_trans_preserves_taint_eq_heap_domain_eq; eauto 2.
            }
            assert (left Φ l3 = Some l2) by (destruct Φ; eauto 2).
            assert (high ℓ s1 w1 l3) by eauto 3.
            assert (exists ℓ μ, heap_lookup l3 w1 = Some (ℓ, μ)).
            {
              repeat invert_wf_aux.
              destruct_high; eauto 3.
            }
            assert (high ℓ s1' w2'' l2) by eauto 3.
            super_destruct'; subst.
            assert (Σ3' l2 = Some (SecType σ ε)) by (repeat invert_wf_aux; eauto 2).
            assert (Σ2 l3 = Some (SecType σ ε)) by (repeat invert_wf_aux; eauto 2).
            remember_simple (H27 l3 l2 _ _ _ _ _ H28 H34 H48 H40 H56 H58 H49).
            super_destruct'; subst.
            assert (exists v1, lookup μ1 n1 = Some v1) by firstorder 2.
            super_destruct'; subst.
            exists v2.
            exists ℓ1 μ1.
            assert (val_taint_eq Φ (SecType σ ε) v2 v1) by eauto 4.
            splits*.
            - destruct ε, ε_y; destruct_prod_join_flowsto.
              eapply val_taint_eq_mon; eauto 2.
            - congruence.
          }
          super_destruct'; subst.
          exists (GetEvent ℓ_x0 i i0 u) 0.
          
          remember_simple (filter_bijection
                             (low ℓ Γ Σ1' (m1 [i → v0]) h2)
                             (low_dec ℓ Γ Σ1' (m1 [i → v0]) h2) φ).
          super_destruct'; subst.
          exists ψ.
          remember_simple (filter_bijection
                             (high ℓ (extend_memory i u s1) w1)
                             (high_dec ℓ (extend_memory i u s1)
                                        w1) Φ).
          super_destruct'; subst.
          rename ψ0 into Ψ.
          exists Ψ.
          exists (extend_memory i u s1).
          exists w1 Σ2.

          assert (state_low_eq ℓ ψ (m1 [i → v0]) h2
                               (s1 [i → u]) w1 Γ Σ1' Σ2).
          {
            repeat destruct_prod_join_flowsto.
            repeat invert_wf_aux.
            eapply state_low_eq_extend_memory; eauto 2.
            - destruct σ.
              + assert (exists n, v0 = ValNum n) by eauto 2.
                assert (exists n, u = ValNum n) by eauto.
                super_destruct; subst; eauto 2.
              + assert (exists loc, v0 = ValLoc loc) by eauto 2.
                assert (exists loc, u = ValLoc loc) by eauto.
                super_destruct; subst; eauto 2.
            - intros; subst.
              assert (exists loc, v0 = ValLoc loc) by eauto 3.
              super_destruct; subst.
              exists loc.
              splits~.
              intros.
              contradiction.
            - intros; subst.
              assert (exists loc, u = ValLoc loc) by eauto 3.
              super_destruct; subst.
              exists loc.
              splits~.
              intros.
              contradiction.
            - intros; subst; eauto 3.
            - intros; subst; eauto 3.
            - eapply wf_tenv_extend.
              + eauto.
              + eauto.
              + intros; subst; eauto.
              + intros; subst; eauto.
          }

          assert (wf_bijection ℓ ψ Γ Σ1' (m1 [i → v0]) h2).
          {
            repeat invert_wf_aux.
            eapply wf_bijection_extend_mem1; intros; subst; eauto 3.
            - subst; eauto 2.
            - subst.
              assert (exists loc, v0 = ValLoc loc) by eauto 3.
              super_destruct; subst.
              exists loc.
              splits~.
              intros.
              contradiction.
          }
          
          assert (wf_taint_bijection ℓ Ψ (s1 [i → u]) w1).
          {
            rewrite_inj.
            eapply wf_taint_bijection_extend_mem1; eauto 2.
            intros; subst.
            eapply reach_heap with (loc0 := l3); eauto 2.
          }

          assert (taint_eq ℓ Ψ Γ Σ2 Σ3' Stop Stop
                           (s1 [i → u]) w1
                           (s1' [i → v1]) w2'').
          {
            remember_simple (low_gc_trans_preserves_taint_eq H5 H7 H21).
            repeat invert_wf_aux.
            assert (taint_eq_heap ℓ (bijection_compose Φ (identity_bijection loc)) Σ2 Σ3' s1 w1 s1' w2'').
            {
              unfold taint_eq in *; super_destruct'.
              eapply taint_eq_heap_trans; eauto 2.
            }
            splits~.
            - eapply taint_eq_mem_extend; eauto 2.
            - eapply taint_eq_reach_extend_mem; eauto 2.
              + rewrite <- (compose_id_right Φ).
                eapply taint_eq_reach_trans; eauto 2.
              + rewrite <- (compose_id_right Φ); eauto 2.
              + eapply low_gc_trans_preserves_wf_taint_bijection; eauto 2.
              + intros; subst.
                rewrite_inj.
                eapply reach_heap; eauto 2.
              + intros; subst.
                rewrite_inj.
                eapply reach_heap; eauto 2.
            - eapply taint_eq_heap_extend_mem; eauto 2.
              + intros; subst; eauto.
              + intros; subst; eauto.
              + intros; subst.
                assert (exists loc, u = ValLoc loc) by eauto.
                super_destruct; subst.
                exists loc.
                splits~.
                rewrite_inj.
                eapply reach_heap; eauto 2.
              + intros; subst.
                assert (exists loc, v1 = ValLoc loc) by eauto.
                super_destruct; subst.
                exists loc.
                splits~.
                rewrite_inj.
                eapply reach_heap; eauto 2.
              + rewrite -> (compose_id_right Φ).
                eapply low_gc_trans_preserves_wf_taint_bijection; eauto 2.
              + rewrite -> (compose_id_right Φ).
                eapply low_gc_trans_preserves_wf_taint_bijection; eauto 2.
              + rewrite -> (compose_id_right Φ); eauto 2.
            - unfold taint_eq in *; super_destruct'.
              eapply taint_eq_heap_size_trans; eauto 2.
            - eapply taint_eq_heap_domain_eq_extend_mem; eauto 2.
              + rewrite <- (compose_id_right Φ).
                eapply taint_eq_heap_domain_eq_trans; eauto 2.
              + eapply low_gc_trans_preserves_wf_taint_bijection; eauto 2.
              + rewrite <- (compose_id_right Φ).
                eauto 2.
              + rewrite <- (compose_id_right Φ).
                eapply taint_eq_reach_trans; eauto 2.
              + eapply low_gc_trans_preserves_wf_taint_bijection; eauto 2.
              + intros; subst.
                assert (exists loc, u = ValLoc loc) by eauto.
                super_destruct; subst.
                exists loc.
                splits~.
                rewrite_inj.
                eapply reach_heap; eauto 2.
              + intros; subst; eauto 3.
              + intros; subst.
                assert (exists loc, v1 = ValLoc loc) by eauto.
                super_destruct; subst.
                exists loc.
                splits~.
                rewrite_inj.
                eapply reach_heap; eauto 2.
              + intros; subst; eauto 3.
            - eapply taint_eq_stenv_extend_mem; eauto 2.
          }
          
          splits~.
          * eapply bridge_stop_num.
            { splits~.
              - constructor.
                constructors; eauto 2.
              - intro; invert_low_event; contradiction.
            }
            { reflexivity. }
          * unfolds.
            splits.
            { splits; intro; invert_low_event; contradiction. }
            { intro; invert_low_event; contradiction. }
          * eapply TaintEqEventGet; eauto 2.
            invert_val_taint_eq; eauto 2.
            assert (high ℓ (s1 [i → ValLoc loc])
                         w1 loc) by eauto 3.
            assert (left Ψ loc = Some loc') by eauto 2.
            eauto 2.
          * splits~.
            {
              - repeat invert_wf_aux.
                repeat destruct_prod_join_flowsto.
                eapply wf_bijection_extend_mem2; try solve[intros; subst; eauto 3].
                {
                  destruct σ.
                  - assert (exists n, v0 = ValNum n) by eauto 2.
                    assert (exists n, u = ValNum n) by eauto.
                    super_destruct'; subst; eauto 2.
                  - assert (exists loc, v0 = ValLoc loc) by eauto 2.
                    assert (exists loc, u = ValLoc loc) by eauto.
                    super_destruct'; subst; eauto 2.
                }
            {
              intros; subst.
              assert (exists loc, u = ValLoc loc) by eauto 3.
              super_destruct; subst.
              exists loc.
              splits~.
              intros.
              contradiction. }
            }
            {
              remember_simple (low_gc_trans_preserves_taint_eq H5 H7 H21).
              repeat invert_wf_aux.
              eapply wf_taint_bijection_extend_mem2 with (m := s1) (h := w1) (Φ := Φ); eauto 2.
              - rewrite <- (compose_id_right Φ).
                eapply taint_eq_reach_trans.
                + eauto.
                + eapply gc_trans_preserves_taint_eq_reach; eauto.
              - rewrite <- (compose_id_right Φ).
                unfold taint_eq in *; super_destruct'.
                eapply taint_eq_heap_trans.
                + eapply H5.
                + eauto 2.
                + eauto 2.
                + eauto 2.
                + eauto 2.
                + eauto 2.
              - rewrite <- (compose_id_right Φ).
                eapply taint_eq_heap_domain_eq_trans; eauto 2.
              - unfold taint_eq in *; super_destruct'; eauto 2.
              - idtac.
                unfold taint_eq in *; super_destruct'; eauto 2.
              - eapply low_gc_trans_preserves_wf_taint_bijection; eauto 2.
              - intros; subst.
                eauto.
              - intros; subst.
                eauto.
              - intros; subst.
                assert (exists loc, v1 = ValLoc loc) by eauto 3.
                super_destruct'; subst.
                exists loc.
                splits~.
                eapply reach_heap; eauto 2.
            }
    }
    (* Time *)
    {
      invert_taint_eq; invert_taint_eq_cmd.
      invert_bridge_step_with_steps 0.
      - invert_low_event_step.
        _apply time_bridge_properties in *.
        super_destruct'; subst.
        assert (wellformed_aux Γ Σ3 ⟨TIME (i), pc, s1', h', g2'' - 1⟩ pc_end) by eauto 2.
        assert (wellformed_aux Γ Σ3' ⟨Stop, pc2'', s2'', w2'', g2''⟩ pc_end) by eauto 2.
        assert (wellformed_aux Γ Σ1' ⟨c2, pc1', m2, h2, t2⟩ pc_end) by eauto 2.
        invert_event_step; invert_low_event.
        invert_bridge_step.
        + invert_low_event_step.
          invert_event_step; invert_low_event.
          do 2 invert_sem_step; rewrite_inj.
          clear H29.
          exists (TimeEvent ℓ1 i t).
          exists 0.
          remember_simple (filter_bijection (low ℓ Γ Σ1' (extend_memory i (ValNum t) m1) h2) (low_dec ℓ Γ Σ1' (extend_memory i (ValNum t) m1) h2) φ).
          super_destruct'; subst.
          exists ψ.

          remember_simple (filter_bijection
                             (high ℓ (extend_memory i (ValNum t) s1) w1)
                             (high_dec ℓ (extend_memory i (ValNum t) s1) w1) Φ).
          super_destruct'; subst.
          rename ψ0 into Ψ.
          exists Ψ.
          exists (extend_memory i (ValNum t) s1).
          exists w1.
          exists Σ2.

          assert (state_low_eq ℓ ψ (m1 [i → ValNum t]) h2
                               (s1 [i → ValNum t]) w1 Γ Σ1' Σ2).
          {
            repeat invert_wf_aux.
            repeat specialize_gen.
            invert_wt_cmd.
            rewrite_inj.
            eapply state_low_eq_extend_memory; eauto 2.
            - intros; discriminate.
            - intros; discriminate.
            - eapply wf_tenv_extend; eauto 2.
              intros; discriminate.
          }

          assert (wf_bijection ℓ ψ Γ Σ1' (m1 [i → ValNum t]) h2).
          {
            repeat invert_wf_aux; repeat specialize_gen; invert_wt_cmd.
            rewrite_inj.
            eapply wf_bijection_extend_mem1; eauto 2.
            intros; discriminate.
          }

          assert (taint_eq ℓ Ψ Γ Σ2 Σ3' Stop Stop
                           (s1 [i → ValNum t]) w1
                           (s1' [i → ValNum (S (g2'' - 1) - 1)]) w2'').
          {
            remember_simple (low_gc_trans_preserves_taint_eq H5 H7 H10).
            unfold taint_eq in *; super_destruct'.
            repeat invert_wf_aux; repeat specialize_gen; invert_wt_cmd;
              rewrite_inj.
            assert (taint_eq_reach Φ s1 w1 s1' w2'').
            {
              rewrite <- (compose_id_right Φ).
              eapply taint_eq_reach_trans; eauto 2.
            }
            assert (taint_eq_heap ℓ Φ Σ2 Σ3' s1 w1 s1' w2'').
            {
              rewrite <- (compose_id_right Φ).
              eapply taint_eq_heap_trans with (h' := w1'); eauto 2.
            }
            assert (wf_taint_bijection ℓ (inverse Φ) s1' w2'').
            {
              eapply low_gc_trans_preserves_wf_taint_bijection with (pc := pc_end); eauto 2.
            }
            splits~.
            - eapply taint_eq_mem_extend; eauto 2.
            - eapply taint_eq_reach_extend_mem; eauto 2.
              + eauto 2.
              + intros; discriminate.
              + intros; discriminate.
            - eapply taint_eq_heap_extend_mem; eauto 2.
              + intros; discriminate.
              + intros; discriminate.
            - eapply taint_eq_heap_size_trans; eauto 2.
            - eapply taint_eq_heap_domain_eq_extend_mem; eauto 2.
              + rewrite <- (compose_id_right Φ).
                eapply taint_eq_heap_domain_eq_trans; eauto 2.
              + intros; discriminate.
              + intros; discriminate.
            - eapply taint_eq_stenv_extend_mem; eauto 2.
          }

          assert (wf_taint_bijection ℓ Ψ (s1 [i → ValNum t]) w1).
          {
            eapply wf_taint_bijection_extend_mem1; eauto 2.
            intros; discriminate.
          }
          
          splits~.
          * constructor.
            splits~.
            constructor.
            eapply event_sem_step_time; eauto 2.
          * splits*.
          * repeat invert_wf_aux; repeat specialize_gen; invert_wt_cmd.
            rewrite_inj.
            eapply TaintEqEventTime; eauto 2.
          * splits~.
            {
              repeat invert_wf_aux; repeat specialize_gen; invert_wt_cmd.
              rewrite_inj.
              eapply wf_bijection_extend_mem2; eauto 2.
              intros; discriminate.
            }
            {
            remember_simple (low_gc_trans_preserves_taint_eq H5 H7 H10).
            repeat invert_wf_aux; repeat specialize_gen; invert_wt_cmd.
            rewrite_inj.            
            unfold taint_eq in *; super_destruct'.
            eapply wf_taint_bijection_extend_mem2 with (m := s1) (h := w1) (Φ := Φ); eauto 2.
            { rewrite <- (compose_id_right Φ).
              eapply taint_eq_reach_trans.
              + eauto.
              + eapply gc_trans_preserves_taint_eq_reach; eauto. }
              { rewrite <- (compose_id_right Φ).
                eapply taint_eq_heap_trans; eauto 2. }
              { rewrite <- (compose_id_right Φ).
                eapply taint_eq_heap_domain_eq_trans; eauto 2. }
              { eapply low_gc_trans_preserves_wf_taint_bijection with (pc := pc_end);
                  eauto 2. }
              { intros; discriminate. }
            }
        + invert_high_event_step.
          invert_event_step.
          do 2 invert_sem_step; rewrite_inj.
          assert (low_event ℓ (TimeEvent ℓ1 i (g2'' - 1))).
          {
            constructor.
            eauto 2.
          }
          contradiction.
      - unfold is_stop_config, cmd_of in *; subst.
        invert_high_event_step.
        _apply time_bridge_properties in *.
        super_destruct'; subst.
        assert (wellformed_aux Γ Σ3 ⟨TIME (i), pc, s1', h', g2'' - 1⟩ pc_end) by eauto 2.
        assert (wellformed_aux Γ Σ3' ⟨Stop, pc2'', s2'', w2'', g2''⟩ pc_end) by eauto 2.
        assert (wellformed_aux Γ Σ1' ⟨Stop, pc1', m2, h2, t2⟩ pc_end) by eauto 2.
        invert_event_step.
        invert_bridge_step.
        + invert_low_event_step.
          invert_event_step.
          rewrite_inj.
          invert_low_event.
          assert (low_event ℓ (TimeEvent ℓ1 i t)) by eauto 2.
          contradiction.
        + invert_high_event_step.
          invert_event_step.
          do 2 invert_sem_step; rewrite_inj.
          clear H30.
          assert (~ ℓ1 ⊑ ℓ).
          {
            intro.
            assert (low_event ℓ (TimeEvent ℓ1 i t)) by eauto 2.
            contradiction.
          }
          exists (TimeEvent ℓ1 i t).
          exists 0.
          remember_simple (filter_bijection (low ℓ Γ Σ1' (extend_memory i (ValNum t) m1) h2) (low_dec ℓ Γ Σ1' (extend_memory i (ValNum t) m1) h2) φ).
          super_destruct'; subst.
          exists ψ.

          remember_simple (filter_bijection
                             (high ℓ (extend_memory i (ValNum t) s1) w1)
                             (high_dec ℓ (extend_memory i (ValNum t) s1) w1) Φ).
          super_destruct'; subst.
          rename ψ0 into Ψ.
          exists Ψ.
          exists (extend_memory i (ValNum t) s1).
          exists w1.
          exists Σ2.

          assert (state_low_eq ℓ ψ (m1 [i → ValNum t]) h2
                               (s1 [i → ValNum t]) w1 Γ Σ1' Σ2).
          {
            repeat invert_wf_aux.
            repeat specialize_gen.
            invert_wt_cmd.
            rewrite_inj.
            eapply state_low_eq_extend_memory; eauto 2.
            - intros; discriminate.
            - intros; discriminate.
            - eapply wf_tenv_extend; eauto 2.
              intros; discriminate.
          }

          assert (wf_bijection ℓ ψ Γ Σ1' (m1 [i → ValNum t]) h2).
          {
            repeat invert_wf_aux; repeat specialize_gen; invert_wt_cmd.
            rewrite_inj.
            eapply wf_bijection_extend_mem1; eauto 2.
            intros; discriminate.
          }

          assert (taint_eq ℓ Ψ Γ Σ2 Σ3' Stop Stop
                           (s1 [i → ValNum t]) w1
                           (s1' [i → ValNum (S (g2'' - 1) - 1)])w2'').
          {
            remember_simple (low_gc_trans_preserves_taint_eq H5 H7 H10).
            unfold taint_eq in *; super_destruct'.
            repeat invert_wf_aux; repeat specialize_gen; invert_wt_cmd;
              rewrite_inj.
            assert (taint_eq_reach Φ s1 w1 s1' w2'').
            {
              rewrite <- (compose_id_right Φ).
              eapply taint_eq_reach_trans; eauto 2.
            }
            assert (taint_eq_heap ℓ Φ Σ2 Σ3' s1 w1 s1' w2'').
            {
              rewrite <- (compose_id_right Φ).
              eapply taint_eq_heap_trans with (h' := w1'); eauto 2.
            }
            assert (wf_taint_bijection ℓ (inverse Φ) s1' w2'').
            {
              eapply low_gc_trans_preserves_wf_taint_bijection with (pc := pc_end); eauto 2.
            }
            splits~.
            - eapply taint_eq_mem_extend; eauto 2.
            - eapply taint_eq_reach_extend_mem; eauto 2.
              + eauto 2.
              + intros; discriminate.
              + intros; discriminate.
            - eapply taint_eq_heap_extend_mem; eauto 2.
              + intros; discriminate.
              + intros; discriminate.
            - eapply taint_eq_heap_size_trans; eauto 2.
            - eapply taint_eq_heap_domain_eq_extend_mem; eauto 2.
              + rewrite <- (compose_id_right Φ).
                eapply taint_eq_heap_domain_eq_trans; eauto 2.
              + intros; discriminate.
              + intros; discriminate.
            - eapply taint_eq_stenv_extend_mem; eauto 2.
          }

          assert (wf_taint_bijection ℓ Ψ (s1 [i → ValNum t]) w1).
          {
            eapply wf_taint_bijection_extend_mem1; eauto 2.
            intros; discriminate.
          }
          
          splits~.
          * eapply bridge_stop_num; eauto 2.
            splits*.
          * splits*.
          * repeat invert_wf_aux; repeat specialize_gen; invert_wt_cmd.
            rewrite_inj.
            eapply TaintEqEventTime; eauto 2.
          * splits~.
            {
              repeat invert_wf_aux; repeat specialize_gen; invert_wt_cmd.
              rewrite_inj.
              eapply wf_bijection_extend_mem2; eauto 2.
              intros; discriminate.
            }
            {
            remember_simple (low_gc_trans_preserves_taint_eq H5 H7 H10).
            repeat invert_wf_aux; repeat specialize_gen; invert_wt_cmd.
            rewrite_inj.            
            unfold taint_eq in *; super_destruct'.
            eapply wf_taint_bijection_extend_mem2 with (m := s1) (h := w1) (Φ := Φ); eauto 2.
            { rewrite <- (compose_id_right Φ).
              eapply taint_eq_reach_trans.
              + eauto.
              + eapply gc_trans_preserves_taint_eq_reach; eauto. }
              { rewrite <- (compose_id_right Φ).
                eapply taint_eq_heap_trans; eauto 2. }
              { rewrite <- (compose_id_right Φ).
                eapply taint_eq_heap_domain_eq_trans; eauto 2. }
              { eapply low_gc_trans_preserves_wf_taint_bijection with (pc := pc_end);
                  eauto 2. }
              { intros; discriminate. }
            }
    }
    (* TimeOut *)
    {
      invert_bridge_step_with_steps 0.
      - invert_low_event_step.
        invert_event_step; try solve[invert_low_event].
      - invert_high_event_step.
        unfold is_stop_config, cmd_of in *; subst.
        invert_event_step.
    }
  }
  (* Inductive case *)
  {
    unfolds.
    intros.
    unfold ni_bridge.
    revert m1 m2 s1 s1' s2'' H0 H1 H2 H3 H4 H5 H6 H7 H9 H10 H11.
    revert h1 h2 w1 w1' w2''.
    revert Σ1 Σ2 Σ3 Σ1' Σ3'.
    revert t t' t2 g2'' ev1 ev2.
    revert pc_end.
    revert n n2 φ Φ H.
    revert c' c2 c2' H12 H13.
    revert pc pc1' pc2'' H8.

    induction c; intros; subst.
    (* Skip *)
    {
      invert_bridge_step_with_steps (S n).
      invert_taint_eq; invert_taint_eq_cmd.
      invert_high_event_step.
      invert_event_step.
      - exfalso; eauto 2.
      - assert (wellformed_aux Γ Σ' ⟨Skip, pc', m', [h1_pc ⊎ h1_not_pc, H15], t + δ⟩ pc_end).
        {
          eapply gc_preserves_wf; eauto 2.
          erewrite -> disjoint_union_proof_irrelevance; eauto 2.
        }
        repeat invert_wf_aux.
        assert (gc_occurred Skip Skip pc' pc' m' m'
                            ([[h1_pc ⊎ h1_not_pc, H15] ⊎ h3, H9])
                            ([h1_pc ⊎ h1_not_pc, H15]) t (t + δ) Σ' Σ') as H'.
        {
          unfolds.
          splits*.
          do 7 eexists.
          splits; reflexivity || eauto 2.
          erewrite -> disjoint_union_proof_irrelevance; eauto 2.
        }
        construct_gc_run.
        super_destruct'; subst.
        assert (δ0 = δ).
        {
          unfold gc_occurred_no_ex in H'.
          super_destruct'; omega.
        }
        subst.
        clear H'.
        unfold gc_occurred_no_ex in *; super_destruct'; subst.
        assert (n <= n) by omega.
        assert (wf_taint_bijection ℓ Φ m2' ([h2_pc ⊎ h2_not_pc, H2'])).
        {
          eapply low_gc_preserves_wf_taint_bijection; eauto 2.
          unfolds.
          splits; reflexivity || eauto 2.
          do 7 eexists.
          splits; reflexivity || eauto 2.
        }
        assert (wellformed_aux Γ Σ' ⟨Skip, pc2', m', [h1_pc ⊎ h1_not_pc, H15], t + δ⟩ pc_end).
        {
          constructor; eauto 2.
        }
        assert (wellformed_aux Γ Σ2' ⟨Skip, pc2', m2', [h2_pc ⊎ h2_not_pc, H2'], t + δ⟩ pc_end).
        {
          constructor; eauto 2.
          eapply lookup_in_bounds_subset; eauto 2.
        }
        assert (wellformed_aux Γ Σ3 ⟨Skip, pc2', s1', w1', t'⟩ pc_end).
        {
          constructor; eauto 2.
        }
        assert (taint_eq ℓ Φ Γ Σ2' Σ3 Skip Skip m2' ([h2_pc ⊎ h2_not_pc, H2']) s1' w1').
        {
          assert (taint_eq ℓ (identity_bijection loc) Γ Σ2' Σ2' Skip Skip m2' ([[h2_pc ⊎ h2_not_pc, H2'] ⊎ h2_gc, H1']) m2' ([h2_pc ⊎ h2_not_pc, H2'])).
          {
            eapply low_gc_preserves_taint_eq; eauto 2.
            unfolds.
            splits; reflexivity || eauto 2.
            do 7 eexists.
            splits; reflexivity || eauto 2.
          }
          rewrite <- (compose_id_left Φ).
          eapply taint_eq_trans
          with (m' := m2') (h' := ([[h2_pc ⊎ h2_not_pc, H2'] ⊎ h2_gc, H1'])).
          - eauto 2.
          - assert (taint_eq ℓ (identity_bijection loc) Γ Σ2' Σ2' Skip Skip m2' ([h2_pc ⊎ h2_not_pc, H2']) m2' ([[h2_pc ⊎ h2_not_pc, H2'] ⊎ h2_gc, H1'])).
            {
              rewrite <- inverse_identity_is_identity.
              eapply taint_eq_symmetry; eauto 2.
            }
            eauto 2.
          - unfolds.
            splits*.
        }
        apply_IH.
        super_destruct'; subst.
        exists ev1' (S n1') ψ0 Ψ s2' w2'; exists Σ2'0.
        splits*.
        eapply bridge_trans_num.
        + unfolds.
          splits.
          * eapply EventGCStep.
            eapply step_gc; reflexivity || eauto 2.
          * intro; invert_low_event.
        + intro; discriminate.
        + intro; discriminate.
        + eauto 2.
    }
    (* Stop *)
    {
      invert_bridge_step_with_steps (S n).
      invert_high_event_step.
      invert_event_step.
      exfalso; eauto 2.
    }
    (* Assign *)
    {
      invert_bridge_step_with_steps (S n).
      invert_taint_eq; invert_taint_eq_cmd.
      invert_high_event_step.
      invert_event_step.
      - exfalso; eauto 2.
      - assert (wellformed_aux Γ Σ' ⟨i ::= e, pc', m', [h1_pc ⊎ h1_not_pc, H15], t + δ⟩ pc_end).
        {
          eapply gc_preserves_wf; eauto 2.
          erewrite -> disjoint_union_proof_irrelevance; eauto 2.
        }
        repeat invert_wf_aux.
        assert (gc_occurred (i ::= e) (i ::= e) pc' pc' m' m'
                            ([[h1_pc ⊎ h1_not_pc, H15] ⊎ h3, H9])
                            ([h1_pc ⊎ h1_not_pc, H15]) t (t + δ) Σ' Σ') as H'.
        {
          unfolds.
          splits*.
          do 7 eexists.
          splits; reflexivity || eauto 2.
          erewrite -> disjoint_union_proof_irrelevance; eauto 2.
        }
        construct_gc_run.
        super_destruct'; subst.
        assert (δ0 = δ).
        {
          unfold gc_occurred_no_ex in H'.
          super_destruct'; omega.
        }
        subst.
        clear H'.
        unfold gc_occurred_no_ex in *; super_destruct'; subst.
        assert (n <= n) by omega.
        assert (wf_taint_bijection ℓ Φ m2' ([h2_pc ⊎ h2_not_pc, H2'])).
        {
          eapply low_gc_preserves_wf_taint_bijection; eauto 2.
          unfolds.
          splits; reflexivity || eauto 2.
          do 7 eexists.
          splits; reflexivity || eauto 2.
        }
        assert (wellformed_aux Γ Σ' ⟨i ::= e, pc2', m', [h1_pc ⊎ h1_not_pc, H15], t + δ⟩ pc_end).
        {
          constructor; eauto 2.
        }
        assert (wellformed_aux Γ Σ2' ⟨i ::= e, pc2', m2', [h2_pc ⊎ h2_not_pc, H2'], t + δ⟩ pc_end).
        {
          constructor; eauto 2.
          eapply lookup_in_bounds_subset; eauto 2.
        }
        assert (wellformed_aux Γ Σ3 ⟨i ::= e, pc2', s1', w1', t'⟩ pc_end).
        {
          constructor; eauto 2.
        }
        assert (taint_eq ℓ Φ Γ Σ2' Σ3 (i ::= e) (i ::= e) m2' ([h2_pc ⊎ h2_not_pc, H2']) s1' w1').
        {
          assert (taint_eq ℓ (identity_bijection loc) Γ Σ2' Σ2' (i ::= e) (i ::= e) m2' ([[h2_pc ⊎ h2_not_pc, H2'] ⊎ h2_gc, H1']) m2' ([h2_pc ⊎ h2_not_pc, H2'])).
          {
            eapply low_gc_preserves_taint_eq; eauto 2.
            unfolds.
            splits; reflexivity || eauto 2.
            do 7 eexists.
            splits; reflexivity || eauto 2.
          }
          rewrite <- (compose_id_left Φ).
          eapply taint_eq_trans
          with (m' := m2') (h' := ([[h2_pc ⊎ h2_not_pc, H2'] ⊎ h2_gc, H1'])).
          - eauto 2.
          - assert (taint_eq ℓ (identity_bijection loc) Γ Σ2' Σ2' (i ::= e) (i ::= e) m2' ([h2_pc ⊎ h2_not_pc, H2']) m2' ([[h2_pc ⊎ h2_not_pc, H2'] ⊎ h2_gc, H1'])).
            {
              rewrite <- inverse_identity_is_identity.
              eapply taint_eq_symmetry; eauto 2.
            }
            eauto 2.
          - unfolds.
            splits*.
        }
        apply_IH.
        super_destruct'; subst.
        exists ev1' (S n1') ψ0 Ψ s2' w2'; exists Σ2'0.
        splits*.
        eapply bridge_trans_num.
        + unfolds.
          splits.
          * eapply EventGCStep.
            eapply step_gc; reflexivity || eauto 2.
          * intro; invert_low_event.
        + intro; discriminate.
        + intro; discriminate.
        + eauto 2.
    }
    (* If *)
    {
      invert_taint_eq; invert_taint_eq_cmd.
      remember_simple (if_bridge_properties H4 H10).
      remember_simple (if_bridge_properties H6 H11).
      super_destruct; subst.
      - replace (S n - 1) with n in * by omega.
        assert (wellformed_aux Γ Σ1 ⟨c1, pc, m1, h1, S t⟩ pc_end) by eauto 2.
        assert (wellformed_aux Γ Σ3 ⟨c1', pc, s1', w1', S t'⟩ pc_end) by eauto 2.
        assert (wellformed_aux Γ Σ2 ⟨c1, pc, s1, w1, S t⟩ pc_end) by eauto 2.
        assert (n <= n) by omega.
        assert (taint_eq ℓ Φ Γ Σ2 Σ3 c1 c1' s1 w1 s1' w1').
        {
          unfolds; splits*.
        }
        apply_IH.
        super_destruct'; subst.
        exists ev1' (S n1') ψ Ψ s2' w2'; exists Σ2'.
        splits*.
        eapply bridge_trans_num.
        + splits*.
          constructor.
          eapply event_sem_step_if; eauto 2.
          eapply step_if_true; eauto 2.
          assert (taint_eq_mem (inverse Φ) Γ s1' s1) by eauto 2.
          repeat invert_wf_aux.
          repeat specialize_gen.
          invert_wt_cmd.
          rewrite_inj.
          invert_state_low_eq.
          remember_simple (eval_taint_eq_possibilistic H29 H49 H50 H36 H21).
          super_destruct'; subst.
          invert_val_taint_eq.
          eauto.
        + intro; unfold is_stop_config, cmd_of in *; subst.
          invert_bridge_step.
          * invert_low_event_step.
            invert_event_step; invert_low_event.
          * invert_high_event_step.
            invert_event_step; eauto 2.
          * invert_high_event_step.
            invert_event_step; exfalso; eauto 2.
        + intro; unfold is_timeout_config, cmd_of in *; subst.
          invert_bridge_step.
          * invert_low_event_step.
            invert_event_step; invert_low_event.
          * invert_high_event_step.
            invert_event_step; eauto 2.
          * invert_high_event_step.
            invert_event_step; exfalso; eauto 2.
        + eauto 2.
      - repeat invert_wf_aux.
        repeat specialize_gen.
        invert_wt_cmd.
        rewrite_inj.
        invert_state_low_eq.
        assert (eval s1 e = Some (ValNum p)).
        {
          assert (taint_eq_mem (inverse Φ) Γ s1' s1) by eauto 2.
          remember_simple (eval_taint_eq_possibilistic H28 H33 H32 H7 H21).
          super_destruct'; subst.
          invert_val_taint_eq.
          eauto.
        }
        assert (val_low_eq ℓ (SecType Int (ℓ0, ∘)) (ValNum 0) (ValNum p) φ) by eauto 2.
        invert_val_low_eq.
        + assert (ℓ0 ⊑ ℓ) by eauto 2.
          contradiction.
        + congruence.
      - repeat invert_wf_aux.
        repeat specialize_gen.
        invert_wt_cmd.
        rewrite_inj.
        invert_state_low_eq.
        assert (eval s1 e = Some (ValNum 0)).
        {
          assert (taint_eq_mem (inverse Φ) Γ s1' s1) by eauto 2.
          remember_simple (eval_taint_eq_possibilistic H28 H33 H32 H7 H21).
          super_destruct'; subst.
          invert_val_taint_eq.
          eauto.
        }
        assert (val_low_eq ℓ (SecType Int (ℓ0, ∘)) (ValNum p) (ValNum 0) φ) by eauto 2.
        invert_val_low_eq.
        + assert (ℓ0 ⊑ ℓ) by eauto 2.
          contradiction.
        + congruence.
      - replace (S n - 1) with n in * by omega.
        assert (wellformed_aux Γ Σ1 ⟨c2, pc, m1, h1, S t⟩ pc_end) by eauto 2.
        assert (wellformed_aux Γ Σ3 ⟨c2'0, pc, s1', w1', S t'⟩ pc_end) by eauto 2.
        assert (wellformed_aux Γ Σ2 ⟨c2, pc, s1, w1, S t⟩ pc_end) by eauto 2.
        assert (n <= n) by omega.
        assert (taint_eq ℓ Φ Γ Σ2 Σ3 c2 c2'0 s1 w1 s1' w1').
        {
          unfolds; splits*.
        }
        idtac.
        apply_IH.
        super_destruct'; subst.
        exists ev1' (S n1') ψ Ψ s2' w2'; exists Σ2'.
        splits*.
        eapply bridge_trans_num.
        + splits*.
          constructor.
          eapply event_sem_step_if; eauto 2.
          eapply step_if_false; eauto 2.
          assert (taint_eq_mem (inverse Φ) Γ s1' s1) by eauto 2.
          repeat invert_wf_aux.
          repeat specialize_gen.
          invert_wt_cmd.
          rewrite_inj.
          invert_state_low_eq.
          remember_simple (eval_taint_eq_possibilistic H27 H47 H48 H34 H21).
          super_destruct'; subst.
          invert_val_taint_eq.
          eauto.
        + intro; unfold is_stop_config, cmd_of in *; subst.
          invert_bridge_step.
          * invert_low_event_step.
            invert_event_step; invert_low_event.
          * invert_high_event_step.
            invert_event_step; eauto 2.
          * invert_high_event_step.
            invert_event_step; exfalso; eauto 2.
        + intro; unfold is_timeout_config, cmd_of in *; subst.
          invert_bridge_step.
          * invert_low_event_step.
            invert_event_step; invert_low_event.
          * invert_high_event_step.
            invert_event_step; eauto 2.
          * invert_high_event_step.
            invert_event_step; exfalso; eauto 2.
        + eauto 2.
    }
    (* While *)
    {
      invert_taint_eq; invert_taint_eq_cmd.
      remember_simple (while_bridge_properties H10).
      remember_simple (while_bridge_properties H11).
      super_destruct; subst.
      - construct_many_gc_run.
        super_destruct'; subst.
        exists EmptyEvent (S n) ψ Φ m2' h2'; exists Σ2'.
        splits.
        + assert (⟨WHILE e DO c END, pc2'', m2', h2', t''0⟩
                    ⇒ [EmptyEvent, Γ, Σ2', Σ2']
                  ⟨Stop, pc2'', m2', h2', S t''0⟩).
          {
            constructor.
            constructor.
            eapply step_while_false; eauto 2.
            assert (eval s1 e = Some (ValNum 0)).
            {
              repeat invert_wf_aux.
              repeat specialize_gen.
              invert_wt_cmd.
              assert (taint_eq_mem (inverse Φ) Γ s2'' s1) by eauto 2.
              remember_simple (eval_taint_eq_possibilistic H6 H32 H31 H4 H20).
              super_destruct'; subst.
              invert_val_taint_eq.
              eauto.
            }
            eapply gc_trans_preserves_eval2; eauto 2.
          }
          eapply gc_run_and_stop_implies_bridge; eauto 2.
        + eauto 2.
        + eauto 2.
        + eauto 2.
        + splits*.
        + eauto 2.
        + eauto 2.
        + splits.
          * eauto 2.
          * eapply low_gc_trans_preserves_wf_taint_bijection; eauto 2.
          * eapply low_gc_trans_preserves_wf_taint_bijection; eauto 2.
          * remember_simple (low_gc_trans_preserves_taint_eq H5 H8 H21).
            remember_simple (low_gc_trans_preserves_taint_eq H6 H8 H26).
            rewrite <- inverse_identity_is_identity in H22.
            eapply taint_eq_symmetry in H22.
            rewrite <- inverse_is_involutive in H22.
            assert (taint_eq ℓ Φ Γ Σ2' Σ3 Stop Stop m2' h2' s2'' w1').
            {
              rewrite <- (compose_id_left Φ).
              eapply taint_eq_trans with (m' := s1) (h' := w1).
              - repeat invert_wf_aux; eauto 2.
              - unfold taint_eq in *; super_destruct'; splits*.
              - unfold taint_eq in *; super_destruct'; splits*.
            }
            
            rewrite <- (compose_id_right Φ).
            eapply taint_eq_trans with (m' := s2'') (h' := w1').
            { repeat invert_wf_aux; eauto 2. }
            { eauto. }
            { unfold taint_eq in *; super_destruct'; splits*. }
      - repeat invert_wf_aux.
        repeat specialize_gen.
        invert_wt_cmd.
        assert (eval s1 e = Some (ValNum 0)).
        {
          assert (taint_eq_mem (inverse Φ) Γ s2'' s1) by eauto 2.
          remember_simple (eval_taint_eq_possibilistic H6 H32 H27 H4 H20).
          super_destruct'; subst.
          invert_val_taint_eq.
          eauto.
        }
        invert_state_low_eq.
        assert (val_low_eq ℓ (SecType Int (ℓ0, ∘)) (ValNum k) (ValNum 0) φ) by eauto 2.
        invert_val_low_eq.
        + assert (ℓ0 ⊑ ℓ) by eauto 2.
          contradiction.
        + congruence.
      - repeat invert_wf_aux.
        repeat specialize_gen.
        invert_wt_cmd.
        assert (eval s1 e = Some (ValNum k)).
        {
          assert (taint_eq_mem (inverse Φ) Γ s1' s1) by eauto 2.
          remember_simple (eval_taint_eq_possibilistic H6 H30 H28 H4 H21).
          super_destruct'; subst.
          invert_val_taint_eq.
          eauto.
        }
        invert_state_low_eq.
        assert (val_low_eq ℓ (SecType Int (ℓ0, ∘)) (ValNum 0) (ValNum k) φ) by eauto 2.
        invert_val_low_eq.
        + assert (ℓ0 ⊑ ℓ) by eauto 2.
          contradiction.
        + congruence.
      - replace (S n - 1) with n in * by omega.
        assert (wellformed_aux Γ Σ1 ⟨c ;; WHILE e DO c END, pc, m1, h1, S t ⟩ pc_end).
        {
          repeat invert_wf_aux; constructor; eauto 2.
          intros.
          repeat specialize_gen.
          invert_wt_cmd.
          constructors; eauto 2.
        }
        assert (wellformed_aux Γ Σ3 ⟨c'0;; WHILE e DO c'0 END, pc, s1', w1', S t'⟩ pc_end).
        {
          repeat invert_wf_aux; constructor; eauto 2.
          intros.
          repeat specialize_gen.
          invert_wt_cmd.
          constructors; eauto 2.
        }
        assert (wellformed_aux Γ Σ2 ⟨c ;; WHILE e DO c END, pc, s1, w1, S t⟩ pc_end).
        {
          repeat invert_wf_aux; constructor; eauto 2.
        }
        assert (taint_eq ℓ Φ Γ Σ2 Σ3 (c;; WHILE e DO c END) (c'0;; WHILE e DO c'0 END) s1 w1 s1' w1').
        {
          unfolds.
          splits*.
        }
        assert (n <= n) by omega.
        apply_IH.
        super_destruct'; subst.
        exists ev1' (S n1') ψ Ψ s2' w2'; exists Σ2'.
        splits*.
        eapply bridge_trans_num.
        + unfolds.
          splits*.
          constructor.
          eapply event_sem_step_while; eauto 2.
          eapply step_while_true; eauto 2.
          repeat invert_wf_aux.
          repeat specialize_gen.
          invert_wt_cmd.
          assert (taint_eq_mem (inverse Φ) Γ s1' s1) by eauto 2.
          remember_simple (eval_taint_eq_possibilistic H6 H47 H44 H4 H21).
          super_destruct'; subst.
          invert_val_taint_eq.
          eauto.
        + intro; discriminate.
        + intro; discriminate.
        + eauto 2.
    }
    (* Sequential composition *)
    {
      invert_taint_eq; invert_taint_eq_cmd.
      remember_simple (about_seq_bridge_step H4 H10).
      remember_simple (about_seq_bridge_step H6 H11).
      super_destruct; subst.
      - assert (exists pc', wellformed_aux Γ Σ1 ⟨c1, pc, m1, h1, t⟩ pc') by eauto 2.
        assert (exists pc', wellformed_aux Γ Σ2 ⟨c1, pc, s1, w1, t⟩ pc') by eauto 2.
        assert (exists pc', wellformed_aux Γ Σ3 ⟨c1', pc, s1', w1', t'⟩ pc') by eauto 2.
        super_destruct'; subst.
        assert (taint_eq ℓ Φ Γ Σ2 Σ3 c1 c1' s1 w1 s1' w1').
        {
          unfolds; splits*.
        }
        assert (c1 <> Stop).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          intro; subst.
          invert_wt_cmd; invert_wt_stop.
        }
        assert (c1 <> TimeOut).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          intro; subst.
          invert_wt_cmd; invert_wt_timeout.
        }
        assert (pc'1 = pc'0).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          eauto 2.
        }
        subst.
        assert (c1' <> Stop).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          intro; subst.
          invert_wt_cmd; invert_wt_stop.
        }

        assert (c1' <> TIMEOUT).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          intro; subst.
          invert_wt_cmd; invert_wt_timeout.
        }
        assert (pc' = pc'0).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          remember_simple (taint_eq_cmd_implies_same_type H22 H48).
          eauto 2.
        }
        subst.
        assert (c1'1 <> TimeOut).
        {
          intro; subst.
          repeat specialize_gen.
          subst.
          assert (wellformed_aux Γ Σ1' ⟨TIMEOUT;; c2, pc1', m2, h2, t2 ⟩ pc_end) by eauto 2.
          invert_wf_aux.
          repeat specialize_gen.
          invert_wt_cmd.
          invert_wt_timeout.
        }
        assert (c1'0 <> TimeOut).
        {
          intro; subst.
          repeat specialize_gen.
          subst.
          assert (wellformed_aux Γ Σ3' ⟨TIMEOUT;; c2'0, pc2'', s2'', w2'', g2''⟩ pc_end) by eauto 2.
          invert_wf_aux.
          repeat specialize_gen.
          invert_wt_cmd.
          invert_wt_timeout.
        }
        remember_simple (IHc1 _ _ _ H8 _ _ _ H37 H38 _ _ _ _ H
                              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                              H0 H1 H2 H3 H29 H30 H31 H7 H32 H9 H20).
        super_destruct'; subst.
        exists ev1' n1' ψ Ψ s2' w2'; exists Σ2'.
        splits; eauto 2.
        + destruct (eq_cmd_dec c1'1 Stop).
          * subst.
            specialize (H27 eq_refl).
            subst.
            eapply bridge_step_seq_low_event_in_left_stop.
            { eauto. }
            { eauto. }
            { intro; subst.
              invert_wf_aux.
              repeat specialize_gen.
              invert_wt_cmd.
              invert_wt_stop. }
          * specialize (H26 n0).
            subst.
            eapply bridge_step_seq_low_event_in_left_nonstop.
            { eauto. }
            { eauto 2. }
            { eauto 2. }
            { intro; subst.
              assert (wellformed_aux Γ Σ1' ⟨TIMEOUT;; c2, pc1', m2, h2, t2⟩ pc_end).
              {
                eauto 2.
              }
              invert_wf_aux.
              repeat specialize_gen.
              invert_wt_cmd.
              invert_wt_timeout. }
        + splits~.
          unfold taint_eq in *; super_destruct'.
          splits~.
          destruct (eq_cmd_dec c1'1 Stop); subst.
          * assert (c0 = c2) by eauto 2.
            subst.
            invert_taint_eq_cmd.
            assert (c2' = c2'0) by eauto 2.
            subst.
            eauto 2.
          * assert (c0 = (c1'1;; c2)) by eauto 2.
            subst.
            assert (c1'0 <> Stop).
            {
              intro; subst.
              invert_taint_eq_cmd; eauto 2.
            }
            repeat specialize_gen.
            subst.
            eauto 2. 
      - assert (exists pc', wellformed_aux Γ Σ1 ⟨c1, pc, m1, h1, t⟩ pc') by eauto 2.
        assert (exists pc', wellformed_aux Γ Σ2 ⟨c1, pc, s1, w1, t⟩ pc') by eauto 2.
        assert (exists pc', wellformed_aux Γ Σ3 ⟨c1', pc, s1', w1', t'⟩ pc') by eauto 2.
        super_destruct'; subst.
        assert (taint_eq ℓ Φ Γ Σ2 Σ3 c1 c1' s1 w1 s1' w1').
        {
          unfolds; splits*.
        }
        assert (c1 <> Stop).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          intro; subst.
          invert_wt_cmd; invert_wt_stop.
        }
        assert (c1 <> TimeOut).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          intro; subst.
          invert_wt_cmd; invert_wt_timeout.
        }
        assert (pc'1 = pc'0).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          eauto 2.
        }
        subst.
        assert (c1' <> Stop).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          intro; subst.
          invert_wt_cmd; invert_wt_stop.
        }

        assert (c1' <> TIMEOUT).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          intro; subst.
          invert_wt_cmd; invert_wt_timeout.
        }
        assert (pc' = pc'0).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          remember_simple (taint_eq_cmd_implies_same_type H22 H61).
          eauto 2.
        }
        subst.
        assert (Stop <> TimeOut) by congruence.
        assert (c1'0 <> TimeOut).
        {
          intro; subst.
          repeat specialize_gen.
          subst.
          
          assert (wellformed_aux Γ Σ3' ⟨ TIMEOUT;; c2'0, pc2'', s2'', w2'', g2''⟩ pc_end) by eauto 2.
          invert_wf_aux.
          repeat specialize_gen.
          invert_wt_cmd.
          invert_wt_timeout.
        }
        assert (k <= n) by omega.
        apply_IH.
        super_destruct'.
        assert (low_event ℓ ev1') by eauto 2.
        assert (low_event ℓ ev').
        {
          unfold event_low_eq in *.
          super_destruct'.
          firstorder 2.
        }
        contradiction.
      - assert (exists pc', wellformed_aux Γ Σ1 ⟨c1, pc, m1, h1, t⟩ pc') by eauto 2.
        assert (exists pc', wellformed_aux Γ Σ2 ⟨c1, pc, s1, w1, t⟩ pc') by eauto 2.
        assert (exists pc', wellformed_aux Γ Σ3 ⟨c1', pc, s1', w1', t'⟩ pc') by eauto 2.
        super_destruct'; subst.
        assert (taint_eq ℓ Φ Γ Σ2 Σ3 c1 c1' s1 w1 s1' w1').
        {
          unfolds; splits*.
        }
        assert (c1 <> Stop).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          intro; subst.
          invert_wt_cmd; invert_wt_stop.
        }
        assert (c1 <> TimeOut).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          intro; subst.
          invert_wt_cmd; invert_wt_timeout.
        }
        assert (pc'1 = pc'0).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          eauto 2.
        }
        subst.
        assert (c1' <> Stop).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          intro; subst.
          invert_wt_cmd; invert_wt_stop.
        }

        assert (c1' <> TIMEOUT).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          intro; subst.
          invert_wt_cmd; invert_wt_timeout.
        }
        assert (pc' = pc'0).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          remember_simple (taint_eq_cmd_implies_same_type H22 H61).
          eauto 2.
        }
        subst.
        assert (Stop <> TimeOut) by congruence.
        assert (c1'0 <> TimeOut).
        {
          intro; subst.
          repeat specialize_gen.
          subst.
          
          assert (wellformed_aux Γ Σ1' ⟨TIMEOUT;; c2, pc1', m2, h2, t2⟩ pc_end) by eauto 2.
          invert_wf_aux.
          repeat specialize_gen.
          invert_wt_cmd.
          invert_wt_timeout.
        }
        remember_simple (IHc1 _ _ _ H8 _ _ _ H39 H38 _ _ _ _ H
                              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                              H0 H1 H2 H3 H30 H31 H32 H7 H33 H9 H25).
        super_destruct'; subst.
        assert (low_event ℓ ev1') by eauto 2.
        assert (low_event ℓ ev').
        {
          unfold event_low_eq in *.
          super_destruct'.
          eauto 2.
        }
        contradiction.
      - replace (S n - k0 - 1) with (n - k0) in * by omega.
        assert (exists pc', wellformed_aux Γ Σ1 ⟨c1, pc, m1, h1, t⟩ pc') by eauto 2.
        assert (exists pc', wellformed_aux Γ Σ2 ⟨c1, pc, s1, w1, t⟩ pc') by eauto 2.
        assert (exists pc', wellformed_aux Γ Σ3 ⟨c1', pc, s1', w1', t'⟩ pc') by eauto 2.
        super_destruct'; subst.
        assert (taint_eq ℓ Φ Γ Σ2 Σ3 c1 c1' s1 w1 s1' w1').
        {
          unfolds; splits*.
        }
        assert (c1 <> Stop).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          intro; subst.
          invert_wt_cmd; invert_wt_stop.
        }
        assert (c1 <> TimeOut).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          intro; subst.
          invert_wt_cmd; invert_wt_timeout.
        }
        assert (pc'1 = pc'0).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          eauto 2.
        }
        subst.
        assert (c1' <> Stop).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          intro; subst.
          invert_wt_cmd; invert_wt_stop.
        }

        assert (c1' <> TIMEOUT).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          intro; subst.
          invert_wt_cmd; invert_wt_timeout.
        }
        assert (pc' = pc'0).
        {
          repeat invert_wf_aux.
          repeat specialize_gen.
          remember_simple (taint_eq_cmd_implies_same_type H22 H50).
          eauto 2.
        }
        subst.
        assert (Stop <> TimeOut) by congruence.
        assert (Stop <> TimeOut) by congruence.
        assert (k0 <= n) by omega.
        apply_IH.
        super_destruct'.
        assert (n - k0 <= n) by omega.
        remember_simple (wf_seq_half_step_implies_wf_bridge_step H4 H29).
        remember_simple (wf_seq_half_step_implies_wf_bridge_step H5 H42).
        remember_simple (wf_seq_half_step_implies_wf_bridge_step H6 H25).
        assert (pc''0 = pc'0).
        {
          eauto 2 using wt_aux_soundness_bridge.
        }
        subst.

        clear H7.
        assert (taint_eq ℓ Ψ Γ Σ2' Σ' c2 c2'0 s2' w2' m'' h'').
        {
          unfold taint_eq in *; super_destruct'; splits*.
        }
        apply_IH.
        super_destruct'; subst.
        exists ev1'0 (S (n1' + n1'0)) ψ0 Ψ0 s2'0 w2'0; exists Σ2'0.
        splits; eauto 2.
        + eapply concat_bridge_step_seq.
          * eauto 2.
          * eauto 2.
          * intro.
            assert (low_event ℓ ev') by eauto 2.
            contradiction.
          * eauto 2.
        + splits*.
    }
    (* At *)
    {
      eauto 2 using ni_bridge_num_at_case.
    }
    {
      eauto 2 using ni_bridge_num_backat_case.
    }
    (* New *)
    {
      invert_bridge_step_with_steps (S n).
      invert_taint_eq; invert_taint_eq_cmd.
      invert_high_event_step.
      invert_event_step.
      - exfalso; eauto 2.
      - assert (wellformed_aux Γ Σ' ⟨NewArr i l e e0, pc', m', [h1_pc ⊎ h1_not_pc, H15], t + δ⟩ pc_end).
        {
          eapply gc_preserves_wf; eauto 2.
          erewrite -> disjoint_union_proof_irrelevance; eauto 2.
        }
        repeat invert_wf_aux.
        assert (gc_occurred (NewArr i l e e0) (NewArr i l e e0) pc' pc' m' m'
                            ([[h1_pc ⊎ h1_not_pc, H15] ⊎ h3, H9])
                            ([h1_pc ⊎ h1_not_pc, H15]) t (t + δ) Σ' Σ') as H'.
        {
          unfolds.
          splits*.
          do 7 eexists.
          splits; reflexivity || eauto 2.
          erewrite -> disjoint_union_proof_irrelevance; eauto 2.
        }
        construct_gc_run.
        super_destruct'; subst.
        assert (δ0 = δ).
        {
          unfold gc_occurred_no_ex in H'.
          super_destruct'; omega.
        }
        subst.
        clear H'.
        unfold gc_occurred_no_ex in *; super_destruct'; subst.
        assert (n <= n) by omega.
        assert (wf_taint_bijection ℓ Φ m2' ([h2_pc ⊎ h2_not_pc, H2'])).
        {
          eapply low_gc_preserves_wf_taint_bijection; eauto 2.
          unfolds.
          splits; reflexivity || eauto 2.
          do 7 eexists.
          splits; reflexivity || eauto 2.
        }
        assert (wellformed_aux Γ Σ' ⟨NewArr i l e e0, pc2', m', [h1_pc ⊎ h1_not_pc, H15], t + δ⟩ pc_end).
        {
          constructor; eauto 2.
        }
        assert (wellformed_aux Γ Σ2' ⟨NewArr i l e e0, pc2', m2', [h2_pc ⊎ h2_not_pc, H2'], t + δ⟩ pc_end).
        {
          constructor; eauto 2.
          eapply lookup_in_bounds_subset; eauto 2.
        }
        assert (wellformed_aux Γ Σ3 ⟨NewArr i l e e0, pc2', s1', w1', t'⟩ pc_end).
        {
          constructor; eauto 2.
        }
        assert (taint_eq ℓ Φ Γ Σ2' Σ3 (NewArr i l e e0) (NewArr i l e e0) m2' ([h2_pc ⊎ h2_not_pc, H2']) s1' w1').
        {
          assert (taint_eq ℓ (identity_bijection loc) Γ Σ2' Σ2' (NewArr i l e e0) (NewArr i l e e0) m2' ([[h2_pc ⊎ h2_not_pc, H2'] ⊎ h2_gc, H1']) m2' ([h2_pc ⊎ h2_not_pc, H2'])).
          {
            eapply low_gc_preserves_taint_eq; eauto 2.
            unfolds.
            splits; reflexivity || eauto 2.
            do 7 eexists.
            splits; reflexivity || eauto 2.
          }
          rewrite <- (compose_id_left Φ).
          eapply taint_eq_trans
          with (m' := m2') (h' := ([[h2_pc ⊎ h2_not_pc, H2'] ⊎ h2_gc, H1'])).
          - eauto 2.
          - assert (taint_eq ℓ (identity_bijection loc) Γ Σ2' Σ2' (NewArr i l e e0) (NewArr i l e e0) m2' ([h2_pc ⊎ h2_not_pc, H2']) m2' ([[h2_pc ⊎ h2_not_pc, H2'] ⊎ h2_gc, H1'])).
            {
              rewrite <- inverse_identity_is_identity.
              eapply taint_eq_symmetry; eauto 2.
            }
            eauto 2.
          - unfolds.
            splits*.
        }
        apply_IH.
        super_destruct'; subst.
        exists ev1' (S n1') ψ0 Ψ s2' w2'; exists Σ2'0.
        splits*.
        eapply bridge_trans_num.
        + unfolds.
          splits.
          * eapply EventGCStep.
            eapply step_gc; reflexivity || eauto 2.
          * intro; invert_low_event.
        + intro; discriminate.
        + intro; discriminate.
        + eauto 2.
    }
    (* Set *)
    {
      invert_bridge_step_with_steps (S n).
      invert_taint_eq; invert_taint_eq_cmd.
      invert_high_event_step.
      invert_event_step.
      - exfalso; eauto 2.
      - assert (wellformed_aux Γ Σ' ⟨SetArr i e e0, pc', m', [h1_pc ⊎ h1_not_pc, H15], t + δ⟩ pc_end).
        {
          eapply gc_preserves_wf; eauto 2.
          erewrite -> disjoint_union_proof_irrelevance; eauto 2.
        }
        repeat invert_wf_aux.
        assert (gc_occurred (SetArr i e e0) (SetArr i e e0) pc' pc' m' m'
                            ([[h1_pc ⊎ h1_not_pc, H15] ⊎ h3, H9])
                            ([h1_pc ⊎ h1_not_pc, H15]) t (t + δ) Σ' Σ') as H'.
        {
          unfolds.
          splits*.
          do 7 eexists.
          splits; reflexivity || eauto 2.
          erewrite -> disjoint_union_proof_irrelevance; eauto 2.
        }
        construct_gc_run.
        super_destruct'; subst.
        assert (δ0 = δ).
        {
          unfold gc_occurred_no_ex in H'.
          super_destruct'; omega.
        }
        subst.
        clear H'.
        unfold gc_occurred_no_ex in *; super_destruct'; subst.
        assert (n <= n) by omega.
        assert (wf_taint_bijection ℓ Φ m2' ([h2_pc ⊎ h2_not_pc, H2'])).
        {
          eapply low_gc_preserves_wf_taint_bijection; eauto 2.
          unfolds.
          splits; reflexivity || eauto 2.
          do 7 eexists.
          splits; reflexivity || eauto 2.
        }
        assert (wellformed_aux Γ Σ' ⟨SetArr i e e0, pc2', m', [h1_pc ⊎ h1_not_pc, H15], t + δ⟩ pc_end).
        {
          constructor; eauto 2.
        }
        assert (wellformed_aux Γ Σ2' ⟨SetArr i e e0, pc2', m2', [h2_pc ⊎ h2_not_pc, H2'], t + δ⟩ pc_end).
        {
          constructor; eauto 2.
          eapply lookup_in_bounds_subset; eauto 2.
        }
        assert (wellformed_aux Γ Σ3 ⟨SetArr i e e0, pc2', s1', w1', t'⟩ pc_end).
        {
          constructor; eauto 2.
        }
        assert (taint_eq ℓ Φ Γ Σ2' Σ3 (SetArr i e e0) (SetArr i e e0) m2' ([h2_pc ⊎ h2_not_pc, H2']) s1' w1').
        {
          assert (taint_eq ℓ (identity_bijection loc) Γ Σ2' Σ2' (SetArr i e e0) (SetArr i e e0) m2' ([[h2_pc ⊎ h2_not_pc, H2'] ⊎ h2_gc, H1']) m2' ([h2_pc ⊎ h2_not_pc, H2'])).
          {
            eapply low_gc_preserves_taint_eq; eauto 2.
            unfolds.
            splits; reflexivity || eauto 2.
            do 7 eexists.
            splits; reflexivity || eauto 2.
          }
          rewrite <- (compose_id_left Φ).
          eapply taint_eq_trans
          with (m' := m2') (h' := ([[h2_pc ⊎ h2_not_pc, H2'] ⊎ h2_gc, H1'])).
          - eauto 2.
          - assert (taint_eq ℓ (identity_bijection loc) Γ Σ2' Σ2' (SetArr i e e0) (SetArr i e e0) m2' ([h2_pc ⊎ h2_not_pc, H2']) m2' ([[h2_pc ⊎ h2_not_pc, H2'] ⊎ h2_gc, H1'])).
            {
              rewrite <- inverse_identity_is_identity.
              eapply taint_eq_symmetry; eauto 2.
            }
            eauto 2.
          - unfolds.
            splits*.
        }
        apply_IH.
        super_destruct'; subst.
        exists ev1' (S n1') ψ0 Ψ s2' w2'; exists Σ2'0.
        splits*.
        eapply bridge_trans_num.
        + unfolds.
          splits.
          * eapply EventGCStep.
            eapply step_gc; reflexivity || eauto 2.
          * intro; invert_low_event.
        + intro; discriminate.
        + intro; discriminate.
        + eauto 2.
    }
    (* Get  *)
    {
      invert_bridge_step_with_steps (S n).
      invert_taint_eq; invert_taint_eq_cmd.
      invert_high_event_step.
      invert_event_step.
      - exfalso; eauto 2.
      - assert (wellformed_aux Γ Σ' ⟨GetArr i i0 e, pc', m', [h1_pc ⊎ h1_not_pc, H15], t + δ⟩ pc_end).
        {
          eapply gc_preserves_wf; eauto 2.
          erewrite -> disjoint_union_proof_irrelevance; eauto 2.
        }
        repeat invert_wf_aux.
        assert (gc_occurred (GetArr i i0 e) (GetArr i i0 e) pc' pc' m' m'
                            ([[h1_pc ⊎ h1_not_pc, H15] ⊎ h3, H9])
                            ([h1_pc ⊎ h1_not_pc, H15]) t (t + δ) Σ' Σ') as H'.
        {
          unfolds.
          splits*.
          do 7 eexists.
          splits; reflexivity || eauto 2.
          erewrite -> disjoint_union_proof_irrelevance; eauto 2.
        }
        construct_gc_run.
        super_destruct'; subst.
        assert (δ0 = δ).
        {
          unfold gc_occurred_no_ex in H'.
          super_destruct'; omega.
        }
        subst.
        clear H'.
        unfold gc_occurred_no_ex in *; super_destruct'; subst.
        assert (n <= n) by omega.
        assert (wf_taint_bijection ℓ Φ m2' ([h2_pc ⊎ h2_not_pc, H2'])).
        {
          eapply low_gc_preserves_wf_taint_bijection; eauto 2.
          unfolds.
          splits; reflexivity || eauto 2.
          do 7 eexists.
          splits; reflexivity || eauto 2.
        }
        assert (wellformed_aux Γ Σ' ⟨GetArr i i0 e, pc2', m', [h1_pc ⊎ h1_not_pc, H15], t + δ⟩ pc_end).
        {
          constructor; eauto 2.
        }
        assert (wellformed_aux Γ Σ2' ⟨GetArr i i0 e, pc2', m2', [h2_pc ⊎ h2_not_pc, H2'], t + δ⟩ pc_end).
        {
          constructor; eauto 2.
          eapply lookup_in_bounds_subset; eauto 2.
        }
        assert (wellformed_aux Γ Σ3 ⟨GetArr i i0 e, pc2', s1', w1', t'⟩ pc_end).
        {
          constructor; eauto 2.
        }
        assert (taint_eq ℓ Φ Γ Σ2' Σ3 (GetArr i i0 e) (GetArr i i0 e) m2' ([h2_pc ⊎ h2_not_pc, H2']) s1' w1').
        {
          assert (taint_eq ℓ (identity_bijection loc) Γ Σ2' Σ2' (GetArr i i0 e) (GetArr i i0 e) m2' ([[h2_pc ⊎ h2_not_pc, H2'] ⊎ h2_gc, H1']) m2' ([h2_pc ⊎ h2_not_pc, H2'])).
          {
            eapply low_gc_preserves_taint_eq; eauto 2.
            unfolds.
            splits; reflexivity || eauto 2.
            do 7 eexists.
            splits; reflexivity || eauto 2.
          }
          rewrite <- (compose_id_left Φ).
          eapply taint_eq_trans
          with (m' := m2') (h' := ([[h2_pc ⊎ h2_not_pc, H2'] ⊎ h2_gc, H1'])).
          - eauto 2.
          - assert (taint_eq ℓ (identity_bijection loc) Γ Σ2' Σ2' (GetArr i i0 e) (GetArr i i0 e) m2' ([h2_pc ⊎ h2_not_pc, H2']) m2' ([[h2_pc ⊎ h2_not_pc, H2'] ⊎ h2_gc, H1'])).
            {
              rewrite <- inverse_identity_is_identity.
              eapply taint_eq_symmetry; eauto 2.
            }
            eauto 2.
          - unfolds.
            splits*.
        }
        apply_IH.
        super_destruct'; subst.
        exists ev1' (S n1') ψ0 Ψ s2' w2'; exists Σ2'0.
        splits*.
        eapply bridge_trans_num.
        + unfolds.
          splits.
          * eapply EventGCStep.
            eapply step_gc; reflexivity || eauto 2.
          * intro; invert_low_event.
        + intro; discriminate.
        + intro; discriminate.
        + eauto 2.
    }
    (* Time *)
    {
      invert_bridge_step_with_steps (S n).
      invert_taint_eq; invert_taint_eq_cmd.
      invert_high_event_step.
      invert_event_step.
      - exfalso; eauto 2.
      - assert (wellformed_aux Γ Σ' ⟨Time i, pc', m', [h1_pc ⊎ h1_not_pc, H15], t + δ⟩ pc_end).
        {
          eapply gc_preserves_wf; eauto 2.
          erewrite -> disjoint_union_proof_irrelevance; eauto 2.
        }
        repeat invert_wf_aux.
        assert (gc_occurred (Time i) (Time i) pc' pc' m' m'
                            ([[h1_pc ⊎ h1_not_pc, H15] ⊎ h3, H9])
                            ([h1_pc ⊎ h1_not_pc, H15]) t (t + δ) Σ' Σ') as H'.
        {
          unfolds.
          splits*.
          do 7 eexists.
          splits; reflexivity || eauto 2.
          erewrite -> disjoint_union_proof_irrelevance; eauto 2.
        }
        construct_gc_run.
        super_destruct'; subst.
        assert (δ0 = δ).
        {
          unfold gc_occurred_no_ex in H'.
          super_destruct'; omega.
        }
        subst.
        clear H'.
        unfold gc_occurred_no_ex in *; super_destruct'; subst.
        assert (n <= n) by omega.
        assert (wf_taint_bijection ℓ Φ m2' ([h2_pc ⊎ h2_not_pc, H2'])).
        {
          eapply low_gc_preserves_wf_taint_bijection; eauto 2.
          unfolds.
          splits; reflexivity || eauto 2.
          do 7 eexists.
          splits; reflexivity || eauto 2.
        }
        assert (wellformed_aux Γ Σ' ⟨Time i, pc2', m', [h1_pc ⊎ h1_not_pc, H15], t + δ⟩ pc_end).
        {
          constructor; eauto 2.
        }
        assert (wellformed_aux Γ Σ2' ⟨Time i, pc2', m2', [h2_pc ⊎ h2_not_pc, H2'], t + δ⟩ pc_end).
        {
          constructor; eauto 2.
          eapply lookup_in_bounds_subset; eauto 2.
        }
        assert (wellformed_aux Γ Σ3 ⟨Time i, pc2', s1', w1', t'⟩ pc_end).
        {
          constructor; eauto 2.
        }
        assert (taint_eq ℓ Φ Γ Σ2' Σ3 (Time i) (Time i) m2' ([h2_pc ⊎ h2_not_pc, H2']) s1' w1').
        {
          assert (taint_eq ℓ (identity_bijection loc) Γ Σ2' Σ2' (Time i) (Time i) m2' ([[h2_pc ⊎ h2_not_pc, H2'] ⊎ h2_gc, H1']) m2' ([h2_pc ⊎ h2_not_pc, H2'])).
          {
            eapply low_gc_preserves_taint_eq; eauto 2.
            unfolds.
            splits; reflexivity || eauto 2.
            do 7 eexists.
            splits; reflexivity || eauto 2.
          }
          rewrite <- (compose_id_left Φ).
          eapply taint_eq_trans
          with (m' := m2') (h' := ([[h2_pc ⊎ h2_not_pc, H2'] ⊎ h2_gc, H1'])).
          - eauto 2.
          - assert (taint_eq ℓ (identity_bijection loc) Γ Σ2' Σ2' (Time i) (Time i) m2' ([h2_pc ⊎ h2_not_pc, H2']) m2' ([[h2_pc ⊎ h2_not_pc, H2'] ⊎ h2_gc, H1'])).
            {
              rewrite <- inverse_identity_is_identity.
              eapply taint_eq_symmetry; eauto 2.
            }
            eauto 2.
          - unfolds.
            splits*.
        }
        apply_IH.
        super_destruct'; subst.
        exists ev1' (S n1') ψ0 Ψ s2' w2'; exists Σ2'0.
        splits*.
        eapply bridge_trans_num.
        + unfolds.
          splits.
          * eapply EventGCStep.
            eapply step_gc; reflexivity || eauto 2.
          * intro; invert_low_event.
        + intro; discriminate.
        + intro; discriminate.
        + eauto 2.
    }
    (* TimeOut *)
    {
      invert_bridge_step_with_steps (S n).
      invert_high_event_step.
      exfalso.
      invert_event_step; eauto 2.
    }

    Unshelve.
    - eauto 2.
    - eauto 2.
    - eauto 2.
    - eauto 2.
    - eauto 2.
    - eauto 2.
    - eauto 2.
    - constructor; eauto 2.
    - eauto 2.
    - eauto 2.
    - eauto 2.
    - eauto 2.
    - eauto 2.
    - eauto 2.
    - eauto 2.
    - eauto 2.
    - eauto 2.
    - eauto 2.
    - eauto 2.
    - eauto 2.
    - eauto 2.
    - eauto 2.
    - eauto 2.
    - eauto 2.
    - eauto 2.
    - eauto 2.
    - eauto 2.
    - eauto 2.
  }
Qed.
End NIBridge.