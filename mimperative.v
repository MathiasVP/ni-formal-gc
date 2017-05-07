Require Import mlattice mmemory id_and_loc language types decision typedefinitions.
Require Import Arith Omega LibTactics tactics Coq.Program.Basics Coq.Program.Equality.

Module Imperative (L: Lattice) (M: Memory L).
  Module TDefs := TypeDefinitions L M.
  Import TDefs M T MemProp LatProp Lang L.
  
  Definition GlobTime := nat.
  
  Inductive config  :=
    Config (c: cmd) (pc: level_proj1) (memory: Memory) (heap: Heap) (time: GlobTime).

  Notation "'⟨' c ',' pc ',' m ',' h ',' t '⟩'" := (Config c pc m h t) (at level 0).

  Definition cmd_of cfg :=
    match cfg with
    | Config c _ _ _ _ => c
    end.

  Definition is_stop_config cfg := cmd_of cfg = Stop.
  Definition is_timeout_config cfg := cmd_of cfg = TimeOut.
  
  Lemma is_stop_trivial:
    forall pc m h t,
      is_stop_config ⟨STOP, pc, m, h, t⟩.
  Proof.
    intros.
    unfolds is_stop_config.
    unfolds cmd_of.
    eauto.
  Qed.
  Hint Resolve is_stop_trivial.

  Lemma is_timeout_trivial:
    forall pc m h t,
      is_timeout_config ⟨TIMEOUT, pc, m, h, t⟩.
  Proof.
    intros.
    unfolds is_timeout_config.
    unfolds cmd_of.
    eauto.
  Qed.
  Hint Resolve is_timeout_trivial.
  
  Inductive gc_step: config -> config -> tenv -> stenv -> stenv -> Prop :=
  | step_gc:
      forall pc m h1 h2 h1_pc h1_not_pc t c Γ Σ δ H1 H2 H3,
        c <> Stop ->
        c <> TimeOut ->
        (forall loc ℓ μ, heap_lookup loc h2 = Some (ℓ, μ) ->
                    ~ reach m ([h1 ⊎ h2, H1]) loc) ->
        levels_satisfy h2 (eq pc) ->
        h1 = [h1_pc ⊎ h1_not_pc, H2] ->
        levels_satisfy h1_pc (eq pc) ->
        levels_satisfy h1_not_pc (compose not (eq pc)) ->
        gc m ([h1_pc ⊎ h2, H3]) δ h1_pc ->
        gc_step (Config c pc m ([h1 ⊎ h2, H1]) t) (Config c pc m h1 (t + δ)) Γ Σ Σ.
  
  Inductive sem_step: config -> config -> tenv -> stenv -> stenv -> Prop :=
  | step_skip:
      forall pc memory heap time Γ Σ,
        sem_step (Config Skip pc memory heap time) (Config Stop pc memory heap (S time)) Γ Σ Σ
  | step_assign:
      forall pc memory heap x e v time Γ Σ,
        eval memory e = Some v ->
        sem_step (Config (Assign x e) pc memory heap time)
             (Config Stop pc (extend_memory x v memory) heap (S time))
             Γ Σ Σ
  | step_if_false:
      forall pc memory heap e c1 c2 n time Γ Σ,
        eval memory e = Some (ValNum n) ->
        n = 0 ->
        sem_step (Config (If e c1 c2) pc memory heap time)
             (Config c2 pc memory heap (S time))
             Γ Σ Σ
  | step_if_true:
      forall pc memory heap e c1 c2 n time Γ Σ,
        eval memory e = Some (ValNum n) ->
        n <> 0 ->
        sem_step (Config (If e c1 c2) pc memory heap time)
             (Config c1 pc memory heap (S time))
             Γ Σ Σ
  | step_while_false:
      forall pc memory heap e c n time Γ Σ,
        eval memory e = Some (ValNum n) ->
        n = 0 ->
        sem_step (Config (While e c) pc memory heap time)
             (Config Stop pc memory heap (S time))
             Γ Σ Σ
  | step_while_true:
      forall pc memory heap e c n time Γ Σ,
        eval memory e = Some (ValNum n) ->
        n <> 0 ->
        sem_step (Config (While e c) pc memory heap time)
             (Config (Seq c (While e c)) pc memory heap (S time))
             Γ Σ Σ
  | step_seq_stop:
      forall pc pc' memory memory' heap heap' c1 c2 time time' Γ Σ Σ',
        step (Config c1 pc memory heap time)
             (Config Stop pc' memory' heap' time') Γ Σ Σ' ->
        sem_step (Config (Seq c1 c2) pc memory heap time)
             (Config c2 pc' memory' heap' time')
             Γ Σ Σ'
  | step_seq_nonstop:
      forall pc pc' memory memory' heap heap' c1 c1' c2 time time' Γ Σ Σ',
        step (Config c1 pc memory heap time)
             (Config c1' pc' memory' heap' time')
             Γ Σ Σ' ->
        c1' <> Stop ->
        c1' <> TimeOut ->
        sem_step (Config (Seq c1 c2) pc memory heap time)
             (Config (Seq c1' c2) pc' memory' heap' time')
             Γ Σ Σ'
  | step_time:
      forall pc memory heap time var Γ Σ,
        sem_step (Config (Time var) pc memory heap time)
             (Config Stop pc (extend_memory var (ValNum time) memory) heap (S time))
             Γ Σ Σ
  | step_new:
      forall pc memory heap time e e_init ℓ_p ℓ var n v l Γ Σ τ H1 H2,
        eval memory e = Some (ValNum n) ->
        eval memory e_init = Some v ->
        Γ var = Some (SecType (Array τ ℓ_p) ℓ) ->
        sem_step (Config (NewArr var ℓ_p e e_init) pc memory heap time)
             (Config Stop pc
                     (extend_memory var (ValLoc l) memory)
                     (heap [l → (n × v, ℓ_p), H1, H2]) (S time))
             Γ Σ (extend_stenv l τ Σ)
  | step_get:
      forall pc memory heap time x y e l n v length Γ Σ t μ ℓ,
        memory_lookup memory y = Some (ValLoc l) ->
        eval memory e = Some (ValNum n) ->
        length_of l heap = Some length ->
        0 <= n ->
        n < length ->
        heap_lookup l heap = Some (ℓ, μ) ->
        lookup μ n = Some v ->
        Γ x = Some t ->
        sem_step (Config (GetArr x y e) pc memory heap time)
             (Config Stop pc (extend_memory x v memory) heap (S time))
             Γ Σ Σ
  | step_set:
      forall pc memory heap time x e1 e2 l n v length Γ Σ,
        memory_lookup memory x = Some (ValLoc l) ->
        eval memory e1 = Some (ValNum n) ->
        length_of l heap = Some length ->
        0 <= n ->
        n < length ->
        eval memory e2 = Some v ->
        sem_step (Config (SetArr x e1 e2) pc memory heap time)
             (Config Stop pc memory (update_heap l n v heap) (S time))
             Γ Σ Σ
  | step_at:
      forall pc memory heap time level c e n Γ Σ,
        eval memory e = Some (ValNum n) ->
        sem_step (Config (At level e c) pc memory heap time)
             (Config (Seq c (BackAt pc (n + time))) level memory heap (S time))
             Γ Σ Σ
  | step_backat_wait:
      forall pc memory heap time level n Γ Σ,
        time < n ->
        sem_step (Config (BackAt level n) pc memory heap time)
                 (Config (BackAt level n) pc memory heap (S time))
                 Γ Σ Σ
  | step_backat_progress:
      forall pc memory heap time level Γ Σ,
        sem_step (Config (BackAt level time) pc memory heap time)
                 (Config Stop level memory heap (S time)) Γ Σ Σ
  | step_timeout:
      forall pc memory heap time level n Γ Σ,
        time > n ->
        sem_step (Config (BackAt level n) pc memory heap time)
                 (Config TimeOut level memory heap (S time))
                 Γ Σ Σ
  with step : config -> config -> tenv -> stenv -> stenv -> Prop :=
       | SemStep:
           forall c c' pc pc' m m' h h' t t' Γ Σ Σ',
             sem_step (Config c pc m h t) (Config c' pc' m' h' t') Γ Σ Σ' ->
             step (Config c pc m h t) (Config c' pc' m' h' t') Γ Σ Σ'
       | GCStep:
           forall c c' pc pc' m m' h h' t t' Γ Σ Σ',
             gc_step (Config c pc m h t) (Config c' pc' m' h' t') Γ Σ Σ' ->
             step (Config c pc m h t) (Config c' pc' m' h' t') Γ Σ Σ'.
  Hint Constructors step.
  Hint Constructors sem_step.
  Hint Constructors gc_step.

  Scheme sem_step_mut := Induction for sem_step Sort Prop
                         with step_mut := Induction for step Sort Prop.

  Derive Dependent Inversion sem_step_inv with
  (forall cfg1 cfg2 Γ Σ1 Σ2,
      sem_step cfg1 cfg2 Γ Σ1 Σ2) Sort Prop.
  
  Notation "cfg1 '⇒' '(' Γ ',' Σ ',' Σ2 ')' cfg2" := (step cfg1 cfg2 Γ Σ Σ2)
                                                       (at level 10, no associativity).
  
  Inductive stepmany: config -> config -> tenv -> stenv -> stenv -> Prop :=
  | StepMany0: forall cfg1 cfg2 Γ Σ, cfg1 = cfg2 -> stepmany cfg1 cfg2 Γ Σ Σ
  | StepManyN:
      forall cfg1 cfg cfg2 Γ Σ Σ' Σ'',
        step cfg1 cfg Γ Σ Σ' -> stepmany cfg cfg2 Γ Σ' Σ'' ->
        stepmany cfg1 cfg2 Γ Σ Σ''.
  Hint Constructors stepmany.

  
  Notation "cfg1 '⇒' '*' '(' Γ ',' Σ ',' Σ2 ')' cfg2" := (stepmany cfg1 cfg2 Γ Σ Σ2)
                                                         (at level 10, no associativity).

  Ltac invert_sem_step:=
    match goal with [ H : sem_step _ _ _ _ _ |-  _ ] => inverts H end.

  Ltac invert_gc_step:=
    match goal with [ H : gc_step _ _ _ _ _ |-  _ ] => inverts H end.
  
  Ltac invert_step:=
    match goal with [ H : _ ⇒ (_, _, _) _ |-  _ ] => inverts H; [> invert_sem_step | invert_gc_step] end.

  Ltac inverts_step:=
    match goal with [ H : _ ⇒ (_, _, _) _ |-  _ ] => inverts H end.

  Definition dangling_pointer_free (m: Memory) (h: Heap) :=
    forall loc, reach m h loc -> exists ℓ μ, heap_lookup loc h = Some (ℓ, μ).
  Hint Unfold dangling_pointer_free.
  
  Ltac invert_dang_free :=
    match goal with
      [H: dangling_pointer_free _ _ |- _] => unfold dangling_pointer_free in H
    end.
  
  Definition consistent (m: Memory) (h: Heap) (tenv : tenv) (stenv : stenv) :=
    (forall x t ε ℓ loc,
        tenv x = Some (SecType (Array t ℓ) ε) ->
        memory_lookup m x = Some (ValLoc loc) ->
        stenv loc = Some t) /\
    (forall loc1 loc2 t ℓ ε n μ l,
        reach m h loc1 ->
        stenv loc1 = Some (SecType (Array t ℓ) ε) ->
        heap_lookup loc1 h = Some (l, μ) ->
        lookup μ n = Some (ValLoc loc2) ->
        stenv loc2 = Some t).
  Hint Unfold consistent.

  Ltac destruct_consistent :=
    match goal with
      [H: consistent _ _ _ _ |- _] => destruct H
    end.
  
  Lemma consistent_proj1:
    forall m h Γ Σ x t ε ℓ loc,
      consistent m h Γ Σ ->
      Γ x = Some (SecType (Array t ℓ) ε) ->
      memory_lookup m x = Some (ValLoc loc) ->
      Σ loc = Some t.
  Proof.
    intros.
    destruct_consistent; eauto.
  Qed.
  Hint Resolve consistent_proj1.

  Lemma consistent_proj2:
    forall m h Γ Σ loc1 loc2 t ℓ ε n μ l,
      consistent m h Γ Σ ->
      reach m h loc1 ->
      Σ loc1 = Some (SecType (Array t ℓ) ε) ->
      heap_lookup loc1 h = Some (l, μ) ->
      lookup μ n = Some (ValLoc loc2) ->
      Σ loc2 = Some t.
  Proof.
    intros.
    destruct_consistent; eauto.
  Qed.
  Hint Resolve consistent_proj2.
  

  Ltac invert_reach :=
    match goal with
      [H: reach _ _ _ |- _] => inverts H
    end.

  Inductive idx_reach_from : id -> Memory -> Heap -> loc -> nat -> Prop :=
  | reach_from_mem:
      forall m h x loc,
        memory_lookup m x = Some (ValLoc loc) -> idx_reach_from x m h loc 0
  | reach_from_heap:
      forall m h x loc loc' ℓ μ n k,
        idx_reach_from x m h loc k ->
        heap_lookup loc h = Some (ℓ, μ) ->
        lookup μ n = Some (ValLoc loc') ->
        idx_reach_from x m h loc' (S k).
  Hint Constructors idx_reach_from.

  Definition reach_from x m h loc := exists k, idx_reach_from x m h loc k.
  Hint Unfold reach_from.
  
  Lemma reach_from_extend_with_num:
    forall x i m h loc n,
      reach_from x (extend_memory i (ValNum n) m) h loc ->
      reach_from x m h loc.
  Proof.
    intros.
    unfold reach_from in *.
    super_destruct.
    revert loc H.
    induction k; intros.
    - inverts H.
      destruct (decide (i = x)); subst.
      + rewrite -> extend_memory_lookup_eq in *.
        discriminate.
      + rewrite -> extend_memory_lookup_neq in * by solve[eauto].
        eauto.
    - inverts H.
      specialize (IHk loc0 H1).
      super_destruct.
      exists (S k0); eauto.
  Qed.
  Hint Resolve reach_from_extend_with_num.

  Lemma reach_from_implies_reach:
    forall x m h loc,
      reach_from x m h loc ->
      reach m h loc.
  Proof.
    intros.
    unfolds in H.
    super_destruct.
    dependent induction H; eauto.
  Qed.
  Hint Resolve reach_from_implies_reach.

  Lemma reach_implies_reach_from:
    forall m h loc,
      reach m h loc ->
      exists x,
        reach_from x m h loc.
  Proof.
    intros.
    unfold reach_from.
    dependent induction H; eauto.
    destruct_exists; eauto.
  Qed.
  Hint Resolve reach_implies_reach_from.
  
  Lemma reach_extend_with_num:
    forall i m h loc n,
      reach (extend_memory i (ValNum n) m) h loc ->
      reach m h loc.
  Proof.
    intros.
    _apply reach_implies_reach_from in *.
    super_destruct.
    eapply reach_from_implies_reach; eauto.
  Qed.
  
  Lemma reach_from_extend:
    forall x y z loc1 loc2 m h,
      reach_from x (extend_memory y (ValLoc loc1) m) h loc2 ->
      reach_from z m h loc1 ->
      reach_from x m h loc2 \/ reach_from z m h loc2.
  Proof.
    intros.
    unfold reach_from in * |-.
    super_destruct.
    revert loc2 H.
    induction k0; intros.
    - inverts H.
      destruct (decide (x = y)); subst.
      + rewrite -> extend_memory_lookup_eq in *.
        rewrite_inj.
        eauto.
      + rewrite -> extend_memory_lookup_neq in * by solve[eauto].
        eauto.
    - inverts H.
      specialize (IHk0 loc H2).
      super_destruct.
      unfold reach_from in * |-.
      super_destruct.
      destruct IHk0; super_destruct.
      + left.
        unfolds.
        exists (S k1).
        eauto.
      + right.
        unfolds.
        exists (S k1).
        eauto.
  Qed.

  Lemma reach_extend:
    forall x loc1 loc2 m h,
      reach (extend_memory x (ValLoc loc1) m) h loc2 ->
      reach m h loc1 ->
      reach m h loc2.
  Proof.
    intros.
    _apply reach_implies_reach_from in *.
    super_destruct.
    assert (reach_from x1 m h loc2 \/ reach_from x0 m h loc2) by eauto using reach_from_extend.
    destruct H1;
      eapply reach_from_implies_reach; eauto.
  Qed.
  Hint Resolve reach_extend.
  
  Lemma reach_extend_implies_reach_if:
    forall m h loc1 loc2 x v n l H1 H2,
      (forall loc', v = ValLoc loc' -> reach m h loc') ->
      reach (extend_memory x (ValLoc loc1) m) (h [loc1 → (n × v, l), H1, H2]) loc2 ->
      loc2 <> loc1 ->
      reach m h loc2.
  Proof.
    intros.
    dependent induction H0.
    - destruct (decide (x = x0)); subst.
      + rewrite -> extend_memory_lookup_eq in *.
        rewrite_inj.
        exfalso; eauto.
      + rewrite -> extend_memory_lookup_neq in * by solve[eauto].
        eauto.
    - destruct (decide (loc = loc1)); subst.
      + apply_heap_lookup_extend_eq.
        super_destruct.
        rewrite_inj.
        assert (v = ValLoc loc').
        {
          specialize (H7 n0).
          rewrite_inj.
          reflexivity.
        }
        subst.
        eauto.
      + rewrite -> heap_lookup_extend_neq in * by solve[eauto].
        assert (reach m h loc) by eauto.
        eauto.
        Unshelve.
        * eauto.
        * constructor; eauto 2.
  Qed.
  Hint Resolve reach_extend_implies_reach_if.

  Definition lookup_in_bounds (m: Memory) (h: Heap) :=
    forall loc n len ℓ μ,
      reach m h loc ->
      length_of loc h = Some len ->
      0 <= n ->
      n < len ->
      heap_lookup loc h = Some (ℓ, μ) ->
      exists v, lookup μ n = Some v.
  Hint Unfold lookup_in_bounds.

  Definition heap_level_bound (Γ : tenv) (m : Memory) (h : Heap) (Σ : stenv) :=
    (forall x s loc l1 l2 ε μ,
        Γ x = Some (SecType (Array s l1) ε) ->
        memory_lookup m x = Some (ValLoc loc) ->
        heap_lookup loc h = Some (l2, μ) ->
        l1 = l2)
    /\
    (forall n s l ℓ ℓ' μ ν loc loc' ℓ_p ι,
        reach m h loc ->
        Σ loc = Some (SecType (Array s ℓ_p) (l, ι)) ->
        heap_lookup loc h = Some (ℓ, μ) ->
        lookup μ n = Some (ValLoc loc') ->
        heap_lookup loc' h = Some (ℓ', ν) ->
        ℓ' = ℓ_p)
    /\
    (forall loc1 loc2 ℓ1 ℓ2 μ ν n,
        reach m h loc1 ->
        heap_lookup loc1 h = Some (ℓ1, μ) ->
        lookup μ n = Some (ValLoc loc2) ->
        heap_lookup loc2 h = Some (ℓ2, ν) ->
        ℓ1 ⊑ ℓ2).
  Hint Unfold heap_level_bound.

  Lemma heap_level_bound_proj1:
    forall Γ m h Σ x s loc l1 l2 ε μ,
      heap_level_bound Γ m h Σ ->
      Γ x = Some (SecType (Array s l1) ε) ->
      memory_lookup m x = Some (ValLoc loc) ->
      heap_lookup loc h = Some (l2, μ) ->
      l1 = l2.
  Proof.
    intros.
    destructs H; eauto.
  Qed.
  Hint Resolve heap_level_bound_proj1.

  Lemma heap_level_bound_proj2:
    forall Γ m h Σ n s l ℓ ℓ' μ ν loc loc' ℓ_p ι,
      heap_level_bound Γ m h Σ ->
      reach m h loc ->
      Σ loc = Some (SecType (Array s ℓ_p) (l, ι)) ->
      heap_lookup loc h = Some (ℓ, μ) ->
      lookup μ n = Some (ValLoc loc') ->
      heap_lookup loc' h = Some (ℓ', ν) ->
      ℓ' = ℓ_p.
  Proof.
    intros.
    destructs H; eauto.
  Qed.
  Hint Resolve heap_level_bound_proj2. 

Lemma heap_level_bound_proj3:
  forall Γ m h Σ loc1 loc2 ℓ1 ℓ2 μ ν n,
    heap_level_bound Γ m h Σ ->
    reach m h loc1 ->
    heap_lookup loc1 h = Some (ℓ1, μ) ->
    lookup μ n = Some (ValLoc loc2) ->
    heap_lookup loc2 h = Some (ℓ2, ν) ->
    ℓ1 ⊑ ℓ2.
  Proof.
    intros.
    destructs H; eauto.
  Qed.
  Hint Resolve heap_level_bound_proj3.
  
  Inductive wellformed: tenv -> stenv -> config -> Prop :=
  | Wellformed:
      forall tenv stenv c pc m h t,
        wf_tenv tenv m ->
        wf_stenv stenv h ->
        consistent m h tenv stenv ->
        (c <> Stop -> c <> TimeOut -> wt tenv pc c) ->
        dangling_pointer_free m h ->
        lookup_in_bounds m h ->
        heap_level_bound tenv m h stenv ->
        wellformed tenv stenv (Config c pc m h t).
  Hint Constructors wellformed.

  Inductive wellformed_aux: tenv -> stenv -> config -> level_proj1 -> Prop :=
  | WellformedAux:
      forall pc' tenv stenv c pc m h t,
        wf_tenv tenv m ->
        wf_stenv stenv h ->
        consistent m h tenv stenv ->
        (c <> Stop -> c <> TimeOut -> wt_aux tenv pc c pc') ->
        dangling_pointer_free m h ->
        lookup_in_bounds m h ->
        heap_level_bound tenv m h stenv ->
        wellformed_aux tenv stenv (Config c pc m h t) pc'.
  Hint Constructors wellformed_aux.

  Notation "'={' Γ ',' Σ '⊢' cfg ':' pc '}='" :=
    (wellformed_aux Γ Σ cfg pc) (at level 40).

  Ltac invert_wf_aux :=
    match goal with
      [H: context[wellformed_aux] |- _] => inverts H
    end.

  Lemma wt_int_lookup_is_num:
    forall tenv stenv m h l n x v ε1 ε2 ℓ l1 μ,
      wf_tenv tenv m ->
      wf_stenv stenv h ->
      consistent m h tenv stenv ->
      tenv x = Some (SecType (Array (SecType Int ε1) ℓ) ε2) ->
      dangling_pointer_free m h ->
      reach_from x m h l ->
      heap_lookup l h = Some (l1, μ) ->
      lookup μ n = Some v ->
      exists n0, v = ValNum n0.
  Proof.
    intros.
    revert dependent l1.
    revert dependent μ.
    revert dependent v.
    revert dependent n.
    unfold reach_from in *.
    super_destruct.
    dependent induction H4; intros.
    - destruct (heap_lookup loc h) eqn:H_heap_lookup.
      + injects.
        destruct_consistent.
        eauto.
      + congruence.
    - do 5 specialize_gen.
      specialize (IHidx_reach_from n (ValLoc loc') μ).
      specialize_gen.
      specialize (IHidx_reach_from ℓ0 H5).
      super_destruct.
      discriminate.
  Qed.
  Hint Resolve wt_int_lookup_is_num.
  
  Lemma wt_array_lookup_is_loc:
    forall tenv stenv m h x t n ε1 ε2 ℓ1 ℓ2 loc v ℓ μ,
      wf_tenv tenv m ->
      wf_stenv stenv h ->
      consistent m h tenv stenv ->
      tenv x = Some (SecType (Array (SecType (Array t ℓ1) ε1) ℓ2) ε2) ->
      dangling_pointer_free m h ->
      memory_lookup m x = Some (ValLoc loc) ->
      heap_lookup loc h = Some (ℓ, μ) ->
      lookup μ n = Some v ->
      exists loc', v = ValLoc loc'.
  Proof.
    intros.
    destruct (heap_lookup loc h) eqn:H_heap_lookup.

    (* heap_lookup loc0 h is Some *)
    super_destruct.

    injects.
    eapply H0; eauto 2.
    destruct_consistent; eauto.

    super_destruct; congruence.
  Qed.
  Hint Resolve wt_array_lookup_is_loc.

  Lemma wellformed_if_1:
    forall Γ Σ e c1 c2 pc m h t pc',
      wellformed_aux Γ Σ ⟨If e c1 c2, pc, m, h, t⟩ pc' ->
      wellformed_aux Γ Σ ⟨c1, pc, m, h, t⟩ pc'.
  Proof.
    intros.
    inverts H.
    do 2 specialize_gen.
    invert_wt_cmd.
    apply WellformedAux; eauto.
  Qed.
  Hint Resolve wellformed_if_1.

  Lemma wellformed_if_2:
    forall Γ Σ e c1 c2 pc m h t pc',
      wellformed_aux Γ Σ ⟨If e c1 c2, pc, m, h, t⟩ pc' ->
      wellformed_aux Γ Σ ⟨c2, pc, m, h, t⟩ pc'.
  Proof.
    intros.
    inverts H.
    do 2 specialize_gen.
    invert_wt_cmd.
    apply WellformedAux; eauto.
  Qed.
  Hint Resolve wellformed_if_2.

  Lemma wf_seq1:
    forall Γ Σ c1 c2 pc m h t pc',
      wellformed_aux Γ Σ ⟨c1 ;; c2, pc, m, h, t ⟩ pc' ->
      exists pc'',
        wellformed_aux Γ Σ ⟨c1, pc, m, h, t ⟩ pc''.
  Proof.
    intros.
    invert_wf_aux.
    do 2 specialize_gen.
    invert_wt_cmd.
    exists pc'0.
    apply WellformedAux; eauto.
  Qed.
  Hint Resolve wf_seq1.

  Lemma wf_seq2:
    forall Γ Σ c1 c2 pc m h t pc',
      wellformed_aux Γ Σ ⟨c1 ;; c2, pc, m, h, t ⟩ pc' ->
      exists pc'' Σ' m' h' t',
        wellformed_aux Γ Σ' ⟨c2, pc'', m', h', t'⟩ pc'.
  Proof.
    intros.
    invert_wf_aux.
    do 2 specialize_gen.
    invert_wt_cmd.
    exists pc'0.
    do 4 eexists; eauto.

    Unshelve.
    eauto.
  Qed.
  Hint Resolve wf_seq2.

  Lemma wf_seq:
    forall Γ Σ c1 c2 pc m h t pc',
      wellformed_aux Γ Σ ⟨c1 ;; c2, pc, m, h, t ⟩ pc' ->
      exists pc'' Σ' m' h' t',
        wellformed_aux Γ Σ ⟨c1, pc, m, h, t ⟩ pc'' /\
        wellformed_aux Γ Σ' ⟨c2, pc'', m', h', t'⟩ pc'.
  Proof.
    intros.
    inverts H.
    do 2 specialize_gen.
    invert_wt_cmd.
    exists pc'0.
    do 4 eexists; eauto.

    Unshelve.
    eauto.
  Qed.
  Hint Resolve wf_seq.
  
  Lemma deterministic_wellformedness:
    forall Γ Σ1 Σ2 c pc m h t s w g pc1 pc2,
      c <> Stop ->
      c <> TimeOut ->
      wellformed_aux Γ Σ1 ⟨c, pc, m, h, t⟩ pc1 ->
      wellformed_aux Γ Σ2 ⟨c, pc, s, w, g⟩ pc2 ->
      pc1 = pc2.
  Proof.
    intros.
    do 2 invert_wf_aux.
    repeat specialize_gen.
    eauto.
  Qed.
  Hint Resolve deterministic_wellformedness.

  Lemma step_if_does_not_step_to_stop:
    forall Γ Σ Σ' e c1 c2 pc m h t  m' h' t' pc' pc'',
      wellformed_aux Γ Σ ⟨If e c1 c2, pc, m, h, t⟩ pc'' ->
      ⟨If e c1 c2, pc, m, h, t⟩ ⇒ (Γ, Σ, Σ') ⟨Stop, pc', m', h', t'⟩ -> False.
  Proof.
    intros.
    invert_wf_aux.
    do 2 specialize_gen.
    invert_wt_cmd.
    invert_step.
    invert_wt_cmd.
    invert_wt_cmd.
  Qed.  
  Hint Resolve step_if_does_not_step_to_stop.

  Lemma wellformed_timeless:
    forall Γ Σ c pc m h t g pc',
      wellformed_aux Γ Σ ⟨c, pc, m, h, t⟩ pc' ->
      wellformed_aux Γ Σ ⟨c, pc, m, h, g⟩ pc'.
  Proof.
    intros.
    invert_wf_aux.
    eauto.
  Qed.
  Hint Immediate wellformed_timeless.

  Definition gc_occurred (c1 c2 : cmd) pc1 pc2 m1 m2 h1 h2 t1 t2 (Σ Σ' : stenv) :=
    c1 = c2 /\ c1 <> Stop /\ c1 <> TimeOut /\ m1 = m2 /\ pc1 = pc2 /\ Σ = Σ' /\
    exists h1_2 h1_1_pc h1_1_not_pc δ H1 H2 H3,
      h1 = [h2 ⊎ h1_2, H1] /\
      disjoint h2 h1_2 /\
      (forall loc ℓ μ, heap_lookup loc h1_2 = Some (ℓ, μ) -> ~ reach m1 h1 loc) /\
      levels_satisfy h1_2 (eq pc1) /\
      h2 = [h1_1_pc ⊎ h1_1_not_pc, H2] /\
      levels_satisfy h1_1_pc (eq pc1) /\
      levels_satisfy h1_1_not_pc (compose not (eq pc1)) /\
      gc m1 ([h1_1_pc ⊎ h1_2, H3]) δ h1_1_pc /\
      t2 = t1 + δ.

  Lemma gc_occurred_implies_subset_heap:
    forall c1 c2 pc1 pc2 m1 m2 h1 h2 t1 t2 Γ Σ1 Σ2 loc ℓ μ,
      step ⟨c1, pc1, m1, h1, t1⟩ ⟨c2, pc2, m2, h2, t2⟩ Γ Σ1 Σ2 ->
      gc_occurred c1 c2 pc1 pc2 m1 m2 h1 h2 t1 t2 Σ1 Σ2 ->
      heap_lookup loc h2 = Some (ℓ, μ) ->
      heap_lookup loc h1 = Some (ℓ, μ).
  Proof.
    intros.
    unfold gc_occurred in *.
    destruct H0.
    destruct H2.
    destruct H3.
    destruct_exists.
    super_destruct.
    subst.
    eauto using disjoint_union_heap_lookup.
  Qed.
    
  Lemma stop_takes_no_step:
    forall c Γ Σ Σ' pc1 pc2 m1 m2 h1 h2 t1 t2,
      step (Config Stop pc1 m1 h1 t1) (Config c pc2 m2 h2 t2) Γ Σ Σ' ->
      False.
  Proof.
    intros.
    invert_step.
    exfalso; eauto.
  Qed.

  Lemma timeout_takes_no_step:
    forall c Γ Σ Σ' pc1 pc2 m1 m2 h1 h2 t1 t2,
      step (Config TimeOut pc1 m1 h1 t1) (Config c pc2 m2 h2 t2) Γ Σ Σ' ->
      False.
  Proof.
    intros.
    invert_step.
    exfalso; eauto.
  Qed.

  Lemma wf_seq_implies_wf_head:
    forall tenv stenv c1 c2 pc m h t pc',
      wellformed_aux tenv stenv (Config (c1;; c2) pc m h t) pc' ->
      exists pc'',
        wellformed_aux tenv stenv (Config c1 pc m h t) pc''.
  Proof.
    intros.
    inversion H; subst.
    do 2 specialize_gen.
    invert_wt_cmd.
    exists pc'0.
    apply (WellformedAux pc'0); auto.
  Qed.

  Lemma wt_aux_soundness:
    forall Γ Σ Σ' pc c pc'' m h t pc' m' h' t',
      wt_aux Γ pc c pc'' ->
      step (Config c pc m h t) (Config Stop pc' m' h' t') Γ Σ Σ' ->
      pc' = pc''.
  Proof.
    intros Γ Σ Σ' pc c.
    revert pc.
    induction c; intros; subst ; try (invert_step; invert_wt_cmd; reflexivity).
    rename H into H_wt.
    rename H0 into H_step.

    invert_step; subst.
    invert_wt_cmd; subst.
    invert_wt_cmd.
    invert_wt_cmd.
    match goal with
      [H: wt_aux _ _ Stop _ |- _] =>
      inverts H
    end.
    assert (pc' = pc') by eauto using IHc1; subst.
    invert_wt_cmd.

    invert_step.
    invert_wt_cmd.
  Qed.

  Lemma location_is_from_lookup:
    forall tenv m e l loc,
      wf_tenv tenv m ->
      expr_has_type tenv e l ->
      eval m e = Some (ValLoc loc) ->
      exists x, e = Var x.
  Proof.
    intros.
    destruct e; subst.
    - unfold eval in H1.
      discriminate.
    - eauto.
    - invert_wt_expr.
      rewrite -> about_eval in *.
      repeat break_match; congruence.
  Qed.

End Imperative.
