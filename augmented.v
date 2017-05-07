Require Import id_and_loc mmemory mlattice mimperative types language LibTactics tactics Coq.Program.Tactics Coq.Program.Equality.

Module Augmented (L: Lattice) (M: Memory L).
  Module Imp := Imperative L M.
  Import Imp TDefs M T LatProp Lang L.
  
  Inductive event  :=
  | EmptyEvent : event
  | AssignEvent : level_proj1 -> id -> value -> event
  | NewEvent : level_proj1 -> id -> loc -> event
  | GetEvent : level_proj1 -> id -> id -> value -> event
  | SetEvent : level_proj1 -> level_proj1 -> id -> nat -> value -> event
  | TimeEvent : level_proj1 -> id -> nat -> event
  | RestoreEvent: level_proj1 -> nat -> event.
  Hint Constructors event.

  Lemma eq_event_dec:
    forall ev1 ev2 : event,
      {ev1 = ev2} + {ev1 <> ev2}.
  Proof.
    repeat decide equality.
  Defined.

  Definition onvals (φ: loc -> option loc) (v: value) :=
    match v with
    | ValNum n => Some (ValNum n)
    | ValLoc l =>
      match φ l with
      | Some l' => Some (ValLoc l')
      | None => None
      end
    end.
  Hint Unfold onvals.
  
  Inductive iso_events: (loc -> option loc) -> event -> event -> Prop :=
  | IsoEventEmpty:
      forall φ,
        iso_events φ EmptyEvent EmptyEvent
  | IsoEventAssign:
      forall φ ℓ x v1 v2,
        onvals φ v1 = Some v2 ->
        iso_events φ (AssignEvent ℓ x v1) (AssignEvent ℓ x v2)
  | IsoEventNew:
      forall φ x ℓ l1 l2 l,
        (φ l1 = Some l -> l = l2) ->
        iso_events φ (NewEvent ℓ x l1) (NewEvent ℓ x l2)
  | IsoEventGet:
      forall φ ℓ_x x y v1 v2,
        onvals φ v1 = Some v2 ->
        iso_events φ (GetEvent ℓ_x x y v1) (GetEvent ℓ_x x y v2)
  | IsoEventSet:
      forall φ ℓ ℓ_x x n v1 v2,
        onvals φ v1 = Some v2 ->
        iso_events φ (SetEvent ℓ ℓ_x x n v1) (SetEvent ℓ ℓ_x x n v2)
  | IsoEventTime:
      forall φ ℓ x n,
        iso_events φ (TimeEvent ℓ x n) (TimeEvent ℓ x n)
  | IsoEventRestore:
      forall ℓ n φ,
        iso_events φ (RestoreEvent ℓ n) (RestoreEvent ℓ n).
  Hint Constructors iso_events.

Inductive event_sem_step : config -> config -> tenv -> stenv -> stenv -> event -> Prop :=
 | event_sem_step_skip:
     forall Γ Σ Σ' pc m h t t',
       sem_step (Config Skip pc m h t) (Config Stop pc m h t') Γ Σ Σ' ->
       event_sem_step (Config Skip pc m h t) (Config Stop pc m h t') Γ Σ Σ' EmptyEvent
 | event_sem_step_assign:
     forall Γ Σ Σ' pc m m' h x e v t t' τ ℓ ι,
       eval m e = Some v ->
       Γ x = Some (SecType τ (ℓ, ι)) ->
       sem_step (Config (Assign x e) pc m h t) (Config Stop pc m' h t') Γ Σ Σ' ->
       event_sem_step (Config (Assign x e) pc m h t) (Config Stop pc m' h t') Γ Σ Σ'
                  (AssignEvent ℓ x v)
 | event_sem_step_if:
     forall Γ Σ Σ' pc m h e c1 c2 c' t t',
       sem_step (Config (If e c1 c2) pc m h t) (Config c' pc m h t') Γ Σ Σ' ->
       event_sem_step (Config (If e c1 c2) pc m h t) (Config c' pc m h t') Γ Σ Σ'
                  EmptyEvent
 | event_sem_step_while:
     forall Γ Σ Σ' pc m h e c c' t t',
       sem_step (Config (While e c) pc m h t) (Config c' pc m h t') Γ Σ Σ' ->
       event_sem_step (Config (While e c) pc m h t) (Config c' pc m h t') Γ Σ Σ' EmptyEvent
 | event_sem_step_seq_nonstop:
     forall Γ Σ Σ' pc pc' m m' h h' c1 c2 c1' t t' ev,
       event_step (Config c1 pc m h t) (Config c1' pc' m' h' t') Γ Σ Σ' ev ->
       c1' <> Stop ->
       c1' <> TimeOut ->
       event_sem_step (Config (Seq c1 c2) pc m h t) (Config (Seq c1' c2) pc' m' h' t') Γ Σ Σ' ev
 | event_sem_step_seq_stop:
     forall Γ Σ Σ' pc pc' m m' h h' c1 c2 t t' ev,
       event_step (Config c1 pc m h t) (Config Stop pc' m' h' t') Γ Σ Σ' ev ->
       event_sem_step (Config (Seq c1 c2) pc m h t) (Config c2 pc' m' h' t') Γ Σ Σ' ev
 | event_sem_step_time:
     forall Γ Σ Σ' pc m m' h t t' x τ ℓ ι,
       Γ x = Some (SecType τ (ℓ, ι)) ->
       sem_step (Config (Time x) pc m h t) (Config Stop pc m' h t') Γ Σ Σ' ->
       event_sem_step (Config (Time x) pc m h t) (Config Stop pc m' h t') Γ Σ Σ'
                  (TimeEvent ℓ x t)
 | event_sem_step_new:
     forall Γ Σ Σ' pc m h t t' e e_init level x l τ ℓ h' ι,
       Γ x = Some (SecType τ (ℓ, ι)) ->
       sem_step (Config (NewArr x level e e_init) pc m h t)
            (Config Stop pc (extend_memory x (ValLoc l) m) h' t') Γ Σ Σ' ->
       event_sem_step (Config (NewArr x level e e_init) pc m h t)
                  (Config Stop pc (extend_memory x (ValLoc l) m) h' t') Γ Σ Σ'
                  (NewEvent ℓ x l)
 | event_sem_step_get:
     forall Γ Σ Σ' pc m m' h t t' x y e l n v τ_x ℓ_x τ_y ℓ_y ι μ ℓ,
       Γ x = Some (SecType τ_x (ℓ_x, ι)) ->
       Γ y = Some (SecType τ_y ℓ_y) ->
       memory_lookup m y = Some (ValLoc l) ->
       eval m e = Some (ValNum n) ->
       heap_lookup l h = Some (ℓ, μ) ->
       lookup μ n = Some v ->
       sem_step (Config (GetArr x y e) pc m h t) (Config Stop pc m' h t') Γ Σ Σ' ->
       event_sem_step (Config (GetArr x y e) pc m h t) (Config Stop pc m' h t') Γ Σ Σ'
                  (GetEvent ℓ_x x y v)
 | event_sem_step_set:
     forall Γ Σ Σ' pc m h h' t t' x e1 e2 l n v τ ℓ ι ℓ_p ℓ_x ι_x,
       memory_lookup m x = Some (ValLoc l) ->
       Γ x = Some (SecType (Array (SecType τ (ℓ, ι)) ℓ_p) (ℓ_x, ι_x)) ->
       eval m e1 = Some (ValNum n) ->
       eval m e2 = Some v ->
       sem_step (Config (SetArr x e1 e2) pc m h t) (Config Stop pc m h' t') Γ Σ Σ' ->
       event_sem_step (Config (SetArr x e1 e2) pc m h t)
                  (Config Stop pc m h' t') Γ Σ Σ' (SetEvent ℓ ℓ_x x n v)
 | event_sem_step_at:
     forall Γ Σ Σ' pc m h t t' level c c' e,
       sem_step (Config (At level e c) pc m h t) (Config c' level m h t') Γ Σ Σ' ->
       event_sem_step (Config (At level e c) pc m h t) (Config c' level m h t') Γ Σ Σ' EmptyEvent
 | event_sem_step_backat_wait:
     forall Γ Σ Σ' pc pc' m h t t' c' level n,
       t < n ->
       sem_step (Config (BackAt level n) pc m h t) (Config c' pc' m h t') Γ Σ Σ' ->
       event_sem_step (Config (BackAt level n) pc m h t) (Config c' pc' m h t') Γ Σ Σ' EmptyEvent
 | event_sem_step_backat_progress:
     forall Γ Σ Σ' pc pc' m h t t' c' level,
       sem_step (Config (BackAt level t) pc m h t) (Config c' pc' m h t') Γ Σ Σ' ->
       event_sem_step (Config (BackAt level t) pc m h t) (Config c' pc' m h t') Γ Σ Σ' (RestoreEvent pc' t)
 | event_sem_step_backat_timeout:
     forall Γ Σ Σ' pc pc' m h t t' c' level n,
       n < t ->
       sem_step (Config (BackAt level n) pc m h t) (Config c' pc' m h t') Γ Σ Σ' ->
       event_sem_step (Config (BackAt level n) pc m h t) (Config c' pc' m h t') Γ Σ Σ' (RestoreEvent pc' t)
with event_step: config -> config -> tenv -> stenv -> stenv -> event -> Prop :=
     | EventSemStep:
         forall c c' pc pc' m m' h h' t t' Γ Σ Σ' ev,
           event_sem_step (Config c pc m h t) (Config c' pc' m' h' t') Γ Σ Σ' ev ->
           event_step (Config c pc m h t) (Config c' pc' m' h' t') Γ Σ Σ' ev
     | EventGCStep:
           forall c c' pc pc' m m' h h' t t' Γ Σ Σ',
             gc_step (Config c pc m h t) (Config c' pc' m' h' t') Γ Σ Σ' ->
             event_step (Config c pc m h t) (Config c' pc' m' h' t') Γ Σ Σ' EmptyEvent.
Hint Constructors event_step.
Hint Constructors event_sem_step.

Scheme event_sem_step_mut := Induction for event_sem_step Sort Prop
                       with event_step_mut := Induction for event_step Sort Prop.

Notation "cfg '⇒' '[' evt ',' Γ ',' Σ ',' Σ2 ']' cfg'":=
  (event_step cfg cfg' Γ Σ Σ2 evt) (at level 0).

Ltac invert_event_sem_step:=
    match goal with [ H : event_sem_step _ _ _ _ _ _ |-  _ ] => inverts H end.
  
  Ltac invert_event_step:=
    match goal with [ H : _ ⇒ [_, _, _, _] _ |-  _ ] => inverts H; [> invert_event_sem_step | invert_gc_step] end.

  Ltac invert_wt_stop :=
    match goal with
      [H: wt_aux _ _ Stop _ |- _] => inverts H
    end.
  
Lemma event_step_if_does_not_step_to_stop:
  forall e c1 c2 pc m h t ev Γ Σ Σ' pc' m' h' t' pc'',
    wellformed_aux Γ Σ ⟨If e c1 c2, pc, m, h, t⟩ pc'' ->
    ⟨If e c1 c2, pc, m, h, t⟩ ⇒ [ev, Γ, Σ, Σ'] ⟨Stop, pc', m', h', t'⟩ -> False.
Proof.
  intros.
  invert_event_step.
  invert_sem_step.
  - invert_wf_aux.
    do 2 specialize_gen.
    invert_wt_cmd.
    invert_wt_stop.
  - invert_wf_aux.
    do 2 specialize_gen.
    invert_wt_cmd.
    invert_wt_stop.
Qed.
Hint Resolve event_step_if_does_not_step_to_stop.

Lemma if_event_step_properties:
  forall Γ Σ Σ' e c1 c2 pc m h t c' pc' m' h' t',
    ⟨If e c1 c2, pc, m, h, t⟩ ⇒ (Γ, Σ, Σ') ⟨c', pc', m', h', t'⟩ ->
    ((exists k, eval m e = Some (ValNum k) /\ k <> 0 /\ c' = c1) \/
     (eval m e = Some (ValNum 0) /\ c' = c2)) \/
    gc_occurred (If e c1 c2) c' pc pc' m m' h h' t t' Σ Σ'.
Proof.
  intros.
  invert_step.
  - left; right.
    eauto.
  - left; left.
    eauto.
  - right.
    unfolds.
    splits*.
    do 7 eexists.
    splits; reflexivity || eauto.
Qed.

Lemma if_does_not_have_fixed_points1:
    forall e c1 c2,
      If e c1 c2 <> c1.
  Proof.
    intros.
    constructors_dont_have_fixed_points c1.
  Qed.
  Hint Resolve if_does_not_have_fixed_points1.

  Lemma if_does_not_have_fixed_points2:
    forall e c1 c2,
      If e c1 c2 <> c2.
  Proof.
    intros.
    constructors_dont_have_fixed_points c2.
  Qed.
  Hint Resolve if_does_not_have_fixed_points2.

  Lemma seq_does_not_have_fixed_points1:
    forall c1 c2,
      c1 <> (c1;; c2).
  Proof.
    constructors_dont_have_fixed_points c1.
  Qed.
  Hint Resolve seq_does_not_have_fixed_points1.
  
  Lemma seq_does_not_have_fixed_points2:
    forall c1 c2,
      c2 <> (c1;; c2).
  Proof.
    constructors_dont_have_fixed_points c2.
  Qed.
  Hint Resolve seq_does_not_have_fixed_points2.

  Lemma event_step_adequacy:
    forall c c' pc pc' pc'' m m' h h' t t' Γ Σ Σ',
      wellformed_aux Γ Σ ⟨c, pc, m, h, t⟩ pc'' ->
      ⟨c, pc, m, h, t⟩ ⇒ (Γ, Σ, Σ') ⟨c', pc', m', h', t'⟩ ->
      exists ev,
        ⟨c, pc, m, h, t⟩ ⇒ [ev, Γ, Σ, Σ'] ⟨c', pc', m', h', t'⟩.
  Proof.
    intros.
    inverts H0; eauto.
    revert c' pc pc' pc'' m m' h h' t t' Σ Σ' H H14.
    induction c; intros; try solve[invert_sem_step; eauto].
    - invert_sem_step.
      invert_wf_aux.
      repeat specialize_gen.
      invert_wt_cmd.
      invert_lifted.
      destruct l2.
      eauto.
    - invert_sem_step.
      + assert (exists pc'', wellformed_aux Γ Σ ⟨c1, pc, m, h, t⟩ pc'') by eauto.
        super_destruct.
        inverts_step; eauto.
        * assert (exists ev, (⟨ c1, pc, m, h, t ⟩) ⇒ [ev, Γ, Σ, Σ'] (⟨ Stop, pc', m', h', t' ⟩)) by eauto 2.
          super_destruct.
          eauto.
      + assert (exists pc'', wellformed_aux Γ Σ ⟨c1, pc, m, h, t⟩ pc'') by eauto.
        inverts_step; eauto.
        super_destruct.
        assert (exists ev, (⟨ c1, pc, m, h, t ⟩) ⇒ [ev, Γ, Σ, Σ'] (⟨ c1', pc', m', h', t' ⟩)) by eauto 2.
        super_destruct.
        eauto.
    - invert_sem_step.
      destruct τ as [σ [ℓ' ι']].
      destruct ℓ.
      eauto.
    - invert_sem_step.
      invert_wf_aux.
      do 2 specialize_gen.
      invert_wt_cmd.
      invert_lifted.
      assert (exists τ, Γ i = Some τ) by eauto.
      super_destruct.
      destruct τ as [σ' [ℓ' ι']].
      assert (exists ℓ μ, heap_lookup l0 h = Some (ℓ, μ)) by eauto.
      super_destruct.
      assert (exists τ, Σ' l0 = Some τ) by eauto.
      super_destruct; subst.
      assert (Σ' l0 = Some (SecType σ l2)) by eauto 2.
      rewrite_inj.
      destruct l2.
      eauto.
    - invert_sem_step.
      invert_wf_aux.
      assert (exists τ, Γ i0 = Some τ) by eauto.
      super_destruct.
      destruct t0.
      destruct τ.
      destruct t1.
      eauto.
    - invert_sem_step.
      invert_wf_aux.
      do 2 specialize_gen.
      invert_wt_cmd.
      eauto.
  Qed.

End Augmented.
