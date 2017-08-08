Require Import Setoid Arith List Omega Coq.Program.Tactics decision types.
Require Import mlattice id_and_loc mmemory language LibTactics tactics.

Module TypeDefinitions (L: Lattice) (M: Memory L).
  Module MemProp := MemoryProperties L M.
  Import MemProp M T L Lang LatProp.
  
  Definition tenv  := id -> option sectype.
  
  Definition emptyTenv : tenv := fun _ => None.
  
  Inductive wf_type: level_proj1 -> sectype -> Prop :=
  | wf_type_int:
      forall ℓ l,
        wf_type ℓ (SecType Int l)
  | wf_type_array:
      forall ℓ l_p l_ref τ,
        wf_type l_p τ ->
        ℓ ⊑ l_p ->
        l_ref ⊑ l_p ->
        wf_type ℓ (SecType (Array τ l_p) (l_ref, ∘)).
  Hint Constructors wf_type.

  Ltac invert_wf_type :=
    match goal with
      [H: wf_type _ _ |- _] =>
      inverts H
    end.
  
  Definition wf_tenv (env : tenv) (m: Memory) :=
    (forall x lev v, memory_lookup m x = Some v ->
                env x = Some (SecType Int lev) ->
                exists n, v = ValNum n)
    /\
    (forall x lev t v l, memory_lookup m x = Some v ->
                    env x = Some (SecType (Array t l) lev) ->
                    exists loc, v = ValLoc loc) /\
    (forall τ x, env x = Some τ -> wf_type bot τ) /\
    (forall x v, memory_lookup m x = Some v ->
            exists t, env x = Some t).

  Lemma wf_tenv_proj1:
    forall Γ m x v lev,
      wf_tenv Γ m ->
      memory_lookup m x = Some v ->
      Γ x = Some (SecType Int lev) ->
      exists n, v = ValNum n.
  Proof.
    intros.
    edestruct H; eauto.
  Qed.
  Hint Resolve wf_tenv_proj1.

  Lemma wf_tenv_proj2:
    forall Γ m x lev t v l,
      wf_tenv Γ m ->
      memory_lookup m x = Some v ->
      Γ x = Some (SecType (Array t l) lev) ->
      exists loc, v = ValLoc loc.
  Proof.
    intros.
    edestruct H.
    super_destruct; eauto.
  Qed.
  Hint Resolve wf_tenv_proj2.
  
  Lemma wf_tenv_proj3:
    forall Γ m τ x,
      wf_tenv Γ m ->
      Γ x = Some τ ->
      wf_type bot τ.
  Proof.
    intros.
    edestruct H; eauto.
    super_destruct.
    eauto.
  Qed.
  Hint Resolve wf_tenv_proj3.

  Lemma wf_tenv_proj4:
    forall Γ m x v,
      wf_tenv Γ m ->
      memory_lookup m x = Some v ->
      exists t, Γ x = Some t.
  Proof.
    intros.
    edestruct H; eauto.
    super_destruct.
    eauto.
  Qed.
  Hint Resolve wf_tenv_proj4.

Definition wf_stenv (env : stenv) (h: Heap) :=
  (forall loc level' n v μ ℓ,
      env loc = Some (SecType Int level') ->
      heap_lookup loc h = Some (ℓ, μ) ->
      lookup μ n = Some v ->
      exists n', v = ValNum n') /\
  (forall loc t level' l n v ℓ μ,
      env loc = Some (SecType (Array t l) level') ->
      heap_lookup loc h = Some (ℓ, μ) ->
      lookup μ n = Some v ->
      exists loc', v = ValLoc loc') /\
  (forall loc τ, env loc = Some τ -> wf_type bot τ) /\
  (forall loc l μ,
      heap_lookup loc h = Some (l, μ) ->
      exists τ, env loc = Some τ).

Lemma wf_stenv_proj1:
  forall Σ loc level' v n h ℓ μ,
    wf_stenv Σ h ->
    Σ loc = Some (SecType Int level') ->
    heap_lookup loc h = Some (ℓ, μ) ->
    lookup μ n = Some v ->
    exists n', v = ValNum n'.
Proof.
  intros.
  edestruct H.
  super_destruct; subst.
  eauto.
Qed.
Hint Resolve wf_stenv_proj1.

Lemma wf_stenv_proj2:
  forall Σ loc t level' l n v h ℓ μ,
    wf_stenv Σ h ->
    Σ loc = Some (SecType (Array t l) level') ->
    heap_lookup loc h = Some (ℓ, μ) ->
    lookup μ n = Some v ->
    exists loc', v = ValLoc loc'.
Proof.
  intros.
  edestruct H.
  super_destruct; subst.
  eauto.
Qed.
Hint Resolve wf_stenv_proj2.

Lemma wf_stenv_proj3:
    forall Σ h τ loc,
      wf_stenv Σ h ->
      Σ loc = Some τ ->
      wf_type bot τ.
  Proof.
    intros.
    edestruct H.
    super_destruct.
    eauto.
  Qed.
  Hint Resolve wf_stenv_proj3.

  
Lemma wf_stenv_proj4:
    forall Σ h μ l loc,
      wf_stenv Σ h ->
      heap_lookup loc h = Some (l, μ) ->
      exists τ, Σ loc = Some τ.
  Proof.
    intros.
    edestruct H.
    super_destruct.
    eauto.
  Qed.
  Hint Resolve wf_stenv_proj4.
  
Definition extend_stenv (loc: loc) (t: sectype) (stenv: stenv) :=
  fun loc' => if decide (loc' = loc) then Some t else stenv loc'.  

Lemma extend_stenv_lookup_neq:
  forall loc1 loc2 τ Σ,
    loc1 <> loc2 ->
    extend_stenv loc1 τ Σ loc2 = Σ loc2.
Proof.
  intros.
  unfold extend_stenv in *.
  rewrite -> neq_loc in * by solve[eauto].
  reflexivity.
Qed.
Hint Resolve extend_stenv_lookup_neq.

Lemma extend_stenv_lookup_eq:
  forall loc τ Σ,
    extend_stenv loc τ Σ loc = Some τ.
Proof.
  intros.
  unfold extend_stenv in *.
  rewrite -> eq_loc in *.
  reflexivity.
Qed.
Hint Resolve extend_stenv_lookup_eq.

Inductive expr_has_type: tenv -> expr -> sectype -> Prop :=
| type_int:
    forall tenv n l,
      expr_has_type tenv (Const n) (SecType Int l)
| type_var:
    forall tenv x t,
      tenv x = Some t ->
      expr_has_type tenv (Var x) t
| type_op:
    forall tenv op e1 e2 l1 l2,
      expr_has_type tenv e1 (SecType Int l1) ->
      expr_has_type tenv e2 (SecType Int l2) ->
      expr_has_type tenv (BinOp op e1 e2) (SecType Int (ProdL.join l1 l2)).

Notation "'{{' Γ '⊢' e ':' τ '}}' " := (expr_has_type Γ e τ) (at level 0, Γ at level 50,
                                                              e at level 99).

Ltac invert_wt_expr :=
  match goal with [H: context[expr_has_type _ _ _] |- _ ] => inverts H end.


Lemma expr_type_is_wf:
  forall Γ m e τ,
    wf_tenv Γ m ->
    expr_has_type Γ e τ ->
    wf_type bot τ.
Proof.
  intros.
  revert τ H0.
  induction e; intros; inverts H0; eauto.
Qed.
Hint Resolve expr_type_is_wf.

Inductive typeflowsto: sectype -> sectype -> Prop :=
| TypeFlowsTo:
    forall t l1 l2,
      l1 ≼ l2 ->
      typeflowsto (SecType t l1) (SecType t l2).

Notation "τ1 '<:' τ2" := (typeflowsto τ1 τ2)  (at level 20).

Inductive lifted: sectype -> level -> sectype -> Prop :=
| Lifted:
    forall t1 l1 l2,
      lifted (SecType t1 l1) l2 (SecType t1 (l1 ⋎ l2)).

Definition raiseto τ ℓ :=
  match τ with
      (SecType base ℓ') => (SecType base (ℓ ⋎ ℓ'))
  end.

Notation " τ '^^' ℓ":= (raiseto τ ℓ) (at level 20).

Inductive contains_backat: cmd -> Prop :=
| ContainsBackAt:
    forall l n,
      contains_backat (BackAt l n)
| ContainsBackAtSeq_left:
    forall c1 c2,
      contains_backat c1 -> contains_backat (c1;; c2)
| ContainsBackAtSeq_right:
    forall c1 c2,
      contains_backat c2 -> contains_backat (c1;; c2)
| ContainsBackAtIf_1:
    forall e c1 c2,
      contains_backat c1 -> contains_backat (If e c1 c2)
| ContainsBackAtIf_2:
    forall e c1 c2,
      contains_backat c2 -> contains_backat (If e c1 c2)
| ContainsBackAtWhile:
    forall e c,
      contains_backat c -> contains_backat (While e c)
| ContainsBackAtAt:
    forall ℓ e c,
      contains_backat c -> contains_backat (At ℓ e c).
Hint Constructors contains_backat.

Inductive wt: tenv -> level_proj1 -> cmd -> Prop :=
| wt_skip:
    forall tenv pc,
      wt tenv pc Skip
| wt_assign:
    forall tenv pc x e ε σ tx,
      tenv x = Some tx ->
      expr_has_type tenv e (SecType σ ε) ->
      SecType σ (ε ⋎ (pc, ∘)) <: tx ->
      wt tenv pc (Assign x e)
| wt_if:
    forall tenv pc e c1 c2 ℓ,
      expr_has_type tenv e (SecType Int (ℓ, ∘)) ->
      ℓ ⊑ pc ->
      wt tenv pc c1 ->
      wt tenv pc c2 ->
      wt tenv pc (If e c1 c2)
| wt_while:
    forall tenv pc e c ℓ,
      expr_has_type tenv e (SecType Int (ℓ, ∘)) ->
      ℓ ⊑ pc ->
      wt tenv pc c ->
      wt tenv pc (While e c)
| wt_seq:
    forall tenv pc c1 c2,
      wt tenv pc c1 ->
      wt tenv pc c2 ->
      wt tenv pc (Seq c1 c2)
| wt_new:
    forall tenv pc x e_size e_init ℓ ℓ_x τ ℓ_size,
      expr_has_type tenv e_size (SecType Int (ℓ_size, ∘)) ->
      expr_has_type tenv e_init τ ->
      tenv x = Some (SecType (Array τ ℓ) (ℓ_x, ∘)) ->
      pc ⊔ ℓ_size ⊑ ℓ_x ->
      wt tenv pc (NewArr x ℓ e_size e_init)
| wt_set:
    forall tenv pc x e e_idx ε_x ε σ τ ε_idx ℓ,
      expr_has_type tenv e_idx (SecType Int ε_idx) ->
      expr_has_type tenv e (SecType σ ε) ->
      tenv x = Some (SecType (Array τ ℓ) ε_x) ->
      ε_idx ⋎ (pc, ∘) ≼ ε_x ->
      SecType σ (ε_x ⋎ ε) <: τ ->
      wt tenv pc (SetArr x e_idx e)
| wt_get:
    forall tenv pc x y e_idx σ ε ε_y tx ℓ ε_idx,
      expr_has_type tenv e_idx (SecType Int ε_idx) ->
      (pc, ∘) ⋎ ε_idx ≼ ε_y ->
      tenv x = Some tx ->
      tenv y = Some (SecType (Array (SecType σ ε) ℓ) ε_y) ->
      SecType σ (ε ⋎ ε_y) <: tx ->
      wt tenv pc (GetArr x y e_idx)
| wt_time:
    forall tenv pc x ℓ,
      tenv x = Some (SecType Int (ℓ, •)) ->
      pc ⊑ ℓ ->
      wt tenv pc (Time x)
| wt_at:
    forall tenv pc ℓ' ℓ e c,
      pc ⊑ ℓ ->
      ℓ' ⊑ pc ->
      expr_has_type tenv e (SecType Int (ℓ', ∘)) ->
      wt tenv ℓ c ->
      wt tenv pc (At ℓ e c).
Hint Constructors wt.

Inductive wt_aux : tenv -> level_proj1 -> cmd -> level_proj1 -> Prop :=
  | wt_aux_skip:
    forall tenv pc,
      wt_aux tenv pc Skip pc
| wt_aux_assign:
    forall tenv pc x e ε σ tx,
      tenv x = Some tx ->
      expr_has_type tenv e (SecType σ ε) ->
      SecType σ (ε ⋎ (pc, ∘)) <: tx ->
      wt_aux tenv pc (Assign x e) pc
| wt_aux_if:
    forall tenv pc pc' e c1 c2 ℓ,
      expr_has_type tenv e (SecType Int (ℓ, ∘)) ->
      ~ contains_backat c1 ->
      ~ contains_backat c2 ->
      ℓ ⊑ pc ->
      wt_aux tenv pc c1 pc' ->
      wt_aux tenv pc c2 pc' ->
      wt_aux tenv pc (If e c1 c2) pc'
| wt_aux_while:
    forall tenv pc e c ℓ,
      expr_has_type tenv e (SecType Int (ℓ, ∘)) ->
      ~ contains_backat c ->
      ℓ ⊑ pc ->
      wt_aux tenv pc c pc ->
      wt_aux tenv pc (While e c) pc
| wt_aux_seq:
    forall tenv pc1 pc2 pc' c1 c2,
      wt_aux tenv pc1 c1 pc' ->
      wt_aux tenv pc' c2 pc2 ->
      wt_aux tenv pc1 (Seq c1 c2) pc2
| wt_aux_new:
    forall tenv pc x e_size e_init ℓ ℓ_x τ ℓ_size,
      expr_has_type tenv e_size (SecType Int (ℓ_size, ∘)) ->
      expr_has_type tenv e_init τ ->
      tenv x = Some (SecType (Array τ ℓ) (ℓ_x, ∘)) ->
      pc ⊔ ℓ_size ⊑ ℓ_x ->
      wt_aux tenv pc (NewArr x ℓ e_size e_init) pc
| wt_aux_set:
    forall tenv pc x e e_idx ε_x ε σ τ ε_idx ℓ,
      expr_has_type tenv e_idx (SecType Int ε_idx) ->
      expr_has_type tenv e (SecType σ ε) ->
      tenv x = Some (SecType (Array τ ℓ) ε_x) ->
      ε_idx ⋎ (pc, ∘) ≼ ε_x ->
      SecType σ (ε_x ⋎ ε) <: τ ->
      wt_aux tenv pc (SetArr x e_idx e) pc
| wt_aux_get:
    forall tenv pc x y e_idx σ ε ε_y tx ℓ ε_idx,
      expr_has_type tenv e_idx (SecType Int ε_idx) ->
      (pc, ∘) ⋎ ε_idx ≼ ε_y ->
      tenv x = Some tx ->
      tenv y = Some (SecType (Array (SecType σ ε) ℓ) ε_y) ->
      SecType σ (ε ⋎ ε_y) <: tx ->
      wt_aux tenv pc (GetArr x y e_idx) pc
| wt_aux_time:
    forall tenv pc x ℓ,
      tenv x = Some (SecType Int (ℓ, •)) ->
      pc ⊑ ℓ ->
      wt_aux tenv pc (Time x) pc
| wt_aux_at:
    forall tenv pc ℓ ℓ' ℓ'' e c,
      pc ⊑ ℓ ->
      ℓ' ⊑ pc ->
      expr_has_type tenv e (SecType Int (ℓ', ∘)) ->
      ~ contains_backat c ->
      wt_aux tenv ℓ c ℓ'' ->
      wt_aux tenv pc (At ℓ e c) pc
| wt_aux_backat:
    forall tenv pc ℓ n,
      ℓ ⊑ pc ->
      wt_aux tenv pc (BackAt ℓ n) ℓ.
Hint Constructors wt_aux.

Notation "'-{' Γ ',' pc '⊢' c ':' pc' '}-'" := (wt_aux Γ pc c pc') (at level 40).

Notation "X ⊑ᵀ Y" := (typeflowsto X Y) (at level 70, no associativity).

Ltac invert_wt_cmd :=
  match goal with [H: context[wt_aux] |- _] => inverts H
  end.

Ltac invert_wt_stop :=
  match goal with
    [H: wt_aux _ _ Stop _ |- _] => inverts H
  end.

Ltac invert_lifted :=
  repeat match goal with
         | [H: context[lifted] |- _] => inverts H
         | [H: context[_ ⊑ᵀ _] |- _] => inverts H
         end.

Fixpoint eval memory e :=
  match e with
  | Const n => Some (ValNum n)
  | Var var => memory_lookup memory var
  | BinOp op e1 e2 =>
    let v1 := eval memory e1 in
    let v2 := eval memory e2 in
    match (v1, v2) with
    | (Some (ValNum n1), Some (ValNum n2)) =>
      match op with
      | Plus => Some (ValNum (n1 + n2))
      | Mult => Some (ValNum (n1 * n2))
      end
    | (_, _) => None
    end
  end.

Ltac invert_eval := match goal with
                    | [H: context[eval] |- _] => inverts H
                    end.

Lemma about_eval_var:
  forall m x v,
    memory_lookup m x = Some v -> eval m (Var x) = Some v.
Proof. eauto. Qed.
Hint Resolve about_eval_var.

Lemma about_type_var:
  forall Γ x τ,
    Γ x = Some τ -> {{ Γ ⊢ (Var x) : τ }}.
Proof.
  intros.
  apply type_var.
  assumption.
Qed.
Hint Resolve about_type_var.

Lemma unfold_eval_binop:
  forall m o e1 e2 v,
    eval m (BinOp o e1 e2) = Some v ->
    exists v1 v2,
      eval m e1 = Some v1 /\
      eval m e2 = Some v2.
Proof.
  intros.
  inversion H; subst.
  destruct (eval m e1); subst.
  destruct (eval m e2); subst.
  destruct v0; subst.
  destruct v1; subst.
  destruct o; subst.

  exists (ValNum n).
  exists (ValNum n0).
  split; reflexivity.

  exists (ValNum n).
  exists (ValNum n0).
  split; reflexivity.

  discriminate H1.
  discriminate H1.

  destruct v0; subst; discriminate H1.

  discriminate H1.
Qed.

Lemma about_eval:
  forall m o e1 e2,
    eval m (BinOp o e1 e2) =
    match eval m e1 with
    | None => None
    | Some v1 =>
      match v1 with
      | ValNum n1 =>
        match eval m e2 with
        | None => None
        | Some v2 =>
          match v2 with
          | ValNum n2 =>
            match o with
            | Plus => Some (ValNum (n1 + n2))
            | Mult => Some (ValNum (n1 * n2))
            end
          | ValLoc _ => None
          end
        end
      | ValLoc _ => None
      end
    end.
Proof.
  reflexivity.
Qed.

Lemma eval_binop_is_num:
  forall m o e1 e2 e,
    eval m (BinOp o e1 e2) = Some e ->
    exists n, e = ValNum n.
Proof.
  intros.
  rewrite -> about_eval in *.
  destruct (eval m e1) eqn:H_e1.
  - destruct (eval m e2) eqn:H_e2.
    + destruct v; destruct v0; destruct o; try (discriminate || (injects; eauto)).
    + destruct v; discriminate.
  - discriminate.
Qed.
Hint Resolve eval_binop_is_num.

Lemma wt_int_e_is_num:
  forall tenv m e v level,
    wf_tenv tenv m ->
    expr_has_type tenv e (SecType Int level) ->
    eval m e = Some v ->
    exists n, v = ValNum n.
Proof.
  intros tenv m e v level H_wf_tenv.
  revert v level.
  induction e; intros; eauto.
  - inversion H0; subst.
    eauto.
  - inversion H; subst.
    eauto.
Qed.
Hint Resolve wt_int_e_is_num.

Lemma wt_array_e_is_loc:
  forall tenv m e t ε ℓ v,
    wf_tenv tenv m ->
    expr_has_type tenv e (SecType (Array t ℓ) ε) ->
    eval m e = Some v ->
    exists loc, v = ValLoc loc.
Proof.
  intros.
  induction e; intros; inverts H0; eauto 2.
Qed.
Hint Resolve wt_array_e_is_loc.

Lemma wf_tenv_extend:
  forall tenv m x v t ε,
    wf_tenv tenv m ->
    tenv x = Some (SecType t ε) ->
    (t = Int -> exists n, v = ValNum n) ->
    (forall t' ε', t = Array t' ε' -> exists loc, v = ValLoc loc) ->
    wf_tenv tenv (extend_memory x v m).
Proof.
  intros.
  unfold wf_tenv in H.
  unfold wf_tenv.
  intros.
  splits; intros.
  
  (* Show: Wellformed wrt. numbers *)
  destruct (decide (x = x0)); subst.

  (*   x = x0 *)
  rewrite -> extend_memory_lookup_eq in *.
  rewrite_inj.
  eauto.
  
  (*   x <> x0 *)
  rewrite -> extend_memory_lookup_neq in * by solve[eauto].
  eauto.

  (* Show: Wellformed wrt. locations *)
  destruct (decide (x = x0)); subst.

  (*   x = x0 *)
  rewrite -> extend_memory_lookup_eq in *.
  rewrite_inj.
  eauto.

  (*   x <> x0 *)
  rewrite -> extend_memory_lookup_neq in * by solve[eauto].
  eauto.

  eauto.

  destruct (decide (x = x0)); subst.

  (* x = x0 *)
  rewrite -> extend_memory_lookup_eq in *.
  eauto.

  (* x <> x0 *)
  rewrite -> extend_memory_lookup_neq in * by solve[eauto 2].
  eauto.
Qed.

Ltac apply_heap_lookup_extend_eq :=
  match goal with
    [H: heap_lookup ?loc (extend_heap ?v ?loc ?l ?n ?h ?H1 ?H2) = Some (_, _) |- _] =>
    let H' := fresh in
    remember_simple (heap_lookup_extend_eq loc l n v h H1 H2) as H';
    decompose_ex H'; destruct H'
  end.

Lemma wf_stenv_extend:
  forall stenv loc ε ℓ n v h t H1 H2,
    wf_stenv stenv h ->
    (t = Int -> exists n0, v = ValNum n0) ->
    (forall t' ε', t = Array t' ε' -> exists loc', v = ValLoc loc') ->
    wf_type bot (SecType t ε) ->
    wf_stenv (extend_stenv loc (SecType t ε) stenv) (h [loc → (n × v, ℓ), H1, H2]).
Proof.
  intros.
  unfold wf_stenv.
  intros.
  
  (* Wellformedness for integers *)
  splits.
  
  intros.
  unfold extend_stenv in *.
  destruct (decide (loc0 = loc)); subst.
  
  (* loc1 = loc0 *)
  rewrite_inj.
  specialize_gen.
  destruct_exists.
  apply_heap_lookup_extend_eq.
  rewrite_inj.
  specialize (H5 n0).
  rewrite_inj.
  eauto.
  
  (* loc1 <> loc0 *)
  rewrite -> heap_lookup_extend_neq in * by solve[eauto 2].
   match goal with
    [H: wf_stenv _ _ |- _] =>
    eapply H; eauto 2
  end.
  
  (* Wellformedness for locations *)
  intros.
  destruct (decide (loc0 = loc)); subst.
  
  (* loc1 = loc0 *)
  rewrite_inj.
  apply_heap_lookup_extend_eq.
  rewrite -> extend_stenv_lookup_eq in * by eauto.
  rewrite_inj.
  specialize (H9 n0).
  rewrite_inj.
  eauto.
  
  (* loc1 <> loc0 *)
  rewrite -> heap_lookup_extend_neq in * by solve[eauto 2].
  rewrite -> extend_stenv_lookup_neq in * by solve[eauto].
  eauto.

  intros.
  destruct (decide (loc = loc0)); subst.
  rewrite -> extend_stenv_lookup_eq in *.
  congruence.

  rewrite -> extend_stenv_lookup_neq in * by solve[eauto].
  eauto.

  intros.
  destruct (decide (loc = loc0)); subst.
  rewrite -> extend_stenv_lookup_eq in *.
  eauto.

  (* loc1 <> loc0 *)
  rewrite -> extend_stenv_lookup_neq in * by solve[eauto].
  rewrite -> heap_lookup_extend_neq in * by solve[eauto 2].
  eauto.  
Qed.

Lemma deterministic_typing:
  forall Γ pc c pc1 pc2,
    wt_aux Γ pc c pc1 ->
    wt_aux Γ pc c pc2 ->
    pc1 = pc2.
Proof.
  intros Γ pc c.
  revert pc.
  induction c; intros; subst;
    repeat match goal with
           | [H: wt_aux Γ ?pc (?c1;;?c2) _ |- _] => inverts H
           | [H1: wt_aux _ ?pc ?c ?pc1, H2: wt_aux _ ?pc ?c ?pc2 |- _] =>
             try (erewrite -> (IHc1 pc pc1 pc2 H1 H2) in *; eauto);
               inverts H1; inverts H2; eauto
           end.
Qed.
Hint Resolve deterministic_typing.
End TypeDefinitions.
