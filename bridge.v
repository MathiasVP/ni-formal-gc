Require Import augmented mimperative mlattice bijection id_and_loc types LibTactics language mmemory.
Set Implicit Arguments.

Module Bridge (L: Lattice) (M: Memory L).
  Module Aug := Augmented L M.
  Import Aug Imp TDefs M T LatProp Lang L.
  
  Inductive low_event: level_proj1 -> event -> Prop :=
  | low_assign_is_low_event:
      forall ℓ_adv ℓ x v,
        ℓ ⊑ ℓ_adv ->
        low_event ℓ_adv (AssignEvent ℓ x v)
  | low_new_is_low_event:
      forall ℓ_adv ℓ x loc,
        ℓ ⊑ ℓ_adv ->
        low_event ℓ_adv (NewEvent ℓ x loc)
  | low_get_is_low_event:
      forall ℓ_adv ℓ_x x y v,
        ℓ_x ⊑ ℓ_adv ->
        low_event ℓ_adv (GetEvent ℓ_x x y v)
  | low_set_is_low_event:
      forall ℓ_adv ℓ ℓ_x x n v,
        ℓ_x ⊑ ℓ_adv ->
        ℓ ⊑ ℓ_adv ->
        low_event ℓ_adv (SetEvent ℓ ℓ_x x n v)
  | low_time_is_low_event:
      forall ℓ_adv ℓ x n,
        ℓ ⊑ ℓ_adv ->
        low_event ℓ_adv (TimeEvent ℓ x n)
  | low_restore_is_low_event:
      forall ℓ ℓ_adv n,
        ℓ ⊑ ℓ_adv ->
        low_event ℓ_adv (RestoreEvent ℓ n).
  Hint Constructors low_event.

  Definition high_event l ev := ~ (low_event l ev).
  Hint Unfold high_event.

  Definition low_event_step l cfg1 cfg2 Γ Σ Σ' ev :=
    (cfg1 ⇒ [ev, Γ, Σ, Σ'] cfg2)  /\ low_event l ev.
  Definition high_event_step l cfg1 cfg2 Γ Σ Σ' ev :=
    event_step cfg1 cfg2 Γ Σ Σ' ev /\ high_event l ev.
  Hint Unfold high_event_step.
  Hint Unfold low_event_step.

  Definition event_low_eq l φ ev1 ev2 :=
    (low_event l ev1 <-> low_event l ev2)
    /\ (low_event l ev1 -> iso_events φ ev1 ev2).
  Hint Unfold event_low_eq.

  Inductive bridge_step_num: level_proj1 -> config -> config -> tenv -> stenv -> stenv -> event -> nat -> Prop :=
  | bridge_low_num:
      forall Γ Σ Σ' l ev cfg1 cfg2,
        low_event_step l cfg1 cfg2 Γ Σ Σ' ev ->
        bridge_step_num l cfg1 cfg2 Γ Σ Σ' ev 0
  | bridge_stop_num:
      forall Γ Σ Σ' l ev cfg1 cfg2,
        high_event_step l cfg1 cfg2 Γ Σ Σ' ev ->
        is_stop_config cfg2 ->
        bridge_step_num l cfg1 cfg2 Γ Σ Σ' ev 0
  | bridge_trans_num:
      forall Γ Σ Σ' Σ'' l ev1 ev2 cfg1 cfg2 cfg3 n,
        high_event_step l cfg1 cfg2 Γ Σ Σ' ev1 ->
        not (is_stop_config cfg2) ->
        not (is_timeout_config cfg2) ->
        bridge_step_num l cfg2 cfg3 Γ Σ' Σ'' ev2 n ->
        bridge_step_num l cfg1 cfg3 Γ Σ Σ'' ev2 (S n).
  Hint Constructors bridge_step_num.
  
Notation "cfg1 '↷' '[' ℓ ',' Γ ',' Σ ',' Σ2 ',' evt ',' n ']' cfg2":=
  (bridge_step_num ℓ cfg1 cfg2 Γ Σ Σ2 evt n) (at level 0, n at level 20).


Ltac invert_high_event_step :=
  match goal with [ H: high_event_step _ _ _ _ _ _ _ |- _] =>
                  inverts H
  end.

Ltac invert_bridge_step :=
  match goal with
  | [H: _ ↷ [_, _, _, _, _, _] _ |- _] => inverts H
  end.

Ltac invert_bridge_step_with_steps n :=
  match goal with
  | [H: _ ↷ [_, _, _, _, _, n] _ |- _] => inverts H
  end.

Ltac invert_low_event_step :=
  match goal with [ H: low_event_step _ _ _ _ _ _ _ |- _] =>
                  inverts H
  end.
Ltac invert_low_event :=
  match goal with [ H : low_event _ _ |- _ ] => inverts H end.

Ltac invert_high_event :=
  match goal with [ H : high_event _ _ |- _ ] => unfolds in H end.

Ltac invert_event_step:= 
  match goal with  [ H: _ ⇒ [_, _, _, _]  _ |- _ ] => inverts H end.

End Bridge.


