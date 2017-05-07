Require Import LibTactics.

Tactic Notation "remember_simple" constr(t) :=
  let h := fresh "H"
  in remember t as h;
     match goal with
     | H' : h = _ |- _ => clear H'
     end.

Tactic Notation "remember_simple" constr(t) "as" ident(h) :=
    remember t as h;
    match goal with
    | H' : h = _ |- _ => clear H'
    end.

Ltac is_not_imp :=
  match goal with
    [H: _ -> _ |- _] => fail 1
  | [H: _ |- _] => idtac
  end.

Ltac decompose_ex H :=
  repeat match type of H with
         | ex (fun x => _) =>
           let x := fresh x in
           destruct H as [x H]
         | sig (fun x => _) =>
           let x := fresh x in
           destruct H as [x H]
         end.

Ltac super_destruct :=
  repeat
    match goal with
      [H: exists _, _ |- _] =>
      decompose_ex H
    | [H: { _ | _} |- _] =>
      decompose_ex H
    | [ H : context [ _ /\ _ ] |- _ ] =>
      destruct H
    end.

Ltac super_destruct' :=
  repeat
    match goal with
      [H: exists _, _ |- _] =>
      decompose_ex H
    | [H: { _ | _} |- _] =>
      decompose_ex H
    | [ H : _ /\ _ |- _ ] =>
      destruct H
    end.
  
Tactic Notation "injects" :=
  match goal with
    [H: _ = _ |- _] => injects H
  end.

Ltac destruct_exists :=
  repeat match goal with
           [H: exists _, _ |- _] =>
           decompose_ex H; try subst
         end.

Ltac specialize_gen:=
  match goal with
  | [  H  : ?F -> _ ,
            H' : ?F |- _] =>
    specialize (H H')
  | [ H : ?X = ?X -> _ |- _ ] =>
    let h := fresh "H"
    in
    assert (X = X) by auto;
    specialize (H h);
    clear h
  | [H : ?X <> ?Y -> _ |- _] =>
    let h := fresh "H"
    in assert (X <> Y) as h by (intro H_absurd; discriminate H_absurd);
       specialize (H h); clear h
  end.

Ltac rewrite_inj :=
  repeat match goal with
         | [H1: ?X = ?Y, H2: ?X = ?Z |- _] =>
           rewrite -> H1 in H2
         | [H: Some _ = Some _ |- _] =>
           injects H
         end;
  repeat match goal with
           [H: ?X = ?X |- _] => clear H
         end.
Ltac deep_rewrite :=
  match goal with
    [H1: ?X = ?Y, H2: context[?X] |- _] =>
    rewrite -> H1 in H2
  end.

Ltac decide_exist :=
  match goal with
    [H: ?X = _ |- context[match ?X with _ => _ end]] =>
    rewrite -> H
  | [H: ?X <> _ |- context[match ?X with _ => _ end]] =>
    destruct X; try solve[exfalso; eauto]
  end.

Ltac decide_if :=
  match goal with
    [H: ?X = _ |- context[if ?X then _ else _]] =>
    rewrite -> H
  end.

Tactic Notation "decide_exist" "in" "*" :=
  match goal with
    [H: ?X = _, H2: context[match ?X with _ => _ end] |- _] =>
    rewrite -> H in H2
  end.

Tactic Notation "decide_if" "in" "*" :=
  match goal with
    [H: ?X = _, H2: context[if ?X then _ else _] |- _] =>
    rewrite -> H in H2
  end.

Tactic Notation "_rewrite" "->" uconstr(H) "in" "*" :=
  match goal with
    [H2: _ |- _] =>
    rewrite -> H in H2
  end.

Tactic Notation "_rewrite" "<-" uconstr(H) "in" "*" :=
  match goal with
    [H2: _ |- _] =>
    rewrite <- H in H2
  end.

Tactic Notation "_rewrite" "->" uconstr(H1) "in" "*" "by" tactic(t) :=
  match goal with
    [H3: _ |- _] =>
    rewrite -> H1 in H3 by t
  end.

Tactic Notation "_rewrite" "<-" uconstr(H) "in" "*" "by" tactic(t) :=
  match goal with
    [H2: _ |- _] =>
    rewrite <- H in H2 by t
  end.

Tactic Notation "_apply " uconstr(H) "in" "*" :=
  repeat match goal with
           [H2: _ |- _] =>
           apply H in H2
         end.

Ltac edestructs_conjunction_tactic N T :=
  match N with
  | 2 => edestruct T as [? ?]
  | 3 => edestruct T as [? [? ?]] | 4 => edestruct T as [? [? [? ?]]] | 5 => edestruct T as [? [? [? [? ?]]]] | 6 => edestruct T as [? [? [? [? [? ?]]]]] | 7 => edestruct T as [? [? [? [? [? [? ?]]]]]] end.

Tactic Notation "edestructs" constr(T) :=
  let TT := type of T in
  let N := get_term_conjunction_arity TT in
  edestructs_conjunction_tactic N T.

Ltac break_match_hyp :=
  match goal with
  | [ H : context [ match ?X with _ => _ end ] |- _] =>
    match type of X with
    | sumbool _ _ => destruct X
    | _ => destruct X eqn:?
    end
  end.

Ltac break_match_goal :=
  match goal with
  | [ |- context [ match ?X with _ => _ end ] ] =>
    match type of X with
    | sumbool _ _ => destruct X
    | _ => destruct X eqn:?
    end
  end.

Ltac break_match := break_match_goal || break_match_hyp.


Ltac constructors_dont_have_fixed_points t := induction t ; inversion 1 ; auto ; try congruence.