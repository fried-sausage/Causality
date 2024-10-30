From EP Require Import EventPreliminaries.
From EP Require Import EventDefinitions.
From EP Require Import EventRelationFacts.
Open Scope event_scope.


Proposition congruence_causality `{Event}:
  forall x x' y y' : universe, x =:= x' -> y =:= y' -> x << y -> x' << y'.
Proof.
  intros x x' y y' H1 H2 H3.
  pose (H12 := proj2 H1). pose (H21 := proj1 H2).
  assert (H4 : x' << y). apply causality_is_transitive with x; assumption.
  apply causality_is_transitive with y; assumption.
Qed.

Proposition congruence_precedence `{Event}:
  forall x x' y y' : universe, x =:= x' -> y =:= y' -> x < y -> x' < y'.
Proof.
  intros x x' y y' H1 H2 H3.
  split.
  - pose (H31 := proj1 H3).
    apply congruence_causality with x y; assumption.
  - intro H4. pose (H32 := proj2 H3). apply H32.
    apply synchronisation_is_symmetric in H1.
    apply congruence_causality with y' x';
    apply synchronisation_is_symmetric in H2; assumption.
Qed.

Proposition congruence_exclusion `{Event}:
  forall x x' y y' : universe, x =:= x' -> y =:= y' -> x # y -> x' # y'.
Proof.
  intros x x' y y' H1 H2 H3.
  elim H3; intro H4.
  - left. apply congruence_precedence with x y; assumption.
  - right. apply congruence_precedence with y x; assumption.
Qed.

Proposition congruence_independence `{Event}:
  forall x x' y y' : universe, x =:= x' -> y =:= y' -> x !! y -> x' !! y'.
Proof.
  intros x x' y y' H1 H2 H3.
  pose (H31 := proj1 H3). pose (H32 := proj2 H3).
  split; intro H4.
  - assert (H5 : x << y).
      apply synchronisation_is_symmetric in H1.
      apply synchronisation_is_symmetric in H2.
      apply congruence_causality with x' y'; assumption.
    contradiction.
  - assert (H5 : y << x).
      apply synchronisation_is_symmetric in H1.
      apply synchronisation_is_symmetric in H2.
      apply congruence_causality with y' x'; assumption.
    contradiction.
Qed.
