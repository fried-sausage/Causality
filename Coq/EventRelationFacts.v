(* Uncomment the string specifying the needed load path *)
Add LoadPath "/home/zholtkevych/OneDrive/Causality/8.6".
(*
Add LoadPath "C:\Users\user\OneDrive\Causality\8.7.2".
*)
Require Import EventPreliminaries.
Require Import EventDefinitions.
Open Scope event_scope.


Proposition synchronisation_implies_causality `{Event} :
  forall x y : universe, x =:= y -> x << y.
Proof. intros x y H0. pose (H01 := proj1 H0). assumption. Qed.

Lemma synchronisation_is_reflexive `{Event} :
  Reflexive universe synchronisation.
Proof.
  unfold Reflexive. intro x.
  destruct causality_constraint as [HR _].
  split; apply HR.
Qed.

Lemma synchronisation_is_transitive `{Event} :
  Transitive universe synchronisation.
Proof.
  unfold Transitive. intros x y z H1 H2.
  destruct causality_constraint as [_ HT].
  pose (H11 := proj1 H1). pose (H21 := proj1 H2).
  pose (H12 := proj2 H1). pose (H22 := proj2 H2).
  split; eauto.
Qed.

Lemma synchronisation_is_symmetric `{Event} :
  Symmetric universe synchronisation.
Proof.
  unfold Symmetric. intros x y H0.
  pose (H01 := proj1 H0). pose (H02 := proj2 H0).
  split; assumption.
Qed.

Hint Resolve
  synchronisation_implies_causality
  synchronisation_is_reflexive
  synchronisation_is_transitive
  synchronisation_is_symmetric : event.

Proposition synchronisation_is_equivalence `{Event} :
  Equivalence universe synchronisation.
Proof. auto with event. Qed.

Proposition precedence_implies_causality `{Event} :
  forall x y : universe, x < y -> x << y.
Proof. intros x y H0. pose (H01 := proj1 H0). assumption. Qed.

Hint Resolve precedence_implies_causality : event.

Lemma precedence_is_irreflexive `{Event} : Irreflexive universe precedence.
Proof.
  unfold Irreflexive. intros x H0.
  pose (H01 := proj1 H0). pose (H02 := proj2 H0).
  auto.
Qed.

Lemma precedence_is_transitive `{Event} : Transitive universe precedence.
Proof.
  intros x y z H1 H2. elim H1; elim H2.
  intros H3 H4 H5 H6. split.
  - apply causality_is_transitive with y; assumption.
  - contradict H4. apply causality_is_transitive with x; assumption.
Qed.

Hint Resolve
  precedence_is_irreflexive
  precedence_is_transitive : event.

Proposition precedence_is_strictOrder `{Event} :
  StrictOrder universe precedence.
Proof. auto with event. Qed.

Proposition exclusion_is_irreflexive `{Event} :
  Irreflexive universe exclusion.
Proof. intros x H0. elim H0; apply precedence_is_irreflexive. Qed.

Proposition exclusion_is_symmetric `{Event} :
  Symmetric universe exclusion.
Proof. intros x y H0. elim H0; intro H1; [ right | left ]; assumption. Qed.

Hint Resolve
  exclusion_is_irreflexive
  exclusion_is_symmetric : event.

Proposition independence_is_irreflexive `{Event} :
  Irreflexive universe independence.
Proof.
  intros x H0. pose (H01 := proj1 H0). apply H01.
  apply causality_is_reflexive.
Qed.

Proposition independence_is_symmetric `{Event} :
  Symmetric universe independence.
Proof.
  intros x y H0. pose (H01 := proj1 H0). pose (H02 := proj2 H0).
  split; assumption.
Qed.

Hint Resolve
  independence_is_irreflexive
  independence_is_symmetric : event.

Lemma incompatibility_of_syncronisation_and_precedence `{Event} :
  forall x y : universe, x =:= y -> x < y -> False.
Proof.
  intros x y H1 H2. elim H2. intros H21 H22.
  pose (H12 := proj2 H1). contradiction.
Qed.

Hint Resolve
  incompatibility_of_syncronisation_and_precedence : event.

Proposition incompatibility_of_syncronisation_and_exclusion `{Event} :
  forall x y : universe, x =:= y -> x # y -> False.
Proof.
  intros x y H1 H2. elim H2;
  apply incompatibility_of_syncronisation_and_precedence;
  assumption || apply synchronisation_is_symmetric; assumption.
Qed.

Proposition incompatibility_of_syncronisation_and_independence `{Event} :
  forall x y : universe, x =:= y -> x !! y -> False.
Proof.
  intros x y H1 H2. elim H2. intros H3 H4.
  pose (H11 := proj1 H1). contradiction.
Qed.

Lemma incompatibility_of_precedence_and_independence `{Event} :
  forall x y : universe, x < y -> x !! y -> False.
Proof.
  intros x y H1 H2. elim H2. intros H3 H4.
  pose (H11 := proj1 H1). contradiction.
Qed.

Proposition incompatibility_of_exclusion_and_independence `{Event} :
  forall x y : universe, x # y -> x !! y -> False.
Proof.
  intros x y H1. elim H1; intro H2;
  [ idtac |
    intro H3; apply independence_is_symmetric in H3; revert H3 ];
  apply incompatibility_of_precedence_and_independence; assumption.
Qed.

Lemma causality_distinguishes_exclusion `{Event} :
  forall x y : universe, x # y -> x << y -> x < y.
Proof.
  intros x y H1 H2. elim H1; intro H3.
  - assumption.
  - contradict H3. intro H3.
    pose (H32 := proj2 H3). contradiction.
Qed.

Lemma decidable_causality_ensures_ixsDecomposition `{Event} :
  Decidable universe causality ->
    forall x y : universe, x !! y \/ x # y \/ x =:= y.
Proof.
  intros H0 x y. elim H0 with x y; intro H1.
  - right. elim H0 with y x; intro H2;
    [ right | left; left ]; split; assumption.
  - apply or_assoc. left. elim (H0 y x); intro H2;
    [ right; right | left ]; split; assumption.
Qed.

Lemma ixsDecomposition_ensures_decidability_of_causality `{Event} :
  (forall x y : universe, x !! y \/ x # y \/ x =:= y) ->
    Decidable universe causality.
Proof.
  intro H0. unfold Decidable. intros x y. elim (H0 x y); intro H1.
  - right. pose (H11 := proj1 H1). assumption.
  - elim H1; intro H2; elim H2.
    + intro H3. elim H3. intros H4 H5. left. assumption.
    + intro H3. right. pose (H32 := proj2 H3). assumption.
    + intros H3 H4. left. assumption.
Qed.

Theorem decidable_causality_is_equivalent_to_ixsDecomposition `{Event}:
  Decidable universe causality <->
    forall x y : universe, x !! y \/ x # y \/ x =:= y.
Proof.
  split;
  [ apply decidable_causality_ensures_ixsDecomposition |
    apply ixsDecomposition_ensures_decidability_of_causality ].
Qed.
