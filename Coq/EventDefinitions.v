(* path to directory containing scripts *)
Require Import EventPreliminaries.

Class Event :=
  {  universe : Type ;
     causality : BiRel universe ;
  (* Constraints *)
    causality_constraint (* causality is a preorder *) :
      Preorder universe causality ;
  (* Derived relations *)
    synchronisation : BiRel universe :=
      fun x y => causality x y /\ causality y x ;
    precedence : BiRel universe :=
      fun x y => causality x y /\ ~ causality y x ;
    exclusion : BiRel universe :=
      fun x y => precedence x y \/ precedence y x ;
    independence : BiRel universe :=
      fun x y => ~ causality x y /\ ~ causality y x
  }.


Proposition causality_is_reflexive `{Event} : Reflexive universe causality.
Proof. unfold Reflexive. intro x. apply causality_constraint. Qed.

Proposition causality_is_transitive `{Event}: Transitive universe causality.
Proof. unfold Transitive. intro x. apply causality_constraint. Qed.

Hint Resolve
  causality_is_reflexive
  causality_is_transitive : event.

Notation (* x causes y *) "x << y" := (causality x y)
  (at level 70) : event_scope.
Notation (* x precedes y *) "x < y" := (precedence x y)
  (at level 70) : event_scope.
Notation (* x and y are synchronous *) "x =:= y" := (synchronisation x y)
  (at level 70) : event_scope.
Notation (* x and y are mutually exclusive *) "x # y" := (exclusion x y)
  (at level 70) : event_scope.
Notation (* x and y are independent *) "x !! y" := (independence x y)
  (at level 70) : event_scope.

