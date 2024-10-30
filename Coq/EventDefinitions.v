From EP Require Import EventPreliminaries.


Class Event {A : Type} :=
  {  universe := A ;
     causality : BiRel universe ;
  (* Constraint *)
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

Hint Resolve causality_is_reflexive : event.
Hint Resolve causality_is_transitive : event.

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

Open Scope event_scope.

Class EventMorphism {A B : Type} `{Event A} `{Event B} (f : A -> B) :=
  {  arrow := f ;
  (* Constraints *)
    preserving_causality : forall x y : A, x << y -> arrow x << arrow y ;
    preserving_exclusion : forall x y : A, x # y -> arrow x # arrow y
  }.
