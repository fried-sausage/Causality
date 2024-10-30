From EP Require Import EventDefinitions.
From EP Require Import EventPreliminaries.
Require Import Arith.

Module FiniteEvent.
Section FiniteEvent.
  Inductive universe := 
  | Start
  | Thread1Event
  | Thread2Event
  | Finish.

  Inductive causality: universe -> universe -> Prop :=
    | start_causes_start: causality Start Start
    | thread1_causes_thread1: causality Thread1Event Thread1Event
    | thread2_causes_thread2: causality Thread2Event Thread2Event
    | finish_causes_finish: causality Finish Finish

    | start_causes_finish: causality Start Finish    
    | start_causes_thread1: causality Start Thread1Event
    | start_causes_thread2: causality Start Thread2Event
    | thread1_causes_finish: causality Thread1Event Finish
    | thread2_causes_finish: causality Thread2Event Finish.


 Lemma causality_is_reflexive: Reflexive universe causality.
  Proof.
    intros a.
    destruct a;
    constructor.
  Qed.

  Lemma causality_is_transitive: Transitive universe causality.
  Proof.
    intros a b c.
    intros H_ab H_bc.
    inversion H_ab; subst;
    inversion H_bc; subst;
    constructor.
  Qed.

  Definition causality_constraint := 
    PreorderDef universe causality causality_is_reflexive causality_is_transitive.

  Instance FiniteEvent: @Event universe := {
    causality := causality;
    causality_constraint := causality_constraint  
  }.

End FiniteEvent.
End FiniteEvent.