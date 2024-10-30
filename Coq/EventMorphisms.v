From EP Require Import EventPreliminaries.
From EP Require Import EventDefinitions.
Open Scope event_scope.


Proposition preserving_sync
  {A B : Type} `{HA : Event A} `{HB : Event B}
  {f : A -> B} {Hf : EventMorphism f} :
    forall x y : A, x =:= y -> f x =:= f y.
Proof.
  intros x y H. pose (H1 := proj1 H). pose (H2 := proj2 H).
  destruct Hf.
  split; apply preserving_causality; assumption.
Qed.

Proposition preserving_prec
  {A B : Type} `{HA : Event A} `{HB : Event B}
  {f : A -> B} {Hf : EventMorphism f} :
    forall x y : A, x < y -> f x < f y.
Proof.
  intros x y H. pose (H1 := proj1 H). pose (H2 := proj2 H).
  destruct Hf.
  split.
  - apply preserving_causality; assumption.
  - intro H3. elim (preserving_exclusion x y).
    + intro H4. pose (H42 := proj2 H4). contradiction.
    + intro H4. pose (H42 := proj2 H4).
      assert (H5 : f x << f y). apply preserving_causality. assumption.
      contradiction.
    + left. split; assumption.
Qed.

Proposition id_is_morphism
  {A : Type} `{HA : Event A} : EventMorphism id.
Proof. split; intros x y H; auto with event. Qed.

Proposition composition_of_morphisms_is_morphism
  {A B C : Type}
  `{HA : Event A} `{HB : Event B} `{HC : Event C}
  {f : A -> B} {g : B -> C} :
    EventMorphism f -> EventMorphism g -> EventMorphism (g * f).
Proof.
  intros Hf Hg.
  destruct Hf as [f_as_arrow Hfpc Hfpe], Hg as [g_as_arrow Hgpc Hgpe].
  constructor; intros x y H.
  - assert (H1 : f x << f y). apply Hfpc. assumption.
    apply Hgpc. assumption.
  - assert (H1 : f x # f y). apply Hfpe. assumption.
    apply Hgpe. assumption.
Qed.
