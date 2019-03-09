Add LoadPath "path to the directory containing library files".
Require Import EventPreliminaries.
Require Import EventDefinitions.
Open Scope event_scope.


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
  destruct Hf as [f_as_arrow Hfps Hfpp], Hg as [g_as_arrow Hgps Hgpp].
  constructor; intros x y H.
  - assert (H1 : f x =:= f y). apply Hfps. assumption.
    apply Hgps. assumption.
  - assert (H1 : f x < f y). apply Hfpp. assumption.
    apply Hgpp. assumption.
Qed.
