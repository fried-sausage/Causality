Create HintDb event.

Axiom eta_conversion :
  forall (A B : Type) (f g : A -> B), (forall x : A, f x = g x) -> f = g.

Hint Resolve eta_conversion : event.

Section EventPreliminaries.
  Variable U : Type.

  Definition BiRel : Type := U -> U -> Prop.

  Definition Reflexive (R : BiRel) : Prop := forall x : U, R x x.
  Definition Irreflexive (R : BiRel) : Prop := forall x : U, ~ R x x.
  Definition Symmetric (R : BiRel) : Prop := forall x y : U, R x y -> R y x.
  Definition Transitive (R : BiRel) : Prop :=
    forall x y z : U, R x y -> R y z -> R x z.

  Inductive Preorder (R : BiRel) : Prop :=
    PreorderDef : Reflexive R -> Transitive R -> Preorder R.
  Inductive Equivalence (R : BiRel) : Prop :=
    EquivalenceDef :
      Reflexive R -> Transitive R -> Symmetric R -> Equivalence R.
  Inductive StrictOrder (R : BiRel) : Prop :=
    StrictOrderDef : Irreflexive R -> Transitive R -> StrictOrder R.

  Definition Decidable (R : BiRel) : Prop :=
    forall x y : U, R x y \/ ~ R x y.

End EventPreliminaries.

Hint Constructors Preorder Equivalence StrictOrder : event.


Definition id {A : Type} := fun x : A => x.

Proposition id_x_equals_x {A : Type} : forall x : A, id x = x.
Proof. intro x. compute. reflexivity. Qed.

Hint Resolve id_x_equals_x : event.

Definition compose {A B C : Type} (f : A -> B) (g : B -> C) : A -> C :=
  fun x : A => g (f x).

Notation "g * f" := (compose f g)
  (at level 40, left associativity) : event_scope.

Open Scope event_scope.

Proposition id_is_leftId {A B : Type} : forall f : A -> B, id * f = f.
Proof. intro f. apply eta_conversion. intro x. compute. reflexivity. Qed.

Proposition id_is_rightId {A B : Type} : forall f : A -> B, f * id = f.
Proof. intro f. apply eta_conversion. intro x. compute. reflexivity. Qed.

Proposition compose_is_assoc {A B C D : Type} :
  forall (f : A -> B) (g : B -> C) (h : C -> D), h * g * f = h * (g * f).
Proof. intros. apply eta_conversion. intro. compute. reflexivity. Qed.

Hint Resolve id_is_leftId : event.
Hint Resolve id_is_rightId : event.
Hint Resolve compose_is_assoc : event.
