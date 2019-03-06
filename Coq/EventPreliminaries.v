Create HintDb event.

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

