Require Import Relations.

Section ERelations.

  Variable A : Type.

  Definition Op1 : Type := A -> A.
  Definition Op2 : Type := A -> A -> A.

  Definition Associative (P : Op2) : Prop :=
    forall x y z : A, P (P x y) z = P x (P y z).

  Definition Commutative (P : Op2) : Prop :=
    forall x y : A, P x y = P y x.

  Definition IdentityL (mult : Op2) (e : A) : Prop :=
    forall x : A, mult e x = x.

  Definition IdentityR (mult : Op2) (e : A) : Prop :=
    forall x : A, mult x e = x.

  Definition Identity (mult : Op2) (e : A) : Prop :=
    IdentityL mult e /\ IdentityR mult e.

  Definition InverseL (mult : Op2)(e : A)(inv : Op1) : Prop :=
    forall x : A, mult (inv x) x = e.

  Definition InverseR (mult : Op2)(e : A)(inv : Op1) : Prop :=
    forall x : A, mult x (inv x) = e.

  Definition Inverse (mult : Op2)(e : A)(inv : Op1) : Prop :=
    InverseL mult e inv /\ InverseR mult e inv.

End ERelations.