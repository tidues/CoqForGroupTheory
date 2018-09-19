Require Import Relations.

(* Operators on a carrier set A *)

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

(* Basic Concepts for Functions *)

Section Functions.

  Definition LeftInverse {A B : Set} (f : B -> A) (g: A -> B) : Prop :=
    forall (a : A), f (g a) = a.

  Definition RightInverse {A B : Set} (f : B -> A) (g: A -> B) : Prop :=
    LeftInverse g f.

  Definition Injective {A B : Set} (f : A -> B) : Prop :=
    forall (a1 a2 : A), f a1 = f a2 -> a1 = a2.

  Definition Surjective {A B : Set} (f : A -> B) : Prop :=
    forall y, exists x, f x = y.

  Definition Bijective {A B : Set} (f : A -> B) : Prop :=
    Injective f /\ Surjective f.

(* An bijection equivalence is assume, can be proved with LEM *)
  Axiom bijecInv : forall {A B : Set}(f : A -> B), Bijective f -> 
    exists g : B -> A, LeftInverse f g /\ RightInverse f g.

  Definition fun_id {A : Type} (a : A) : A := a.

End Functions.

(* Finite Numbers *)
Section Finite.

  Inductive Fin : nat -> Set :=
    | zero : forall {n : nat}, Fin n
    | suc : forall {n : nat} (i : Fin n), Fin (S n).

  Definition Finite (n : nat) (A : Set) : Prop :=
    exists f : Fin n -> A, Bijective f.

  Theorem finFinite : forall {n : nat}, Finite n (Fin n).
  Proof.
  unfold Finite.
  intros.
  exists fun_id.
  unfold Bijective.
  split.
  unfold Injective.
  intros.
  compute in H.
  assumption.
  unfold Surjective.
  intros.
  exists y.
  compute.
  reflexivity.
  Qed.

End Finite.

