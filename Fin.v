

Inductive Fin : nat -> Set :=
  | zero : forall {n : nat}, Fin n
  | suc : forall {n : nat} (i : Fin n), Fin (S n).


