(*Consider databases and queries.*)
Inductive Key (A:Type) : Type :=
  | Keyof : nat -> Key A.

(*get : forall (A:Type) (k:Key A), A -> table A -> option A.*)
