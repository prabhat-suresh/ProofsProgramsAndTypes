Inductive Poly R :=
    | Const : R -> Poly R
    | Add : Poly R -> Poly R -> Poly R
    | Mul : Poly R -> Poly R -> Poly R
    | Zero : Poly R
    | One : Poly R.

Fixpoint polyDenote (p : Poly nat) : nat :=
  match p with
  | Const _ n => n
  | Add _ p1 p2 => polyDenote p1 + polyDenote p2
  | Mul _ p1 p2 => polyDenote p1 * polyDenote p2
  | Zero _ => 0
  | One _ => 1
  end.
