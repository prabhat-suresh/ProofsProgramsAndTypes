Definition square := fun x => x * x.
Check square.

(* equivalently square can be defined as *)

Definition square' (x : nat) := x * x.
Check square'.

(* types can be mentioned in the definition of a function but should ideally be left to the type inference of gallina unless it's not able to infer on its own (as the types that gallina deals with can make type inference undecidable unlike Ocaml or Haskell's type system) *)

Definition square'' (x : nat) : nat := x * x.
Check square''.

(* the type of square'' is nat -> nat *)

Definition square''' : nat -> nat := fun x => x * x.
Check square'''.
