(*This doesn't capture the red-black tree properties in the data structure.*)
(*Inductive tree (A : Type) : Type :=*)
(*| Red : tree A -> A -> tree A -> tree A*)
(*| Black : tree A -> A -> tree A -> tree A*)
(*| Nil : tree A.*)

Variant colour := red | black.

(*The indices will maintain the colour of the tree and the black height of the tree.*)
Inductive tree (A : Type) : colour -> nat -> Type :=
| Nil : tree A black 0
| Red {n}: tree A black n -> A -> tree A black n -> tree A red n
| Black {c1 c2 n}: tree A c1 n -> A -> tree A c2 n -> tree A black (S n).
