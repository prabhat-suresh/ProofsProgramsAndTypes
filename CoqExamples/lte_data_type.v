Inductive lte : nat -> nat -> Prop :=
| lte_0 {n} : lte n n
| lte_S {m n}:  lte m n -> lte m (S n).

Inductive eq : nat -> nat -> Prop :=
| eq_refl {n} : eq n n.
