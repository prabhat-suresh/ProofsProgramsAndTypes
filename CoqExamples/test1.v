(* Question 2*)
Definition myand (P Q : bool) : bool :=
  match Q with
  | true => P
  | false => false
  end.

Lemma myand_true_r : forall P : bool, myand P true = P.
Proof.
  trivial.
Qed.

Lemma myand_true_l : forall Q : bool, myand true Q = Q.
Proof.
  intros Q.
  destruct Q.
  - trivial.
  - trivial.
Qed.

(* Question 3*)
Definition something := fun x : bool => x.
Check something.
Definition something' := fun x : True => x.
Check something'.
Definition something'' := fun x : False => x.
Check something''.
(* Definition something'' := fun x : true => x. is ill formed coz true is not a type *)

Check True.
Print True.
Check False.
Print False.

(* Question 4*)
Definition plus (x y : nat) : nat := Nat.add x y.

Print nat.

Definition mult (x y : nat) : nat := match y with
  | O => O
  | S y_minus1 => plus x (mult x y_minus1)
end.

(* Question 5*)
Check Prop.
Inductive Even : nat -> Prop :=
| Even_O : Even O
| Even_SS : forall n, Even n -> Even (S (S n)).

Check Even O.
Example even4 := Even 4.
Check even4.
Check Even 3.
Check Even 4.
Check True.

Inductive Odd : nat -> Prop :=
| Odd_1 : Odd (S O)
| Odd_SS : forall n, Odd n -> Odd (S (S n)).
