(* 2023 Test 1 *)
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

(* Question 5 - Even Proposition*)
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

(* Question 5 - Prisoners and Guards *)
Print bool.
Inductive Prisoner: Set := prisoner.
Inductive Guard: Set := guard.
Check Prisoner.
Print Prisoner.

Inductive valid_line_of_prisoners_and_guards := EmptyLine
  | LonePrisoner: Prisoner -> valid_line_of_prisoners_and_guards
  | ConsGuard: Guard -> valid_line_of_prisoners_and_guards -> valid_line_of_prisoners_and_guards
  | ConsPrisonerWithGuard: Prisoner -> Guard -> valid_line_of_prisoners_and_guards -> valid_line_of_prisoners_and_guards.
Check valid_line_of_prisoners_and_guards.
Print valid_line_of_prisoners_and_guards.

(* 14 Feb 2025 Test 1 *)
(* Question 1 *)
Inductive expr := Const (n : nat) | Plus (e1 e2 : expr) | Minus (e1 e2 : expr).

Fixpoint countOp (e : expr) : nat :=
  match e with 
  | Const _ => 0
  | Plus e1 e2 => countOp e1 + countOp e2 + 1
  | Minus e1 e2 => countOp e1 + countOp e2 + 1
  end.

(* Question 3 *)
Fixpoint plus' (a b : nat) : nat :=
  match a with
  | O => b
  | S a_minus1 => S (plus' a_minus1 b)
  end.

Fixpoint mult' (a b : nat) : nat :=
  match a with
  | O => O
  | S a_minus1 => plus' b (mult' a_minus1 b)
  end.

(* Question 4 *)
Lemma implies : forall P Q : Prop, (not P \/ Q) -> (P -> Q).
Proof.
  refine (fun P Q nPorQ => match nPorQ with
                           | or_introl nP => fun p: P => 
                               let absurd (f : False) : Q := match f with end
                           in absurd (nP p)
                           | or_intror q => fun _ => q
                           end).
Qed.

(* Lemma implies' : forall P Q : Prop, (P -> Q) -> (not P \/ Q). *)
(* Proof. *)
(*   refine (fun P Q PtoQ => _). *)
