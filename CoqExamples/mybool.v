Print bool.
About bool.

(* Check Bool. *)
(* Check TRUE. *)

Inductive Bool : Set :=
| TRUE : Bool
| FALSE : Bool.

Check Bool.
Check TRUE.

Check negb.
Compute negb true.
Compute negb false.

(* negation for Bool *)
Definition negB (b : Bool) : Bool :=
  match b with
  | TRUE => FALSE
  | FALSE => TRUE
  end.

Check negB.
Compute negB TRUE.
Compute negB FALSE.

Lemma notnot_id : forall x : bool, negb (negb x) = x.
Proof.
  intro x.
  destruct x.
  - trivial.
  - trivial.
  Show Proof.
Qed.

(* The proof object is interestingly a function that takes b and produces a proof of the lemma *)

Check eq_refl.

(* Using refine *)
Lemma notnot_id' (x : bool) : negb (negb x) = x.
Proof.
  refine (match x with
          | true => eq_refl
          | false => eq_refl
          end).

