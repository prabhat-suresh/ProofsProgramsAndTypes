Print eq.
(*Inductive eq {A : Type} : A -> A -> Prop :=*)
(*  | eq_refl {x : A} : eq x x.*)

Definition eq_sym {A: Type} (x y : A) (pf : eq x y) : eq y x :=
  match pf with
    | eq_refl => eq_refl
  end.
Print eq_sym.

Lemma eq_trans {A: Type} (x y z : A) (pf1 : eq x y) (pf2 : eq y z) : eq x z.
Proof.
  destruct pf1.
  exact pf2.
  Show Proof.
Qed.

Lemma eq_trans2 {A: Type} (x y z : A) (pf1 : eq x y) (pf2 : eq y z) : eq x z.
    refine (match pf2 with
            | eq_refl => pf1
            end).
Qed.
    (*(match pf1,pf2 with*)
    (*          | eq_refl, eq_refl => pf1*)
    (*        end).*)

Definition eq_trans3 {A: Type} (x y z : A) (pf1 : eq x y) (pf2 : eq y z) : eq x z :=
  match pf2 with
    | eq_refl => pf1
  end.
Print eq_trans3.


(* Definition foo := forall {A: Type} (x y: A), (pf: x=y) -> pf = eq_refl. Not even well-typed *)

(*Cannot prove the following*)
(*Lemma foo : forall {A: Type} (x: A) (pf: x=x), pf = eq_refl.*)
(*Proof.*)
(*  intros.*)
(*  induction pf.*)
(*  reflexivity.*)

Definition plus_O_n : forall n:nat, 0+n=n :=
(*Proof.*)
(*  trivial.*)
(*refine (fun _ => eq_refl).*)
fun _ => eq_refl.


Print Nat.add.
(* The 0+n is n by definition. However n+0 is not n by definition. It has to be proved using induction *)

Goal forall n:nat, plus_O_n n = eq_refl.
refine (fun _ => eq_refl).
(*Proof.*)
(*  intros n.*)
(*  simpl.*)
(*  compute.*)
(*  trivial.*)
(*  Show Proof.*)
Qed.

Lemma plus_n_O : forall n:nat, n+0=n.
(*refine (fun _ => eq_refl).*)
Proof.
  intros n.
  induction n.
  - trivial.
  - simpl. rewrite IHn. trivial.
Qed.

(*Goal forall n:nat, plus_n_O n = eq_refl. (* Not even well-typed *)*)

(*Goal 42 + 0 = 42.*)
(*  eq_refl.*)

Print nat_ind.
Check nat_ind.
