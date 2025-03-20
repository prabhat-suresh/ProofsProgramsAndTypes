(*Test 2 question paper Nov 9 2023*)
(*Question 1*)
Inductive ex (A: Type) (P: A -> Prop) : Prop :=
  | ex_intro: forall x: A, P x -> ex A P.

Inductive sig (A: Type) (P: A -> Prop) : Type :=
  | exist: forall x: A, P x -> sig A P.

Check ex.
Check sig.
Check ex_intro.
Check exist.
(* Part (a) *)
(*Definition exToSig : forall (A: Type) (P: A -> Prop), ex A P -> sig A P :=*)
(*  fun (A: Type) (P: A -> Prop) (e: ex A P) =>*)
(*    match e with*)
(*      | ex_intro _ _ x p => exist _ _ x p*)
(*    end.*)
(* The above cannot be defined in Gallina because it takes a Prop and examines its contents (by pattern matching on its constructors) and returns a Type which is not possible in Coq as the Props are stripped off from the definition in the end result *)

(* Part (b) *)
Definition sigToEx (A: Type) (P: A -> Prop) (s: sig A P): ex A P :=
    match s with
      | exist _ _ x p => ex_intro _ _ x p
    end.
Check sigToEx.
(* The above can be defined in Gallina because it takes a Type and returns a Prop which is possible allowed *)


(*Question 2*)
(*implement intro tactic using refine tactic*)

Ltac my_intro :=
  refine (fun _ => _). (* Introduces a hypothesis by refining the goal into a function *)

Ltac my_intro_arg x :=
  refine (fun x => _).

(* Example Usage *)
Goal forall A B : Prop, A -> B -> A.
Proof.
    my_intro. (* Or my_intro_arg A. *)
    my_intro_arg B. (* Or my_intro. *)
    trivial.
Qed.

(*Question 3*)
Print sumor.

Definition map_sumor (A B : Type) (P : Prop) (f : A -> B) (s : sumor A P) : sumor B P :=
    match s with
        | inleft a => inleft (f a)
        | inright p => inright p
    end.

(*Question 4*)
(* Part (a) *)
Inductive Vlog : nat -> Type :=
    | Vnil : Vlog 0 (* O balance in the vending machine initially *)
    | Vadd_coin : forall n, Vlog n -> Vlog (S n)
    | Vdispense_toffee : forall n, Vlog (S n) -> Vlog n
    | Vdispense_vada : forall n, Vlog (S (S n)) -> Vlog n.

(*Part (b)*)
Variant Action: Set :=
    | Coin
    | Toffee
    | Vada.

Inductive LogSequence : Type :=
    | LogSequence_nil : LogSequence
    | LogSequence_cons : Action -> LogSequence -> LogSequence.

Fixpoint compute_sales (l: LogSequence) : nat :=
    match l with
        | LogSequence_nil => 0
        | LogSequence_cons Coin l' => 1 + compute_sales l'
        | LogSequence_cons _ l' => compute_sales l'
    end.
