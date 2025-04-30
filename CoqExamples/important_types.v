Print or.

Inductive sumbool (A B : Prop) : Type :=
  | left : A -> sumbool A B
  | right : B -> sumbool A B.

(* Written concisely as {A} + {B} *)

Inductive sumor (A : Type) (B : Prop) : Type :=
  | in_left : A -> sumor A B
  | in_right : B -> sumor A B.

(* Written concisely as A + {B} *)

Inductive sum (A B : Type) : Type :=
  | inl : A -> sum A B
  | inr : B -> sum A B.

(* Written concisely as A + B *)

(* Sigma types *)

Check ex.
Print ex.

Check ex_intro.

Check sig.
Print sig.

Check exist.

Check sigT.
Print sigT.

Check existT.

Inductive sort : Type :=
  | NAT : sort
  | BOOL : sort
  | PROD : sort -> sort -> sort.

Fixpoint denote (s : sort) : Type :=
  match s with
  | NAT => nat
  | BOOL => bool
  | PROD s1 s2 => denote s1 * denote s2
  end.

Definition Dyn := {s: sort & denote s}.
(* Now a list of Dyn will be heterogeneous and we can also inspect the type *)
(*cast : forall s, Dyn -> Option (denote s)*)
Fixpoint type_cast (s : sort) (d : Dyn) : option (denote s) :=
  match d with
  | (existT _ s' d') => match s with
                       | s => Some d'
                       | _ => None
                       end
  end.
