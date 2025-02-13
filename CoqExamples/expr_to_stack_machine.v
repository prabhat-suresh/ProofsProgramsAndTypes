Require Import List.
Import ListNotations.
(* Could be inductively defined but as it's not recursive we use variant instead *)
Variant op :=
  | Plus : op
  | Minus : op.

Inductive exp :=
  | Const : nat -> exp
  | Binop : exp -> op -> exp -> exp.

Variant inst :=
  | Push : nat -> inst
  | Exe : op -> inst.

Definition program := list inst.

(* As it recursively calls compile use Fixpoint instead of Definition *)
Fixpoint compile (e : exp) : program :=
  match e with
    | Const n => [Push n]
    | Binop e1 o e2 => let p1 := compile e1 in 
                        let p2 := compile e2 in 
                        p1 ++ p2 ++ [Exe o]
  end.

(* When you don't want to really make it a definition *)
Example e1 := Binop (Const 2) Plus (Const 3).
Example e2 := Binop e1 Minus (Const 5).

Compute compile e2.

Locate "+".
Check Nat.add.
Search (nat -> nat -> nat).

Definition opDenote (o : op) : nat -> nat -> nat :=
  match o with 
  | Plus => Nat.add
  | Minus => Nat.sub
  end.

Fixpoint expDenote (e : exp) : nat :=
  match e with
  | Const n => n
  | Binop e1 o e2 => opDenote o (expDenote e1) (expDenote e2)
  end.

Definition stack := list nat.

Definition instDenote (i : inst) (st : stack) : option stack :=
  match (i, st) with
  | (Push n, _) => Some (n::st)
  | (Exe o, x::y::rest) => Some (opDenote o x y :: rest)
  | _ => None
  end.

Fixpoint progDenote (p : program) (st : stack) : option stack :=
  match p with
  | nil => Some st 
  | cons i prest => let ostp := instDenote i st in
      match ostp with
      | Some stp => progDenote prest stp
      | None => None
      end
  end.

(* Can write this as a fold left but have to produce a summarising function slighlty different from instDenote *)
Check List.fold_left.

(* summarising function sfun : option stack -> inst -> option stack *)
Definition sfun (ostp : option stack) (i : inst) :=
  match ostp with
  | Some stp => instDenote i stp
  | None => None
  end.

Definition pDenote (p : program) (st : stack) : option stack :=
  List.fold_left sfun p (Some st).
