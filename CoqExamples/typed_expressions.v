Variant sort := NAT | BOOL.

Variant op : sort -> sort -> sort -> Type :=
| Plus : op NAT NAT NAT
| Minus : op NAT NAT NAT
| Mul : op NAT NAT NAT
| GT : op NAT NAT BOOL.

Inductive exp : sort -> Type :=
| NConst : nat -> exp NAT
| BConst : bool -> exp BOOL
| Binop{s1 s2 s3} : exp s1 -> op s1 s2 s3 -> exp s2 -> exp s3
| If{s} : exp BOOL -> exp s -> exp s -> exp s.

Check Binop.

(*sortDenote : sort -> Type.*)

Definition sortDenote (s : sort) : Type :=
  match s with
  | NAT => nat
  | BOOL => bool
  end.

(*opDenote : forall s1 s2 s3, op s1 s2 s3 -> (sortDenote s1 -> sortDenote s2 -> sortDenote s3)*)

Search ( nat -> nat -> bool).

Definition opDenote {s1 s2 s3 : sort} (op : op s1 s2 s3): sortDenote s1 -> sortDenote s2 -> sortDenote s3 :=
    match op with
      | Plus => Nat.add
      | Minus => Nat.sub
      | Mul => Nat.mul
      | GT => Nat.ltb
    end.

(*expDenote : forall s, exp s -> sortDenote s.*)

Fixpoint expDenote {s : sort} (e : exp s) : sortDenote s :=
  match e with
  | NConst n => n
  | BConst b => b
  | Binop e1 op e2 => opDenote op (expDenote e1) (expDenote e2)
  | If e1 e2 e3 => if expDenote e1 then expDenote e2 else expDenote e3
  end.

(*If you use coercion, you don't need to write sortDenote s*)
(*Coercion sortDenote : sort >-> Sortclass.*)

(* Now what if sort is defined to be Set? *)

Definition sort' := Set.

Check nat.

Variant op' : sort' -> sort' -> sort' -> Type :=
| Plus' : op' nat nat nat
| Minus' : op' nat nat nat
| Mul' : op' nat nat nat
| GT' : op' nat nat bool.

Inductive exp' : sort' -> Type :=
| NConst' : nat -> exp' nat
| BConst' : bool -> exp' bool
| Binop' {s1 s2 s3} : exp' s1 -> op' s1 s2 s3 -> exp' s2 -> exp' s3
| If' {s} : exp' bool -> exp' s -> exp' s -> exp' s.

Check Binop'.

(*sortDenote : sort -> Type.*)

Check id.
Print id.

Definition sortDenote' (s : sort') : Type :=
    s.

(*opDenote : forall s1 s2 s3, op s1 s2 s3 -> (sortDenote s1 -> sortDenote s2 -> sortDenote s3)*)

Search ( nat -> nat -> bool).

Definition opDenote' {s1 s2 s3 : sort'} (op : op' s1 s2 s3): s1 -> s2 -> s3 :=
    match op with
      | Plus' => Nat.add
      | Minus' => Nat.sub
      | Mul' => Nat.mul
      | GT' => Nat.ltb
    end.

(*expDenote : forall s, exp s -> sortDenote s.*)

Fixpoint expDenote' {s : sort'} (e : exp' s) : sortDenote' s :=
  match e with
  | NConst' n => n
  | BConst' b => b
  | Binop' e1 op e2 => opDenote' op (expDenote' e1) (expDenote' e2)
  | If' e1 e2 e3 => if expDenote' e1 then expDenote' e2 else expDenote' e3
  end.



(* From Piyush sir's repo *)


(* This is the typed version of the calculator. From Chapter 2 of cpdt *)

Require Import Nat.
Require Import Bool.
Require Import List.

Inductive type : Set := Nat | Bool.


Definition typeDenote (t : type) :=
  match t with
    | Nat  => nat
    | Bool => bool
  end.


Inductive tbinop : type -> type -> type -> Set :=
| tPlus            : tbinop Nat Nat Nat
| tMul             : tbinop Nat Nat Nat
| tLe              : tbinop Nat Nat Bool
| tEq   {t : type} : tbinop t   t   Bool

(* tEq : forall {t : type}, tbinot t t Bool *)
.
 Print tEq.


Inductive texpr : type -> Set :=
| tConst {t : type} : typeDenote t  -> texpr t
| tBinOp  {t1 t2 t3 : type} : (tbinop t1 t2 t3) -> texpr t1 -> texpr t2 -> texpr t3
.

Compute @tConst Nat 2.
Compute @tConst Bool true.
(* Now comes the stack machine. *)

(* The type of the stack *)
Definition tstack := list type.

(* The value stack *)
Fixpoint vstack (ts : tstack) : Set :=
  match ts with
    | nil       => unit
    | t :: ts   => typeDenote t * vstack ts
  end.


Inductive tinstr : tstack  -> tstack -> Set :=
| tpush {ts : tstack}{t : type}     : typeDenote t -> tinstr  ts (t :: ts)
| texec {ts : tstack}{s t r : type} : tbinop s t r -> tinstr (s :: t :: ts) (r :: ts)
.

Inductive tprogram : tstack -> tstack -> Set :=
| pNil   {s : tstack}        : tprogram s s
| pInstr  {s1 s2 s3 : tstack} : tinstr s1 s2 -> tprogram s2 s3  -> tprogram s1 s3
.

Fixpoint app_p {s t} {tp} (p : tprogram s t) : tprogram t tp -> tprogram s tp :=
  match p with
    | pNil       => fun pnew => pnew
    | pInstr i pp => fun pnew => pInstr i (app_p pp pnew)
  end.

Notation "{{ x }}"  := (pInstr x pNil).
Notation "x +++ y"  := (app_p x y) (at level 70, right associativity).

(** Associativity of appending *)
Lemma app_assoc s1 s2 s3 s4 : forall (p1 : tprogram s1 s2)(p2 : tprogram s2 s3)(p3 : tprogram s3 s4),
    (p1 +++ p2 +++ p3) = ((p1 +++ p2) +++ p3).
  intro p1. induction p1 as [ | a b c i p IH].
  - simpl; trivial.
  - intros p2 p3.
    simpl; rewrite IH; trivial.
Qed.

(* meaning of the constructs of the language *)

Definition tbinopDenote {s t r : type}(op : tbinop s t r)
: typeDenote s -> typeDenote t -> typeDenote r
  :=
  match op in tbinop s t r return  typeDenote s -> typeDenote t -> typeDenote r
  with
    | tPlus    => plus
    | tMul     => mult
    | tLe      => Nat.leb
    | @tEq Nat => Nat.eqb
    | @tEq Bool => eqb
  end.


Fixpoint texprDenote {t : type}(e : texpr t) : typeDenote t :=
  match e with
    | tConst  c          => c
    | tBinOp  op e1 e2   => tbinopDenote op (texprDenote e1) (texprDenote e2)
  end.



Definition tinstrDenote {s0 s1} (i : tinstr s0 s1)  :=
  match i in tinstr s0 s1 return vstack s0 -> vstack s1
  with
    | tpush  x  => fun vs  => (x, vs)
    | texec op
      => fun vs => let '(a,(b,vsp)) := vs in (tbinopDenote op a b , vsp)
  end.

Fixpoint tprogramDenote {s0 s1}(p : tprogram s0 s1) :=
  match p with
    | pNil       => fun vs => vs
    | pInstr i pp  => fun vs => tprogramDenote pp (tinstrDenote i vs)
  end.

Check tinstrDenote.
Check (tinstrDenote, tprogramDenote).
(* meanings *)



(* The compiler *)

Fixpoint compile {t}(e : texpr t) : forall {ts : tstack},  tprogram ts (t :: ts) :=
  match e in texpr t return forall ts, tprogram ts (t :: ts) with
    | tConst c         => fun _ => {{ tpush c }}
    | tBinOp op e0 e1  => fun _ => compile e1  +++ compile e0  +++ {{ texec op }}
  end.


Definition y := tBinOp (tMul) (@tConst Nat 5) (@tConst Nat 6).

Eval compute in compile y.

Theorem compiler_is_correct : forall (t : type)(e : texpr t), tprogramDenote (@compile _ e nil) tt = (texprDenote e, tt).

Abort. (* Proof left as exercise *)

(*

compiler_is_better : forall e p s, programDenote (compile e ++ p) s  = programDenote p (expDenote e :: s).

*)
Theorem compiler_is_better t (e : texpr t) :
   forall s0 s1 (p : tprogram (t :: s0) s1) (vs : vstack s0), tprogramDenote (compile e +++ p) vs = tprogramDenote p (texprDenote e, vs).

  (*

  induction e.
  - simpl; trivial.
  - simpl. intro .
    intros.
    rewrite <- app_assoc.
    rewrite IHe2.
    rewrite <- app_assoc.
    rewrite IHe1.
    simpl; trivial.

   *)
  
Abort.
