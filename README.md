# Proofs, Programs and Types
[Course Repo](https://bitbucket.org/piyush-kurur/ppt/src/master/)

1. Formal Proofs: Mathematical proofs that are machine checked

- Rigorous mathematical proofs assume a lot of things in the steps involved, leaving the possibility of a bug in the proof possibly due to a misunderstanding of the theorem or a wrong theorem being used
- The only way forward is machine verification of the proofs

> Classification of finite simple groups, a theorem with volumes written on its proof

2. Formally certified software: correctness of the software is proved and the proof is machine checked

## Proof Assistant
> A "program" that takes as input a formal proof and checks
- Coq, Lean etc
- Constructive based on type theory

### Check the course page and set up Coq and editor

> [!TIP] Reference Book: [Certified Programming with Dependent Types](./cpdt.pdf)

Programming Language (Typed) ~== Proof Assistant
Type Checking ~== Proof Checking

- The reason they are equivalent is that the programming language is a very simple language called the Calculus of Constuction (CoC) -> Coq (Due to Coquand).
- The core of the system is a trusted kernel that should be as simple as possible.
- There can be many layers to make life easier, which need not be trusted because if it proves something wrong, the trusted kernel will catch it.

## Type Theory

- Modus Ponens and Function Application showing underlying connection between programming language type theory and Logic

    | Programming | Logic                             |
    |-------------|-----------------------------------|
    | Types       | Statements                        |
    | Terms       | Proof                             |
    | x:A         | x is the proof of the statement A |

## Coq
- Gallina: an implementation of CoC, a simple language for writing proofs
    - The trusted part of the system where all the type checking is done
- Vernacular: Management layer
- Tactics: Meta programming part (untrusted)
    - The macro system
    - Can be as complicated as you want
    - You can fit in anything here, heck even an ML model

### Gallina
- Check galinaexp. -> checks if expr is well typed and gives the type
- Check galinaexp:type. -> checks if expr is well typed and is of given type

- exp: A -> Most important judgement that Coq verifies

```coq
Lemma name: type.
Proof.
    tactics
Qed.

Definition foo: type := exp
Definition foo: nat := 2+40

Definition thm: type := __

Compute exp. (* simplifies and then Checks *)
```

#### Gallina Expression
```
exp = Variable
    | f e (function application)
    | fun x:A => exp (function abstraction)
```

#### Calculus of Construction
Types: Type universes and function types

[Square example](./CoqExamples/square.v)

[Types of Bool and Nat](./CoqExamples/print.v) -> inductive sets

[andb](./CoqExamples/andb.v)

### Defining new types (inductive definition)

- The core types are type universes and function types (Built in)
- You can add on top of that using inductive definitions (Definiting types using finitely many cases)
- Nat, Bool etc are defined in the standard library

#### Boolean
1. true : bool (Axiom)
2. false : bool (Axiom)
3. ~There are no other booleans (implicit when you say boolean is defined inductively as)~

[MyBool](./CoqExamples/mybool.v)

### Dependent Types
- Dependently typed functions have outputs whose type depends on the input
- If you follow the first principles:
    1. every statement is a type
    2. A proof of the statement is an element of that type

To prove for all x -> P x, we will end up with dependently typed functions
- CoC + Inductive types (also Type Universes, which we'll look into later) makes up the whole system
- eq_refl is an element of type x=x for all x (it does this by taking in implicit arguments)

#### forall
forall A:Prop A -> A

fun A: Prop => fun a:A => a

forall a:A, B a

fun a.A, ...

### Type universes
Prop, Set, Type

- Prop is built into the language. You cannot produce it using induction or in any other way.
- Set is an inductive type.

> [!IMPORTANT] list is not a type. "list of a" is a type
list A: Type -> Type (list can be thought of as Type -> Type)

[ANDB](./CoqExamples/andb.v)

Gallena has no Polymorphism baked into the language. The dependent functions and type universes are so powerful that including them in the language gives us polymorphism automatically as a result.

#### Prop
- A proposition should not be reduced to the world of true and false. They are mathematical/propositional statements.
andb is not inductively defined whereas "and" is

```coq
Inductive and (A B: Prop): Prop
| conj: A -> B -> and A B
(* takes a pair of proofs of A and B then produces a proof of their conjunction *)
```

andb is defined with the appropriate match (as bool is an inductive type)
> andb: bool -> bool -> bool
but
> and: Prop -> Prop -> Prop
> A and B are propositions, what is the proposition A ^ B: Prop?
```coq
Inductive and (A B : Prop) : Prop :=  conj : A -> B -> A /\ B.
```
the conj (conjunction) constructor is used to construct the proof of A and B
> [and](./CoqExamples/and.v)

Similarly or: Prop -> Prop -> Prop is defined as
```coq
Inductive or (A B : Prop) : Prop :=
    or_introl : A -> A \/ B | or_intror : B -> A \/ B.
```
> [or](./CoqExamples/or.v)

False is defined as follows:
```coq
Inductive False : Prop :=  .
```
- It's a type that has no elements/inhabitants (otherwise that element would be a proof of False)

> [!NOTE] not of A cannot be defined in constructive logic and hence LEM (law of excluded middle), double negation etc cannot be proved.

[not and false](./CoqExamples/not_and_false.v)

not : Prop -> Prop
```coq
Definition not (A: Prop) := A -> False
```
> [!IMPORTANT] (Currency notes are promises) We are not proving False. We promise to prove Fale by providing an element of it if an element of A is given, which indirectly implies that there is no element of A.

Everything here assumes that the system is consistent (Refer Hurdle's incompleteness theorem)

> [!NOTE] Equivalence of not (not A) and A is not provable in constructive logic
> A equivalent to B is same as A -> B ^ B -> A

A -> not (not A) is provable but the converse is not
> [!NOTE] : this is for all A. For a particular A it's possible through case by case analysis (like in the case of negb(negb x))

DeMorgan's Laws
```
not a \/ not b === not (a /\ b) (converse i.e. reverse direction is not provable, though forward is)
not a /\ not b === not (a \/ b) (Both directions provable)

```
[DeMorgan](./CoqExamples/demorgan.v)

> [!TIP] A few useful tactics to keep in mind: refine, exact, intros, intuition, eauto, induction, destruct, inversion
### Stack Machine and Expression Language

expression language --> (Compiled to) Stack machine 
(Just like C --> X86 assembly)
```
exp = nat 
    | exp op exp
```
### Stack Machine instructions
1. push nat
2. pop
3. exec op

[Stack Machine compiler](./CoqExamples/expr_to_stack_machine.v)

- To prove that the compiler works as expected we have to express it in coq's language: Gallina (Denotational semantics)
- The theorem that we want to prove is a weak lemma and thus the induction hypothesis is also weak and not sufficient to prove the theorem.
- Often in such cases it is easier to prove a more general theorem and then state that the weak lemma is a special case of the more general theorem. That's because the more general theorem also has a more general and powerful induction hypothesis.

[Test1](./CoqExamples/test1.v)

## Correctness by construction
- Rule out bad behaviour by using types

```coq
list : forall A:Type, Type = Type -> Type

Inductive list (A : Type) : Type :=
    nil : list A | cons : A -> list A -> list A.

nil : forall A : Type, list A.
cons : forall A : Type, A -> list A -> list A.

Arguments nil {A}. (* A is an implicit argument which is maximally inserted *)
          nil [A]. (* warned by compiler as it's implicit but not maximally inserted *)
Arguments cons {A}.
```

- The coq interpreter solves the unification problem by looking at the context and inferring the types.
- let x in the following function be an implicit argument
```coq
f: (x: T1) -> (y: T2) -> T3
```
- if f is maximally inserted then Check f will give f _ that is T2 -> T3
- if f is not maximally inserted then Check f will give f that is T1 -> T2 -> T3
- f (y=t) or equivalently @f _ t can be used to make the implicit arguments explicit
- That is for functions with more than one argument. For one argument functions there is no choice - it has to be maximally inserted

- The A in the definition of list is a parameter and has a scope till the end of the definition
- In the following definition A is an index
```coq
Inductive list : forall A:Type, Type -> Type :=
    | nil {A: Type}: list A (* nil : list nat - this definition will rule out the creation of lists of any other type other than nat *)
    | cons {A: Type}: A -> list A -> list A.
```
- The above definition is equivalent to the one before except that we didn't have to write Arguments nil {A} etc.
But the more interesting part of using index instead of parameters is when we:

- Consider the following expression language with two types of values
```coq
Inductive exp :=
    | Bconst: bool -> exp
    | Nconst: nat -> exp
    | Plus: exp -> exp -> exp
    | And: exp -> exp -> exp
    | If: exp -> exp -> exp -> exp
```
- This exp allows creation of expressions like Plus (Bconst true) (Nconst 1) which are semantically ill-typed
- So we use index instead of parameter like [bool and nat expr](./CoqExamples/bool_nat_expr.v) to ensure correctness by construction

- We haven't seen types of the kind [Absurd foo](./CoqExamples/absurd_foo.v)
- This function can be used to make sure at compile time that the value received is indeed of type A using the power of dependent types [recover](./CoqExamples/recover.v)

#### Vector type
- List of length n
```coq
Inductive vector (A : Type) : nat -> Type :=
    | vnil : vector A 0
    | vcons : forall n : nat, A -> vector A n -> vector A (S n).

Arguments vnil {A}.
Arguments vcons {A} _ {n}.
(* vcons : forall A : Type, A -> forall n : nat, vector A n -> vector A (S n) A and n are implicit arguments and we name them but we don't know the first argument's (whose type is A) name and thus put an _ *)
```
[vector](./CoqExamples/vector.v)

#### Red Black Tree
- A red black tree is a binary search tree where each node is either red or black
- The root is black (not really important as if it's red then it can be changed to black (But black nodes can't be changed to red))
- Every path from the root to a leaf has the same number of black nodes
- Every red node has black children
[Red Black Tree](./CoqExamples/red_black_tree.v)

### Phantom Types
- Phantom types are types that are not used in that particular function but used elsewhere to ensure correctness.
[Phantom Types](./CoqExamples/phantom_types.v)

#### Less than or equal to and equality
- We like to think of them as mathematical statements rather than booleans.
- Define inductive types that capture the mathematical statements such that it's correct by construction.
[less than or equal to](./CoqExamples/lte_data_type.v)
- The general equality type (Polymorphic) is not built in. It's also defined inductively with the same idea as for nats
[general equality](./CoqExamples/general_eq.v)
- In general, the general equality is not decidable. However, just like other undecidable problems, we can define it nevertheless.
- eq is a very mysterious type. The definition of eq might lead us to believe that all proofs of x=y are eq_refl. However, this is not the case. You cannot prove the following lemma which captures this notion as it's not even consistent with the types let alone be wrong.
```coq
Definition foo := forall {A: Type} (x y: A) (pf: x=y) -> pf = eq_refl.
(* Heck you can't even prove the following lemma (though it's well typed unlike the above one) *)
Lemma foo : forall {A: Type} (x: A) (pf: x=x), pf = eq_refl.
```
- The mathematics of eq and paths in a topological space are similar. eq_refl is like the trivial path from x to x. There can be other non-trivial paths from x to x. These other ways of constructing eq will not be possible directly as a term, but could be produced indirectly like False.
- eq_refl can be used only in the case that two terms are equal by definition.
- In mathematics, the extentiality principle - forall f,g: A -> B, forall x: A, f x = g x -> f = g. But in type theory this is blasphemy. As a computer scientist, this is inacceptable as this would mean bubble sort, merge sort and the worst sorting algorithms are all the same. The functions f and g carry computational value.
- Constructive logic is more powerful and richer than classical logic. Classical logic is a subset that can be embedded in constructive logic using Continuation Passing Style (CPS)

## Props
- So far you could work completely without Props. But Props are useful when you only worry about the mathematical propositions and not the computations involved.
- Just like the Ocaml compiler does all the type checks at compile time and the run time is stripped of all the types, if you extract coq to Ocaml or Haskell the Props will be stripped off in the resulting code which is still safe if used that way (just like the Ocaml runtime having type guarantees after compiling).
- Removing Props is fine as we just need the proof term and not the computation involved.
- But this has a caveat. You can't return a Type or Set from a match if you inspect the computation involved in the Prop term.
- You can however return a Prop from such a match as all of them eventually will be removed.

## Tactics
- Automating proofs using tactics (imperative languages which are allowed to fail) using Ltac
- Ltac is an imperative language with bits of logical programming
- Difference between . and ; -> t1 . t2 applies t2 to one goal in t1 whereas t1 ; t2 applies t2 to all the goals in t1
- Ltac is a typeless or dynamically typed language in some sense
```coq
Ltac name := Ltac_script. (* syntax for defining an Ltac script *)

Ltac induct_on_n n := induction n; compute

(* Defining the assumption tactic on our own without using the standard library *)
Ltac my_assumption := match goal with
    | Hyp: ?G |- ?G => exact Hyp
end.
```
> [!NOTE] The ? is for unification variables

[Ltac](./CoqExamples/ltac.v)
- The match in Ltac is not a pattern matching, but rather a search where if a branch fails, the search continues with the next branch.
- A typical example of an Ltac script:
```coq
Ltac foo := repeat match goal with
    | ... |- ... => _
    | ... |- ... => _
    | ... |- ... => _
    | _ => simple; eauto
end.
```
[Test2](./CoqExamples/test2.v)

> 2025-03-21

### Tactic Scripts
1. match - proof search happens
2. repeat - repeats the tactic script
3. do n tac

- Tactics can take arguments which can be Coq terms
- You almost always want to use eauto instead of auto
- eauto is a tactic that tries to automatically solve the goal by using the Lemmas and Theorems that are already defined in the context.
- But this will be slow in implementation. So we have databases
> [!NOTE] eauto uses the core database by default
```coq
Lemma foo: forall x y z, x <= y -> x + z <= y + z.
Hint Resolve foo : core. (* hints the core database to use foo *)
Hint Constructor bar : db. (* hints the db database to use bar *)
```

### Proof automation: The big picture
```coq
Ltac crush := repeat match goal with
    | H: ?G |- ?G => exact
    (* and other generic tactics like intros, simpl, trivial, compute, induction, destruct, apply, lazy, inversion, rewrite (in forward and reverse direction) etc *)
    | ......
    | ......
    | _ => eauto
end.
```
- The idea is to develop your proofs alongside your codebase 
- The specific parts of the lemmas about your codebase and business logic goes into a database
- The crush tactic is therefore very powerful and can be used to automate proofs of lemmas about your codebase
- You start with simple lemmas about your codebase that you can prove and then add it to your database. In more complex theorems you can use eauto and see if it proves it. If not you'll have to prove it by hand or add more lemmas to your database
- There are a lot of tactics out there, but you can do without most of them by just using the common ones mentioned above and look up the more rare ones when needed (like there are dependent versions of induction, inversion etc)
> Going back to the [Stack Machine](./CoqExamples/expr_to_stack_machine.v) example and automating the proof
- Use dumb tactics inside the Ltac script - the dumber the tactic the more statements it can prove

### A few important types
[Important Types](./CoqExamples/important_types.v)
#### Disjoint union or sum type
- Essentially, the following types are cousins of the sum type:
```coq
Inductive sum (A B : Type) : Type :=
  | inl : A -> sum A B
  | inr : B -> sum A B.

(* Written concisely as A + B *)
```
##### Sumbool type:
```coq
Inductive sumbool (A B : Prop) : Type :=
  | left : A -> sumbool A B
  | right : B -> sumbool A B.

(* Written concisely as {A} + {B} *)
```
- This can be used wherever a boolean is used and in the extracted code all the props will be gone and it boils down to just a boolean
- But the advantage is that in the Coq/Gallina world the type still carries the proof term of the associated Prop which is much more useful for proving stuff than reducing it down to a boolean from which you can't recover the proof term later
- For example instead of the plain '<':
```coq
< : nat -> nat -> bool
<? : (x:nat) -> (y:nat) -> sumbool {x<y} {x>=y}
```
- The above replacement of '<' is way more useful and you can match on it using the constructors of the associated proof terms
##### Sumor type:
```coq
Inductive sumor (A : Type) (B : Prop) : Type :=
  | in_left : A -> sumor A B
  | in_right : B -> sumor A B.

(* Written concisely as A + {B} *)
```
- On extraction and stripping off all the props this would be equivalent to the Option type.
- But again the advantage is that you can use the type B to convey the reason of error such as an error message or such instead of just None which can help with proofs
#### Sigma types
- pi (product) type - forall x: A, B     pi (x belongs to A) B
- sigma (summation) type - exists x: A, B
	- conveys the existence of x in A such that B
```coq
ex
     : forall A : Type, (A -> Prop) -> Prop

Inductive ex (A : Type) (P : A -> Prop) : Prop :=
    ex_intro : forall x : A, P x -> exists y, P y.
	
ex_intro
     : forall (A : Type) (P : A -> Prop) (x : A), P x -> exists y, P y
```
- sig type: These types are calles refinement types
```coq
sig
     : forall A : Type, (A -> Prop) -> Type

Inductive sig (A : Type) (P : A -> Prop) : Type :=
    exist : forall x : A, P x -> {x : A | P x}.

exist
     : forall (A : Type) (P : A -> Prop) (x : A), P x -> {x : A | P x}
```
- 
```coq
(*sig A B = {x : A | B x}.*)

sig nat (le 4) = {x: nat | le 4 <= x}
(* Vectors could have been defined as follows as well.*)
vector A n = {xs: list A | length xs = n}
```
- sigT type: referred to as the actual existential type
```coq
sigT
     : forall A : Type, (A -> Type) -> Type

Inductive sigT (A : Type) (P : A -> Type) : Type :=
    existT : forall x : A, P x -> {x : A & P x}.

Arguments sigT [A]%type_scope P%type_scope
Arguments existT [A]%type_scope P%function_scope x _

existT
     : forall (A : Type) (P : A -> Type) (x : A), P x -> {x : A & P x}

```
- An application is to have a heterogeneous lists:
```coq
Definition pointedType A := sigT A (fun T => T). (* Using identity function *)
pointedType = {A: Type & A}
(* This type is basically a space along with a point in it (like vector spaces with an origin) *)
(* list pointedType will be a heterogeneous list but you will not be able to inspect its type and make decisions based on its type. For that you will have to do a workaround as shown in important_types.v *)
```

> [!TIP] Read [Robert Harper's blog on how dynamic languages are unityped :)](https://existentialtype.wordpress.com/2011/03/19/dynamic-languages-are-static-languages/)

### Proof by reflection
- So far we have used two methods:
	1. Correctness by construction
	2. Automated proofs using proof tactics
- Limitations of computationally infeasible proof terms like 2^35 <= 2^36 which will have 2^35 terms of le_S
- One approach to prove such a lemma is to make the trade off between space and time by computing values:
	- Use leb (the boolean equivalent) to compute the boolean equivalent and then prove the correctness of leb
```coq
	Lemma leb_le : forall m n, leb m n = true <-> le m n
```
- The second approach is to structurally analyze the terms and prove them based on those properties: i.e., proving m<=n <=> a^m <= b^n.

> [!NOTE] The ring tactic is implemented using proof by reflection

[ring tactic](./CoqExamples/poly.v)

- Will have to represent the core datatype (Polynomials in this case). A simplified version is as follows:
```coq
Inductive Poly R :=
    | Const : R -> Poly R
    | Add : Poly R -> Poly R -> Poly R
    | Mul : Poly R -> Poly R -> Poly R
    | Zero : Poly R
    | One : Poly R.
```

[!IMPORTANT] Read [boolean blindness](https://existentialtype.wordpress.com/2011/03/15/boolean-blindness/)

- reflect and reduce the goal into something in the gallina word
	- called reification (reify) -> the opposite of abstraction

### Monoid Simplification
(A,\*,e)
1. * is associative
	1. x\*e = e\*x = e
[Monoids](./CoqExamples/monoid.v)

Main idea of reflection is:
1. Build a small Ast to capture terms (In Gallina world)
2.  Reify actual terms to the above Ast (Tactic - Ltac world)
3. Normalization of Ast (Gallina)
4. Lemma - Normalization preserves meaning (Gallina)
	- denote e = denote (normalization e)
- For equational proofs (e1 = e2) change to equivalent: denote me1 = denote me2 (by computation, tactic guesses the term that under compute of denote will give back the same expression)
- Then using normalization lemma it's changed to: denoteL (normalization me1) = denoteL (normalization me2)

### SSreflect library
- new tactics
- better rewrites

#### Boolean reflection
**Prop:** the universe of all constructive Logical statements
- For example <=   : nat -> nat -> Prop is a meta concept in your head
- and le : nat -> nat -> Prop is defined such that forall x,y and x<=y then le x y is inhabited

It so happens that for nats le is decidable
- dec_le : forall x, y  : nat x<=y \\/ not (x<=y)
- Definition Dec (P: Prop) = P \\/ not P
- dec_le : forall x,y : nat, Dec (x<=y)

leb : nat -> nat -> bool
- The proof term is just one bit, whereas it could be huge for the Prop world proof term
- Apart from boolean blindness this has one more disadvantage: for symbolic terms you cannot use this.
	- For example if you have a proof of x<=y you can prove x+n<=y+n and use it.
	- Therefore the boolean variant is better for concrete values and Prop variant is better for symbolic values

- Boolean reflection is a mechanism to reflect bools as Props and vice versa
- bools as Props:
```coq
is_true = fun b : bool => b = true
     : bool -> Prop
```
[SSreflect](./CoqExamples/ssreflect.v)
- stands for small scale reflection
- Both of these convey the same logical meaning if and only if
	- a && b <-> a ^ b
	- andP: reflect (a^b) (a&&b)           (this is better and more idiomatic because it's a reflection view - a bridge between the Prop and boolean world)

### Topics not covered so far
- Co-inductive types
- General recursion
	- For a proof assistant like Coq, Termination checker is important (otherwise it would lead to unsound logic)
	- Algorithms like merge sort are not easy to prove for termination as the smaller parts into which the list is recursively divided are not structurally lesser than the original list

### Typed expressions
- We'll revisit the stack machine
[Typed Expressions](./CoqExamples/typed_expressions.v)
- Shallow vs Deep embedding: shallow embedding doesn't let you to introspect into the types, whereas Deep embedding allows introspection
```coq
Variant sort := NAT | BOOL (* Deep embedding *)
Definition sort := Set (* Shallow embedding *)
```
- Shallow allows for easy and quick implementation and is suitable when we don't want to look into the types. But if you want to introspect and pattern match use deep embedding

- Having typed low level machine language ensures that the bug that we identified by proving in the untyped stack machine cannot even be created in the typed version. So much guaranteed by types.

## Overview
- Correctness of Programs, using a language that is:
	1. Simple (only a few constructs)
	2. Powerful
	3. A principled approach
	4. Elegant
- Type checking <=> Proof checking
- Programs <--(Types)--> proofs

- Write programs matching specification (which is expressed as a type) all within the same framework
	1. Tactics to write code
	2. Correct by construction
	3. Reflection: Computational reasoning <=> Intuitive reasoning