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

> Reference Book: [Certified Programming with Dependent Types](./cpdt.pdf)

Programming Language (Typed) ~== Proof Assistant
Type Checking ~== Proof Checking

- The reason they are equivalent is that the programming language is a very simple language called the Calculus of Constuction (CoC) -> Coq (Due to Coquand).
- The core of the system is a trusted kernel that should be as simple as possible.
- There can be many layers to make life easier, which need not be trusted because if it proves something wrong, the trusted kernel will catch it.

## Type Theory

- Modus Ponens and Function Application showing underlying connection between programming language type theory and Logic

| Programming | Logic |
| ----------- | ----- |
| Types      | Statements |
| Terms | Proof |
| x:A | x is the proof of the statement A |

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
Lemme name: type.
Proof.
    tactics
Qed.

Definition foo: type := exp
Definition foo: nat := 2+40

Definition thm: type := __

Compute exp. (* simplifies and then Checks *)
```

#### Gallina Expression
exp = Variable
        | f e (function application)
        | fun x:A => exp (function abstraction)

#### Calculus of Construction
Types: Type universes and function types

[Square example](./CoqExamples/square.v)
[Types of Bool and Nat](./CoqExamples/print.v) -> inductive sets

<!-- TODO: AND, OR, NOT -->
[AND](./CoqExamples/andb.v)

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
    to prove for all x -> P x, we will end up with dependently typed functions
- CoC + Inductive types (also Type Universes, which we'll look into later) makes up the whole system
- eq_refl is an element of type x=x for all x (it does this by taking in implicit arguments)

#### forall
forall A:Prop A -> A
fun A: Prop => fun a:A => a

forall a:A, B a
fun a.A, ...

### Type universes
Prop, Set, Type
Prop is built into the language. You cannot produce it using induction or in any other way.
Set is an inductive type.

list is not a type. "list of a" is a type
list A: Type -> Type (list can be thought of as Type -> Type)

[ANDB](./CoqExamples/andb.v) and1

#### Prop
A proposition should not be reduced to the world of true and false. They are mathematical/propositional statements.
andb is not inductively defined whereas and is

Inductive and (A B: Prop): Prop
| conj: A -> B -> and A B
(takes a pair of proofs of A and B then produces a proof of their conjunction)

andb is defined with the appropriate match as bool is an inductive type
andb: bool -> bool -> bool

but and: Prop -> Prop -> Prop
A and B are propositions, what is the proposition A ^ B: Prop?

Inductive and (A B : Prop) : Prop :=  conj : A -> B -> A /\ B.
the conj (conjunction) constructor is used to construct the proof of A and B

[and](./CoqExamples/and.v)

Similarly or: Prop -> Prop -> Prop is defined as

```coq
Inductive or (A B : Prop) : Prop :=
    or_introl : A -> A \/ B | or_intror : B -> A \/ B.
```

[or](./CoqExamples/or.v)

False is defined as follows:
Inductive False : Prop :=  .

It's a type that has no elements (otherwise that element would be a proof of False)

not of A cannot be defined in constructive logic and hence LEM (law of excluded middle) double negation etc cannot be proved.

[not and false](./CoqExamples/false.v)

not : Prop -> Prop
Definition not (A: Prop) := A -> False
(Currency notes are promises) We are not proving False. We promise to prove Fale by providing an element of it if an element of A is given, which indirectly implies that there is no element of A.

Everything here assumes that the system is consistent (Refer Hurdle's incompleteness theorem)

Equivalence of not (not A) and A is not provable in constructive logic
A equivalent to B is same as A -> B ^ B -> A

A -> not (not A) is provable but the converse is not
Note: this is for all A. For a particular A it's possible through case by case analysis (like in the case of negb(negb x))

DeMorgan's Laws
```
not a \/ not b === not (a /\ b) (converse i.e. reverse direction is not provable, though forward is)
not a /\ not b === not (a \/ b) (Both directions provable)

```
[DeMorgan](./CoqExamples/demorgan.v)

> A few useful tactics to keep in mind: refine, exact, intros, intuition, eauto, induction, destruct, inversion

expression language --> (Compiled to) Stack machine
C --> X86 assembly

exp = nat | exp op exp

### Stack Machine instructions
1. push nat
2. pop
3. exec op

[Stack Machine compiler](./CoqExamples/expr_to_stack_machine.v)

- To proove that the compiler works as expected we have to express it in coq's language: Gallina (Denotational semantics)
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
- But the more interesting part of using index instead of parameters is when we

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
