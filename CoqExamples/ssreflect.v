Require Import ssreflect ssrbool.

Example foo: Prop := true.
Example nfoo: Prop := false.

Print foo.
Print nfoo.

Set Printing Coercions.

Print foo.
Print nfoo.

Print is_true.

(*Unset Printing Coercions.*)

Goal forall a b : bool, a && b <-> a /\ b.
    constructor. Show Proof.
    - move => H. Show Proof. apply /andP. Show Proof. trivial. Show Proof.
    - move => H. Show Proof. apply /andP. Show Proof. trivial. Show Proof.
    Check andP.
    (*- case a; case b.*)
    (* essentially wrting the truth table proof by hand *)
    (*    + constructor; trivial.*)
    (*    + simpl; move => h.*)
    (*    constructor; trivial.*)
Qed.

Search (reflect _ _).

Check reflect.
Print reflect.
Print Bool.reflect.

Lemma myandP (a b : bool) : reflect (a /\ b) (a && b).
    refine match a, b with
           | true, true => ReflectT _ (conj eq_refl eq_refl)
           | _, _ => ReflectF _ _
           end; intuition.
    (*case a; case b; simpl.*)
    (*- apply ReflectT; intuition.*)
    (*- apply ReflectF; intuition.*)
    (*- apply ReflectF; intuition.*)
    (*- apply ReflectF; intuition.*)
Qed.

Lemma myorP (a b : bool) : reflect (a \/ b) (a || b).
    (*case a; case b; simpl.*)
    (*- apply ReflectT; intuition.*)
    (*- apply ReflectT; intuition.*)
    (*- apply ReflectT; intuition.*)
    (*- apply ReflectF; intuition.*)
    refine match a, b with
           | false, false => ReflectF _ _
           | _, _ => ReflectT _ _
           end; intuition.
Qed.
