Require Import List.
Import ListNotations.
Section Monoid.
Context (A : Type)(e : A)(op : A -> A -> A).

Infix "*" := op.

Hypothesis identityL : forall x : A, x * e = x.
Hypothesis identityR : forall x : A, e * x = x.
Hypothesis assoc : forall x y z : A, x * (y * z) = (x * y) * z.


Inductive mexpr :=
| mone : mexpr
| mconst : A -> mexpr
| mop : mexpr -> mexpr -> mexpr.


Fixpoint denote (me : mexpr) : A :=
  match me with
  | mone => e
  | mconst x => x
  | mop me1 me2 => denote me1 * denote me2
  end.


Fixpoint normalise (me : mexpr) : list A :=
  match me with
  | mone => []
  | mconst x => [x]
  | mop me1 me2 => normalise me1 ++ normalise me2
  end%list.

Definition denoteL (la : list A) :=
  List.fold_left op la e.

Lemma denoteL_null : denoteL [] = e.
  compute; trivial.
Qed.

Lemma fold_op :  forall l a, fold_left op l a = a * fold_left op l e.
  intro l.
  induction l.
  - intro a. simpl. eauto.
  -  intro a0. simpl. rewrite IHl.
     rewrite <- assoc.
     rewrite <- IHl.
     rewrite identityR; trivial.
Qed.

Lemma denoteL_cons : forall l a , denoteL (a :: l) = a * denoteL l.
  intros l a.
  unfold denoteL.
  simpl; rewrite identityR. apply fold_op.
Qed.

Lemma denoteL_app: forall l1 l2, denoteL l1 * denoteL l2 = denoteL (l1 ++ l2).
  intro l1.
  induction l1.
  - intro l2; rewrite denoteL_null; rewrite app_nil_l; eauto.
  - intro l2.
    rewrite denoteL_cons.
    rewrite <- assoc.
    rewrite IHl1.
    rewrite <- denoteL_cons.
    rewrite <- List.app_comm_cons.
    trivial.
Qed.

Lemma normalise_lemma : forall me : mexpr, denote me = denoteL (normalise me).
  intro me.
  induction me.
  - compute; eauto.
  - compute; eauto.
  - simpl; rewrite IHme1.
    rewrite IHme2.
    apply denoteL_app.
Qed.

Ltac useless_reify ex := constr:(mconst ex).
(*  Ltac expects a tactic, so we have to use constr to tell coq that it's a Gallina term *)

Ltac reify ex := match ex with
                | ?ex1 * ?ex2 => let mex1 := reify ex1 in
                                 let mex2 := reify ex2 in
                                 constr:(mop mex1 mex2)
                | e => constr:(mone)
                | _ => constr:(mconst ex)
                end.

Section TestingReify.
  Context (x1 x2 x3 : A).
  Definition foo : mexpr := ltac: (let u := reify (x1 * ( x2 * x3 )) in exact u).
  
    (*
    mop (mconst x1) (mop (mconst x2) (mconst x3)) : mexpr
    *)
  Compute foo.

End TestingReify.

Ltac monoid := match goal with
            | |- ?ex1 = ?ex2 =>
            let mex1 := reify ex1 in
            let mex2 := reify ex2 in
            change (denote mex1 = denote mex2);
                do 2 rewrite normalise_lemma;
                compute; trivial
            end.

Goal forall x y z : A, x * (y * z) = (x * y) * z.
    intros.
    monoid.

