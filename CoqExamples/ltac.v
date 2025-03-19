Ltac my_assumption := match goal with
    | Hyp: ?G |- ?G => exact Hyp
end.

Ltac my_induction := match goal with
    | |- nat -> _ => let n := fresh "n" in intro n; induction n
end.

Goal forall A: Prop, A -> A.
    intros.
    my_assumption.
Qed.

Goal forall n: nat, 0 + n = n.
    my_induction; trivial.
Qed.
