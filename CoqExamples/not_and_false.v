Check False.
Print False.

Check not.
Print not.

Search (False -> _).

Lemma negneg: forall A: Prop, A -> not(not A).
refine (fun A: Prop => fun x => fun f: not A => f x).
Defined.

Lemma absurd: forall A: Prop, False -> A.
refine (fun A:Prop => fun x: False => match x with
                                        end).
Defined.
