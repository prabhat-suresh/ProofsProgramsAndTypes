Lemma dM1: forall A B:Prop, ~A \/ ~B -> ~ (A /\ B).
  refine (fun A B => fun nAornB => match nAorB with
                           | or_introl f => fun x: A /\ B => match x with
                                    | conj a b => f a
                                    end

                           | or_intror f => fun x: A /\ B => match x with
                                    | conj a b => f b
                                    end
                            end).
Qed.

Lemma dM3: forall A B: Prop, ~A /\ ~B -> ~ (A \/ B).
  refine (fun A B => fun nAandnB => match nAandnB with
                          | conj nA nB => fun AorB => match AorB with
                              or_introl).
