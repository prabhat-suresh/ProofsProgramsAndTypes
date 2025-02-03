Print and.

Lemma proj1: forall (A:Prop) (B:Prop), and A B -> A.
  refine (fun A:Prop => fun B:Prop => fun pAnB =>
  match pAnB with 
  | conj x y => x 
  end).

Check conj.
