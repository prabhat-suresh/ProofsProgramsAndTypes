Print or.

(* for all prop A B and C, (A -> C) -> (B -> C) -> (A \/ B -> C) *)
(* Note: we used -> instead of ^ above *)

Lemma foo: forall (A:Prop)(B:Prop)(C: Prop), (A->C)->(B->C)-> or A B -> C.
refine (fun A B C:Prop => fun f => fun g => fun pAoB => 
  match pAoB with
  | or_introl x => f x
  | or_intror y => g y
  end).
