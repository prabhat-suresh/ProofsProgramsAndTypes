Check True.
(* Check trivial. *)
Theorem mythm : 2 = 2.
Proof.
  trivial. (* This is a tactic *)
  Show Proof.
Qed.

Check mythm.
(* Check (mythm : 1 = 1). *)
Check (eq_refl : 2 = 2).

(* Equivalently *)
Definition mythm : 2 = 2 := eq_refl.

Theorem foo : forall a b : nat, (a + b)^2 = a^2 + b^2 + 2*a*b
