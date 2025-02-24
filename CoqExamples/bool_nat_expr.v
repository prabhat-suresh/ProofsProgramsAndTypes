Variant sort: Type := NAT | BOOL.
Inductive exp: sort -> Type :=
| Bconst: bool -> exp BOOL
| Nconst: nat -> exp NAT
| Plus: exp NAT -> exp NAT -> exp NAT
| And: exp BOOL -> exp BOOL -> exp BOOL
| If{s}: exp BOOL -> exp s -> exp s -> exp s.

Definition sortDenote (s: sort): Set :=
  match s with
  | NAT => nat
  | BOOL => bool
  end.

Search (bool -> bool -> bool).

Fixpoint expDenote {s} (e: exp s): sortDenote s :=
  match e with
    (* In older versions of coq you would have to write an explicit match which newer versions of coq manages to infer and rewrite:
       match e in exp s0 as e0 return sortDenote s0 with
    *)
  | Bconst b => b
  | Nconst n => n
  | Plus e1 e2 => (expDenote e1) + (expDenote e2)
  | And e1 e2 => andb (expDenote e1) (expDenote e2)
  | If e1 e2 e3 => if (expDenote e1) then (expDenote e2) else (expDenote e3)
  end.

Check expDenote.
Print expDenote.
