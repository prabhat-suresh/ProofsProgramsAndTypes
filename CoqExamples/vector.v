Require Coq.Vectors.Vector.
Import Vector.VectorNotations.
Check Vector.t.
Print Vector.t.
Check Vector.cons.

Definition hd {A : Type} {n : nat} (v : Vector.t A (S n)) : A :=
    match v with
    | a :: _ => a
    end.

Check hd.
Print hd.

Definition tl {A : Type} {n : nat} (v : Vector.t A (S n)) : Vector.t A n :=
    match v with
    | _ :: v' => v'
    end.

Check tl.
Print tl.

Check IDProp.
Print IDProp.

Check Vector.map.

Fixpoint my_map {A B : Type} (f : A -> B) {n : nat} (v : Vector.t A n) : Vector.t B n :=
    match v with
    | [] => []
    | a::v' => f a :: my_map f v'
    end.

(*Section Zip.*)
(*    Context {A B C : Type}.*)
(*    Context {f : A -> B -> C}.*)
(*    Fixpoint zip {n : nat} (u : Vector.t A n) (v : Vector.t B n) : Vector.t C n :=*)
(*        match u, v with*)
(*        | x::xs, y::ys => f x y :: zip xs ys*)
(*        | [], _ => []*)
(*        end.*)
(*End Zip.*)
(* The elaborator is not able to translate the above definition like it did in the case of the hd function and Gallina rejects it as all cases are not exhaustively matched *)
(* In general, looking at the types and deducing the possible branches is undecidable (higher order unification problem). The elaborator just takes care of a few simple cases *)
Section Zip.
    Context {A B C : Type}.
    Context {f : A -> B -> C}.
    Fixpoint zip {n : nat} (u : Vector.t A n) : Vector.t B n -> Vector.t C n :=
        (*refine (match u with*)
        (*        | [] => fun _ => []*)
        (*        | x::xs => fun v: Vector.t B (S _) => f x (hd v) :: zip xs (tl v)*)
        (*        end).*)
        match u with
        | [] => fun _ => []
        | x::xs => fun v => f x (hd v) :: zip xs (tl v)
        end.
    Check zip.
    Print zip.
End Zip.
