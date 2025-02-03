Definition andb: bool -> bool -> bool
:= fun x: bool => match x with
                  | true => fun y: bool => y
                  | false => fun y: bool => false
                  end.
Check andb.

(* Definition and (P Q : bool) : bool := *)
(*   match P, Q with *)
(*   | true, true => true *)
(*   | _, _ => false *)
(*   end. *)
(* Check and. *)

Print and.
