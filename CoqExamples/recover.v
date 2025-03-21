Check option.
Print option.

Check tt.

Definition recover {A} (o : option A) : match o with
                                            | Some _ => A
                                            | None => unit
                                          end :=
  match o with
    | Some a => a
    | None => tt
  end.

Check recover.
Print recover.

(* Definition something: nat = recover (hd ... ). *)
