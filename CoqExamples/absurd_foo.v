Definition foo (n : nat) : match n with
                            | 0 => bool
                            | S _ => nat 
                            end 
  := match n with
      | 0 => true
      | S _ => 42
      end.

Check foo.
Print foo.
