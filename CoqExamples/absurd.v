Definition absurd {A:Type} (pf: False): A :=
    match pf with
    end.

Check gt.

Definition absurd_nat n (pf: n > 0) :=
    match pf with
    |gt n 0 => 42
    end.
