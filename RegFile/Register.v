Require Import Omega.

Module RegFileArray.

  Fixpoint leb (m:nat) : nat -> bool :=
    match m with
    | O => fun _:nat => true
    | S m' =>
      fun n:nat => match n with
              | O => false
              | S n' => leb m' n'
              end
    end.



Eval compute in (leb 2).