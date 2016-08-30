Inductive even : nat -> Prop :=
|EvenO : even 0
|EvenSS : forall n : nat, even n -> even(S(S n)).


Theorem even_0 : even 0.
Proof.
apply EvenO.
Qed.

Theorem even_4 : even 4.
Proof.
apply EvenSS.
apply EvenSS.
apply EvenO.
Qed.

Theorem even_4_1 : even 4.
Proof.
constructor. constructor. constructor.
Qed.

(*
Hint Resolve EvenO.
Hint Resolve EvenSS.
*)

Hint Constructors even.

Theorem even_4_2 : even 4.
Proof.
auto.
Qed.
