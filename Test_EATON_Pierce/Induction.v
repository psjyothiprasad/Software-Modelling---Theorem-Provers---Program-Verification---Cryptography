(*
Theorem plus_0_r_firsttry : forall n:nat,
  n + 0 = n.
Proof.
intros.
induction n.
simpl. reflexivity.
simpl. rewrite IHn.
simpl. reflexivity.
Qed.
*)

Fixpoint minus (m n : nat) :=
match m, n with
  | O   , _    => O
  | S _ , O    => n
  | S m', S n' => minus m' n'
  end.
 
Theorem minus_diag : forall n,
  minus n n = 0. 
Proof.
induction n.
simpl. reflexivity.
simpl. rewrite IHn.
simpl. reflexivity.
Qed.

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
intros.
induction m.
simpl. reflexivity.
simpl. reflexivity.
Qed.

Theorem mult_0_plus'_1 : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
intros n m.
simpl. reflexivity.
Qed.

Theorem mult_0_plus'_2 : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
intros.
assert (H: 0+n=n).
simpl. reflexivity.
rewrite H.
simpl. reflexivity.
Qed.



(*

Theorem plus_swap : forall n m p : nat, 
  n + (m + p) = m + (n + p).
Proof.
intros.
assert (H : n+m = m+n).
simpl. 
*)