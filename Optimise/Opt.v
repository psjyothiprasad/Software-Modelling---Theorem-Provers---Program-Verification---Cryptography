Inductive AE : Type :=
|num : nat -> AE
|plus : AE -> AE -> AE
|minus : AE -> AE -> AE
|times : AE -> AE -> AE.

Fixpoint opt(e:AE) : AE :=
match e with
|num n => num n
|plus (num 0) r => (opt r)
|plus l r => plus (opt l) (opt r)
|minus p q => minus (opt p) (opt q)
|times m n => times (opt m) (opt n)
end. 

Eval compute in opt(plus(num 0)(num 5)).


Example ex1 : opt(plus (num 0) (num 5)) = (num 5).
Proof.
intros.
simpl. reflexivity.
Qed.

Eval compute in opt(plus(num 0)(num 10)).