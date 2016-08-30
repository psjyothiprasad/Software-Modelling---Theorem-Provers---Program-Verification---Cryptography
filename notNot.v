Inductive bool:Type:=
|true : bool
|false : bool.

Definition not(x:bool):bool:=
match x with
|true => false
|false => true
end.

Definition and(x y : bool):bool:=
match x with
|true => y
|false => false
end.

Theorem not_not: forall x:bool, not(not x) = x.
Proof.
intros.
destruct x.
simpl. reflexivity.
simpl. reflexivity.
Qed.

Eval compute in (not_not false).

Eval compute in (and true false).