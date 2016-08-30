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

Definition nand(x y : bool):bool:=
match x with
|true => not y
|false => true
end.

Definition or(x y : bool):bool:=
match x with
|true => true
|false => y
end.


Definition nor(x y : bool):bool:=
match x with
|true => false
|false => not y
end.


Theorem not_not: forall x:bool, not(not x) = x.
Proof.
intros.
destruct x.
simpl. reflexivity.
simpl. reflexivity.
Qed.

Example ex1 : (nor true false) = false.
Proof.
intros.
simpl. reflexivity.
Qed.

