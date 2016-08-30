Inductive bool:Type:=
|true : bool
|false : bool.

Definition not(x:bool):bool:=
match x with
|true => false
|false => true
end.

Definition and(y z : bool):bool:=
match y with
|true => z
|false => false
end.

Definition nand3(x y z : bool):bool:=
match x with
|true => (and y z)
|false => true
end.


Theorem not_not: forall x:bool, not(not x) = x.
Proof.
intros.
destruct x.
simpl. reflexivity.
simpl. reflexivity.
Qed.


Eval compute in (nand3 true true true).

