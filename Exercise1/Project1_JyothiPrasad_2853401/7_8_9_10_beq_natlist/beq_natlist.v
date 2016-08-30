Require Export Arith.EqNat. 

Inductive natlist : Type :=
| nil : natlist
| cons : nat -> natlist -> natlist.

Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition new_bob (a:bool)(b:bool):bool := if a then b else false.

Fixpoint beq_natlist (l : natlist) (m : natlist) : bool :=
match l,m with
|[] , [] => true
| _ , [] => false
|[] , _ => false
|h :: t , h'::t' =>  new_bob (beq_nat h h') (beq_natlist t t')
end.

Check new.

Eval compute in (beq_natlist [1;2;3] [4;5;6]).
Eval compute in (beq_natlist [1;1;1] [1;1;1]).

Example test_beq_natlist1 : (beq_natlist [] [] = true).
Proof.
simpl. reflexivity.
Qed.
 
Example test_beq_natlist2 : beq_natlist [1;2;3] [1;2;3] = true.
Proof.
simpl. reflexivity.
Qed.

Example test_beq_natlist3 : beq_natlist [1;2;3] [1;2;4] = false.
Proof. 
simpl. reflexivity.
Qed.



