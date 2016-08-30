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

Check new_bob.

Eval compute in (beq_natlist [1;2;3] [4;5;6]).
Eval compute in (beq_natlist [1;1;1] [1;1;1]).


(*SearchAbout beq_nat.*)


Theorem beq_nat_refl : forall n: nat, true = beq_nat n n.
Proof.
intros.
induction n. 
simpl. reflexivity.
simpl. rewrite IHn.
simpl. reflexivity.
Qed.


Theorem beq_natlist_refl : forall l:natlist, true = beq_natlist l l.
Proof.
simpl. 
induction l.
simpl. reflexivity.
simpl. rewrite <- IHl.
simpl. rewrite <- beq_nat_refl.
simpl. reflexivity.
Qed.


Eval compute in (beq_natlist_refl [1;2;3]).

