Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.


Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint append(m n :natlist) : natlist :=
match m with
|[] => n
|a :: b => a::(append b n)
end.

Notation "x ++ y" := (append x y)(at level 60, right associativity).

Theorem appendEmptyList : forall list : natlist, list ++ [] = list.   
Proof.
  intros.
    induction list as [| x xs].
    simpl.
    reflexivity.
    simpl. rewrite -> IHxs.
    reflexivity.
Qed.



Eval compute in ( appendEmptyList [1;2;3] , []).