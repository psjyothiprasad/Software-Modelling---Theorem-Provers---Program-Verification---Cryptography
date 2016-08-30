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

Fixpoint snoc(m:natlist)(n:nat) :natlist:=
match m with
|[] => [n]
|a::b => a:: (snoc b n)
end.

Notation "x ++ y" := (append x y)(at level 60, right associativity).

Theorem appendList : forall (list : natlist) (n : nat), snoc list n = list ++ [n].   
Proof.
  intros.    
    induction list as [| x xs].
    simpl.
    reflexivity.
    simpl. 
    rewrite -> IHxs.
    reflexivity.
Qed.

Eval compute in ( append [1;2;3] [6;7;8]).
Eval compute in ( appendList [1;2;3] 6).