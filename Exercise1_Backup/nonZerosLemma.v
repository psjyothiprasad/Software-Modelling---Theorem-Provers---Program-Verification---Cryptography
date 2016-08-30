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

Fixpoint snoc(m:natlist)(n:nat) :natlist:=
match m with
|[] => [n]
|a::b => a:: (snoc b n)
end.

Fixpoint reverse(n:natlist) : natlist :=
match n with
|[] => []
|a::b => snoc(reverse b) a
end.

Theorem associative_L3 : forall n o p : natlist, n++(o++p) = (n++o)++p.
Proof.
intros n o p.
induction n.
simpl. reflexivity.
simpl. rewrite -> IHn.
reflexivity.
Qed.

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

Theorem appendEmptyList : forall list : natlist, list ++ [] = list.   
Proof.
  intros.
    induction list as [| x xs].
    simpl.
    reflexivity.
    simpl. 
    rewrite -> IHxs.
    reflexivity.
Qed.

Fixpoint nonZeros(n:natlist) : natlist :=
match n with
| [] => []
| x :: xs => match x with
    | 0 => nonZeros(xs)
    | _ => x :: nonZeros(xs)
    end
end.

Theorem distr_rev : forall l1 l2 : natlist, reverse (l1 ++ l2 ) = (reverse l2 ) ++ (reverse l1 ).
Proof.
intros l1 l2.
induction l1.
simpl. rewrite appendEmptyList.
simpl. reflexivity.
simpl. rewrite IHl1.
simpl. rewrite appendList.
simpl. rewrite appendList.
simpl. rewrite associative_L3.
reflexivity.
Qed.

Lemma nonZerosLemma : forall l1 l2 : natlist, nonZeros (l1 ++ l2 ) = (nonZeros l1 ) ++ (nonZeros l2 ).
Proof.
intros l1 l2.
induction l1.
simpl. reflexivity. 
simpl. 
destruct n.
simpl. rewrite IHl1.
reflexivity.
simpl. rewrite IHl1.
reflexivity.
Qed.

Eval compute in( nonZerosLemma[0;1;2] [1;2;3]).