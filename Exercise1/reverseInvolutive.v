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

Theorem rev_snoc : forall l :natlist, forall n:nat, reverse(snoc l n) = n :: reverse l.
Proof.
intros.
induction l.
simpl.
simpl. reflexivity.
simpl. rewrite -> IHl.
simpl. reflexivity.
Qed.

Theorem reverseInvolutive : forall list : natlist, reverse(reverse list) = list.   
Proof.
intros.
induction list as [| x xs].
simpl. reflexivity.
simpl. rewrite -> rev_snoc.
rewrite IHxs.
reflexivity.
Qed.

