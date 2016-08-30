Require import appendEmptyList.v .

Inductive natlist : Type :=
  | nil : natlist
  | snoc : natlist -> natlist -> natlist.

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
(*Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).*)
Notation "x ++ y" := (append x y)(at level 60, right associativity).


Fixpoint snoc(m : natlist)(n : natlist) : natlist :=
match m with
| [] => [n]
| a::b => a::(snoc b n)
end.

Fixpoint reverse(n : natlist) : natlist :=
match n with
|[] => []
|a :: b => snoc (rev b) a
end.



(*Notation "x ++ y" := (append x y)(at level 60, right associativity).*)


Theorem reverseInvolutive : forall list : natlist, reverse(reverse l) = l.   
Proof.
  intros.
    induction list as [| x xs].
    simpl.
    reflexivity.
    simpl. 
    rewrite -> IHxs.
    reflexivity.
Qed.