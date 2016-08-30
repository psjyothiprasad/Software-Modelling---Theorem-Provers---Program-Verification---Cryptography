Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.
 
Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(*Fixpoint length(l:natlist):nat:=
match l with
|[ ] = 0
|h::t => 1+ length t
end.*)

Fixpoint append(m n :natlist) : natlist :=
match m with
|[] => n
|a :: b => a::(append b n)
end.

Notation "x ++ y" := (append x y)(at level 60, right associativity).

Theorem associative_L3 : forall n o p : natlist, n++(o++p) = (n++o)++p.
Proof.
intros n o p.
induction n.
simpl. reflexivity.
simpl. rewrite -> IHn.
reflexivity.
Qed.

Theorem associative_L4 : forall m n o p : natlist, m++(n++(o++p)) = ((m++n)++o)++p.
Proof.
intros m n o p.
simpl.
induction m as [| x xs]. 
simpl. 
rewrite associative_L3. 
reflexivity.
simpl.
rewrite -> IHxs. reflexivity.
Qed. 




 
(*
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

*)