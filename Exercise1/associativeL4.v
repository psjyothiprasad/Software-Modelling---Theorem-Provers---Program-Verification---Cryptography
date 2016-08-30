Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.
 


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
simpl. induction m as [| x xs]. 
simpl. rewrite associative_L3. 
reflexivity.
simpl. rewrite -> IHxs. reflexivity.
Qed.