(**

Inductive bool:Type:=
|true : bool
|false : bool.

Definition and(x y z : bool):bool:=
match x with
|false => false
|true => match y with
         |true => z
         |false => false
         end
end.



Example and3 : (and true false false) = false.
Proof.
simpl. reflexivity. Qed.

Eval compute in (and true true false).

Check (and).


------

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Eval compute in (minustwo 6).
Eval compute in (minustwo 4).
Eval compute in (minustwo 2).

Check S.
Check S(O).
Check S(S O).
Check S(S(S(O))).
Check S(S(S(S(O)))).
Check minustwo.


Require Export Arith.EqNat.
SearchAbout beq_nat.
SearchAbout negb.

*)


Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.


Eval compute in ( evenb 4 ).
Check O.
Check S.
Check S O.
Check S (S O).
Check S (S (S O)).

Fixpoint oddb (n:nat) : bool :=
  match n with
  | O        => false
  | S O      => true
  | S (S n') => oddb n'
  end.

Eval compute in ( oddb 4 ).

Theorem plus_O_n : forall n : nat, 0 + n = n.
intros n.
simpl. reflexivity. Qed.

Theorem plus_1_l : forall n:nat, 1 + n = S n. 
Proof.
intros.
simpl. reflexivity.
Qed.


Theorem plus_id_example : forall n m:nat,
  n = m -> 
  n + n = m + m.
Proof.
intros. rewrite H.
reflexivity.
Qed.


Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
intros. rewrite H.
rewrite H0.
reflexivity.
Qed.

Require Export Arith.EqNat.
SearchAbout(beq_nat).


Theorem plus_1_neq_0_firsttry : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
intros.
induction n.
simpl. reflexivity.
simpl. reflexivity.
Qed. 


Theorem plus_1_neq_0_firsttry_1 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
intros.
destruct n as [|n'].
simpl. reflexivity.
simpl. reflexivity.
Qed.

Theorem identity_fn_applied_twice : 
  forall (f : bool -> bool), 
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
intros.
induction b.
rewrite H.
rewrite H.
simpl. reflexivity.
rewrite H.
rewrite H.
simpl. reflexivity.
Qed. 