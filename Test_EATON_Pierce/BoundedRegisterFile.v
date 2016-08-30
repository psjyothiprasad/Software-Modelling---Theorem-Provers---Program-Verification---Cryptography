Require Import Omega.

Module RegFileArray.

  Fixpoint leb (m:nat) : nat -> bool :=
    match m with
    | O => fun _:nat => true
    | S m' =>
      fun n:nat => match n with
              | O => false
              | S n' => leb m' n'
              end
    end.
  
  Inductive RC : Type :=
  | val : nat -> RC
  | unknown : RC.
  
  Notation "??" := unknown.

  Definition RFC : Type := nat -> RC.
  
  Inductive RF : Type :=
  | file : nat -> RFC -> RF.

  Definition empty_rf(s:nat):RF := file s (fun n:nat => ??).

  Definition get(i:nat)(f:RF):RC :=
    match f with
    | file s c => if (leb i s) then (c i) else ??
    end.

  Definition put(i:nat)(f:RF)(v:RC):RF :=
    match f with
    | file s c => if (leb i s)
                 then file s (fun n:nat => if (beq_nat i n) then v else c n)
                 else f
    end.

  Example test1: (get 3 (put 3 (empty_rf 10) (val 3))) = (val 3).
  Proof.
    reflexivity.
  Qed.

  Example test2: (get 2 (put 3 (empty_rf 10) (val 3))) = ??.
  Proof. reflexivity. Qed.

  Example test3: (get 4 (put 3 (empty_rf 10) (val 3))) = ??.
  Proof. reflexivity. Qed.

  Theorem update_position_3: forall m, (get 3 (put 3 (empty_rf 10) (val m))) = (val m).
  Proof.
    intros.
    trivial.
  Qed.

  Theorem update_position_size: forall v s rfc,
      leb 3 s = true -> (get 3 (put 3 (file s rfc) (val v))) = val v.
  Proof.
    intros. unfold put.
    rewrite H.
    unfold get.
    rewrite H.
    reflexivity.
  Qed.

  Lemma beq_refl: forall i, beq_nat i i = true.
  Proof.
    intros.
    induction i.
    reflexivity.
    auto.
  Qed.

  Theorem empty_empty: forall i s, (leb i s) = true -> (get i (empty_rf s)) = ??.
  Proof.
    intros. simpl. destruct (leb i 10); rewrite H; reflexivity.
  Qed.
    
  Theorem unknown_oob: forall i s rfc, (leb i s) = false -> (get i (file s rfc)) = ??.
  Proof.
    intros.
    simpl. rewrite H. reflexivity.
  Qed.
  
  Theorem update_immediate: forall v i s rfc,
      (leb i s) = true -> (get i (put i (file s rfc) (val v))) = val v.
  Proof.
    intros.
    simpl.
    rewrite H.
    simpl.
    rewrite beq_refl.
    rewrite H.
    trivial.
  Qed.
   
  Theorem update_invariant: forall v i j s rfc,
      (beq_nat j i) = false -> (leb j s) = true -> (leb i s) = true -> (get i (put j (file s rfc) (val v))) = rfc i.
  Proof.
    intros.
    simpl.
    rewrite H0.
    simpl.
    rewrite H.
    rewrite H1.
    trivial.
  Qed.

  Theorem update_invariant': forall v i j s rfc,
      (beq_nat j i) = false -> (leb j s) = false -> (leb i s) = true -> (get i (put j (file s rfc) (val v))) = rfc i.
  Proof.
    intros.
    simpl.
    rewrite H0.
    simpl.
    rewrite H1.
    trivial.
  Qed.

  Theorem update_invariant'': forall v i j s rfc,
      (beq_nat j i) = false -> (get i (put j (file s rfc) (val v))) = (get i (file s rfc)).
  Proof.
    intros.
    simpl.
    destruct (leb j s).
    simpl.
    rewrite H.
    trivial.
    simpl.
    trivial.
  Qed.

  Theorem update_size_invariant: forall s rfc i v,
      match (put i (file s rfc) v) with
      | file s' rfc' => is_true (beq_nat s s')
                     end.
  Proof.
    intros.
    unfold is_true.
    unfold put.
    destruct (leb i s).
    apply beq_refl.
    apply beq_refl.
  Qed.

End RegFileArray.