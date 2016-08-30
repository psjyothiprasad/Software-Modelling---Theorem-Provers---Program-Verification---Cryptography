Require Import Omega.

Module Array.

  Fixpoint leb (m:nat) : nat -> bool :=
    match m with
    | O => fun _:nat => true
    | S m' =>
      fun n:nat => match n with
              | O => false
              | S n' => leb m' n'
              end
    end.
  
  (** Register contents.  Either a natural number value or unknown. *)

  Inductive RC : Type :=
  | val : nat -> RC
  | unknown : RC.
  
  Notation "??" := unknown.

  (** Register file contents.  Function from natural to RC. *)
  
  Definition RFC : Type := nat -> RC.

  (** Empty register file contents *)
  
  Definition empty_rf: RFC := (fun n:nat => ??).

  (** [get] applies the register file function to its argument *)
  
  Definition get(i:nat)(f:RFC):RC := (f i).

  (** [put] uses an [if] expression to modify an existing register file *)
  
  Definition put(i:nat)(f:RFC)(v:RC):RFC :=
    (fun n:nat => if (beq_nat i n) then v else f n).

  (** Some tests to make sure the implementation is close to correct. *)
  
  Example test1: (get 3 (put 3 empty_rf (val 3))) = (val 3).
  Proof. reflexivity. Qed.

  Example test2: (get 2 (put 3 empty_rf (val 3))) = ??.
  Proof. reflexivity. Qed.

  Example test3: (get 4 (put 3 empty_rf (val 3))) = ??.
  Proof. reflexivity. Qed.

  (** Making the test slightly more abstract by checking all contents values *)
  
  Theorem update_position_3: forall m, (get 3 (put 3 empty_rf (val m))) = (val m).
  Proof.
    intros.
    trivial.
  Qed.

  (** Lemma showing that [beq] is reflexive.  Will be used in a later proof *)
  
  Lemma beq_refl: forall i, beq_nat i i = true.
  Proof.
    intros.
    induction i.
    reflexivity.
    auto.
  Qed.

  (** All elements of the empty register file are unknown *)
  
  Theorem empty_empty: forall i , (get i empty_rf) = ??.
  Proof.
    intros. reflexivity.
  Qed.

  (** [get] applied to a [put] on the same index updates the register file
    contents.  This is correctness of the update function. *)
  
  Theorem update_immediate: forall v i rfc,
      (get i (put i rfc (val v))) = val v.
  Proof.
    intros.
    unfold get.
    unfold put.
    rewrite beq_refl.
    reflexivity.
  Qed.

  (** [get] applied to a [put] on different indexes results in the value
    before updating.  An invariant on update. *)
  
  Theorem update_invariant: forall v i j rfc,
      (beq_nat j i) = false -> (get i (put j rfc (val v))) = rfc i.
  Proof.
    intros.
    unfold get.
    unfold put.
    rewrite H.
    trivial.
  Qed.

End Array.