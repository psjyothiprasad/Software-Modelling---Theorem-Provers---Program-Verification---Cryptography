Require Import Omega.

(** Key values will be [nat] *)

Definition key_val : Type := nat.

(** Key types are [symmetric], [public] and [private]. *)
Inductive keyType: Type :=
| symmetric : key_val -> keyType
| private : key_val -> keyType
| public : key_val -> keyType.

(** A [symmetric] key is its own inverse.  A [public] key is the inverse of
  the [private] key with the same [key_val].  A [private] key is the inverse of
  the [public] key with the same [key_val]. *)

Fixpoint inverse(k:keyType):keyType :=
match k with
| symmetric k => symmetric k
| public k => private k
| private k => public k
end.

Inductive message(basicType:Type) : Type :=
| basic : basicType -> message basicType
| key : keyType -> message basicType
| encrypt : message basicType -> keyType -> message basicType
| sign : message basicType -> keyType -> message basicType
| hash : message basicType -> message basicType
| pair : message basicType -> message basicType -> message basicType.

(** Predicate that determines if a message cannot be decrypted.  Could be
  that it is not encrypted to begin with or the wrong key is used. *)

Definition is_not_decryptable{T:Type}(m:message T)(k:keyType):Prop :=
  match m with
  | basic _ => True
  | key _ => True
  | encrypt m' k' => k <> inverse k'
  | sign _ _ => True
  | hash _ => True
  | pair _ _ => True
  end.


(** Proof that inverse is decidable for any two keys. The resulting proof
 gives us the function [is_inverse] that is a decision procedure for key 
 inverse checking.  It will be used in [decrypt] and [check] later in the
 specification. *)
Theorem is_inverse:forall k k', {k = (inverse k')}+{k <> (inverse k')}.
Proof.
  intros.
  destruct k; destruct k'.
  destruct (eq_nat_dec k k0) as [Hinv | Hninv].
    left. simpl. auto.
    right. simpl. unfold not. intros. inversion H. contradiction.
  right; simpl; unfold not; intros; inversion H.
  right. simpl. unfold not. intros. inversion H.
  right. simpl. unfold not. intros. inversion H.
  right. simpl. unfold not. intros. inversion H.
  destruct (eq_nat_dec k k0) as [Hinv | Hninv].
    left. simpl. auto.
    right. simpl. unfold not. intros. inversion H. contradiction.
  right. simpl. unfold not. intros. inversion H.
  destruct (eq_nat_dec k k0) as [Hinv | Hninv].
    left. simpl. auto.
    right. simpl. unfold not. intros. inversion H. contradiction.
  right. simpl. unfold not. intros. inversion H.
Defined.

(** [decrypt] returns either a decrypted message or a proof of why the message
  cannot be decrypted. *)

Fixpoint decrypt{T:Type}(m:message T)(k:keyType):(message T)+{(is_not_decryptable m k)}.
refine
  match m with
  | basic c => inright _ _
  | key _ => inright _ _
  | encrypt m' j => (if (is_inverse k j) then (inleft _ m') else (inright _ _ ))
  | sign m' k => inright _ _
  | hash _ => inright _ _
  | pair _ _ => inright _ _
  end.
Proof.
  reflexivity.
  reflexivity.
  simpl. assumption.
  reflexivity.
  reflexivity.
  reflexivity.
Defined.


Definition is_signed{T:Type}(m:message T)(k:keyType):Prop :=
  match m with
  | basic _ => False
  | key _ => False
  | encrypt _ _ => False
  | sign m' k' => k = inverse k'
  | hash _ => False
  | pair _ _ => False
  end.

(** Signature check returns either a proof that the signature is correct
  or a proof that the signature is not correct. *)

Fixpoint check{T:Type}(m:message T)(k:keyType):{(is_signed m k)}+{not (is_signed m k)}.
refine
  match m with
  | basic c => right _ _
  | key _ => right _ _
  | sign m' j => (if (is_inverse k j) then (left _ _) else (right _ _ ))
  | encrypt m' k => right _ _
  | hash _ => right _ _
  | pair _ _ => right _ _
  end.
Proof.
  unfold not. intros. simpl in H. assumption.
  unfold not. intros. simpl in H. assumption.
  unfold not. intros. simpl in H. assumption.
  destruct (is_inverse j k).
  simpl. rewrite _H. reflexivity.
  simpl. rewrite <- _H. reflexivity.
  simpl. assumption.
  unfold not. intros. simpl in H. assumption.
  unfold not. intros. simpl in H. assumption.
Defined.

Inductive Node:Type:=
|privateNode: nat -> keyType -> keyType -> Node
|symmetricNode : nat -> keyType -> Node.


(*Server Contents are represented as SC here*)
(*Inductive keyServer:Type :=*)
Inductive SC : Type :=
  | keyVal : keyType -> SC
  | unknown : SC.
  
  Notation "??" := unknown.

  Definition KSC : Type  := nat -> SC.
  
  Inductive KS : Type :=
  | server : keyType -> keyType -> KSC -> KS.

  Definition empty_server(pu:keyType)(pr:keyType):KS := server pu pr (fun n:nat => ??).


(*Definition filled_server(pu:nat)(pr:nat)()*)


Definition extract(c:SC): keyType:=
match c with
|keyVal pu => pu 
|??=> private O
end.

(* retreive function tries to obtain the id of sender, id of receiver and the keyServer itself. 
It obtains the public key of the receiver as per the id which is passed as argument and
encrypts it with the public key of sender and signs it with private key of the server *)

Definition retreive(i:nat)(sender:nat)(s:KS): message keyType :=
match s with
| server pu pr ksc => sign keyType (encrypt keyType (basic keyType (extract (ksc i))) (extract (ksc sender))) pr 
end.


Definition store(i:nat)(s:KS)(v:keyType): KS :=
    match s with
    | server pu pr ksc =>  server pu pr (fun n:nat => if(beq_nat i n) then keyVal v else keyVal (extract (ksc n)))
    end.

Definition delete(i:nat)(s:KS):KS:=
match s with 
| server pu pr ksc => server pu pr (fun n:nat => if(beq_nat i n) then ?? else keyVal (extract (ksc n)))
end.

(** Function to validate the key *)
Fixpoint key_valid {T:Type}(k':keyType)(m:message T): Prop :=
  match m with
  | basic _ => False
  | key _ => False
  | encrypt _ _ => False
  | sign m k => k = inverse k'
  | hash _ => False
  | pair _ _ => False
  end.  

(*Encryption and signing is encryption with a recipient’s public key and signing 
  with the sender’s private key *)
(* Encrpt is combining message and the other(b's) nodes public key)
(Signing is combinig encrypted file with same nodes's (a's ) private key)*)

Definition is_not_signable{T:Type}(m:message T)(k:keyType):Prop :=
  match m with
  | basic _ => True
  | key _ => True
  | encrypt m' k' => k <> inverse k'
  | sign _ _ => True
  | hash _ => True
  | pair _ _ => True
  end.

Fixpoint encrypt_and_sign {T:Type} (m:message T)(prik:keyType):(message T)+{(is_not_signable m prik)}.
refine
  match m with
  | basic c => inright _ _
  | key _ => inright _ _
  | encrypt m' j => inleft _ (sign T m prik)
  | sign m' k => inright _ _
  | hash _ => inright _ _
  | pair _ _ => inright _ _
  end. 
Proof.
  reflexivity.
  reflexivity.
  simpl. trivial.
  reflexivity.
  reflexivity.
Defined.


Definition keyServer1:KS :=  
store 4 (store 3 (store 2 (store 1 (empty_server (public 23) (private 32)) (public 1)) (public 2)) (public 3)) (public 4).


Definition keyRequest(i:nat)(s:nat):message keyType := retreive i s keyServer1.

Fixpoint pickRecPublicKey {T:Type}(privKey:keyType)(m:message T): (message T)+{(is_not_decryptable m privKey)}.
refine
 match m with
  | basic _ => inright _ _
  | key _ => inright _ _
  | encrypt m' k => (if(is_inverse privKey k) then (inleft _ m') else (inright _ _ ))
  | sign _ _ => inright _ _
  | hash _ => inright _ _
  | pair _ _ => inright _ _
  end.
Proof.
  reflexivity.
  reflexivity.
  simpl. assumption.
  reflexivity.
  reflexivity.
  reflexivity.
Defined.