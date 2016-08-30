Inductive SC(T:Type): Type :=
| Value : T -> SC T
| Unknown : SC T.

Inductive Stack(T:Type): Type :=
| Empty : Stack T
| Push:  T -> Stack T -> Stack T.
(* For better readability I renamed Add constructor in Ex1.v to Push *)

(* not_empty checks if the stack is empty or not by returning a Proposition*)
Definition not_empty(T:Type)(s:Stack T):Prop := s <> Empty T.

Definition isEmpty (T:Type)(s:Stack T) : bool :=
match s with 
| Empty => true
| Push _ _ => false
end.


(*pop and top are defined by doing the compile-time check that the stack is non empty *)
Definition pop(T:Type)(s:Stack T):not_empty T s -> Stack T := 
match s with 
| Empty => (fun proof: not_empty T s => (Empty T))
| Push x r => (fun proof: not_empty T s => r )
end.

Definition top(T:Type)(s:Stack T) : not_empty T s -> SC T :=
match s with
| Empty => (fun proof: not_empty T s => Unknown T)
| Push x _ => (fun proof: not_empty T s => Value T x)
end.

(*post-conditions of push :
Since the precondition of top is not_empty, it is used as an assumption here*)
Theorem push_post_condition : forall t x xs, forall proof:not_empty t xs,(top t (Push t x xs))= (fun proof => Value t x).

Proof.
intros.
simpl.
reflexivity.
Qed.

(*push invariant : all other elements should remain unchanged , pop( push x ts)=ts*) 
(*Since the precondition of pop is not_empty, it is used as an assumption here*)

Theorem push_invariant : forall t x xs, forall proof:not_empty t xs, pop t (Push t x xs)=(fun proof =>xs).
Proof.
intros.
simpl.
reflexivity.
Qed.

(* post condition of isEmpty: returns true if the stack is empty*)


Theorem isEmpty_post_condition :forall t, isEmpty t (Empty t)= true.
Proof.
intros.
simpl.
reflexivity.
Qed.


Theorem safe: forall (T:Type)(x y:T)(s:Stack T)(proof:not_empty T (Push T x s))(proof1:not_empty T (Push T y (Push T x s))),
 (s=Empty T)->(pop T ((pop T (Push T y (Push T x s))) proof1)) proof = Empty T.
Proof.
intros.
unfold pop.
rewrite H.
reflexivity.
Qed.

(*
During the second pop, the compile time check sees if the stack is empty or not.
as the stack is empty at this point, it cant return the proof for the not_empty and 
the program crashes.
*)
Theorem crash: forall (T:Type)(x:T)(s:Stack T)(proof:not_empty T (Push T x s))(proof1:not_empty T (Push T x (Push T x s))),((pop T ((pop T (Push T x s)) proof)) proof1) = Empty T.
Proof.
Abort.

