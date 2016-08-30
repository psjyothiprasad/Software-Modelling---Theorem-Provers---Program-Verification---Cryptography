Inductive SC(T:Type): Type :=
| Value : T -> SC T
| Unknown : SC T.

Inductive Stack(T:Type): Type :=
| Empty : Stack T
| Push:  T -> Stack T -> Stack T.
(* For better readability I renamed Add constructor in Ex1.v to Push *)

(*Stack is parameterized over the stack element.*)

Definition pop(T:Type) (s:Stack T):(Stack T):=
match s with 
| Empty => Empty T
| Push _ xs => xs
end.

Definition top (T:Type)(s:Stack T) : SC T :=
match s with
| Empty => Unknown T
| Push s' _ => Value T s'
end.

Definition isEmpty (T:Type) (s:Stack T) : bool :=
match s with 
|Empty => true
|Push _ _ => false
end.

Theorem push_post_condition : forall t x xs, (top t (Push t x xs))= Value t x.
Proof.
intros.
simpl.
reflexivity.
Qed.

Theorem push_invariant : forall t x xs, pop t (Push t x xs) = xs.
Proof.
intros.
simpl.
reflexivity.
Qed.

Theorem pop_post_condition : forall t x xs, pop t (Push t x xs) = xs.
Proof.
intros.
simpl.
reflexivity.
Qed.

Theorem top_post_condition : forall t x xs, (top t (Push t x xs)) = Value t x.
Proof.
 intros.
 simpl.
 reflexivity.
Qed.

Theorem isEmpty_post_condition: forall t, isEmpty t (Empty t)=true.
Proof.
intros.
reflexivity.
Qed.

(* For arbitrary x and y, on an empty stack, we are pushing twice and popping 
   twice on the same stack. So, it is safe and doesnot crash. The final state
   of the stack is empty.
*)
Theorem proof1: forall t x y, (pop t (pop t ( Push t y (Push t x (Empty t)))))= (Empty t).
Proof.
intros.
simpl.
reflexivity.
Qed.

(* For arbitrary x and y, on an empty stack, we are pushing once and popping twice.
   Since we wrote the contuctor for "empty" in pop definition, the below theorem doesnot crash.
   Otherwise (pop (pop (push x empty)) is unsafe.
*)

Theorem proof2: forall t x, (pop t (pop t (Push t x (Empty t))))= (Empty t).
Proof.
intros.
simpl.
reflexivity.
Qed.
