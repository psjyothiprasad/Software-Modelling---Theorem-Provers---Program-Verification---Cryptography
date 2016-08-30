Inductive SC : Type :=
| Value : nat -> SC
| Unknown : SC.

Inductive NatStack : Type :=
| Empty : NatStack
| Add : nat -> NatStack -> NatStack.

Definition pop(s:NatStack) : NatStack :=
match s with
| Empty => Empty
| Add _ xs => xs
end.

Definition top(s:NatStack) : SC :=
match s with
| Empty => Unknown
| Add s' _ => Value s'
end.

Fixpoint isEmpty (s:NatStack):bool:=
match s with
| Empty => true
| Add _ s' => false
end.

(* 
Add::
Add is already a constructor in Inductive Definition. So, need not explicitly define it again.
Precondition : Add doesnot have any precondition.
Post Condition : If we add an element to stack and evaluate top of stack, 
                 it should return the same value.
                   (top ( Add x xs )) = Value x.
Invariant : Add an element into stack and pop the stack, 
            will return the original stack eliminating the top value.
                   (pop ( Add x xs )) = xs.
*)

Theorem add_post_condition : forall x xs, (top ( Add x xs )) = Value x.
Proof.
 intros.
 simpl.
 reflexivity.
Qed.

Theorem add_invariant : forall x xs, pop ( Add x xs ) = xs.
Proof.
intros.
simpl.
reflexivity.
Qed.

(*
Pop::
Precondition : The stack is not empty.
Poscondition : This is similar to the invariant of Add.
               pop ( Add x xs ) = xs.
invariant : The post condition is an invariant itself.
*)

Theorem pop_post_condition : forall x xs, pop ( Add x xs ) = xs.
Proof.
intros.
simpl.
reflexivity.
Qed.

(*
top::
Precondition : The stack is not empty.
Postcondition : Add an element and return the top of the stack,
                should return the element which we added.
                    top ( Add x xs) = Value x.
Invariant : Since top operation not changing the other elements of stack, it should remain unchanged.
*)

Theorem top_post_condition : forall x xs, top ( Add x xs) = Value x.
Proof.
 intros.
 simpl.
 reflexivity.
Qed.

(*
isEmpty ::
Precondition : Doesn't have any precondition
PostCondition : The result should return  boolean value(true) if the stack is empty and viceversa.
invariant : Since this doesn't have any effects, no invariant exists. 
*)

Theorem isEmpty_post_condition : isEmpty ( Empty ) = true.
Proof.
simpl.
reflexivity.
Qed.

