(** The [constructor] tactic is one of the most basic forms of
automation available in Coq. What it does is simple: in order to prove
a proposition, the tactic tries to apply each of its constructors in
sequence, until one succeeds. In that case, the proof proceeds with
all the subgoals generated by that constructor, if any. If no
constructor can be applied, the tactic just fails. There is also an
[econstructor] variant, which defers the instantiation of arguments
required by a constructor when it can't infer them immediately. Thus, it
is the analog of [eapply] for [constructor].

The tactic becomes particularly useful when applied to multiple goals
simultaneously, usually in a sequence of tactics separated by the [;]
operator. Suppose that you can solve each goal in a proof by applying
roughly the same tactic, but need a different constructor for each case:

[[
   beginning_of_proof. (* Generates some subcases.*)

   (* Case 1 *)
   apply Constructor1.
   rest_of_proof.

   (* Case 2 *)
   apply Constructor2.
   rest_of_proof.

   ...

]]

By combining the tactics with [;] and using [constructor], Coq can
figure out by itself what needs to be applied for each case, which
results in a more concise proof:

[[
   beginning_of_proof; constructor; rest_of_proof.
]]

[constructor]'s method for choosing what to apply is clearly not very
sophisticated and does not always work. Sometimes, a proof can proceed
by applying multiple constructors, but only some of them will allow
the proof to be completed. [constructor], on the other hand, will
always choose the first that can be applied, which may or may not be
the one we need.

Fortunately, there is a more general version of [constructor] that can
be used to solve this problem. If [t] is a tactic, invoking
[constructor t] will search for a constructor that can be applied to
the current goal _and_ allows [t] to be executed in sequence. Thus, if
[constructor] can't find the correct constructor to apply, you can try
to guide the tactic by doing something like

[[
  beginning_of_proof; constructor (solve [rest_of_proof]).
]]

This nice feature, which is currently not documented in the Coq user
manual, has already been #<a
href="https://sympa.inria.fr/sympa/arc/coq-club/2012-05/msg00097.html">#
discussed#</a># in the Coq mailing list, and was pointed out to me by
David Pichardie.

** An example

Let's investigate a specific example to see when this feature could be
useful. Here's a definition of standard binary trees in Coq, with
elements drawn from an arbitrary type [A]: *)

Section Tree.

Variable A : Type.

Inductive tree : Type :=
| Leaf
| Node (t1 : tree) (a : A) (t2 : tree).

(** If [A] has a function for comparing its elements, we can use it to
implement a function that inserts an element of [A] in a sorted binary
tree while preserving its order. *)

Variable comp : A -> A -> comparison.

Fixpoint insert (a : A) (t : tree) : tree :=
  match t with
    | Leaf => Node Leaf a Leaf
    | Node t1 a' t2 =>
      match comp a a' with
        | Lt => Node (insert a t1) a' t2
        | Eq => Node t1 a t2
        | Gt => Node t1 a' (insert a t2)
      end
  end.

(** Using Coq, we should be able to prove that an element [a] always
appears in [insert a t] for all trees [t]. Formally, [a] appears in the
tree [t] if it is the label of the root of [t], or if it appears
recursively in the left or right subtrees of [t], which we can
promptly define as an inductive proposition: *)

Inductive appears (a : A) : tree -> Prop :=
| AHere : forall t1 t2, appears a (Node t1 a t2)
| ALeft : forall t1 a' t2,
            appears a t1 ->
            appears a (Node t1 a' t2)
| ARight : forall t1 a' t2,
             appears a t2 ->
             appears a (Node t1 a' t2).

(** Let's now try to prove our theorem. Here's a first attempt, using
the regular [constructor] tactic. *)

Theorem insertAppears : forall a t, appears a (insert a t).
Proof.
  intros a t.
  induction t as [|t1 IH1 a' t2 IH2]; simpl;

  (* We must consider all three places where "a" can go,
     hence the "destruct" *)
  try destruct (comp a a') eqn: H;
  constructor; auto.

(** Our proof state now looks like this:

[[
  A : Type
  comp : A -> A -> comparison
  a : A
  t1 : tree
  a' : A
  t2 : tree
  IH1 : appears a (insert a t1)
  IH2 : appears a (insert a t2)
  H : comp a a' = Gt
  ============================
   appears a t1
]]

Clearly, there is no way of solving this goal. The problem is that
[constructor] chose the first constructor that could apply to our
conclusion ([ALeft] in this case), which requires an assumption that
isn't available in our context. We can easily fix this problem by
using the more general variant. *)

Restart.
  intros a t.
  induction t as [|t1 IH1 a' t2 IH2]; simpl;
  try destruct (comp a a') eqn: H;
  constructor (solve [auto]).
Qed.

(** Now, Coq attempts to execute [solve [auto]] for each constructor
it tries. This will fail when testing [ALeft] on our problematic case,
causing Coq to skip it and try [ARight], which does work and solves
the goal.

This smarter variant of [constructor] is obviously very useful, and it
would be great to see it properly described in the Coq user manual as
it deserves!

*** Note

In this case, it would have also been possible to prove our theorem by
adding the constructors of [appears] to the [auto] hint database. *)

Hint Constructors appears.

Theorem insertAppears' : forall a t, appears a (insert a t).
Proof.
  intros a t.
  induction t as [|t1 IH1 a' t2 IH2]; simpl;
  try destruct (comp a a') eqn: H;
  auto.
Qed.

(** I tried to find a simple and natural example where just using
[auto] would not be enough to solve the goal, but wasn't able to come
up anything better than this. If you can find a better example, please
let me know. *)

End Tree.
