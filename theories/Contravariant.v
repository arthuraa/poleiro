(* begin hide *)
From mathcomp Require Import ssreflect ssrfun ssrbool.
(* end hide *)
(** Convincing Coq that a function terminates can be frustrating.  When modeling
programming languages with subtyping, in particular, you might run into
situations where the _contravariance_ of function types forces you to swap the
arguments of a recursive function.  Coq does not know how to handle this
recursion pattern and rejects the definition.  This post presents a technique
for dealing with such cases.

Suppose that we want to model a programming language with the following types:
*)

Inductive type :=
| Top (* Any value whatsoever, akin to Object in Java or Ruby *)
| Int
| Arrow (T S : type) (* Functions from T to S *).

Notation "T ⟶ S" := (Arrow T S) (at level 25, right associativity).

(** Our language comes with a _subtyping_ relation [T <: S] that tells when it
is safe to use elements of [T] in a context that expects elements of [S].  Its
definition is given below as an inductive declaration. *)
(* begin hide *)
Reserved Notation "T <: S" (at level 50, no associativity).
(* end hide *)
Inductive subtype : type -> type -> Prop :=
| STTop T
: T <: Top

| STInt
: Int <: Int

| STArrow T1 T2 S1 S2 of
  T2 <: T1 & S1 <: S2
: T1 ⟶ S1 <: T2 ⟶ S2

where "T <: S" := (subtype T S).

(** Since [Top] contains arbitrary values, it makes sense for it to be a
supertype of every other type in the language.  Things get more interesting for
functions, as subtyping goes in opposite directions for arguments and results;
in common jargon, we say that subtyping treats arguments _contravariantly_ and
results _covariantly_.  If arguments worked covariantly, any function [f] of
type [(Int → Int) → Int] would also have the type [Top → Int], since [Int → Int
<: Top].  Thus, it would be possible to apply [f] to an [Int], which has no
reason to be safe if [f] expects a function argument.

We would like to show that subtyping is decidable by expressing this relation as
a boolean function.  Its definition is not difficult in principle, but the naive
attempt is rejected: *)

Fail Fixpoint subtypeb T S {struct T} :=
  match T, S with
  | _, Top => true
  | Int, Int => true
  | T1 ⟶ S1, T2 ⟶ S2 => subtypeb T2 T1 && subtypeb S1 S2
  | _, _ => false
  end.

(** [[
Recursive definition of subtypeb is ill-formed.
...
Recursive call to subtypeb has principal argument equal to "T2"
instead of one of the following variables: "T1" "S1".
]]
*)
(** What happened? Recursive functions in Coq are always defined with respect to
a _principal argument_.  In this case, the argument was marked as [T] using the
[struct] keyword, but it can usually be inferred by Coq automatically.  For the
definition to be valid, all the recursive calls must be performed on principal
arguments that are subterms of the original principal argument.  However, one of
the calls to [subtypeb] swaps its two arguments, leading to the above error
message.

Coq provides _well-founded recursion_ to circumvent this rigid check, which
allows recursive calls whenever the arguments decrease according to a suitable
relation.  In the case of [subtypeb], for instance, we could show termination by
proving that the combined sizes of the two arguments decrease on every call.
However, there is a more direct route in this case: it suffices to add a flag to
the function to specify if we are computing subtyping in the correct or opposite
order.  If we flip the flag on the first call, we do not need to swap the
arguments. *)

Fixpoint subtypeb_gen b T S :=
  match T, S with
  | Top, Top => true
  | Top, _   => ~~ b
  | _  , Top =>    b
  | Int, Int => true
  | T1 ⟶ S1, T2 ⟶ S2 => subtypeb_gen (~~ b) T1 T2 && subtypeb_gen b S1 S2
  | _, _ => false
  end.

Definition subtypeb := subtypeb_gen true.

Notation "T <:? S" := (subtypeb T S) (at level 20, no associativity).

(** To relate the two definitions of subtyping, we first show that flipping the
flag of [subtypeb_gen] is equivalent to swapping the other arguments.  *)

Lemma subtypeb_genC b T S : subtypeb_gen (~~ b) T S = subtypeb_gen b S T.
Proof.
by elim: T S b => [| |? IH1 ? IH2] [| |??] //= b; rewrite -?IH1 ?IH2 negbK.
Qed.

(** This yields a more convenient equation for [subtypeb].  (We match on [S]
first to ensure that the RHS is definitionally equal to [true] when [S] is
[Top].) *)

Lemma subtypebE T S :
  T <:? S =
  match S, T with
  | Top, _   => true
  | Int, Int => true
  | T2 ⟶ S2, T1 ⟶ S1 => T2 <:? T1 && S1 <:? S2
  | _  , _   => false
  end.
Proof.
case: T S=> [| |??] [| |??]; by rewrite /subtypeb  //= -(subtypeb_genC false).
Qed.

(** Finally, we can prove that the two definitions are equivalent using the
[reflect] predicate of Ssreflect.  Showing that the inductive formulation
implies the boolean one is easy: we just proceed by induction on the relation.
Proving the converse is a bit more subtle, as it requires generalizing the
statement with [subtypeb_gen]. *)

Lemma subtypebP T S : reflect (T <: S) (T <:? S).
Proof.
apply/(iffP idP); last first.
  by elim: T S / => [T| |???? _ IH1 _ IH2] //=; rewrite subtypebE ?IH1 ?IH2.
suffices /(_ true): forall b, subtypeb_gen b T S ->
  subtype (if b then T else S) (if b then S else T) by [].
elim: T S=> [| |T1 IH1 S1 IH2] [| |T2 S2] [] //=;
try case/andP=> /IH1 ? /IH2 ?; by constructor.
Qed.

(** *** Update (August 9, 2019)

Robert Rand and Anton Trunov proposed an alternative approach based on mutual
recursion, which I've included here for completeness.  Notice how the two
recursive functions have different recursive arguments.  *)

(* begin hide *)
Module MutRec.
(* end hide *)
Definition body T S := fun subtypeb subtypeb' =>
match T, S with
| _, Top => true
| Int, Int => true
| T1 ⟶ S1, T2 ⟶ S2 => subtypeb' T2 T1 && subtypeb S1 S2
| _, _ => false
end.

Fixpoint subtypeb T S {struct T} := body T S subtypeb subtypeb'
with subtypeb' T S {struct S} := body T S subtypeb' subtypeb.

Notation "T <:? S" := (subtypeb T S) (at level 20, no associativity).

Lemma subtypeb'_subtypeb S T :
(subtypeb' T S = subtypeb T S) * (subtypeb' S T = subtypeb S T).
Proof.
elim: S T=> [| |Ts IHt Ss IHs] [| | Tt St] //=.
by rewrite !IHt !IHs.
Qed.

Lemma subtypebP T S : reflect (T <: S) (T <:? S).
Proof.
apply/(iffP idP); last first.
- by elim: T S / => [[] //| |???? _ IH1 _ IH2] //=; rewrite subtypeb'_subtypeb IH1 IH2.
suffices : (T <:? S -> T <: S) /\ (S <:? T -> S <: T) by case.
elim: S T => [| |T1 IH1 S1 IH2] [| |T2 S2] //=; try by split=>//; constructor.
rewrite !subtypeb'_subtypeb.
split; case/andP.
- by move=> /(proj2 (IH1 _)) subT12 /(proj1 (IH2 _)); constructor.
by move=> /(proj1 (IH1 _)) subT21 /(proj2 (IH2 _)); constructor.
Qed.
(* begin hide *)
End MutRec.
(* end hide *)
