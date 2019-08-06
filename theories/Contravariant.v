(* begin hide *)
From mathcomp Require Import ssreflect ssrfun ssrbool.
(* end hide *)
(** Convincing Coq that a function terminates can be frustrating.  Suppose we
want to formalize a static programming language with types given by the
following grammar: *)

Inductive type :=
| Top (* Any value whatsoever, akin to Object in Java or Ruby *)
| Int
| Arrow (T S : type) (* Functions from T to S *).

Notation "T ⟶ S" := (Arrow T S) (at level 25, right associativity).

(** We would like to define a notion of subtyping for this language, so that we
can use elements of [Int] or [T ⟶ S] in contexts that expect a value of type
[Top].  For this to make sense, subtyping must be _contravariant_ with respect
to the domain of function types.  For instance, [Top ⟶ Int] should be a subtype
of [Int ⟶ Int] even though [Top] is not a subtype of [Int]: intuitively, if a
function takes an argument of _any_ type, it is safe to view it as taking only
integers as arguments.  On the other hand, [Int ⟶ Int] is _not_ a subtype of
[Top ⟶ Int]: if a function only works for integer arguments, passing it
arguments of other types might cause it to behave improperly.  The induction
relation below formalizes subtyping in the language. (Note that the _codomain_
of the function is _covariant_, meaning that it goes in the same direction as
the subtyping relation.) *)
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

(** We would like to show that subtyping is decidable by expressing this
relation as a function returning a boolean.  Writing this function is not
difficult in principle, but the obvious definition is rejected: *)

Fail Fixpoint subtypeb T S {struct T} :=
  match T, S with
  | _, Top => true
  | Int, Int => true
  | T1 ⟶ S1, T2 ⟶ S2 => subtypeb T2 T1 && subtypeb S1 S2
  | _, _ => false
  end.

(**
[[
Recursive definition of subtypeb is ill-formed.
...
Recursive call to subtypeb has principal argument equal
to "T2" instead of one of the following variables: "T1" "S1".
]]

What happened? Recursive functions in Coq are always defined with respect to
a _principal argument_.  In this case, the argument was marked as [T] using the
[struct] keyword, but Coq can usually find the principal argument by itself when
this declaration is omitted.  For the definition to be valid, all the recursive
calls must be performed on principal arguments that are subterms of the original
principal argument.  However, our definition of [subtypeb] swaps its two
arguments to decide if the domain types are related, leading to the above error
message.

Coq provides _well-founded recursion_ to circumvent this rigid check, which
allows recursive calls whenever the arguments decrease according to a suitable
relation.  In the case of [subtypeb], for instance, we could show termination by
proving that the combined sizes of the two arguments decrease on every call.
However, there is a more direct route: it suffices to add a flag to the function
to specify if we are computing subtyping in the correct or opposite order.  If
we flip the flag on the first call, we do not need to flip the arguments. *)

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

(** To relate the two definitions of subtyping, we must prove a few results.
First, we show that flipping the flag of [subtypeb_gen] is equivalent to
flipping the two other arguments.  *)

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
