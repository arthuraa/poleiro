(* begin hide *)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool.
Require Import Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq.
Require Import Ssreflect.fintype.

Require Import MathComp.prime MathComp.tuple MathComp.finset MathComp.fingroup.
Require Import MathComp.perm MathComp.path.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printint Implicit Defensive.

Section Sorting.
(* end hide *)

(** In this post, we will formalize one of the most well-known results
of algorithm analysis: no comparison sort can run in asymptotically
less than [n * log n] steps, where [n] is the size of its input.

Before starting, I should point out that this is the first post in
this blog to use the Ssreflect and the Mathematical Components
(MathComp) #<a
href="http://ssr.msr-inria.inria.fr">libraries</a>#. Ssreflect is an
amazing Coq extension that brings several improvements, including a
nicer set of base tactics. Both libraries cover a wide range of
theories, including fairly sophisticated Mathematics - as a matter of
fact, they are featured in the Coq formalization of the #<a
href="http://en.wikipedia.org/wiki/Feit%E2%80%93Thompson_theorem">Feit-Thompson
theorem</a>#, known for its extremely complex and detailed proof.

As we will see, having good library support can help a lot when doing
mechanized proofs, even for such simple results as this one. Two
things that come in handy here, in particular, are the theories of
_permutations_ and _sets_ over finite types that are available in
MathComp. Indeed, the MathComp definitions enable many useful,
higher-level reasoning principles that don't come for free in Coq,
such as extensional and decidable equality. Furthermore, many lemmas
on the library require a fair amount of machinery to be developed on
their own - for example, showing that there are exactly [n!]
permutations over a set of [n] elements. Previous versions of this
post (which you can still find on the repository) tried to avoid
external libraries, but were much longer and more complicated,
prompting me to bite the bullet and port everything to
Ssreflect/MathComp.

** Basics

The informal proof of this result is fairly simple:

  - If a comparison sort is correct, then it must be capable of
    shuffling an input vector of size [n] according to _any_ of the
    [n!] permutations of its elements.

  - On the other hand, any such algorithm can recognize at most [2 ^
    k] distinct permutations, where [k] is the maximum number of
    comparisons performed. Hence, [n! <= 2 ^ k] or, equivalently,
    [log2 n! <= k].

  - To conclude, Stirling's approximation tells us that [n * log2 n =
    O(log2 n!)], which yields our result.

We'll begin our formalization by defining a convenient datatype for
representing the execution of a comparison sort. For our purposes, a
comparison sort can be seen as a binary tree: internal nodes indicate
when a comparison between two elements occurs, with the right and left
branches telling how to proceed depending on its result. The leaves of
the tree mark when the algorithm ends and yields back a result. Thus,
we obtain the following type: *)

Inductive sort_alg (n : nat) : Type :=
| Compare (i j : 'I_n) (l r : sort_alg n)
| Done of 'S_n.

(** Let's analyze this declaration in detail. The [n] parameter will
be used later to track the length of the array that we are
sorting. ['I_n] is the type of natural numbers bounded by [n], whereas
['S_n] represents permutations of elements of that type. The idea is
that, when running our algorithm, the [i] and [j] arguments of
[Compare] tell which elements of our array to compare. The permutation
in [Done] specifies how to rearrange the elements of the input array
to produce an answer. We can formalize the previous description in the
following function: *)

Fixpoint execute T n c (a : sort_alg n) (xs : n.-tuple T) :=
  match a with
  | Compare i j l r =>
    let a' := if c (tnth xs i) (tnth xs j) then l else r in
    execute c a' xs
  | Done p => [tuple tnth xs (p i) | i < n]
  end.

(** [execute] is a polymorphic function that works for any type [T]
with a comparison operator [c]. Given an algorithm [a] and an input
array [xs] of length [n], the function compares the elements of [a],
following the appropriate branches along the way, until finding out
how to rearrange [a]'s elements.

With [execute], we can define what it means for a sorting algorithm to
be correct, by relating its results to the MathComp [sort] function:
*)

Definition sort_alg_ok n (a : sort_alg n) :=
  forall (T : eqType) (le : rel T),
  forall xs, execute le a xs = sort le xs :> seq T.

(** Finally, to translate the above informal argument, we will need
some more definitions. Let's first write a function for computing how
many comparisons an algorithm performs in the worst case: *)

Fixpoint comparisons n (a : sort_alg n) : nat :=
  match a with
  | Compare _ _ l r => (maxn (comparisons l) (comparisons r)).+1
  | Done _ => 0
  end.

(** And here's a function for computing the set of permutations that
an algorithm can perform (notice the use of the set library of
MathComp; here, [:|:] denotes set union): *)

Fixpoint perms n (a : sort_alg n) : {set 'S_n} :=
  match a with
  | Compare _ _ l r => perms l :|: perms r
  | Done p => [set p]
  end.

(** (Strictly speaking, both [comparisons] and [perms] give upper
bounds on the values they should compute, but this does not affect us
in any crucial way.)

** Show me the proofs

To show that a correct algorithm must be able of performing arbitrary
permutations, notice that, if [xs] is a sorted array with distinct
elements, then permuting its elements is an _injective_
operation. That is, different permutations produce different
arrays. *)
(* begin hide *)
Section WithGroupScope.
Import GroupScope.
(* end hide *)
Lemma permsT n (a : sort_alg n) : sort_alg_ok a -> perms a = [set: 'S_n].
Proof.
move=> a_ok.
apply/eqP; rewrite -subTset; apply/subsetP=> /= p _.
move: {a_ok} (a_ok _ leq [tuple val (p^-1 i) | i < n]).
rewrite (_ : sort _ _ = [tuple val i | i < n]); last first.
  apply: (eq_sorted leq_trans anti_leq (sort_sorted leq_total _)).
    by rewrite /= val_enum_ord iota_sorted.
  rewrite (perm_eq_trans (introT perm_eqlP (perm_sort _ _))) //.
  apply/tuple_perm_eqP; exists p^-1; congr val; apply/eq_from_tnth=> i.
  by rewrite 3!tnth_map 2!tnth_ord_tuple.
elim: a=> [/= i j l IHl r IHr|p'].
  by case: ifP=> [_ /IHl|_ /IHr]; rewrite in_setU => -> //; rewrite orbT.
move/val_inj=> /=.
rewrite in_set1=> e; apply/eqP/permP=> i; apply/esym/(canRL (permKV p)).
apply/val_inj.
rewrite (_ : val i = tnth [tuple val i | i < n] i); last first.
  by rewrite tnth_map tnth_ord_tuple.
by rewrite -{}e 2!tnth_map !tnth_ord_tuple.
Qed.
(* begin hide *)
End WithGroupScope.
(* end hide *)

(** Bounding the number of permutations performed by an algorithm is
simple, and amounts to invoking basic lemmas about arithmetic and
sets. *)

Lemma card_perms n (a : sort_alg n) : #|perms a| <= 2 ^ comparisons a.
Proof.
elim: a=> [i j l IHl r IHr|p] /=; last by rewrite cards1.
rewrite (leq_trans (leq_of_leqif (leq_card_setU (perms l) (perms r)))) //.
by rewrite expnS mul2n -addnn leq_add // ?(leq_trans IHl, leq_trans IHr) //
   leq_exp2l // ?(leq_maxl, leq_maxr).
Qed.

(** Doing the last step is a bit trickier, as we don't have a proof of
Stirling's approximation we can use. Instead, we take a more direct
route, showing the following lemma by induction on [n] ([trunc_log],
as its name implies, is the truncated logarithm): *)

Local Notation log2 := (trunc_log 2).

Lemma log2_fact n : (n * log2 n)./2 <= log2 n`!.
Proof.
(** In order to get our proof to go through, we must strengthen our
induction hypothesis a little bit: *)
suff: n * (log2 n).+2 <= (log2 n`! + 2 ^ (log2 n)).*2.+1.
  (* begin hide *)
  move: (leq0n n); rewrite leq_eqVlt=> /orP [/eqP <- //|pos].
  move/half_leq; rewrite -(addn1 _.*2) halfD odd_double add0n addn0 doubleK.
  rewrite -addn2 mulnDr muln2 halfD odd_double andbF doubleK add0n.
  rewrite (addnC (log2 _)) -leq_subLR -addnBA ?trunc_logP //.
  exact/leq_trans/leq_addr.
  (* end hide *)
(** We can then proceed with a straightforward (although not
completlely trivial) inductive argument. *)
elim: n=> [|n IH] //=.
(* ... *)
(* begin hide *)
have [lb|] := boolP (3 <= n); last by case: n IH => [|[|[|[|]]]] //=.
have: log2 n.+1 = log2 n \/ log2 n.+1 = (log2 n).+1 /\ 2 ^ (log2 n.+1) = n.+1.
  move: (@trunc_log_bounds 2 _ erefl (@leq_trans 3 1 n erefl lb))
        (@trunc_log_bounds 2 _ erefl (@leq_trans 4 1 n.+1 erefl lb))
        => /andP [e1 e2] /andP [e3 e4].
  move: (leq_trans e3 e2); rewrite leq_exp2l leq_eqVlt //.
  case/orP=> [/eqP e5|].
    by right; split=> //; apply/eqP; rewrite eqn_leq e3 e5.
  rewrite ltnS leq_eqVlt=> /orP [/eqP ?|e5]; left=> //.
  rewrite -(@leq_exp2l 2) // in e5.
  by move: (leq_trans e4 (leq_trans e5 e1)); rewrite ltnNge leqnSn.
have lb1: 2 <= log2 n.+1 by rewrite trunc_log_max //.
have lb2: log2 n.+1 + log2 n`! <= log2 (n.+1)`!.
  by rewrite trunc_log_max // factS expnD leq_mul // trunc_logP // fact_gt0.
case=> [e|[e1 e2]].
  have lb3: (log2 n).+2 <= (log2 n).*2 by rewrite -addnn -addn2 leq_add2l -e.
  rewrite e mulSn (leq_trans (leq_add lb3 IH)) // addnS -doubleD ltnS.
  by rewrite leq_double addnA leq_add2r -e.
rewrite e1 mulSn mulnS (addnC n) addnA (addnC _.+3) -addnA.
rewrite (leq_trans (leq_add IH (leqnn _))) // -e1 e2 doubleD.
rewrite -[(2 ^ _).*2]muln2 mulnC -expnS -e1 e2 addSn ltnS.
rewrite -addnA (addnA _.+1) (addnC _.+1) 2!addnA -addnA doubleD leq_add //.
  rewrite -(addn2 (log2 _)) addnA.
  rewrite (leq_trans (leq_add (leqnn _) lb1)) // -addnA addnn -doubleD.
  by rewrite addnC leq_double.
by rewrite -addnn leq_add2l.
(* end hide *)
Qed.

(** Our main result follows almost immediately from these three
intermediate lemmas: *)

Lemma sort_alg_ok_leq n (a : sort_alg n) :
  sort_alg_ok a -> (n * log2 n)./2 <= comparisons a.
Proof.
move=> a_ok; suff lb: n`! <= 2 ^ comparisons a.
  rewrite (leq_trans (log2_fact n)) // -(@leq_exp2l 2) //.
  by rewrite (leq_trans (trunc_logP (leqnn 2) (fact_gt0 n))).
rewrite (leq_trans _ (card_perms a)) // -{1}(card_ord n) -cardsT -card_perm.
by rewrite -(cardsE (perm_on [set: 'I_n])) subset_leq_card // permsT //.
Qed.
(* begin hide *)
End Sorting.
(* end hide *)
(** ** Summary

We've seen how to formalize a result of algorithm analysis in an
_abstract_ setting: although it is fair to say that our model of a
comparison sort is detailed enough for our purposes, we haven't
connected it yet to a more traditional computation model, something I
plan to discuss on a future post.

Aside from that, we've seen how a rich set of theories, such as the
ones in MathComp, allow us to express higher-level concepts in our
definitions and proofs, leading to much shorter formalizations. *)
