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
of algorithm analysis: no comparison sort can run in less than [O(n *
log n)] steps on an array of size [n].

Before starting, I should point out that this is the first post in
this blog to use the Ssreflect and the Mathematical Components #<a
href="http://ssr.msr-inria.inria.fr">libraries</a>#. Ssreflect is an
amazing Coq extension that brings several improvements, including a
nicer set of base tactics. Both libraries cover a wide range of
theories, including fairly sophisticated Mathematics - as a matter of
fact, both libraries form the basis of the Coq formalization of the
#<a
href="http://en.wikipedia.org/wiki/Feit%E2%80%93Thompson_theorem">Feit-Thompson
theorem</a>#, known for its extremely complex and detailed proof. The
theory of permutations over finite types available in the Mathematical
Components library will be particularly useful for our problem.

We'll begin our formalization by defining a convenient datatype for
representing the execution of a sorting algorithm. For our purposes, a
sorting algorithm can be seen as a binary tree: internal nodes denote
a comparison between two elements, with the right and left branches
telling how to proceed on each case. The leaves of the tree signal
that the algorithm halted, producing a result. This results in the
following type: *)

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

With [execute], we can now define what it means for a sorting
algorithm to be correct: *)

Definition sort_alg_ok n (a : sort_alg n) :=
  forall (T : eqType) (le : rel T),
  forall xs, execute le a xs = sort le xs :> seq T.

(** With [sort_alg_ok] in hand, we are ready to formulate our main
result. Informally, its proof works as follows:

  - In the worst case, an array of size [n] has [n!] permutations.

  - A sorting algorithm can distinguish at most [2 ^ k] permutations,
    where [k] is the maximum number of comparisons performed.

  - Since our algorithm must work on every possible permutation of a
    given array, we know that [n! <= 2 ^ k]. By taking the logarithm
    of both sides, we get [log2 n! <= k].

  - Stirling's approximation tells us that the left-hand side of this
    inequality grows like [n * log n], modulo a multiplicative
    constant. This allows us to conclude.

Using the Mathematical Components library, we can formalize almost all
of the above steps. For instance, here's how we bound the number of
permutations an algorithm can distinguish: *)

Fixpoint comparisons n (a : sort_alg n) : nat :=
  match a with
  | Compare _ _ l r => (maxn (comparisons l) (comparisons r)).+1
  | Done _ => 0
  end.

Fixpoint perms n (a : sort_alg n) : {set 'S_n} :=
  match a with
  | Compare _ _ l r => perms l :|: perms r
  | Done p => [set p]
  end.

Lemma card_perms n (a : sort_alg n) : #|perms a| <= 2 ^ comparisons a.
Proof.
elim: a=> [i j l IHl r IHr|p] /=; last by rewrite cards1.
rewrite (leq_trans (leq_of_leqif (leq_card_setU (perms l) (perms r)))) //.
by rewrite expnS mul2n -addnn leq_add // ?(leq_trans IHl, leq_trans IHr) //
   leq_exp2l // ?(leq_maxl, leq_maxr).
Qed.

(** A crucial part of the above argument, that was left implicit, was
showing that a correct comparison sort must contain all possible
permutations: *)

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

(** Notice how we leveraged the finite sets of Mathematical Components
to help us here.

Unfortunately, we don't have a proof of Stirling's approximation we
can use for the last step, which forces us to take a more direct
route. We show the following lemma by induction ([trunc_log], as its
name says, is the truncated logarithm): *)

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
(** We can then proceed with a reasonably straightforward inductive
argument. *)
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

(* begin hide *)
Import GroupScope.
(* end hide *)
(** We can now conclude with our main result: *)
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
