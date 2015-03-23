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
log n)] steps when sorting an array of size [n].

First, we must define a convenient datatype for representing the
execution of a sorting algorithm. For our purposes, a sorting
algorithm can be seen as a binary tree: internal nodes denote a
comparison between two elements, with the right and left branches
telling how to proceed on each case. The leaves of the tree signal
that the algorithm halted, producing a result. This results in the
following type: *)

Inductive sort_alg (n : nat) : Type :=
| Compare (i j : 'I_n) (l r : sort_alg n)
| Done of 'S_n.

(** Let's analyze this declaration in detail. The [n] parameter will
be used later to track the length of the array that we are
sorting. ['I_n] and ['S_n] are types defined in Ssreflect: the former
is the type of natural numbers bounded by [n], whereas the latter
represents permutations of that type. The idea is that, when running
our algorithm, the [i] and [j] arguments of [Compare] tell which
elements of our array to compare. The permutation in [Done] specifies
how to rearrange the elements of the input array to produce an
answer. We can formalize the previous description in the following
function: *)

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

Definition sort_alg_ok (a : forall n, sort_alg n) :=
  forall (T : eqType) (le : rel T),
  forall n xs, execute le (a n) xs = sort le xs :> seq T.

(** With [sort_alg_ok] in hand, we are ready to formulate our main
result. Informally, our proof works as follows:

  - In the worst case, an array of size [n] has [n!] permutations.

  - A sorting algorithm can distinguish at most [2 ^ k] permutations,
    where [k] is the maximum number of comparisons performed.

  - Therefore, [n! <= 2 ^ k], implying [log_2 n! <= k].

  - Using Stirling's approximation, we can weaken this lower bound and
    derive the final result.

Unfortunately, we don't have a Coq proof of Stirling's approximation
we can use here, which forces us to adapt the last step. We show the
following lemma by induction ([trunc_log], as its name says, is the
truncated logarithm): *)

Local Notation log2 := (trunc_log 2).

Lemma log2_fact n : (n * log2 n)./2 <= log2 n`!.
Proof.
(** In order to get our proof to go through, we must strengthen our
induction hypothesis a little bit: *)

suff: n * (log2 n).+2 <= (log2 n`! + 2 ^ (log2 n)).*2.+1.
  (* ... *)
  (* begin hide *)
  move: (leq0n n); rewrite leq_eqVlt=> /orP [/eqP <- //|pos].
  move/half_leq; rewrite -(addn1 _.*2) halfD odd_double add0n addn0 doubleK.
  rewrite -addn2 mulnDr muln2 halfD odd_double andbF doubleK add0n.
  rewrite (addnC (log2 _)) -leq_subLR -addnBA ?trunc_logP //.
  exact/leq_trans/leq_addr.
  (* end hide *)
have [|] := boolP (3 <= n); last by case: n => [|[|[|[|]]]] //=.
elim: n=> [|n IH] //=.
rewrite leq_eqVlt=> /orP [/eqP <- //|lb]; move/(_ lb) in IH.

(** On the inductive step, we also have two cases to consider: whether
or not [log2 n] is less than [log2(n.+1)]. *)
have: log2 n.+1 = log2 n \/ log2 n.+1 = (log2 n).+1 /\ 2 ^ (log2 n.+1) = n.+1.
(* ... *)
(* begin hide *)
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

Fixpoint comparisons n (a : sort_alg n) : nat :=
  match a with
  | Compare _ _ l r => (maxn (comparisons l) (comparisons r)).+1
  | Done _ => 0
  end.

(* begin hide *)
Import GroupScope.
(* end hide *)
Lemma sort_alg_ok_leq n a :
  sort_alg_ok a -> (n * log2 n)./2 <= comparisons (a n).
Proof.
move/(_ _ _ n); move: {a} (a n) => a a_ok.
suff lb: n`! <= 2 ^ comparisons a.
  rewrite (leq_trans (log2_fact n)) // -(@leq_exp2l 2) //.
  by rewrite (leq_trans (trunc_logP (leqnn 2) (fact_gt0 n))).
pose fix ps a : {set 'S_n} :=
  match a with
  | Compare _ _ l r => ps l :|: ps r
  | Done p => [set p]
  end.
have ub: #|ps a| <= 2 ^ comparisons a.
  elim: {a_ok} a=> [i j l IHl r IHr|p] /=; last by rewrite cards1.
  rewrite (leq_trans (leq_of_leqif (leq_card_setU (ps l) (ps r)))) //.
  by rewrite expnS mul2n -addnn leq_add // ?(leq_trans IHl, leq_trans IHr) //
     leq_exp2l // ?(leq_maxl, leq_maxr).
rewrite (leq_trans _ ub) // {ub} -{1}(card_ord n) -cardsT -card_perm.
rewrite -(cardsE (perm_on [set: 'I_n])) subset_leq_card //.
apply/subsetP=> /= p _; move: {a_ok} (a_ok _ leq [tuple val (p^-1 i) | i < n]).
rewrite (_ : sort _ _ = [tuple val i | i < n]); last first.
  apply: (eq_sorted leq_trans anti_leq (sort_sorted leq_total _)).
    by rewrite /= val_enum_ord iota_sorted.
  rewrite (perm_eq_trans (introT perm_eqlP (perm_sort _ _))) //.
  apply/tuple_perm_eqP; exists p^-1; congr val; apply/eq_from_tnth=> i.
  by rewrite 3!tnth_map 2!tnth_ord_tuple.
elim: a=> [/= i j l IHl r IHr|p'].
  by case: ifP=> [_ /IHl|_ /IHr]; rewrite in_setU => -> //; rewrite orbT.
move/val_inj=> /= {ps}.
rewrite in_set1=> e; apply/eqP/permP=> i; apply/esym/(canRL (permKV p)).
apply/val_inj.
rewrite (_ : val i = tnth [tuple val i | i < n] i); last first.
  by rewrite tnth_map tnth_ord_tuple.
by rewrite -{}e 2!tnth_map !tnth_ord_tuple.
Qed.

(* begin hide *)
End Sorting.
(* end hide *)
