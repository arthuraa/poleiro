(* begin hide *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq bigop.
From mathcomp Require Import ssralg ssrnum ssrint.
(* end hide *)
(** Hillel Wayne #<a
href="https://www.hillelwayne.com/post/theorem-prover-showdown/">posted a
challenge</a># to compare different verification methods: are functional
programs really easier to verify than imperative ones, as some claim?  The
challenge comprised three problems, and I am posting Coq solutions here (two of
them by myself).


** Padding

The first challenge was to prove the correctness of a padding function.  Given a
padding character [c], a length [n] and a sequence [s], [left_pad c n s] should
return the result of adding copies of [c] at the beginning of [s] until the size
reaches [n].  If the original string is larger than [n], the function should do
nothing.  My implementation is similar to other solutions on the web, and reuses
functions and lemmas available in the Math Comp libraries.  *)

Section LeftPad.

Variable T : Type.

Implicit Types (c def : T) (i n : nat) (s : seq T).

Definition left_pad c n s := nseq (n - size s) c ++ s.

(** The call to [nseq] creates a constant sequence with the number of [c]s that
needs to be added, and appends that sequence to [s].  Note that subtraction is
truncated: [n - size s] is equal to 0 when [n <= size s].

As the specification for [left_pad], I am taking the properties that were
verified in the #<a href="https://rise4fun.com/Dafny/nbNTl">Dafny solution</a>#
in Hillel's post.  The proofs are not automated like in Dafny, but still fairly
easy.  (The statements are slightly different because they use the [nth]
function to index into a sequence, which returns a default element when the
index overflows.) *)

Lemma left_pad1 c n s : size (left_pad c n s) = maxn n (size s).
Proof.
by rewrite /left_pad size_cat size_nseq maxnC maxnE [RHS]addnC.
Qed.

Lemma left_pad2 c n s i :
  i < n - size s ->
  nth c (left_pad c n s) i = c.
Proof.
move=> bound.
by rewrite /left_pad nth_cat size_nseq bound nth_nseq bound.
Qed.

Lemma left_pad3 c n s i :
  nth c (left_pad c n s) (n - size s + i) = nth c s i.
Proof.
by rewrite /left_pad nth_cat size_nseq ltnNge leq_addr /= addKn.
Qed.

(** Interestingly, these properties completely characterize the result of
[left_pad]: any function [f] that satisfies the same specification must produce
the same output. *)

Lemma left_padP f :
 (forall c n s, size (f c n s) = maxn n (size s)) ->
 (forall c n s i, i < n - size s -> nth c (f c n s) i = c) ->
 (forall c n s i, nth c (f c n s) (n - size s + i) = nth c s i) ->
  forall c n s, f c n s = left_pad c n s.
Proof.
move=> P1 P2 P3 c n s.
apply: (@eq_from_nth _ c); rewrite {}P1 ?left_pad1 //.
move=> i iP; case: (ltnP i (n - size s))=> [i_n_s|n_s_i].
  rewrite P2 // left_pad2 //.
by rewrite -(subnKC n_s_i) P3 left_pad3.
Qed.

(** Some fans of functional programming claim that it obviates the need for
verification, since the code serves as its own specification.  Though exaggerate
(as we will see in the next problem), the claim does have a certain appeal: the
definition of [left_pad] is shorter and more direct than the specification that
we proved.  Whether it is also easier to understand is a matter of personal
opinion; at the very least, we must know what what [nseq], [++] and [size] are.
*)

End LeftPad.

(**

** Unique

The second problem of the challenge asked us to write a function that removes
all duplicate elements from a sequence.  I decided not to include a solution of
my own here, since it is #<a
href="https://math-comp.github.io/htmldoc/mathcomp.ssreflect.seq.html#undup">already
done in Math Comp</a># under the name [undup].  The intended specification for
this function was showing that the set of elements in its output is the same as
in its input, and that no element occurs twice.  Both properties are proved in
Math Comp (look for [mem_undup] and [undup_uniq]).  Hillel wrote that imperative
programs had an advantage for this problem because of its symmetry.  I am not
sure what was meant by that, but both the Dafny and the Coq proof are comparable
in terms of complexity. (To be fair, Dafny has better automation than Coq, but
this is not related to being functional or imperative.)


** Fulcrum

The last problem was also the most challenging.  We had to write a function to
compute the _fulcrum_ of a sequence of integers [s], which is defined to be the
index [i] that maximizes the quantity [fv s i] shown below. *)

(* begin hide *)
Section Fulcrum.

Open Scope ring_scope.

Import GRing.Theory Num.Theory.
(* end hide *)
Implicit Types (s : seq int) (n : int) (i j : nat).

Definition sumz s := \sum_(n <- s) n.

Definition fv s i := sumz (take i s) - sumz (drop i s).

Definition is_fulcrum s i := forall j, fv s j <= fv s i.

(** It is easy to compute the fulcrum by computing [fv s i] for all values of
[i].  However, this results in a quadratic algorithm, and the problem asked for
a linear solution.  To avoid this pitfall, note that optimizing [fv s i] is
equivalent to optimizing [sumz s (take i s)]. *)

Lemma fvE s i : fv s i = sumz (take i s) *+ 2 - sumz s.
Proof.
by rewrite /sumz -{3}(cat_take_drop i s) big_cat /= opprD addrA mulr2n addrK.
Qed.

Fact is_fulcrumP s i :
  is_fulcrum s i <-> forall j, sumz (take j s) <= sumz (take i s).
Proof.
have P j: (sumz (take j s) <= sumz (take i s)) = (fv s j <= fv s i).
  by rewrite 2!fvE ler_add2r ler_muln2r.
by rewrite /is_fulcrum; split=> H j; rewrite ?P // -P.
Qed.

(** This enables a simple, efficient solution by dynamic programming, computed
    in the following two functions. The main loop is tail-recursive, and takes
    the following parameters:

    - [rest]: The part of the sequence that we still have to traverse;

    - [best]: the optimal value of [sumz s i], where [s] is the sequence of
      elements we have traversed thus far;

    - [curr]: the current sum [sumz s];

    - [best_i]: the index where the optimum [best] is attained; and

    - [curr_i]: the number of elements traversed thus far.

    The top-level function is defined by calling the main loop with suitable
    initial values. *)

Implicit Types (best curr : int) (best_i curr_i : nat).

Fixpoint loop rest best curr best_i curr_i : nat :=
  if rest is x :: rest' then
    let curr' := curr + x in
    if best < curr' then loop rest' curr' curr' curr_i.+1 curr_i.+1
    else loop rest' best curr' best_i curr_i.+1
  else best_i.

Definition fulcrum s := loop s 0 0 0 0.

(** To prove the correctness of [fulcrum], we need to relate the optimal index
    for [rcons s x] in terms of the optimal index for [s].  ([rcons s x] means
    the result of appending [x] to the end of [s].) *)

Lemma sumz1 s x : sumz (rcons s x) = sumz s + x.
Proof. by rewrite /sumz -cats1 big_cat big_seq1. Qed.

Lemma is_fulcrum_rcons s best_i x :
  is_fulcrum s best_i ->
  (best_i <= size s)%N ->
  is_fulcrum (rcons s x)
             (if sumz (take best_i s) < sumz s + x then (size s).+1
              else best_i).
Proof.
rewrite !is_fulcrumP=> best_iP bounds j.
case: ltrP=> [/ltrW le|ge].
  rewrite -(size_rcons s x) take_size sumz1.
  case: (ltnP j (size (rcons s x))) => [|s_j].
    rewrite size_rcons -cats1 => j_s; rewrite takel_cat //.
    exact: ler_trans le.
  by rewrite take_oversize // sumz1.
case: (ltnP j (size (rcons s x))) => [|s_j].
  by rewrite size_rcons -cats1 => j_s; rewrite !takel_cat.
by rewrite take_oversize // sumz1 -cats1 takel_cat.
Qed.

(** This result implies that [is_fulcrum s best_i] is a loop invariant, from
    which the final result follows. *)

Lemma loopP best_i s rest :
  is_fulcrum s best_i ->
  (best_i <= size s)%N ->
  is_fulcrum (s ++ rest)
             (loop rest (sumz (take best_i s)) (sumz s) best_i (size s)).
Proof.
elim: rest s best_i=> [|x rest IH] s1 best_i //=; first by rewrite cats0.
move=> best_iP best_le_s; rewrite -cat1s catA cats1.
have := is_fulcrum_rcons _ _ x best_iP best_le_s.
rewrite -sumz1 -(size_rcons s1 x).
case: ifP=> _ best_iP'; first by rewrite -{2}[rcons _ _]take_size; apply: IH.
rewrite -(takel_cat [:: x] best_le_s) cats1; apply: IH=> //.
by rewrite size_rcons; apply: leq_trans (leqnSn (size _)).
Qed.

Theorem fulcrumP s : is_fulcrum s (fulcrum s).
Proof.
have base : is_fulcrum [::] 0 by rewrite is_fulcrumP /= /sumz big_nil.
by have /= := loopP _ _ s base (leq0n _); rewrite /sumz big_nil.
Qed.

(** for every [i] by storing them in a list; this was the idea behind the #<a
href="https://rise4fun.com/Dafny/UD9n">original Dafny solution</a>#.  *)

End Fulcrum.
