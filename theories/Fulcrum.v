(* begin hide *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From mathcomp Require Import fintype bigop ssralg ssrnum ssrint tuple.
(* end hide *)
(** Hillel Wayne #<a
href="https://www.hillelwayne.com/post/theorem-prover-showdown/">posted a
challenge</a># to compare different verification methods: are functional
programs really easier to verify than imperative ones, as some claim?  There
were three problems in the challenge, and I am posting Coq solutions here (two
of them by myself).


** Padding

The first challenge was to prove the correctness of a padding function.  Given a
padding character [c], a length [n] and a sequence [s], [left_pad c n s] should
return the result of adding copies of [c] at the beginning of [s] until the size
reaches [n].  If the original string is larger than [n], the function should do
nothing.  My implementation is similar to other solutions on the web, and reuses
functions and lemmas available in the Math Comp libraries.  *)
(* begin hide *)
Section LeftPad.

Variable char : Type.
(* end hide *)
Implicit Types (c : char) (i n : nat) (s : seq char).

Definition left_pad c n s := nseq (n - size s) c ++ s.

(** The call to [nseq] creates a constant sequence with the number of [c]s that
needs to be added, and appends that sequence to [s].  Note that subtraction is
truncated: [n - size s] is equal to 0 when [n <= size s].

As the specification for [left_pad], I am taking the properties that were
verified in the #<a href="https://rise4fun.com/Dafny/nbNTl">Dafny solution</a>#
in Hillel's post.  The proofs are not automated like in Dafny, but still fairly
easy.  (The statements are slightly different because they use the [nth]
function to index into a sequence, which requires a default element to return
when the index overflows.) *)

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
(* begin hide *)
Proof.
move=> P1 P2 P3 c n s.
apply: (@eq_from_nth _ c); rewrite {}P1 ?left_pad1 //.
move=> i iP; case: (ltnP i (n - size s))=> [i_n_s|n_s_i].
  rewrite P2 // left_pad2 //.
by rewrite -(subnKC n_s_i) P3 left_pad3.
Qed.
(* end hide *)
(** Some fans of functional programming claim that it obviates the need for
verification, since the code serves as its own specification.  Though exaggerate
(as we will see in the last problem), the claim does have a certain appeal: the
definition of [left_pad] is shorter and more direct than the specification that
we proved.  Whether it is also easier to understand is a matter of personal
opinion; at the very least, we must know what what [nseq], [++] and [size] are.
*)
(* begin hide *)
End LeftPad.
(* end hide *)
(** ** Unique

The second problem of the challenge asked to remove all duplicate elements from
a sequence.  I decided not to include a solution of my own here, since it is #<a
href="https://math-comp.github.io/htmldoc/mathcomp.ssreflect.seq.html#undup">already
done in Math Comp</a># under the name [undup].  We had to show that the set of
elements in its output is the same as in its input, and that no element occurs
twice, properties that are both proved in Math Comp ([mem_undup] and
[undup_uniq]).  Hillel wrote that imperative programs had an advantage for this
problem because of its symmetry.  I am not sure what was meant by that, but the
Dafny and the Coq proofs are comparable in terms of complexity.  (To be fair,
Dafny has better automation than Coq, but this has probably little to do with
being functional or imperative: other functional provers fare better than Coq in
this respect as well.)


** Fulcrum

The last problem was also the most challenging.  The goal was to compute the
_fulcrum_ of a sequence of integers [s], which is defined to be the index [i]
that maximizes the quantity [fv s i] shown below. *)

(* begin hide *)
Section Fulcrum.

Open Scope ring_scope.

Import GRing.Theory Num.Theory.
(* end hide *)
Implicit Types (s : seq int) (n : int) (i j : nat).

Definition sumz s := \sum_(n <- s) n.

Definition fv s i := sumz (take i s) - sumz (drop i s).

Definition is_fulcrum s i := forall j, fv s j <= fv s i.

(** It would be easy to write another functional program that is obviously
correct in this case: just compute [fv s i] for all indices [i] and return the
index that yields the largest value.  Indeed, Math Comp already provides this
functionality for us. *)

Definition fulcrum_naive s :=
  [arg maxr_(i > ord0 : 'I_(size s).+1) fv s (val i)].

Lemma fulcrum_naiveP s : is_fulcrum s (fulcrum_naive s).
Proof.
rewrite /fulcrum_naive; case: arg_maxrP=> //= i _ iP j.
have jP: (minn j (size s) < (size s).+1)%N by rewrite ltnS geq_minr.
pose j' : 'I_(size s).+1 := Ordinal jP.
suff ->: fv s j = fv s (val j') by exact: iP.
rewrite /fv /=; case: (ltnP j (size s))=> [/ltnW/minn_idPl -> //|s_j].
by rewrite (minn_idPr s_j) take_size drop_size take_oversize // drop_oversize.
Qed.

(** Unfortunately, this would run in quadratic time, and the problem asked for a
_linear_ solution.  We can do better by noting that optimizing [fv s i] is
equivalent to optimizing [sumz (take i s)]. *)

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

(** Thus, instead of computing each [sumz (take i s)] from scratch, we can
simply compute [sumz (take (i + 1) s)] from [sumz (take i s)] by adding the
missing value.  This enables a simple, efficient solution by dynamic
programming.  The workhorse is [loop], which computes the fulcrum of a sequence
of the form [s ++ rest] assuming that we have already computed the fulcrum of
[s].  It takes the following parameters:

- [rest]: The part of the sequence that we still have to traverse;

- [best]: the optimal value of [sumz (take i s)];

- [best_i]: the index where the optimum [best] is attained; and

- [curr]: the current sum [sumz s];

- [curr_i]: the number of elements traversed so far. *)

Implicit Types (rest : seq int) (best curr : int) (best_i curr_i : nat).

Fixpoint loop rest best best_i curr curr_i : nat :=
  if rest is n :: rest' then
    let curr'   := curr + n  in
    let curr_i' := curr_i.+1 in
    let best'   := if best < curr' then curr'   else best   in
    let best_i' := if best < curr' then curr_i' else best_i in
    loop rest' best' best_i' curr' curr_i'
  else best_i.

Definition fulcrum s := loop s 0 0 0 0.

(** To prove the correctness of [fulcrum], we just need to prove the correctness
of [loop], for which it suffices to assume that the parameters are set up
appropriately. *)
(* begin hide *)
Lemma sumz1 s n : sumz (rcons s n) = sumz s + n.
Proof. by rewrite /sumz -cats1 big_cat big_seq1. Qed.
(* end hide *)
Lemma loopP best_i s rest :
  is_fulcrum s best_i ->
  (best_i <= size s)%N ->
  is_fulcrum (s ++ rest)
    (loop rest (sumz (take best_i s)) best_i (sumz s) (size s)).
(* begin hide *)
Proof.
elim: rest s best_i=> [|n rest IH] s best_i /=; first by rewrite cats0.
move=> best_iP bounds; rewrite -cat1s catA cats1 -sumz1 -(size_rcons s n).
suff: is_fulcrum (rcons s n)
        (if sumz (take best_i s) < sumz (rcons s n) then size (rcons s n)
         else best_i).
  case: ifP=> _ ?; first by rewrite -{2}[rcons _ _]take_size; apply: IH.
  rewrite -(takel_cat [:: n] bounds) cats1; apply: IH=> //.
  by rewrite size_rcons; apply: leq_trans (leqnSn (size _)).
move: best_iP; rewrite !is_fulcrumP; case: ltrP=> [/ltrW le|ge] best_iP j.
  rewrite take_size.
  case: (ltnP j (size (rcons s n))) => [|?]; last by rewrite take_oversize.
  rewrite size_rcons -{1}cats1 => j_s; rewrite takel_cat //.
  exact: ler_trans le.
case: (ltnP j (size (rcons s n))) => [|?].
  by rewrite size_rcons -cats1 => j_s; rewrite !takel_cat.
by rewrite take_oversize // -{2}cats1 takel_cat.
Qed.
(* end hide *)
Theorem fulcrumP s : is_fulcrum s (fulcrum s).
Proof.
have base : is_fulcrum [::] 0 by rewrite is_fulcrumP /= /sumz big_nil.
by have /= := loopP _ _ s base (leq0n _); rewrite /sumz big_nil.
Qed.

(** The algorithm presented here makes one small improvement over the #<a
href="https://rise4fun.com/Dafny/UD9n">Dafny solution</a>#: it traverses the
input list only once, which would allow to compute the fulcrum _online_, without
having the entire sequence stored in memory.  The original program had to
traverse the sequence forward and backward to compute the values of [sumz (take
i s)] and [sumz (drop i s)], whereas our algorithm only needs the values of
[sumz (take i s)], thanks to [is_fulcrumP].  It would be interesting to see how
a Dafny solution would leverage this property.  *)
(* begin hide *)
End Fulcrum.
(* end hide *)
(** ** Conclusion

So, is functional really better than imperative for verification?  Though I am a
fan of functional languages, I will not attempt to offer a definitive answer.
It is true that simple programs such as [left_pad] are often as good (or better)
than their specifications, but some of those would be inefficient in practice,
and fast implementations might be tricky to verify.

As mentioned in Hillel's post, the main issue when verifying imperative code is
aliasing: we must argue that every call preserves the assumptions made in other
parts of the code, something that comes for free with functional programming.
However, if a program only modifies local state (like the Dafny solutions did),
this kind of interference becomes much more manageable.

Of course, nothing prevents us from combining the benefits of functional and
imperative programming.  We can implement an efficient algorithm using mutable
state and verify it against a specification that mixes logic and pure code.
Most of the Dafny solution was spent on writing and verifying purely functional
code used in its specification -- indeed, many frameworks for verifying
imperative code only allow pure code in specifications.

In the end, what seems to matter the most is how rich of a specification
language you have, how convenient it is for reasoning, and how much automation
it provides.

*)
