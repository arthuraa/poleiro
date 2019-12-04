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
that minimizes the quantity [fv s i] shown below. *)

(* begin hide *)
Section Fulcrum.

Open Scope ring_scope.

Import GRing.Theory Num.Theory.
(* end hide *)
Implicit Types (s : seq int) (n : int) (i j : nat).

Definition sumz s := \sum_(n <- s) n.

Definition fv s i := `|sumz (take i s) - sumz (drop i s)|.

Definition is_fulcrum s i := forall j, fv s i <= fv s j.

(** It would be easy to write another functional program that is obviously
correct in this case: just compute [fv s i] for all indices [i] and return the
index that yields the smallest value.  Indeed, Math Comp already provides this
functionality for us. *)

Definition fulcrum_naive s :=
  [arg minr_(i < ord0 : 'I_(size s).+1) fv s (val i)].

Lemma fulcrum_naiveP s : is_fulcrum s (fulcrum_naive s).
Proof.
rewrite /fulcrum_naive; case: arg_minrP=> //= i _ iP j.
have jP: (minn j (size s) < (size s).+1)%N by rewrite ltnS geq_minr.
pose j' : 'I_(size s).+1 := Ordinal jP.
suff ->: fv s j = fv s (val j') by exact: iP.
rewrite /fv /=; case: (ltnP j (size s))=> [/ltnW/minn_idPl -> //|s_j].
by rewrite (minn_idPr s_j) take_size drop_size take_oversize // drop_oversize.
Qed.

(** Unfortunately, this would run in quadratic time, and the problem asked for a
_linear_ solution.  We can do better by computing the values of [fv s i]
incrementally, as in dynamic programming.  We begin by recasting [fv] in a more
convenient form.  *)

Lemma fvE s i : fv s i = `|sumz (take i s) *+ 2 - sumz s|.
(* begin hide *)
Proof.
by rewrite /sumz -{3}(cat_take_drop i s) big_cat /= opprD addrA mulr2n addrK.
Qed.
(* end hide *)

(** This allows us to compute the fulcrum of [s] by traversing [s] and keeping
the following variables:

- [best_i]: The fulcrum of [s] with respect to the positions traversed so far;

- [curr_i]: The current position;

- [best]: The value of [sumz (take best_i s) * 2 - sumz s];

- [curr]: The value of [sumz (take curr_i s) * 2 - sumz s] *)

Implicit Types (best curr : int) (best_i curr_i : nat).

Fixpoint loop s best_i curr_i best curr : nat :=
  if s is n :: s' then
    let curr'   := n *+ 2 + curr  in
    let curr_i' := curr_i.+1 in
    let best'   := if `|curr'| < `|best| then curr'   else best   in
    let best_i' := if `|curr'| < `|best| then curr_i' else best_i in
    loop s' best_i' curr_i' best' curr'
  else best_i.

Definition fulcrum s := loop s 0 0 (- sumz s) (- sumz s).

(** To prove the correctness of [fulcrum], we just need to prove the correctness
of [loop], for which it suffices to assume that the parameters are set up
appropriately.  We generalize the property a little bit so that it can be proved
inductively.  *)
(* begin hide *)
Lemma sumz1 s n : sumz (rcons s n) = sumz s + n.
Proof. by rewrite /sumz -cats1 big_cat big_seq1. Qed.
(* end hide *)

Definition inv s k best_i curr_i :=
  forall j, (j <= curr_i)%N ->
    `|sumz (take best_i s) *+ 2 - k| <= `|sumz (take j s) *+ 2 - k|.

Lemma loopP best_i s1 k s2 :
  inv (s1 ++ s2) k best_i (size s1) ->
  (best_i <= size s1)%N ->
  inv (s1 ++ s2) k
    (loop s2 best_i (size s1)
      (sumz (take best_i (s1 ++ s2)) *+ 2 - k) (sumz s1 *+ 2 - k))
    (size (s1 ++ s2)).
(* begin hide *)
Proof.
elim: s2 s1 best_i=> [|n s2 IH] s1 best_i /=; first by rewrite cats0.
rewrite -cat1s catA cats1 -(size_rcons s1 n).
rewrite addrA -mulrnDl [n + _]addrC -sumz1 => best_iP bounds.
set best    := sumz (take best_i (rcons s1 n ++ s2)) *+ 2 - _.
set curr'   := sumz (rcons s1 n) *+ 2 - _.
set best'   := if `|curr'| < `|best| then curr' else best.
set best_i' := if `|curr'| < `|best| then size _ else best_i.
have bounds': (best_i' <= size (rcons s1 n))%N.
  rewrite /best_i'; case: ifP=> _ //.
  by rewrite size_rcons; apply: leq_trans (leqnSn (size _)).
have ->: best' = sumz (take best_i' (rcons s1 n ++ s2)) *+ 2 - k.
  by rewrite /best' /best_i'; case: ifP=> _; rewrite // takel_cat // take_size.
apply: IH=> // j jP; rewrite /best_i'; case: ltrP=> [found|not_found].
  rewrite takel_cat // take_size.
  case: ltngtP jP=> // [|<-]; last by rewrite takel_cat // take_size.
  rewrite size_rcons => jP _; apply: ler_trans (ltrW found) _; exact: best_iP.
case: ltngtP jP=> // [|<-].
  by rewrite size_rcons => jP _; apply: best_iP.
by rewrite [take (size _) _]takel_cat // ?take_size.
Qed.
(* end hide *)
Theorem fulcrumP s : is_fulcrum s (fulcrum s).
Proof.
have base: inv ([::] ++ s) (sumz s) 0 (size (Nil int)) by case.
have /= := loopP _ _ _ s base (leq0n _).
rewrite take0 [sumz [::]]/sumz big_nil add0r => endP j; rewrite !fvE.
suff ->: take j s = take (minn j (size s)) s.
  apply: endP; exact: geq_minr.
case: (leqP j (size s))=> [/minn_idPl -> //|/ltnW s_j].
by rewrite take_oversize // (minn_idPr s_j) take_size.
Qed.

(** The algorithm presented here makes one small improvement over the #<a
href="https://rise4fun.com/Dafny/UD9n">Dafny solution</a>#: it uses constant
auxiliary memory, whereas the original program used intermediate arrays to store
the values of [sumz (take i s)] and [sumz (drop i s)].  It would be interesting
to try to translate this algorithm back into Dafny.  *)
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
