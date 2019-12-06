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

Lemma foldlP T S f (s : seq T) x0 (I : nat -> S -> Prop) :
  I 0 x0 ->
  (forall (i : 'I_(size s)) x,
     I i x ->
     I i.+1 (f x (tnth (in_tuple s) i))) ->
  I (size s) (foldl f x0 s).
Proof.
rewrite -[s]cat0s [in foldl _ _ _]/= -[0]/(size (Nil T)).
elim: s [::] x0=> [|a s2 IH] s1 x0; first by rewrite cats0.
rewrite -cat1s catA cats1 => x0P inv /=; apply: IH=> //.
have iP: size s1 < size (rcons s1 a ++ s2).
  by rewrite size_cat size_rcons leq_addr.
move: (inv (Sub (size s1) iP) _ x0P).
by rewrite (tnth_nth a) /= nth_cat size_rcons leqnn nth_rcons ltnn eqxx.
Qed.

Section Fulcrum.

Open Scope ring_scope.

Import GRing.Theory Num.Theory.
(* end hide *)
Implicit Types (s : seq int) (n : int).

Definition fv s i :=
  \sum_(l < i) s`_l - \sum_(i <= l < size s) s`_l.

Definition is_fulcrum s i := forall j, `|fv s i| <= `|fv s j|.

(** It would be easy to write another functional program that is obviously
correct in this case: just compute [fv s i] for all indices [i] and return the
index that yields the smallest value.  Indeed, Math Comp already provides this
functionality for us. *)

Definition fulcrum_naive s :=
  [arg minr_(i < ord0 : 'I_(size s).+1) `|fv s i|].

Lemma fvE s i : fv s i = (\sum_(l < i) s`_l) *+ 2 - \sum_(l < size s) s`_l.
(* begin hide *)
Proof.
suff: \sum_(l < size s) s`_l = \sum_(0 <= l < i) s`_l + \sum_(i <= l < size s) s`_l.
  by rewrite !big_mkord => ->; rewrite opprD addrA mulr2n addrK.
rewrite -[\sum_(l < size s) _](big_mkord predT) /=.
case: (leqP i (size s))=> [i_s|/ltnW s_i].
  exact: big_cat_nat.
rewrite (big_geq s_i) addr0.
rewrite (big_nat_widen _ _ _ _ _ s_i) /= big_mkcond /=.
by apply/eq_bigr=> l _; case: ltnP=> // ?; rewrite nth_default.
Qed.
(* end hide *)

Lemma fv_overflow s i : fv s i = fv s (minn i (size s)).
Proof.
rewrite !fvE; congr (_ *+ 2 - _).
case: (leqP i (size s))=> [/minn_idPl -> //|/ltnW s_i].
rewrite (minn_idPr s_i) (big_ord_widen _ _ s_i) [RHS]big_mkcond /=.
by apply/eq_bigr=> l; case: ltnP=> //= ? _; rewrite nth_default.
Qed.

Lemma fulcrum_naiveP s : is_fulcrum s (fulcrum_naive s).
Proof.
rewrite /fulcrum_naive; case: arg_minrP=> //= i _ iP j.
move/(_ (inord (minn j (size s))) erefl): iP.
rewrite (_ : fv s (inord _) = fv s j) //= [RHS]fv_overflow.
by rewrite inordK ?ltnS ?geq_minr //.
Qed.

(** Unfortunately, this would run in quadratic time, and the problem asked for a
_linear_ solution.  We can do better by computing the values of [fv s i]
incrementally, as in dynamic programming.  We begin by recasting [fv] in a more
convenient form.  *)

Record state := State {
  best_i : nat;
  curr_i : nat;
  best   : int;
  curr   : int;
}.

Variant fulcrum_inv s i st : Prop :=
| FlucrumInv of
 (st.(best_i) <  (size s).+1)%N   &
 (st.(best_i) <= i)%N             &
  st.(curr_i) =  i                &
  st.(best)   =  fv s st.(best_i) &
  st.(curr)   =  fv s i           &
  (forall j, (j <= i)%N -> `|fv s st.(best_i)| <= `|fv s j|).

Definition fulcrum_body st n :=
  let curr'   := n *+ 2 + st.(curr)  in
  let curr_i' := st.(curr_i).+1 in
  let best'   := if `|curr'| < `|st.(best)| then curr'   else st.(best)   in
  let best_i' := if `|curr'| < `|st.(best)| then curr_i' else st.(best_i) in
  State best_i' curr_i' best' curr'.

Definition fulcrum s :=
  let k := - \sum_(n <- s) n in
  (foldl fulcrum_body (State 0 0 k k) s).(best_i).

Lemma fulcrumP s : is_fulcrum s (fulcrum s).
Proof.
rewrite /fulcrum; set st := foldl _ _ _.
suff: fulcrum_inv s (size s) st.
  case=> ????? iP j; rewrite [fv s j]fv_overflow; apply: iP.
  exact: geq_minr.
apply: foldlP=> {st}; first split=> //=.
- by rewrite fvE big_ord0 add0r !(big_nth 0) big_mkord.
- by rewrite fvE big_ord0 add0r !(big_nth 0) big_mkord.
- move=> [|] //.
move=> i [best_i _ _ _] [/= b1 b2 -> -> -> inv].
have e: fv s i.+1 = s`_i *+ 2 + fv s i.
  by rewrite !fvE big_ord_recr /= [_ + s`_i]addrC mulrnDl addrA.
split=> //=; rewrite ?(tnth_nth 0) //=.
- by case: ifP=> //=; rewrite ltnS (valP i).
- by case: ifP=> //; rewrite -ltnS ltnW.
- by case: ifP.
move=> j; case: ltngtP=> // [j_i|<-] _.
  case: ifP=> [|_]; last exact: inv.
  rewrite -e=> /ltrW iP; apply: ler_trans iP _; exact: inv.
by case: ifP=> //; rewrite -e ltrNge => /negbFE ->.
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
