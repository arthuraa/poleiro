(* begin hide *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq bigop.
From mathcomp Require Import ssralg ssrnum ssrint.
(* end hide *)

Section Padding.

Variable T : Type.

Implicit Types (c def : T) (i n : nat) (s : seq T).

Definition left_pad c n s := nseq (n - size s) c ++ s.

Lemma left_pad1 c n s : size (left_pad c n s) = maxn n (size s).
Proof.
by rewrite /left_pad size_cat size_nseq maxnC maxnE [RHS]addnC.
Qed.

Lemma left_pad2 c n s i def :
  i < n - size s ->
  nth def (left_pad c n s) i = c.
Proof.
move=> bound.
by rewrite /left_pad nth_cat size_nseq bound nth_nseq bound.
Qed.

Lemma left_pad3 c n s i def :
  nth def (left_pad c n s) (n - size s + i) = nth def s i.
Proof.
by rewrite /left_pad nth_cat size_nseq ltnNge leq_addr /= addKn.
Qed.

End Padding.

From mathcomp
Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq ssralg ssrnum ssrint bigop.

Section Fulcrum.

Local Open Scope ring_scope.

Import GRing.Theory Num.Theory.

Implicit Types (best curr : int) (best_i curr_i : nat) (s : seq int).

Definition sumz s := \sum_(n <- s) n.

Lemma sumz1 s x : sumz (rcons s x) = sumz s + x.
Proof. by rewrite /sumz -cats1 big_cat big_seq1. Qed.

(** This is the quantity that we are trying to optimize by varying [i]. *)

Definition fv s i := sumz (take i s) - sumz (drop i s).

(** [is_answer s i] holds when [i] is the index that optimizes [fv s i].  By
    simple arithmetic, we don't have to consider the second term in the
    definition of [fv]; only the first. *)

Definition is_answer s i :=
  all (fun i' => fv s i' <= fv s i) (iota 0 (size s).+1).

Lemma fvE s i : fv s i = sumz (take i s) *+ 2 - sumz s.
Proof.
by rewrite /sumz -{3}(cat_take_drop i s) big_cat /= opprD addrA mulr2n addrK.
Qed.

Fact is_answerE s i :
  is_answer s i
  = all (fun i' => sumz (take i' s) <= sumz (take i s)) (iota 0 (size s).+1).
Proof. by apply/eq_all=> i'; rewrite 2!fvE ler_add2r ler_muln2r. Qed.

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

Lemma is_answer_next s best_i x :
  is_answer s best_i ->
  (best_i <= size s)%N ->
  is_answer (rcons s x)
            (if sumz (take best_i s) < sumz s + x then (size s).+1
             else best_i).
Proof.
rewrite !is_answerE -[(size (rcons _ _)).+1]addn1 iota_add add0n all_cat.
set best := sumz (take best_i s) => base bounds; rewrite /= andbT take_size.
case: lerP=> [le|gt] /=.
  rewrite sumz1 -{2 4}cats1 takel_cat // le andbT size_rcons /is_true -base.
  apply/eq_in_all=> i; rewrite mem_iota add0n leq0n ltnS leq_eqVlt /=.
  by case/orP=> [/eqP ->|?]; rewrite -cats1 takel_cat // ltnW.
rewrite -(size_rcons s x) take_size lerr andbT size_rcons.
apply/allP=> i iP; rewrite sumz1 -{1}cats1 takel_cat.
  move/ltrW: gt; move/allP/(_ _ iP): base; exact/ler_trans.
by move: iP; rewrite mem_iota /= add0n ltnS.
Qed.

(** This result implies that [is_answer s best_i] is a loop invariant, from
    which the final result follows. *)

Lemma loopP best_i s rest :
  is_answer s best_i ->
  (best_i <= size s)%N ->
  is_answer (s ++ rest)
            (loop rest (sumz (take best_i s)) (sumz s) best_i (size s)).
Proof.
elim: rest s best_i=> [|x rest IH] s1 best_i //=; first by rewrite cats0.
move=> best_iP best_le_s; rewrite -cat1s catA cats1.
have := is_answer_next _ _ x best_iP best_le_s; rewrite -sumz1 -(size_rcons s1 x).
case: ifP=> _ best_iP'; first by rewrite -{2}[rcons _ _]take_size; apply: IH.
rewrite -(takel_cat [:: x] best_le_s) cats1; apply: IH=> //.
by rewrite size_rcons; apply: leq_trans (leqnSn (size _)).
Qed.

Theorem fulcrumP s : is_answer s (fulcrum s).
Proof.
have base : is_answer [::] 0 by rewrite is_answerE /= /sumz big_nil.
by have /= := loopP _ _ s base (leq0n _); rewrite /sumz big_nil.
Qed.

End Fulcrum.
