(* begin hide *)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool.
Require Import Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq.
Require Import Ssreflect.fintype.

Require Import MathComp.prime MathComp.tuple MathComp.finset MathComp.fingroup.
Require Import MathComp.perm MathComp.path.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printint Implicit Defensive.
(* end hide *)

Section Sorting.

Local Notation log2 := (trunc_log 2).

Lemma log2_fact n : (n * log2 n)./2 <= log2 n`!.
Proof.
suff: n * (log2 n).+2 <= (log2 n`! + 2 ^ (log2 n)).*2.+1.
  move: (leq0n n); rewrite leq_eqVlt=> /orP [/eqP <- //|pos].
  move/half_leq; rewrite -(addn1 _.*2) halfD odd_double add0n addn0 doubleK.
  rewrite -addn2 mulnDr muln2 halfD odd_double andbF doubleK add0n.
  rewrite (addnC (log2 _)) -leq_subLR -addnBA ?trunc_logP //.
  exact/leq_trans/leq_addr.
have [|] := boolP (3 <= n); last by case: n => [|[|[|[|]]]] //=.
elim: n=> [|n IH] //=.
rewrite leq_eqVlt=> /orP [/eqP <- //|lb]; move/(_ lb) in IH.
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
Qed.

Inductive trace (n : nat) : Type :=
| Compare (i j : 'I_n) (tl tr : trace n)
| Done of 'S_n.

Fixpoint comparisons n (t : trace n) : nat :=
  match t with
  | Compare _ _ tl tr => (maxn (comparisons tl) (comparisons tr)).+1
  | Done _ => 0
  end.

Section Correctness.

Variables (T : eqType) (le : rel T).

Fixpoint execute n (t : trace n) (xs : n.-tuple T) : n.-tuple T :=
  match t with
  | Done p => [tuple tnth xs (p i) | i < n]
  | Compare i j tl tr =>
    if le (tnth xs i) (tnth xs j) then execute tr xs
    else execute tl xs
  end.

End Correctness.

Definition trace_ok (t : forall n, trace n) :=
  forall (T : eqType) (le : rel T),
    transitive le ->
    forall n xs, execute le (t n) xs =
                 sort le xs :> seq T.

Import GroupScope.

Lemma trace_ok_leq n t : trace_ok t -> (n * log2 n)./2 <= comparisons (t n).
Proof.
move/(_ _ _ leq_trans n); move: {t} (t n) => t t_ok.
suff lb: n`! <= 2 ^ comparisons t.
  rewrite (leq_trans (log2_fact n)) // -(@leq_exp2l 2) //.
  by rewrite (leq_trans (trunc_logP (leqnn 2) (fact_gt0 n))).
pose fix ps t : {set 'S_n} :=
  match t with
  | Compare _ _ tl tr => ps tl :|: ps tr
  | Done p => [set p]
  end.
have ub: #|ps t| <= 2 ^ comparisons t.
  elim: {t_ok} t=> [i j tl IHl tr IHr|p] /=; last by rewrite cards1.
  rewrite (leq_trans (leq_of_leqif (leq_card_setU (ps tl) (ps tr)))) //.
  by rewrite expnS mul2n -addnn leq_add // ?(leq_trans IHl, leq_trans IHr) //
     leq_exp2l // ?(leq_maxl, leq_maxr).
rewrite (leq_trans _ ub) // {ub} -{1}(card_ord n) -cardsT -card_perm.
rewrite -(cardsE (perm_on [set: 'I_n])) subset_leq_card //.
apply/subsetP=> /= p _; move: {t_ok} (t_ok [tuple val (p^-1 i) | i < n]).
rewrite (_ : sort _ _ = [tuple val i | i < n]); last first.
  apply: (eq_sorted leq_trans anti_leq (sort_sorted leq_total _)).
    by rewrite /= val_enum_ord iota_sorted.
  rewrite (perm_eq_trans (introT perm_eqlP (perm_sort _ _))) //.
  apply/tuple_perm_eqP; exists p^-1; congr val; apply/eq_from_tnth=> i.
  by rewrite 3!tnth_map 2!tnth_ord_tuple.
elim: t=> [/= i j tl IHl tr IHr|p'].
  by case: ifP=> [_ /IHr|_ /IHl]; rewrite in_setU => -> //; rewrite orbT.
move/val_inj=> /= {ps}.
rewrite in_set1=> e; apply/eqP/permP=> i; apply/esym/(canRL (permKV p)).
apply/val_inj.
rewrite (_ : val i = tnth [tuple val i | i < n] i); last first.
  by rewrite tnth_map tnth_ord_tuple.
by rewrite -{}e 2!tnth_map !tnth_ord_tuple.
Qed.

End Sorting.
