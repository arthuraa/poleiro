(* begin hide *)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool.
Require Import Ssreflect.ssrnat Ssreflect.eqtype.

Require Import MathComp.prime.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printint Implicit Defensive.
(* end hide *)

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

Inductive sorting_algorithm (s : nat) : Type :=
| Compare (n m : nat) (l r : sorting_algorithm s)
| Done (p : nat) (H : p < fact s).

Fixpoint comparisons s (alg : sorting_algorithm s) : nat :=
  match alg with
  | Compare _ _ l r => S (max (comparisons l) (comparisons r))
  | Done _ _ => 0
  end.

Fixpoint execute s (alg : sorting_algorithm s) (xs : list nat) : list nat :=
  match alg with
  | Done res _ => decode_permutation res s
  | Compare n m l r => if leb (nth n xs 0) (nth m xs 0) then
                         execute r xs
                       else
                         execute l xs
  end.

Definition algorithm_correct s (alg : sorting_algorithm s) (p : nat) : bool :=
  if list_eq_dec Nat.eq_dec
                 (execute alg (decode_permutation p s))
                 (decode_permutation p s)
  then true
  else false.

Lemma algorithm_correct_compare s n m (l r : sorting_algorithm s) p :
  algorithm_correct (Compare n m l r) p = true ->
  algorithm_correct l p || algorithm_correct r p = true.
Proof.
  unfold algorithm_correct. simpl.
  destruct (leb (nth n (decode_permutation p s) 0) (nth m (decode_permutation p s) 0)).
  - destruct (list_eq_dec Nat.eq_dec
                          (execute r (decode_permutation p s))
                          (decode_permutation p s));
    try discriminate.
    now rewrite Bool.orb_true_r.
  - destruct (list_eq_dec Nat.eq_dec
                          (execute l (decode_permutation p s))
                          (decode_permutation p s));
    try discriminate.
    reflexivity.
Qed.

Definition count {A} (f : A -> bool) (l : list A) : nat :=
  length (filter f l).

Lemma count_or A (f g : A -> bool) (l : list A) :
  count (fun a => f a || g a) l <= count f l + count g l.
Proof.
  unfold count.
  induction l as [|a l IH]; simpl; trivial.
  destruct (f a), (g a); simpl; omega.
Qed.

Lemma count_impl A (f g : A -> bool) (l : list A) :
  (forall a, In a l -> f a = true -> g a = true) ->
  count f l <= count g l.
Proof.
  unfold count.
  intros H.
  induction l as [|a l IH]; simpl; trivial.
  specialize (IH (fun a' H1 H2 => H a' (or_intror H1) H2)).
  destruct (f a) eqn:E.
  - rewrite (H a (or_introl eq_refl) E); simpl; auto.
    omega.
  - destruct (g a); simpl; omega.
Qed.

Lemma count_ext A (f g : A -> bool) (l : list A) :
  (forall a, In a l -> f a = g a) ->
  count f l = count g l.
Proof.
  intros H.
  cut (count f l <= count g l <= count f l); try solve [intuition lia].
  split; apply count_impl; intros a H'; specialize (H a H'); congruence.
Qed.

Lemma count_eq_seq : forall s l n, count (beq_nat n) (seq s l) <= 1.
Proof.
  intros s l n.
  cut (count (beq_nat n) (seq s l) =
       if leb s n && negb (leb (s + l) n) then 1 else 0);
  try solve [destruct (leb s n && negb (leb (s + l) n)); omega].
  generalize dependent s.
  induction l as [|l IH]; intros s; simpl.
  - rewrite plus_0_r.
    now destruct (leb s n).
  - unfold count in *. simpl.
    destruct (beq_nat n s) eqn:E; simpl.
    + rewrite IH.
      rewrite beq_nat_true_iff in E. subst n.
      rewrite (leb_correct_conv s (S s)); try omega. simpl.
      rewrite (leb_correct s s); try omega. simpl.
      now rewrite (leb_correct_conv s (s + S l)); try omega.
    + rewrite IH.
      rewrite beq_nat_false_iff in E.
      rewrite <- plus_n_Sm.
      cut (leb (S s) n = leb s n).
      { intros E'. now rewrite E'. }
      destruct (leb s n) eqn:LE.
      * rewrite leb_iff in *. omega.
      * rewrite leb_iff_conv in *. omega.
Qed.

Lemma nth_in :
  forall A def a (l : list A),
    In a l ->
    exists i, i < length l /\
              nth i l def = a.
Proof.
  intros A def a l H.
  induction l as [|a' l IH].
  - destruct H.
  - destruct H as [H | H].
    + subst a'.
      exists 0.
      simpl. split; trivial.
      omega.
    + specialize (IH H).
      destruct IH as (i & H1 & H2).
      exists (S i). simpl. split; trivial.
      omega.
Qed.

Lemma comp_lb_1 s (alg : sorting_algorithm s) :
  count (algorithm_correct alg) (seq 0 (fact s)) <=
  2 ^ (comparisons alg).
Proof.
  induction alg as [n m l IHl r IHr|p H].
  - simpl.
    rewrite (count_impl _ _ _
                        (fun p _ => algorithm_correct_compare n m l r p)),
            count_or.
    rewrite (Nat.pow_le_mono_r _ _ (max (comparisons l) (comparisons r))) in IHl; try lia.
    rewrite (Nat.pow_le_mono_r _ _ (max (comparisons l) (comparisons r))) in IHr; try lia.
  - unfold algorithm_correct. simpl.
    rewrite (@count_ext _ _ (beq_nat p)).
    + apply count_eq_seq.
    + intros p' Hp'.
      destruct (beq_nat p p') eqn:E1,
               (list_eq_dec Nat.eq_dec
                            (decode_permutation p s)
                            (decode_permutation p' s)) as [E2 | NE]; trivial.
      * rewrite beq_nat_true_iff in E1. subst p'.
        congruence.
      * rewrite beq_nat_false_iff in E1. contradict E1.
        rewrite <- (@encode_decode p s H).
        rewrite <- (@encode_decode p' s); try congruence.
        apply (nth_in 0) in Hp'.
        destruct Hp' as (i & H1 & H2).
        rewrite seq_length in H1.
        rewrite <- H2, seq_nth; trivial.
Qed.

Lemma count_true A (l : list A) : count (fun _ => true) l = length l.
Proof.
  induction l as [|? l IH]; trivial.
  unfold count in *. simpl.
  now rewrite IH.
Qed.

Lemma comp_lb_2 s (alg : sorting_algorithm s) :
  forallb (algorithm_correct alg) (seq 0 (fact s)) = true ->
  s * log2 s / 2 <= comparisons alg.
Proof.
  intros H.
  rewrite log2_fact.
  rewrite <- (Nat.log2_pow2 (log2 (fact s))); try omega.
  rewrite <- (Nat.log2_pow2 (comparisons alg)); try omega.
  apply Nat.log2_le_mono.
  rewrite <- comp_lb_1.
  rewrite (@count_ext _ _ (fun _ => true)).
  - rewrite count_true, seq_length.
    pose proof (log2_spec (fact s) (lt_O_fact s)).
    omega.
  - now rewrite forallb_forall in H.
Qed.
