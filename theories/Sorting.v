(* begin hide *)
Require Import NPeano.
Require Import Coq.Arith.Arith.
Require Import Psatz.
(* end hide *)
Fixpoint fact (n : nat) : nat :=
  match n with
  | 0 => 1
  | S n' => fact n' * n
  end.

Fixpoint pow2 (n : nat) : nat :=
  match n with
  | 0 => 1
  | S n' => pow2 n' * 2
  end.

Lemma pow2_lower_bound n : n < pow2 n.
Proof.
  induction n as [|n IH]; simpl; try lia.
Qed.

Lemma pow2_plus n m :
  pow2 (n + m) = pow2 n * pow2 m.
Proof.
  induction n as [|n IH]; simpl; lia.
Qed.

Lemma mono1 :
  forall (f : nat -> nat),
    (forall x y, x < y -> f x < f y) ->
    forall x y, x <= y -> f x <= f y.
Proof.
  intros f Hf x y Hxy.
  apply le_lt_eq_dec in Hxy.
  destruct Hxy as [Hxy | Hxy]; subst; try lia.
  pose proof (Hf x y Hxy). lia.
Qed.

Lemma mono2 :
  forall (f : nat -> nat),
    (forall x y, x < y -> f x < f y) ->
    forall x y, f x <= f y -> x <= y.
Proof.
  intros f Hf x y Hxy.
  apply le_not_lt in Hxy.
  destruct (le_lt_dec x y) as [LE|LT]; trivial.
  contradict Hxy.
  eauto.
Qed.

Lemma mono3 :
  forall (f : nat -> nat),
    (forall x y, x < y -> f x < f y) ->
    forall x y, f x < f y -> x < y.
Proof.
  intros f Hf x y Hxy.
  destruct (le_lt_dec y x) as [LE|LT]; trivial.
  apply (mono1 _ Hf) in LE. lia.
Qed.

Lemma mono4 :
  forall (f : nat -> nat),
    (forall x y, x <= y -> f x <= f y) ->
    forall x y, f x < f y -> x < y.
Proof.
  intros f Hf x y Hxy.
  destruct (le_lt_dec y x) as [LE|LT]; trivial.
  apply Hf in LE. lia.
Qed.

Lemma pow2_monotone n m :
  n < m -> pow2 n < pow2 m.
Proof.
  intros H.
  replace m with (m - n + n) by lia.
  rewrite pow2_plus.
  pose proof (pow2_lower_bound (m - n)).
  pose proof (pow2_lower_bound n).
  destruct (pow2 (m - n)) as [|[|]]; simpl; try lia.
Qed.

Fixpoint log2loop (n fuel : nat) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
    if leb (pow2 fuel') n then
      fuel'
    else
      log2loop n fuel'
  end.

Definition log2 (n : nat) : nat := log2loop n n.

Require Import ZArith.

Definition log2' (n : nat) : nat :=
  Z.to_nat (Z.log2 (Z.of_nat n)).

Lemma log2loop_correct :
  forall n fuel,
    0 < n ->
    n < pow2 fuel ->
    pow2 (log2loop n fuel) <= n < pow2 (S (log2loop n fuel)).
Proof.
  intros n fuel POS H.
  induction fuel as [|fuel IH].
  - simpl in *.
    destruct n as [|[|n]]; lia.
  - simpl in *.
    destruct (leb (pow2 fuel) n) eqn:E.
    + rewrite leb_iff in E; lia.
    + rewrite leb_iff_conv in E.
      now apply IH in E.
Qed.

Lemma log2_correct :
  forall n,
    0 < n ->
    pow2 (log2 n) <= n < pow2 (S (log2 n)).
Proof.
  intros n H.
  unfold log2.
  apply log2loop_correct; trivial.
  now apply pow2_lower_bound.
Qed.

Lemma pow2K n : log2 (pow2 n) = n.
Proof.
  assert (H : pow2 (log2 (pow2 n)) <= pow2 n < pow2 (S (log2 (pow2 n)))).
  { pose proof (pow2_lower_bound n).
    apply log2_correct. lia. }
  destruct H as [H1 H2].
  apply (mono2 _ pow2_monotone) in H1.
  apply (mono3 _ pow2_monotone) in H2. lia.
Qed.

Lemma log2_monotone :
  forall n m,
    n <= m ->
    log2 n <= log2 m.
Proof.
  intros [|n] [|m] H; try (compute; lia).
  assert (Hn : pow2 (log2 (S n)) <= S n < pow2 (S (log2 (S n)))).
  { apply log2_correct; lia. }
  assert (Hm : pow2 (log2 (S m)) <= S m < pow2 (S (log2 (S m)))).
  { apply log2_correct; lia. }
  assert (Hnm : pow2 (log2 (S n)) < pow2 (S (log2 (S m)))) by lia.
  apply (mono3 _ pow2_monotone) in Hnm. lia.
Qed.

Lemma log2_mult :
  forall n m,
    0 < n ->
    0 < m ->
    log2 n + log2 m <= log2 (n * m).
Proof.
  intros n m Hn Hm.
  assert (Hnm : 0 < n * m) by (destruct n; destruct m; simpl; lia).
  assert (Hln := log2_correct n Hn).
  assert (Hlm := log2_correct m Hm).
  assert (Hlnm := log2_correct (n * m) Hnm).
  assert (Hlnm' : pow2 (log2 n) * pow2 (log2 m) <= n * m)
   by (apply mult_le_compat; lia).
  clear Hln Hlm.
  destruct (le_lt_dec (S (log2 (n * m))) (log2 n + log2 m)) as [LE|LT]; try lia.
  apply (mono1 _ pow2_monotone) in LE.
  rewrite pow2_plus in LE.
  lia.
Qed.

Lemma log2_S :
  forall n,
    0 < n ->
    log2 (S n) = log2 n \/
    log2 (S n) = S (log2 n) /\
    pow2 (log2 (S n)) = S n.
Proof.
  intros n H.
  assert (Hn := log2_correct n H).
  assert (HSn : pow2 (log2 (S n)) <= S n < pow2 (S (log2 (S n)))).
  { apply log2_correct. lia. }
  assert (Hln : log2 n <= log2 (S n)) by (apply log2_monotone; lia).
  assert (Hln' : log2 (S n) = log2 n \/
                 log2 (S n) = S (log2 n) \/
                 S (log2 n) < log2 (S n)) by lia.
  destruct Hln' as [Hln' | [Hln' | Hln' ] ]; auto.
  - right. split; trivial.
    rewrite <- Hln' in Hn. lia.
  - apply pow2_monotone in Hln'. lia.
Qed.

Fixpoint summation (f : nat -> nat) (n : nat) : nat :=
  match n with
  | 0 => f 0
  | S n' => f n + summation f n'
  end.

Lemma fact_pos n : 0 < fact n.
Proof.
  induction n as [|n IH]; simpl; try lia.
  rewrite mult_comm. simpl. lia.
Qed.

Fixpoint fact' (n : nat) : Z :=
  match n with
  | 0 => 1%Z
  | S n' => (fact' n' * Z.of_nat n)%Z
  end.

Definition bounds n : nat * nat :=
  (n * log2' n +
   summation log2' n -
   pow2 (log2' n),
   2 * Z.to_nat (Z.log2 (fact' n))).

Require Import List.
Import ListNotations.

Fixpoint range (n : nat) : list nat :=
  match n with
  | 0 => []
  | S n' => 0 :: map (plus 1) (range n')
  end.

Definition tests := Eval compute in range 100.

Compute (map bounds tests).

Definition bounds2 n :=
  (summation log2' n, Z.to_nat (Z.log2 (fact' n))).

Compute (map bounds2 tests).

Definition bounds3 n :=
  (n, Z.to_nat (Z.log2 (fact' n)) + log2' (n + 1),
   Z.to_nat (Z.log2 (fact' (n + 1)))).

Compute (map bounds3 tests).

Definition bounds4 n :=
  (n * log2' n +
   summation log2' n -
   summation (fun i => pow2 i - 1) (log2' n),
   Z.to_nat (2 * Z.log2 (fact' n))).

Definition equiv1 n :=
  (summation (fun i => pow2 i - 1) (log2' n),
   (2 ^ (Z.log2 (Z.of_nat n) + 1) - 1 - (Z.log2 (Z.of_nat n) + 1))%Z).

Compute (map bounds4 tests).

Compute (map equiv1 tests).

Lemma log2_fact_1 :
  forall n,
    n * log2 n +
    summation log2 n <=
    log2 (fact n) * 2 +
    summation (fun i => pow2 i - 1) (log2 n).
Proof.
  induction n as [|n IH].
  - compute. lia.
  - simpl.
    assert (H : n = 0 \/ 0 < n) by lia.
    destruct H as [?|POS].
    { subst. compute. lia. }
    assert (POS' : 0 < S n) by lia.
    generalize (log2_mult _ _ (fact_pos n) POS').
    destruct (log2_S n POS) as [H | [H1 H2]].
    + rewrite H. lia.
    + rewrite H1 in *. simpl summation. simpl in H2.
      rewrite H2. simpl. lia.
Qed.

Definition bounds5 n :=
  (n,
   summation (fun i => pow2 i - 1) (log2' n),
   summation log2' n).

(* Compute (map bounds5 tests).*)

Lemma sum_pow2 n :
  summation (fun i => pow2 i - 1) n =
  pow2 (S n) - n - 2.
Proof.
  induction n as [|n IH]; trivial.
  unfold summation. fold summation.
  rewrite IH.
  change (pow2 (S (S n))) with (pow2 (S n) * 2).
  generalize (pow2_lower_bound (S n)).
  lia.
Qed.

Compute (map (fun i => (2 * i, summation log2' i + log2' i + 2)) tests).

Lemma log2_fact_3 n :
  3 < n ->
  2 * n <= summation log2 n + log2 n + 2.
Proof.
  induction n as [|n IH]; try lia.
  assert (H : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ 5 <= S n) by lia.
  destruct H as [H | [H | [H | [H | H]]]]; try (subst; compute; lia).
  intros _.
  assert (LB : 3 < n) by lia.
  apply log2_monotone in H.
  change (log2 5) with 2 in H.
  simpl.
  assert (log2 n <= log2 (S n)) by (apply log2_monotone; lia).
  lia.
Qed.

Lemma log2_fact_2 :
  forall n,
    summation (fun i => pow2 i - 1) (log2 n) <=
    summation log2 n.
Proof.
  intros n.
  rewrite sum_pow2.
  assert (LB := pow2_lower_bound (S (log2 n))).
  cut (pow2 (S (log2 n)) <= summation log2 n + log2 n + 2); try lia.
  assert (H : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ 3 < n) by lia.
  intuition (try (subst n; compute; lia)).
  cut (pow2 (S (log2 n)) <= 2 * n <= summation log2 n + log2 n + 2); try lia.
  split.
  - simpl.
    assert (H' : 0 < n) by lia.
    generalize (log2_correct n H'). lia.
  - now apply log2_fact_3.
Qed.

Lemma log2_fact_5 n :
  n * log2 n / 2 <= log2 (fact n).
Proof.
  assert (H : n * log2 n <= 2 * log2 (fact n)).
  { pose proof (log2_fact_1 n).
    pose proof (log2_fact_2 n).
    lia. }
  rewrite (div_mod (n * log2 n) 2) in H; [lia | congruence].
Qed.

Lemma log2_fact_6 n :
  n * log2 n / 2 <= log2 (fact n).
Proof.
  assert (n * log2 n + n * 2 <= log2 (fact n) * 2 + pow2 (log2 n) * 2 + 1).
  { induction n as [|n IH].
    - compute. lia.
    - assert (H : n = 0 \/ n = 1 \/ n = 2 \/ 4 <= S n) by lia.
      destruct H as [H | [H | [H | H]]]; try (subst n; compute; lia).
      assert (LB1 := log2_monotone _ _ H).
      change (log2 4) with 2 in LB1.
      assert (LB2 : 0 < n) by lia.
      assert (LB3 : 0 < S n) by lia.
      clear H.
      assert (LB4 := log2_mult _ _ (fact_pos n) LB3).
      simpl.
      destruct (log2_S _ LB2) as [H | [H1 H2]].
      + simpl. rewrite H in *. lia.
      + simpl.
        assert (B := log2_correct _ LB2).
        rewrite H1 in *. simpl in H2. simpl.
        lia. }
  assert (LB : n = 0 \/ 0 < n) by lia.
  destruct LB as [LB|LB]; try (subst n; reflexivity).
  assert (B := log2_correct _ LB).
  rewrite (div_mod (n * log2 n) 2) in H; lia.
Qed.
