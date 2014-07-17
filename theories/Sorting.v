(* begin hide *)
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

(*

    T.S.:
    forall n,
      2 log2 n! >=
      n log2 n + \sum_i^n [log2 i] - 2^(log2 n) + 1

    2 log2 (n+1)! >=
    2 log2 (n+1) + 2 log2 n >=
    2 log2 (n+1) + n log2 n + \sum_i^n [log2 i] - 2^(log2 n) + 1 =
    log2 (n+1) + n log2 n + \sum_i^(n+1) [log2 i] - 2^(log2 n) + 1

    - case 1: log2 (n+1) = log2 n

      2 log2 (n+1)! >=
      (n+1) log2 (n+1) + \sum_i^(n+1) [log2 i] - 2^(log2 (n+1)) + 1

    - case 2: log2 (n+1) = log2 n + 1

      2 log2 (n+1)! >=
      log2 (n+1) + n log2 (n+1) - n - n log2 n
        + n log2 n + \sum_i^(n+1) [log2 i] - 2^(log2 n) + 1 =
      (n+1) log2 (n+1) - (n+1) + \sum_i^(n+1) [log2 i]
        - 2^(log2 n) + 2 =
      (n+1) log2 (n+2) + \sum_i^(n+1) [log2 i] - 2^(log2 (n+1)) - 2^(log2 n) + 2 =
      (n+1) log2 (n+2) + \sum_i^(n+1) [log2 i] - 2 * 2^(log2 n) - 2^(log2 n) + 2 =
      (n+1) log2 (n+2) + \sum_i^(n+1) [log2 i] - 2 * 2^(log2 n) - 2^(log2 n) + 2 =
*)

Definition bounds n : nat * nat :=
  (n * log2 n +
   summation log2 n -
   pow2 (log2 n),
   2 * log2 (fact n)).

Compute (log2 120).

Definition ub n : nat :=
  2 * log2 (fact n).

Compute




Lemma log_fact_n_log_n_aux :
  forall n,
    n * log2 n +
    summation log2 n -
    pow2 (log2 n) + 1 <=
    log2 (fact n) * 2.
Proof.
  induction n as [|n IH].
  - simpl. lia.
  - simpl.
    assert (H : n = 0 \/ 0 < n) by lia.
    destruct H as [?|POS]; try solve [subst; simpl; lia].
    destruct (log2_S n POS).
    + rewrite H.
