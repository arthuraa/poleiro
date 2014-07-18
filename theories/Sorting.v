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

Lemma fact_pos n : 0 < fact n.
Proof.
  induction n as [|n IH]; simpl; try lia.
  rewrite mult_comm. simpl. lia.
Qed.

Lemma log2_fact_inv n :
  n * log2 n + n * 2 <= log2 (fact n) * 2 + 2 ^ (log2 n) * 2 + 1.
Proof.
  induction n as [|n IH].
  - compute. lia.
  - assert (H : n = 0 \/ n = 1 \/ n = 2 \/ 4 <= S n) by lia.
    destruct H as [H | [H | [H | H]]]; try (subst n; compute; lia).
    assert (LB1 := Nat.log2_le_mono _ _ H).
    change (log2 4) with 2 in LB1.
    assert (LB2 : 0 < n) by lia.
    assert (LB3 : 0 < S n) by lia.
    clear H.
    assert (LB4 := Nat.log2_mul_below _ _ (fact_pos n) LB3).
    simpl.
    destruct (Nat.log2_succ_or n) as [H | H].
    + simpl.
      assert (Bn  := log2_spec _ LB2).
      assert (BSn := log2_spec _ LB3).
      assert (Hn : 2 ^ (log2 (S n)) = S n).
      { apply Nat.log2_eq_succ_is_pow2 in H.
        destruct H as [l H].
        rewrite H at 2.
        f_equal.
        apply Nat.log2_unique; simpl; lia. }
      rewrite H in *.
      simpl in BSn.
      lia.
    + rewrite H. lia.
Qed.

Lemma log2_fact n :
  n * log2 n / 2 <= log2 (fact n).
Proof.
  assert (LB : n = 0 \/ 0 < n) by lia.
  destruct LB as [LB|LB]; try (subst n; reflexivity).
  assert (H := log2_fact_inv n).
  generalize (log2_spec _ LB).
  rewrite (div_mod (n * log2 n) 2) in H; lia.
Qed.
