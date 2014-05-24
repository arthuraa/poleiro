Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Omega.
Import ListNotations.

Inductive strategy : Type :=
| Guess (floor : nat)
| Drop  (floor : nat) (broken intact : strategy).

Fixpoint eggs (s : strategy) : nat :=
  match s with
  | Guess _ => 0
  | Drop _ broken intact => max (S (eggs broken)) (eggs intact)
  end.

Fixpoint tries (s : strategy) : nat :=
  match s with
  | Guess _ => 0
  | Drop _ broken intact => S (max (tries broken) (tries intact))
  end.

Fixpoint guesses (s : strategy) : nat :=
  match s with
  | Guess _ => 1
  | Drop _ broken intact => guesses broken + guesses intact
  end.

Fixpoint play (goal : nat) (s : strategy) : bool :=
  match s with
  | Guess floor => beq_nat floor goal
  | Drop floor broken intact => play goal (if leb goal floor then broken else intact)
  end.

Definition winning (lower n : nat) (s : strategy) : Prop :=
  forall goal, lower <= goal < lower + n -> play goal s = true.

Definition is_optimal (lower n : nat) (s : strategy) : Prop :=
  winning lower n s /\
  forall s', eggs s' = eggs s ->
             winning lower n s' ->
             tries s <= tries s'.

Lemma winning_inv lower n floor broken intact :
  winning lower n (Drop floor broken intact) ->
  exists n1 n2 lower',
    n = n1 + n2 /\
    winning lower n1 broken /\
    winning lower' n2 intact.
Proof.
  unfold winning. simpl. intros WIN.
  destruct (le_lt_dec (lower + n) floor) as [LE | LT].
  - eexists n, 0, 0.
    split; try omega.
    split; try solve [intros; omega].
    intros goal I.
    assert (BOUND : goal <= floor) by omega.
    apply WIN in I.
    rewrite <- leb_iff in BOUND. now rewrite BOUND in I.
  - destruct (le_lt_dec lower floor) as [LE' | LT'].
    + eexists (S floor - lower), (lower + n - S floor), (S floor).
      split; try omega.
      split; intros goal I;
      assert (I' : lower <= goal < lower + n) by omega;
      apply WIN in I'.
      * assert (BOUND : goal <= floor) by omega.
        rewrite <- leb_iff in BOUND. now rewrite BOUND in I'.
      * assert (BOUND : floor < goal) by omega.
        rewrite <- leb_iff_conv in BOUND. now rewrite BOUND in I'.
    + eexists 0, n, lower.
      split; trivial.
      split; intros goal I; try omega.
      assert (BOUND : floor < goal) by omega.
      apply WIN in I.
      rewrite <- leb_iff_conv in BOUND. now rewrite BOUND in I.
Qed.

Lemma winning_guesses lower n s :
  winning lower n s -> n <= guesses s.
Proof.
  generalize dependent n.
  generalize dependent lower.
  induction s as [floor|floor broken IH1 intact IH2];
  intros lower n WIN.
  - unfold winning in WIN. simpl in WIN.
    destruct (le_lt_dec n 1) as [?|CONTRA]; trivial.
    assert (H1 : beq_nat floor lower = true) by (apply WIN; omega).
    assert (H2 : beq_nat floor (S lower) = true) by (apply WIN; omega).
    rewrite beq_nat_true_iff in H1, H2. omega.
  - apply winning_inv in WIN.
    destruct WIN as (n1 & n2 & lower' & ? & WIN1 & WIN2). subst n. simpl.
    apply IH1 in WIN1. apply IH2 in WIN2. omega.
Qed.

Fixpoint optimal (eggs tries : nat) : nat :=
  match tries, eggs with
  | S tries', S eggs' => S (optimal eggs' tries' + optimal (S eggs') tries')
  | _, _ => 0
  end.

Fixpoint optimal_strategy (eggs tries lower : nat) : strategy :=
  match tries, eggs with
  | S tries', S eggs' =>
    let floor := lower + optimal eggs' tries' in
    Drop floor
         (optimal_strategy eggs' tries' lower)
         (optimal_strategy (S eggs') tries' (S floor))
  | _, _ => Guess lower
  end.

Fixpoint counter (lower : nat) (s : strategy) : nat :=
  match s with
  | Guess floor =>
    if beq_nat floor lower then S lower
    else lower
  | Drop floor broken intact =>
    if leb lower floor then
      if leb (counter lower broken) floor then counter lower broken
      else counter (S floor) intact
    else counter lower intact
  end.

Lemma counter_lower lower s : lower <= counter lower s.
Proof.
  generalize dependent lower.
  induction s as [floor|floor broken IH1 intact IH2]; intros lower; simpl.
  - destruct (beq_nat floor lower); try omega.
  - destruct (leb lower floor) eqn:E; auto.
    destruct (leb (counter lower broken) floor) eqn:E'; auto.
    rewrite leb_iff in E.
    etransitivity; eauto.
    transitivity (S floor); eauto.
Qed.

Lemma counter_correct lower s :
  play (counter lower s) s = false.
Proof.
  generalize dependent lower.
  induction s as [floor|floor broken IH1 intact IH2]; intros lower; simpl.
  - destruct (beq_nat floor lower) eqn:E; trivial.
    rewrite beq_nat_true_iff in E. subst lower.
    rewrite beq_nat_false_iff. omega.
  - destruct (leb lower floor) eqn:E.
    + destruct (leb (counter lower broken) floor) eqn:E'.
      * rewrite E'. apply IH1.
      * destruct (leb (counter (S floor) intact) floor) eqn:E''; eauto.
        rewrite leb_iff in E''.
        cut (floor < counter (S floor) intact); try omega.
        apply counter_lower.
    + destruct (leb (counter lower intact) floor) eqn:E'; auto.
      apply leb_iff in E'. apply leb_iff_conv in E.
      generalize (counter_lower lower intact). omega.
Qed.

Lemma counter_minimal lower s goal :
  lower <= goal < counter lower s -> play goal s = true.
Proof.
  generalize dependent lower.
  induction s as [floor|floor broken IH1 intact IH2]; intros lower H; simpl in *.
  - destruct (beq_nat floor lower) eqn:E; try omega.
    assert (lower = goal) by omega. subst goal.
    rewrite beq_nat_true_iff in E. subst.
    now rewrite <- beq_nat_refl.
  - destruct (leb goal floor) eqn:E.
    + rewrite leb_iff in E.
      destruct (leb lower floor) eqn:E'.
      * rewrite leb_iff in E'.
        destruct (leb (counter lower broken) floor) eqn:E''; eauto.
        rewrite leb_iff_conv in E''. apply (IH1 lower). omega.
      * rewrite leb_iff_conv in E'. assert (H' := counter_lower lower broken).
        apply (IH1 lower). omega.
    + rewrite leb_iff_conv in E.
      destruct (leb lower floor) eqn:E'.
      * rewrite leb_iff in E'.
        destruct (leb (counter lower broken) floor) eqn:E''.
        { rewrite leb_iff in E''. omega. }
        rewrite leb_iff_conv in E''.
        apply (IH2 (S floor)). omega.
      * rewrite leb_iff_conv in E'.
        apply (IH2 lower). omega.
Qed.
