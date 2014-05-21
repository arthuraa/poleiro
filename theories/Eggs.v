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

Fixpoint play (goal : nat) (s : strategy) : bool :=
  match s with
  | Guess floor => beq_nat floor goal
  | Drop floor broken intact => play goal (if leb goal floor then broken else intact)
  end.

Definition winning (bound : nat) (s : strategy) : Prop :=
  forall goal, goal < bound -> play goal s = true.

Definition is_optimal (bound : nat) (s : strategy) : Prop :=
  winning bound s /\
  forall s', eggs s' = eggs s ->
             winning bound s' ->
             tries s <= tries s'.

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