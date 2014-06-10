(* begin hide *)
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Omega.
Import ListNotations.
(* end hide *)
(** Let's consider the following problem. Suppose that we are in a
100-story building. We know that, when dropping an egg from the
window, that egg will stay intact if we are below a certain
floor. However, if we repeat the same exercise above that critical
floor, the egg will break. How can we find this floor and minimize the
number of egg drops performed in the worst case, if we have only two
eggs? We suppose that we're allowed to reuse eggs that fall without
breaking.

To solve this problem, we will begin by formalizing it. We will model
a playing strategy as a decision tree: *)

Inductive strategy : Type :=
| Guess (floor : nat)
| Drop  (floor : nat) (broken intact : strategy).

(** In the above definition, [Guess floor] represents the end of the
algorithm, when we try to guess at which floor eggs start breaking. If
[floor] is equal to the goal, we win the game. Otherwise, we
lose. [Drop floor broken intact] represents an egg drop at [floor]. If
the egg breaks, we will continue playing with strategy [broken];
otherwise, we continue with [intact].

Given some floor [goal], it is easy to test whether a given strategy
will succeed in guessing it. The [play] function is just a translation
of the above protocol as Coq code: *)

Fixpoint play (goal : nat) (s : strategy) : bool :=
  match s with
  | Guess floor => beq_nat floor goal
  | Drop floor broken intact => play goal (if leb goal floor then broken else intact)
  end.

(** Our model so far does not take into account some of the
restrictions of the original problem, namely the number of floors in
the building and the number of eggs that we can use. Instead of wiring
those in the problem definition, we will reason about them
separately. For instance, [winning lower n s] says that [s] is able to
successfully guess all [n] floors starting from [lower]. *)

Definition winning (lower n : nat) (s : strategy) : Prop :=
  forall goal, lower <= goal < lower + n -> play goal s = true.

(** As we will see, allowing our count to start from [lower] instead
of [0] will help us later.

To define what an optimal strategy is, we need to define the two
missing concepts from our original formulation: how many egg drops a
strategy performs, and how many eggs it needs in the worst case. These
can be readily defined as simple functions. Notice that the definition
of [eggs] is asymmetric, since one of the paths requires us to use one
extra egg, but not the other. *)

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

(** An optimal strategy, for a given range of floors, is one that has
a minimal number of tries among all other minimal strategies for the
same range of floors and same number of eggs. *)

Definition is_optimal (lower n : nat) (s : strategy) : Prop :=
  winning lower n s /\
  forall s', eggs s' = eggs s ->
             winning lower n s' ->
             tries s <= tries s'.

Fixpoint linear (lower upper : nat) : strategy :=
  match upper with
  | 0 => Guess lower
  | S upper' => Drop lower (Guess lower) (linear (S lower) upper')
  end.

Lemma linear_correct lower n :
  winning lower (S n) (linear lower n).
Proof.
  generalize dependent lower.
  induction n as [|n IH]; intros lower goal WIN; simpl.
  - assert (lower = goal) by omega. subst lower.
    now rewrite <- beq_nat_refl.
  - destruct (leb goal lower) eqn:E.
    + apply leb_iff in E.
      assert (lower = goal) by omega.
      subst lower. simpl.
      now rewrite <- beq_nat_refl.
    + apply IH.
      apply leb_iff_conv in E.
      omega.
Qed.

Lemma linear_eggs lower n : eggs (linear lower n) = match n with
                                                    | 0 => 0
                                                    | _ => 1
                                                    end.
Proof.
  generalize dependent lower.
  induction n as [|[|n] IH]; intros lower; trivial.
  replace (eggs (linear lower (S (S n)))) with (eggs (linear (S lower) (S n))); eauto.
  simpl.
  now destruct (eggs (linear (S (S lower)) n)).
Qed.

Lemma linear_tries lower n : tries (linear lower n) = n.
Proof.
  generalize dependent lower.
  induction n as [|n IH]; intros lower; trivial.
  simpl.
  now rewrite IH.
Qed.

Fixpoint guesses (s : strategy) : nat :=
  match s with
  | Guess _ => 1
  | Drop _ broken intact => guesses broken + guesses intact
  end.

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

Lemma optimal_monotone e e' t t' :
  e <= e' -> t <= t' -> optimal e t <= optimal e' t'.
Proof.
  generalize dependent t'.
  generalize dependent e'.
  generalize dependent e.
  induction t as [|t IH]; intros e e' t' He Ht; simpl; try omega.
  destruct e as [|e], e' as [|e'], t' as [|t']; try omega.
  simpl.
  assert (optimal e t <= optimal e' t') by (apply IH; omega).
  assert (optimal (S e) t <= optimal (S e') t') by (apply IH; omega).
  omega.
Qed.

Lemma optimal_monotone_inv e t t' :
  optimal (S e) t <= optimal (S e) t' ->
  t <= t'.
Proof.
  generalize dependent t'.
  generalize dependent e.
  induction t as [|t IH]; intros e t'; simpl; intros H; try omega.
  destruct (le_lt_dec t' t) as [LT |]; try omega.
  assert (optimal (S e) t' <= optimal (S e) t) by (apply optimal_monotone; omega).
  omega.
Qed.

Lemma optimal_guesses s :
  guesses s <= S (optimal (eggs s) (tries s)).
Proof.
  induction s as [floor|floor broken IH1 intact IH2]; simpl; try omega.
  destruct (eggs intact) as [|e'];
  match goal with
  | |- context [optimal ?e ?t + _] =>
    match type of IH1 with
    | _ <= S ?o =>
      assert (o <= optimal e t)
        by (apply optimal_monotone; try omega;
            eauto using Max.le_max_l, Max.le_max_r)
    end;
    match type of IH2 with
    | _ <= S ?o =>
      assert (o <= optimal (S e) t)
        by (apply optimal_monotone; try omega;
            eauto using Max.le_max_l, Max.le_max_r, le_n_S)
    end
  end;
  omega.
Qed.

Fixpoint optimal_strategy (e t lower : nat) : strategy :=
  match t, e with
  | S t', S e' =>
    let floor := lower + optimal e' t' in
    Drop floor
         (optimal_strategy e' t' lower)
         (optimal_strategy (S e') t' (S floor))
  | _, _ => Guess lower
  end.

Let optimal_strategy_correct_aux e t lower :
  winning lower (S (optimal e t)) (optimal_strategy e t lower).
Proof.
  generalize dependent lower.
  generalize dependent e.
  induction t as [|t' IH]; intros e lower goal BOUNDS; simpl.
  - destruct e as [|e']; simpl in *; apply beq_nat_true_iff; omega.
  - destruct e as [|e']; simpl in *;
    try (apply beq_nat_true_iff; omega).
    destruct (leb goal (lower + optimal e' t')) eqn:E.
    + apply IH. apply leb_iff in E. omega.
    + apply IH. apply leb_iff_conv in E. omega.
Qed.

Lemma optimal_strategy_eggs e t lower :
  eggs (optimal_strategy e t lower) = min e t.
Proof.
  generalize dependent lower.
  generalize dependent e.
  induction t as [|t IH]; simpl; intros e lower.
  - now rewrite Min.min_0_r.
  - destruct e as [|e]; trivial.
    simpl.
    rewrite IH. rewrite IH.
    destruct t as [|t].
    + simpl. now rewrite Min.min_0_r.
    + simpl. f_equal.
      rewrite max_l; trivial.
      eapply Min.min_glb.
      * apply Min.le_min_l.
      * etransitivity; try apply Min.le_min_r.
        omega.
Qed.

Lemma optimal_strategy_tries e t lower :
  tries (optimal_strategy e t lower) = match e with 0 => 0 | _ => t end.
Proof.
  generalize dependent lower.
  generalize dependent e.
  induction t as [|t IH]; simpl; intros [|e] lower; trivial.
  simpl.
  repeat rewrite IH.
  destruct e; trivial.
  now rewrite Max.max_idempotent.
Qed.

Theorem optimal_strategy_correct e t lower :
  is_optimal lower (S (optimal e t)) (optimal_strategy e t lower).
Proof.
  split. { apply optimal_strategy_correct_aux. }
  intros s E WIN.
  assert (WIN' := le_trans _ _ _
                           (winning_guesses _ _ _ WIN)
                           (optimal_guesses s)).
  apply le_S_n in WIN'.
  rewrite E in *. clear E.
  rewrite optimal_strategy_eggs in *.
  rewrite optimal_strategy_tries.
  destruct e as [|e]; try omega.
  assert (B' : optimal (min (S e) t) t <= optimal (min (S e) t) (tries s)).
  { etransitivity; try eassumption.
    apply optimal_monotone; try omega.
    apply Min.le_min_l. }
  destruct t as [|t]; try omega.
  eapply optimal_monotone_inv.
  exact B'.
Qed.
