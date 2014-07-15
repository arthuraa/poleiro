(* begin hide *)
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Omega.
Require Import Psatz.
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

Definition is_optimal (n : nat) (s : strategy) : Prop :=
  exists lower, winning lower n s /\
  forall lower' s', eggs s' <= eggs s ->
             winning lower' n s' ->
             tries s <= tries s'.

(** A simple strategy is to perform linear search, starting at the
bottom and going up one floor at a time. As soon as the egg breaks, we
know we've found our goal. *)

Fixpoint linear (lower n : nat) : strategy :=
  match n with
  | 0 => Guess lower
  | S n' => Drop lower (Guess lower) (linear (S lower) n')
  end.

(** [linear lower n] works for a range of up to [n] floors, and uses
at most one egg. Unfortunately, it is not very efficient, performing
[n] tries in the worst case. *)

Lemma linear_winning lower n :
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

Lemma linear_eggs lower n : eggs (linear lower n) = min 1 n.
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

(** How can we optimize how many tries we need in the worst case for
solving a given range of floors? The key insight is to reason by
_duality_ and, instead, ask "what is the largest instance of our
problem that we can solve with a given maximum number of eggs and
tries?" When looking at the problem this way, it becomes clear that
optimality has a recursive structure that is easy to describe: to find
a floor using at most [e] eggs and [t] tries, we need to combine two
optimal strategies: one using at most [e-1] eggs and [t-1] tries, for
the case where our first drop causes the egg to break, and another
using at most [e] eggs and [t-1] tries, for the case where our egg
doens't break at first. We can readily express this idea as
code. [optimal_range e t] computes the maximal instance size that can
be solved using [e] eggs and [t] tries at most, while
[optimal_strategy e t lower] computes a strategy for doing so starting
from floor [lower]. *)

Fixpoint optimal_range (e t : nat) {struct t} : nat :=
  match t, e with
  | S t', S e' => S (optimal_range e' t' +
                     optimal_range (S e') t')
  | _, _ => 0
  end.

Fixpoint optimal_strategy (e t lower : nat) : strategy :=
  match t, e with
  | S t', S e' =>
    let floor := lower + optimal_range e' t' in
    Drop floor
         (optimal_strategy e' t' lower)
         (optimal_strategy (S e') t' (S floor))
  | _, _ => Guess lower
  end.

(** It is easy to show that [optimal_strategy] indeed uses the
resources that we expect. *)

Lemma optimal_strategy_winning e t lower :
  winning lower (S (optimal_range e t)) (optimal_strategy e t lower).
Proof.
  generalize dependent lower.
  generalize dependent e.
  induction t as [|t' IH]; intros e lower goal BOUNDS; simpl.
  - destruct e as [|e']; simpl in *; apply beq_nat_true_iff; omega.
  - destruct e as [|e']; simpl in *;
    try (apply beq_nat_true_iff; omega).
    destruct (leb goal (lower + optimal_range e' t')) eqn:E.
    + apply IH. apply leb_iff in E. omega.
    + apply IH. apply leb_iff_conv in E. omega.
Qed.

Lemma optimal_strategy_eggs e t lower :
  eggs (optimal_strategy e t lower) = min e t.
Proof.
  generalize dependent lower.
  generalize dependent e.
  induction t as [|t IH]; simpl; intros e lower; try lia.
  destruct e as [|e]; trivial.
  simpl. repeat rewrite IH.
  destruct t; simpl; lia.
Qed.

Lemma optimal_strategy_tries e t lower :
  tries (optimal_strategy e t lower) = min 1 e * t.
Proof.
  generalize dependent lower.
  generalize dependent e.
  induction t as [|t IH]; simpl; intros [|e] lower; trivial.
  simpl.
  repeat rewrite IH. simpl.
  destruct e; lia.
Qed.

(** To actually show optimality, we need to show that [optimal_range]
indeed computes what it's supposed to. We start by showing two
inversion lemmas. *)

Lemma winning_inv_guess lower n floor :
  winning lower n (Guess floor) -> n <= 1.
Proof.
  intros WIN.
  destruct n as [|[|n]]; try omega.
  assert (play lower (Guess floor) = true) by (apply WIN; omega).
  assert (play (lower + 1) (Guess floor) = true) by (apply WIN; omega).
  simpl in *. rewrite beq_nat_true_iff in *. omega.
Qed.

Lemma winning_inv_drop lower n floor broken intact :
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

Lemma optimal_range_correct :
  forall t e s lower n,
    tries s <= t ->
    eggs s  <= e ->
    winning lower n s ->
    n <= S (optimal_range e t).
Proof.
  induction t as [|t IH]; intros e s lower n Ht He WIN;
  destruct s as [floor|floor broken intact]; try solve [inversion Ht].
  - apply winning_inv_guess in WIN. lia.
  - apply winning_inv_guess in WIN.
    destruct e as [|e]; simpl in *; try lia.
  - apply winning_inv_drop in WIN.
    destruct WIN as (n1 & n2 & lower' & ? & WIN1 & WIN2). subst n.
    assert (He' : exists e', e = S e' /\
                             eggs broken <= e' /\
                             eggs intact <= S e').
    { unfold eggs in He. fold eggs in He.
      destruct e as [|e']; try lia.
      exists e'. repeat split; lia. }
    destruct He' as (e' & ? & Heb & Hei). subst e. clear He.
    assert (Ht' : tries broken <= t /\
                  tries intact <= t).
    { unfold tries in Ht. fold tries in Ht. lia. }
    destruct Ht' as [Htb Hti]. clear Ht.
    simpl.
    cut (n1 <= S (optimal_range e' t) /\
         n2 <= S (optimal_range (S e') t)); try lia.
    split.
    + apply (IH e' broken lower n1); try lia.
      now trivial.
    + apply (IH (S e') intact lower' n2); try lia.
      now trivial.
Qed.

(** Using this lemma, we can derive some useful facts about
[optimal_range]. *)

Lemma optimal_range_monotone :
  forall t t' e e',
    t <= t' ->
    e <= e' ->
    optimal_range e t <= optimal_range e' t'.
Proof.
  intros t t' e e' Ht He.
  cut (S (optimal_range e t) <= S (optimal_range e' t')); try lia.
  apply (optimal_range_correct t' e' (optimal_strategy e t 0) 0);
    [ rewrite optimal_strategy_tries; destruct e; simpl; lia
    | rewrite optimal_strategy_eggs; lia
    | apply optimal_strategy_winning ].
Qed.

Lemma optimal_range_lower_bound :
  forall e t, t <= (optimal_range (S e) t).
Proof.
  intros e t.
  cut (S t <= S (optimal_range (S e) t)); try lia.
  apply (optimal_range_correct t (S e) (linear 0 t) 0);
    [ rewrite linear_tries
    | rewrite linear_eggs
    | apply linear_winning ]; lia.
Qed.

Fixpoint find_root (f : nat -> nat) (goal n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' =>
    if leb goal (f n') then
      find_root f goal n'
    else
      S n'
  end.

Lemma find_root_correct :
  forall f goal n,
    (forall x y, x <= y -> f x <= f y) ->
    goal <= f n ->
    let x := find_root f goal n in
    goal <= f x /\
    forall y, y < x -> f y < goal.
Proof.
  intros f goal n MONO START.
  induction n as [|n IH]; simpl.
  - split; trivial. intros. lia.
  - destruct (leb goal (f n)) eqn:E.
    + rewrite leb_iff in E. now apply IH.
    + apply leb_iff_conv in E.
      split; trivial.
      intros y Hy.
      assert (f y <= f n) by (apply MONO; lia). lia.
Qed.

Definition find_optimum e goal :=
  find_root (fun t => S (optimal_range e t)) goal goal.

Lemma find_optimum_correct :
  forall e goal,
    let t := find_optimum (S e) goal in
    is_optimal goal (optimal_strategy (S e) t 0).
Proof.
  intros e goal t.
  assert (H : goal <= S (optimal_range (S e) t) /\
              forall t', t' < t -> S (optimal_range (S e) t') < goal).
  { subst t.
    apply (find_root_correct (fun t => S (optimal_range (S e) t)) goal goal).
    - intros t t' Ht.
      cut (optimal_range (S e) t <= optimal_range (S e) t'); try lia.
      apply optimal_range_monotone; lia.
    - cut (goal <= optimal_range (S e) goal); try lia.
      apply optimal_range_lower_bound. }
  destruct H as [H1 H2].
  exists 0. split.
  - intros x Hx.
    apply optimal_strategy_winning. lia.
  - intros lower s Hs WIN.
    rewrite optimal_strategy_eggs in Hs.
    rewrite optimal_strategy_tries. simpl. rewrite plus_0_r.
    destruct (le_lt_dec t (tries s)) as [LE | LT]; trivial.
    assert (Ht : tries s <= tries s) by lia.
    assert (He : eggs s <= S e) by lia.
    pose proof (H2 _ LT).
    pose proof (optimal_range_correct _ _ _ _ _ Ht He WIN). lia.
Qed.
