(* begin hide *)
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Omega.
Require Import Psatz.
Import ListNotations.
(* end hide *)
(** Consider the following problem. Suppose we are in a 100-story
building. We know that, when dropping an egg from the window, the egg
will stay intact if we are below a certain floor. However, if we
repeat the same exercise above that critical floor, the egg will
break. How can we find this floor and minimize the number of egg drops
performed in the worst case if we have only two eggs? We suppose that
we are allowed to reuse eggs that fall without breaking.

We will see how we can model this problem in Coq and find a correct
solution. We model a playing strategy as a decision tree: *)

Inductive strategy : Type :=
| Guess (floor : nat)
| Drop  (floor : nat) (broken intact : strategy).

(** In the above definition, [Guess floor] represents the end of the
algorithm, when we try to guess the target floor. If [floor] is equal
to the target, we win the game; otherwise, we lose. [Drop floor broken
intact] represents an egg drop at [floor]. If the egg breaks, we
continue playing with strategy [broken]; otherwise, we continue with
[intact].

Simulating an egg-drop game is just a matter of performing a tree
search. [play target s] returns [true] if and only if strategy [s]
succeeds in guessing floor [target]. *)

Fixpoint play (target : nat) (s : strategy) : bool :=
  match s with
  | Guess floor =>
    beq_nat floor target
  | Drop floor broken intact =>
    play target (if leb target floor then broken
                 else intact)
  end.

(** We can also find how many eggs a strategy needs and how many drops
are performed in the worst case. [drops] just computes the strategy
tree height, whereas [eggs] computes a "skewed" height, where right
branches do not add to the final value. *)

Fixpoint eggs (s : strategy) : nat :=
  match s with
  | Guess _ => 0
  | Drop _ broken intact => max (S (eggs broken)) (eggs intact)
  end.

Fixpoint drops (s : strategy) : nat :=
  match s with
  | Guess _ => 0
  | Drop _ broken intact => S (max (drops broken) (drops intact))
  end.

(** Finally, using these concepts, we can describe what the solution
for our problem is. [winning lower range s] says that strategy [s] is
able to find [range] target floors starting at [lower], while
[is_optimal range e d] states that there is a winning strategy for
guessing [range] target floors, uses at most [e] eggs and performing
at most [d] drops, such that [d] is the smallest possible number. *)

Definition winning (lower range : nat) (s : strategy) : Prop :=
  forall target, lower <= target < lower + range ->
                 play target s = true.

Definition is_optimal (range e d : nat) : Prop :=
  exists s : strategy,
    eggs s <= e /\
    drops s = d /\
    winning 0 range s /\
    forall s', eggs s' <= e ->
               winning 0 range s' ->
               d <= drops s'.

(** A simple strategy is to perform linear search, starting at the
bottom and going up one floor at a time. As soon as the egg breaks, we
know we've found our target. *)

Fixpoint linear (lower range : nat) : strategy :=
  match range with
  | 0 => Guess lower
  | S range' => Drop lower (Guess lower) (linear (S lower) range')
  end.

(** [linear lower n] works for a range of up to [n] floors, and uses
at most one egg. Unfortunately, it is not very efficient, performing
[n] drops in the worst case. *)

Lemma linear_winning lower range :
  winning lower (S range) (linear lower range).
(* begin hide *)
Proof.
  generalize dependent lower.
  induction range as [|range IH]; intros lower target WIN; simpl.
  - assert (lower = target) by omega. subst lower.
    now rewrite <- beq_nat_refl.
  - destruct (leb target lower) eqn:E.
    + apply leb_iff in E.
      assert (lower = target) by omega.
      subst lower. simpl.
      now rewrite <- beq_nat_refl.
    + apply IH.
      apply leb_iff_conv in E.
      omega.
Qed.
(* end hide *)

Lemma linear_eggs lower range :
  eggs (linear lower range) = min 1 range.
(* begin hide *)
Proof.
  generalize dependent lower.
  induction range as [|[|range] IH]; intros lower; trivial.
  replace (eggs (linear lower (S (S range)))) with (eggs (linear (S lower) (S range))); eauto.
  simpl.
  now destruct (eggs (linear (S (S lower)) range)).
Qed.
(* end hide *)

Lemma linear_drops lower range :
  drops (linear lower range) = range.
(* begin hide *)
Proof.
  generalize dependent lower.
  induction range as [|range IH]; intros lower; trivial.
  simpl.
  now rewrite IH.
Qed.
(* end hide *)

(** ** Improving our strategy

Now that we know a naive search strategy, we will try to find an
optimal one. Intuitively, it seems that it should be possible to
perform some form of binary search, starting at the middle of our
floor range, and continuing recursively depending on the outcome of
our drop. *)

Definition solution_take_1 : strategy :=
  Drop 49 (linear 0 49) (linear 50 49).

Lemma solution_take_1_winning :
  winning 0 100 solution_take_1.
(* begin hide *)
Proof.
  intros target Ht.
  unfold solution_take_1, play. fold play.
  destruct (leb target 49) eqn:E.
  - rewrite leb_iff in E.
    apply linear_winning.
    lia.
  - rewrite leb_iff_conv in E.
    apply linear_winning.
    lia.
Qed.
(* end hide *)

Lemma solution_take_1_eggs :
  eggs solution_take_1 = 2.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Lemma solution_take_1_drops :
  drops solution_take_1 = 50.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

(** Although much better than a pure linear strategy, this is still
far from being optimal: if our egg doesn't break on our first drop, we
will still be using at most only one egg on that upper range. If we
allowed ourselves to break one of them, presumably, we would be able
to solve the upper range in less than 50 drops, which would in turn
allow us to perform our first drop at a lower floor, e.g. *)

Definition solution_take_2 : strategy :=
  Drop 33 (linear 0 33)
          (Drop 66 (linear 34 32) (linear 67 32)).

Lemma solution_take_2_winning :
  winning 0 100 solution_take_2.
(* begin hide *)
Proof.
  intros target Ht.
  unfold solution_take_2, play. fold play.
  destruct (leb target 33) eqn:E.
  - rewrite leb_iff in E.
    apply linear_winning.
    lia.
  - rewrite leb_iff_conv in E.
    unfold play. fold play.
    destruct (leb target 66) eqn:E'.
    + rewrite leb_iff in E'.
      apply linear_winning. lia.
    + rewrite leb_iff_conv in E'.
      apply linear_winning. lia.
Qed.
(* end hide *)

Lemma solution_take_2_eggs :
  eggs solution_take_2 = 2.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Lemma solution_take_2_drops :
  drops solution_take_2 = 34.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

(** Our new solution performs much better, but there is still room for
improvement. Once again, if our first two drops are below the target
floor, we will be using only one egg to search through 33 floors,
which could be done better if we had used both of them. This suggests
that the optimal strategy should be some form of skewed binary search,
where the upper range that is produced by an egg drop should use its
available eggs in an optimal way.

** Finding the optimum

How can we formalize the intuition that we just developed? The key
insight is to reason by _duality_ and, instead, ask "what is the
largest range of floors we can scan using at most some number of eggs
and drops?" When looking at the problem this way, it becomes clear
that optimality has a recursive structure that is easy to describe: to
find a floor using at most [e] eggs and [d] drops, we need to combine
two optimal strategies: one using at most [e-1] eggs and [d-1] drops,
for the case where our first drop causes the egg to break, and another
using at most [e] eggs and [d-1] drops, for the case where our egg
doens't break at first. We can readily express this idea as
code. [optimal_range e d] computes the maximal range size that can be
solved using [e] eggs and [d] drops at most, while [optimal lower e d]
computes a strategy for doing so starting from floor [lower]. *)

Fixpoint optimal_range_minus_1 (e d : nat) {struct d} : nat :=
  match d, e with
  | S d', S e' => S (optimal_range_minus_1 e' d' +
                     optimal_range_minus_1 (S e') d')
  | _, _ => 0
  end.

Definition optimal_range e d := S (optimal_range_minus_1 e d).

Fixpoint optimal (lower e d : nat) {struct d} : strategy :=
  match d, e with
  | S d', S e' =>
    let floor := lower + optimal_range_minus_1 e' d' in
    Drop floor
         (optimal lower e' d')
         (optimal (S floor) (S e') d')
  | _, _ => Guess lower
  end.

(** It is easy to show that [optimal] indeed uses the
resources that we expect. *)

Lemma optimal_winning lower e d :
  winning lower (optimal_range e d) (optimal lower e d).
(* begin hide *)
Proof.
  generalize dependent lower.
  generalize dependent e.
  unfold optimal_range.
  induction d as [|d' IH]; intros e lower target BOUNDS; simpl.
  - destruct e as [|e']; simpl in *; apply beq_nat_true_iff; omega.
  - destruct e as [|e']; simpl in *;
    try (apply beq_nat_true_iff; omega).
    destruct (leb target (lower + optimal_range_minus_1 e' d')) eqn:E.
    + apply IH. apply leb_iff in E. omega.
    + apply IH. apply leb_iff_conv in E. omega.
Qed.
(* end hide *)

Lemma optimal_eggs lower e d :
  eggs (optimal lower e d) = min e d.
(* begin hide *)
Proof.
  generalize dependent lower.
  generalize dependent e.
  induction d as [|d IH]; simpl; intros e lower; try lia.
  destruct e as [|e]; trivial.
  simpl. repeat rewrite IH.
  destruct d; simpl; lia.
Qed.
(* end hide *)

Lemma optimal_drops lower e d :
  drops (optimal lower e d) = min 1 e * d.
(* begin hide *)
Proof.
  generalize dependent lower.
  generalize dependent e.
  induction d as [|d IH]; simpl; intros [|e] lower; trivial.
  simpl.
  repeat rewrite IH. simpl.
  destruct e; lia.
Qed.
(* end hide *)

(** To actually show optimality, we need to show that [optimal_range]
indeed computes what it's supposed to. We start by showing two
inversion lemmas. *)

Lemma winning_inv_guess lower range floor :
  winning lower range (Guess floor) -> range <= 1.
(* begin hide *)
Proof.
  intros WIN.
  destruct range as [|[|range]]; try omega.
  assert (play lower (Guess floor) = true) by (apply WIN; omega).
  assert (play (lower + 1) (Guess floor) = true) by (apply WIN; omega).
  simpl in *. rewrite beq_nat_true_iff in *. omega.
Qed.
(* end hide *)

Lemma winning_inv_drop lower range floor broken intact :
  winning lower range (Drop floor broken intact) ->
  exists r1 r2 lower',
    range = r1 + r2 /\
    winning lower r1 broken /\
    winning lower' r2 intact.
(* begin hide *)
Proof.
  unfold winning. simpl. intros WIN.
  destruct (le_lt_dec (lower + range) floor) as [LE | LT].
  - eexists range, 0, 0.
    split; try omega.
    split; try solve [intros; omega].
    intros target I.
    assert (BOUND : target <= floor) by omega.
    apply WIN in I.
    rewrite <- leb_iff in BOUND. now rewrite BOUND in I.
  - destruct (le_lt_dec lower floor) as [LE' | LT'].
    + eexists (S floor - lower), (lower + range - S floor), (S floor).
      split; try omega.
      split; intros target I;
      assert (I' : lower <= target < lower + range) by omega;
      apply WIN in I'.
      * assert (BOUND : target <= floor) by omega.
        rewrite <- leb_iff in BOUND. now rewrite BOUND in I'.
      * assert (BOUND : floor < target) by omega.
        rewrite <- leb_iff_conv in BOUND. now rewrite BOUND in I'.
    + eexists 0, range, lower.
      split; trivial.
      split; intros target I; try omega.
      assert (BOUND : floor < target) by omega.
      apply WIN in I.
      rewrite <- leb_iff_conv in BOUND. now rewrite BOUND in I.
Qed.
(* end hide *)

Lemma optimal_range_correct :
  forall lower e d s range,
    eggs s  <= e ->
    drops s <= d ->
    winning lower range s ->
    range <= optimal_range e d.
(* begin hide *)
Proof.
  intros lower e d.
  generalize dependent e.
  generalize dependent lower.
  unfold optimal_range.
  induction d as [|d IH]; intros lower e s range He Hd WIN;
  destruct s as [floor|floor broken intact]; try solve [inversion Hd].
  - apply winning_inv_guess in WIN. lia.
  - apply winning_inv_guess in WIN.
    destruct e as [|e]; simpl in *; try lia.
  - apply winning_inv_drop in WIN.
    destruct WIN as (r1 & r2 & lower' & ? & WIN1 & WIN2). subst range.
    assert (He' : exists e', e = S e' /\
                             eggs broken <= e' /\
                             eggs intact <= S e').
    { unfold eggs in He. fold eggs in He.
      destruct e as [|e']; try lia.
      exists e'. repeat split; lia. }
    destruct He' as (e' & ? & Heb & Hei). subst e. clear He.
    assert (Hd' : drops broken <= d /\
                  drops intact <= d).
    { unfold drops in Hd. fold drops in Hd. lia. }
    destruct Hd' as [Hdb Hdi]. clear Hd.
    simpl.
    cut (r1 <= S (optimal_range_minus_1 e' d) /\
         r2 <= S (optimal_range_minus_1 (S e') d)); try lia.
    split.
    + apply (IH lower e' broken r1); try lia.
      now trivial.
    + apply (IH lower' (S e') intact r2); try lia.
      now trivial.
Qed.
(* end hide *)

(** Combining this lemma with the ranges we had derived for [linear]
and [optimal], we can prove useful results about [optimal_range]. *)

Lemma optimal_range_monotone :
  forall e e' d d',
    e <= e' ->
    d <= d' ->
    optimal_range e d <= optimal_range e' d'.
Proof.
  intros e e' d d' He Hd.
  apply (optimal_range_correct 0 e' d' (optimal 0 e d));
    [ rewrite optimal_eggs; lia
    | rewrite optimal_drops; destruct e; simpl; lia
    | apply optimal_winning ].
Qed.

Lemma optimal_range_lower_bound :
  forall e d, d <= (optimal_range (S e) d).
Proof.
  intros e d.
  cut (S d <= optimal_range (S e) d); try lia.
  apply (optimal_range_correct 0 (S e) d (linear 0 d));
    [ rewrite linear_eggs
    | rewrite linear_drops
    | apply linear_winning ]; lia.
Qed.

(** Given that [optimal_range] is monotone, we can find what the
optimal number of drops for a given range is by picking the smallest
value of [t] such that [range <= optimal_range e t]. We formalize this
idea by writing a generic function [find_root] that can find such
values for any monotone function [f], given a suitable initial
guess. *)

Fixpoint find_root (f : nat -> nat) (target n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' =>
    if leb target (f n') then
      find_root f target n'
    else
      S n'
  end.

Lemma find_root_correct :
  forall f target n,
    (forall x y, x <= y -> f x <= f y) ->
    target <= f n ->
    let x := find_root f target n in
    target <= f x /\
    forall y, y < x -> f y < target.
(* begin hide *)
Proof.
  intros f target n MONO START.
  induction n as [|n IH]; simpl.
  - split; trivial. intros. lia.
  - destruct (leb target (f n)) eqn:E.
    + rewrite leb_iff in E. now apply IH.
    + apply leb_iff_conv in E.
      split; trivial.
      intros y Hy.
      assert (f y <= f n) by (apply MONO; lia). lia.
Qed.
(* end hide *)

(** By instantiating this theorem with [optimal_range] and applying
the appropriate theorems, we obtain our final result. The proof of
optimality goes by contradiction. Let [t = find_optimum (S e)
range]. if we find another strategy [s] such that [eggs s <= S e] and
[drops s < t], we know that [range <= optimal_range (S e) t] by
[optimal_range_correct], but we must also have [optimal_range (S e) t
< range] by the correctness of [find_root]. *)

Definition find_optimum e target :=
  find_root (optimal_range e) target target.

Lemma find_optimum_correct :
  forall e range,
    let d := find_optimum (S e) range in
    is_optimal range (S e) d.
Proof.
  intros e range d.
  assert (H : range <= optimal_range (S e) d /\
              forall d', d' < d -> optimal_range (S e) d' < range).
  (* By correctness of find_root *)
  (* begin hide *)
  { subst d.
    apply (find_root_correct (optimal_range (S e)) range range).
    - intros d d' Hd.
      apply optimal_range_monotone; lia.
    - apply optimal_range_lower_bound. }
  (* end hide *)
  destruct H as [H1 H2].
  exists (optimal 0 (S e) d).
  rewrite optimal_drops, optimal_eggs.
  repeat split; try lia; simpl; try lia.
  - intros x Hx.
    apply optimal_winning. lia.
  - intros s Hs WIN.
    destruct (le_lt_dec d (drops s)) as [LE | LT]; trivial.
    assert (Hd : drops s <= drops s) by lia.
    assert (He : eggs s <= S e) by lia.
    (* optimal_range < range *)
    pose proof (H2 _ LT).
    (* range <= optimal_range *)
    pose proof (optimal_range_correct _ _ _ _ _ He Hd WIN).
    lia.
Qed.

(** Using this result, we can find the answer for our original problem. *)

Lemma solution :
  is_optimal 100 2 14.
Proof. apply find_optimum_correct. Qed.
