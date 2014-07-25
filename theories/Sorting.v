(* begin hide *)
Require Import NPeano.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Import ListNotations.
Require Import Psatz.

Set Implicit Arguments.
(* end hide *)

Definition no_dup {A} (l : list A) :=
  forall a (i j : nat),
    i < length l ->
    j < length l ->
    nth i l a = nth j l a ->
    i = j.

Lemma no_dup_seq : forall start len, no_dup (seq start len).
Proof.
  intros start len a i j Hi Hj H.
  rewrite seq_length in Hi, Hj.
  rewrite seq_nth in H; trivial.
  rewrite seq_nth in H; trivial.
  omega.
Qed.

Definition shuffle m n p : nat :=
  if leb m p then p - m
  else p + n.

Lemma shuffle_lt m n p :
  p < m + n -> shuffle m n p < m + n.
Proof.
  unfold shuffle.
  destruct (leb m p) eqn:E;
  [rewrite leb_iff in E|rewrite leb_iff_conv in E]; omega.
Qed.

Lemma shuffle_inj n m p1 p2 :
  p1 < m + n -> p2 < m + n ->
  shuffle m n p1 = shuffle m n p2 ->
  p1 = p2.
Proof.
  unfold shuffle.
  destruct (leb m p1) eqn:E1,
           (leb m p2) eqn:E2;
  try rewrite leb_iff in *;
  try rewrite leb_iff_conv in *; try omega.
Qed.

Lemma nth_app {A} (a : A) l1 l2 i :
  i < length l1 + length l2 ->
  nth i (l1 ++ l2) a =
  nth (shuffle (length l1) (length l2) i) (l2 ++ l1) a.
Proof.
  unfold shuffle.
  intros H.
  destruct (leb (length l1) i) eqn:E.
  - rewrite leb_iff in E.
    rewrite app_nth2; try omega.
    rewrite app_nth1; try omega.
    now trivial.
  - rewrite leb_iff_conv in E.
    rewrite app_nth1; trivial.
    rewrite app_nth2; try omega.
    now rewrite plus_comm, minus_plus.
Qed.

Lemma no_dup_app {A} (l1 l2 : list A) :
  no_dup (l1 ++ l2) ->
  no_dup (l2 ++ l1).
Proof.
  intros H a i j Hi Hj E.
  rewrite app_length in Hi, Hj.
  apply (shuffle_inj (length l1) (length l2)); trivial.
  apply (H a); try (rewrite app_length, plus_comm; apply shuffle_lt; omega).
  rewrite <- nth_app; try omega.
  now rewrite <- nth_app; try omega.
Qed.

Lemma map_ext_in {A B} (f g : A -> B) (l : list A) :
  (forall a, In a l -> f a = g a) ->
  map f l = map g l.
Proof.
  induction l as [|a l IH]; intros Hfg; simpl; trivial.
  f_equal.
  - apply Hfg. simpl. auto.
  - apply IH. intros a' Ha'. apply Hfg. simpl. eauto.
Qed.

Definition concat {A} (l : list (list A)) : list A :=
  fold_right (fun x y => x ++ y) [] l.

Definition sum (l : list nat) : nat :=
  fold_right plus 0 l.

Lemma sum_const {A} (n : nat) (l : list A) :
  sum (map (fun _ => n) l) = length l * n.
Proof.
  induction l as [|a l IH]; simpl; trivial.
  rewrite IH.
  omega.
Qed.

Lemma concat_length :
  forall A (l : list (list A)),
    length (concat l) = sum (map (fun x => length x) l).
Proof.
  intros A l.
  induction l as [|a l IH]; simpl; trivial.
  now rewrite app_length, IH.
Qed.

Lemma concat_in :
  forall A (a : A) (l : list (list A)),
    In a (concat l) ->
    exists l', In l' l /\ In a l'.
Proof.
  intros A a l.
  induction l as [|l' l IH]; simpl; try solve [intuition].
  intros IN.
  apply in_app_or in IN.
  destruct IN as [IN | IN]; eauto.
  apply IH in IN.
  destruct IN as (l'' & H1 & H2).
  now eauto.
Qed.

Section Permutations.

Variable A : Type.

Fixpoint insert_all (a : A) (pre post : list A) : list (list A) :=
  match post with
  | [] => [pre ++ [a]]
  | a' :: post' => (pre ++ a :: post) :: insert_all a (pre ++ [a']) post'
  end.

Lemma insert_all_length :
  forall a pre post,
    length (insert_all a pre post) = S (length post).
Proof.
  intros a pre post.
  generalize dependent pre.
  induction post as [|a' post IH]; intros pre; simpl; trivial.
  now rewrite IH.
Qed.

Lemma insert_all_in :
  forall l a pre post,
    In l (insert_all a pre post) ->
    Permutation l (a :: pre ++ post).
Proof.
  intros l a pre post IN.
  generalize dependent pre.
  induction post as [|a' post IH]; simpl; intros pre IN.
  - destruct IN as [? | []].
    subst l. rewrite app_nil_r.
    symmetry.
    apply Permutation_cons_app. rewrite app_nil_r.
    reflexivity.
  - destruct IN as [IN | IN].
    + subst l. symmetry. apply Permutation_middle.
    + apply IH in IN.
      rewrite <- app_assoc in IN.
      assumption.
Qed.

Lemma insert_all_in' :
  forall l a pre post,
    In l (insert_all a pre post) ->
    exists post1 post2,
      post = post1 ++ post2 /\
      l = pre ++ post1 ++ a :: post2.
Proof.
  intros l a pre post.
  generalize dependent pre.
  induction post as [|a' post IH]; intros pre Hin.
  - destruct Hin as [Hin | []].
    subst l. eexists [], []. auto.
  - destruct Hin as [Hin | Hin].
    + subst l. eexists [], (a' :: post). eauto.
    + destruct (IH _ Hin) as (post1 & post2 & H1 & H2).
      subst post l.
      exists (a' :: post1), post2.
      now rewrite <- app_assoc.
Qed.

Fixpoint permutations (l : list A) : list (list A) :=
  match l with
  | [] => [[]]
  | a :: l' =>
    concat (map (insert_all a []) (permutations l'))
  end.

Lemma permutations_in :
  forall l l',
    In l' (permutations l) ->
    Permutation l' l.
Proof.
  induction l as [|a l IH]; simpl; intros l' IN.
  - destruct IN as [? | []]. subst l'. reflexivity.
  - apply concat_in in IN.
    destruct IN as (p & INp & INl').
    apply in_map_iff in INp.
    destruct INp as (p' & ? & INp). subst p.
    assert (PERM := IH _ INp).
    assert (PERM' := insert_all_in _ _ _ _ INl').
    now rewrite PERM', <- PERM.
Qed.

Lemma permutations_length :
  forall l, length (permutations l) = fact (length l).
Proof.
  induction l as [|a l IH]; simpl; trivial.
  rewrite concat_length, map_map.
  rewrite (map_ext_in (fun x => length (insert_all a [] x))
                      (fun _ => S (length l))).
  - rewrite sum_const, IH, mult_comm. reflexivity.
  - intros l' Hl'.
    rewrite insert_all_length.
    apply permutations_in in Hl'.
    apply Permutation_length in Hl'.
    now rewrite Hl'.
Qed.

Lemma no_dup_insert_all :
  forall a pre post,
    no_dup (a :: pre ++ post) ->
    no_dup (insert_all a pre post) /\
    forall l, In l (insert_all a pre post) ->
              no_dup l.
Proof.
  intros a pre post.
  generalize dependent pre.
  induction post as [|a' post IH]; simpl; intros pre H; simpl.
  - split.
    + clear H. intros ? i j Hi Hj Hin.
      simpl in Hi, Hj. omega.
    + intros l [? | []]. subst l.
      replace (a :: pre ++ []) with ([a] ++ pre) in H
        by now rewrite app_nil_r.
      now apply no_dup_app.
  - split.
    + intros l' [|i] [|j] Hi Hj H'; trivial; simpl in *.
      * apply lt_S_n in Hj.
        assert (Hin := nth_In _ l' Hj).
        rewrite <- H' in Hin.
        apply insert_all_in' in Hin.
        destruct Hin as (post1 & post2 & ? & Hin). subst.


assert (Hj' : j < length (insert_all a (pre ++ [a']) post)) by omega.

Lemma NoDup_permutations l :
  NoDup l ->
  NoDup


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
    assert (LB4 := Nat.log2_mul_below _ _ LB3 (lt_O_fact n)).
    rewrite mult_succ_l.
    change (fact (S n)) with (S n * fact n).
    destruct (Nat.log2_succ_or n) as [H | H].
    + assert (Bn  := log2_spec _ LB2).
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

(*
Inductive sorting_algorithm : Type :=
| Compare (n m : nat) (l r : sorting_algorithm)
| Done (res : list nat).



Fixpoint comparisons (s : sorting_algorithm) : nat :=
  match s with
  | Compare _ _ l r => max (comparisons l) (comparisons r)
  | Done => 0
  end.

Fixpoint sort
*)
