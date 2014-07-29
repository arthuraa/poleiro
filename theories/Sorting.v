(* begin hide *)
Require Import NPeano.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Import ListNotations.
Require Import Psatz.

Set Implicit Arguments.
(* end hide *)

Fixpoint take {A} (n : nat) (l : list A) : list A :=
  match n, l with
  | 0, _ => []
  | _, [] => l
  | S n', a :: l' => a :: take n' l'
  end.

Fixpoint drop {A} (n : nat) (l : list A) : list A :=
  match n, l with
  | 0, _ => l
  | _, [] => []
  | S n', _ :: l' => drop n' l'
  end.

Lemma take_drop :
  forall A n l,
    take n l ++ drop n l = l :> list A.
Proof.
  intros A.
  induction n as [|n IH]; intros [|a l]; simpl; trivial.
  - now rewrite IH.
Qed.

Lemma take_nil :
  forall A n, take n [] = [] :> list A.
Proof. now intros A [|?]. Qed.

Lemma take_take :
  forall A n m l,
    take n (take m l) = take (min n m) l :> list A.
Proof.
  intros A.
  induction n as [|n IH]; intros [|m] [|a l]; simpl; trivial.
  now rewrite IH.
Qed.

Lemma length_take :
  forall A n (l : list A),
    length (take n l) = min n (length l).
Proof.
  intros A.
  induction n as [|n IH]; intros [|a l]; simpl; trivial.
  now rewrite IH.
Qed.

Lemma take_app :
  forall A n (l1 l2 : list A),
    take n (l1 ++ l2) =
    take n l1 ++ take (n - length l1) l2.
Proof.
  intros A.
  induction n as [|n IH]; intros [|a1 l1] [|a2 l2]; simpl; trivial.
  - now rewrite take_nil, app_nil_r, app_nil_r.
  - now rewrite IH.
Qed.

Lemma drop_app :
  forall A n (l1 l2 : list A),
    drop n (l1 ++ l2) =
    drop n l1 ++ drop (n - length l1) l2.
Proof.
  intros A.
  induction n as [|n IH]; intros [|a1 l1] [|a2 l2]; simpl; trivial.
Qed.

Lemma drop_all :
  forall A n (l : list A),
    length l <= n ->
    drop n l = [].
Proof.
  intros A.
  induction n as [|n IH]; intros [|a l]; simpl; trivial; try omega.
  intros H.
  apply IH; omega.
Qed.

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

Definition insert_at {A} (l : list A) (n : nat) (a : A) :=
  take n l ++ a :: drop n l.

(*
Fixpoint permutations (l : list A) : list (list A) :=
  match l with
  | [] => [[]]
  | a :: l' =>
    concat (map (fun p => map (fun n => insert_at p n a)
                              (seq 0 (length l')))
                (permutations l'))
  end.
*)

Fixpoint decode_permutation (n s : nat) : list nat :=
  match s with
  | 0 => []
  | S s' => insert_at (decode_permutation (n mod fact s') s') (n / fact s') s'
  end.

Lemma permutation_length n s : length (decode_permutation n s) = s.
Proof.
  generalize dependent n.
  induction s as [|s IH]; intros n; simpl; trivial.
  unfold insert_at.
  rewrite <- (IH (n mod fact s)) at 8.
  rewrite <- (take_drop (n / fact s) (decode_permutation _ _)) at 3.
  repeat rewrite app_length. simpl. omega.
Qed.

Lemma permutation_range (n s i : nat) :
  n < fact s ->
  s <= i ->
  existsb (beq_nat i) (decode_permutation n s) = false.
Proof.
  generalize dependent n.
  induction s as [|s IH]; simpl; intros n Hn Hi.
  - assert (n = 0) by omega. now subst n.
  - assert (existsb (beq_nat i) (decode_permutation (n mod fact s) s) = false).
    { apply IH; try omega.
      apply Nat.mod_upper_bound. apply fact_neq_0. }
    unfold insert_at.
    rewrite existsb_app. simpl.
    rewrite <- (take_drop (n / fact s) (decode_permutation (n mod fact s) s)) in H.
    rewrite existsb_app in H.
    rewrite Bool.orb_false_iff in H.
    destruct H as [H1 H2].
    rewrite H1, H2, Bool.orb_false_r. simpl.
    rewrite beq_nat_false_iff. omega.
Qed.

Fixpoint find {A} (p : A -> bool) (l : list A) : nat :=
  match l with
  | [] => 0
  | a :: l' => if p a then 0 else S (find p l')
  end.

Lemma find_app {A} (p : A -> bool) (l1 l2 : list A) :
  find p (l1 ++ l2) =
  if existsb p l1 then find p l1
  else length l1 + find p l2.
Proof.
  induction l1 as [|a l1 IH]; simpl; trivial.
  destruct (p a); simpl; trivial.
  rewrite IH.
  now destruct (existsb p l1).
Qed.

Fixpoint encode_permutation (p : list nat) (len : nat) : nat :=
  match len with
  | 0 => 0
  | S len' =>
    let pos := find (beq_nat len') p in
    pos * fact len' +
    encode_permutation (take pos p ++ drop (pos + 1) p) len'
  end.

Lemma encode_decode n s :
  n < fact s ->
  encode_permutation (decode_permutation n s) s = n.
Proof.
  generalize dependent n.
  induction s as [|s IH]; simpl; intros n Hn; try omega.
  assert (H : existsb (beq_nat s) (decode_permutation (n mod fact s) s) = false).
  { apply permutation_range; try omega.
    apply Nat.mod_upper_bound.
    apply fact_neq_0. }
  rewrite <- (take_drop (n / fact s) _), existsb_app, Bool.orb_false_iff in H.
  destruct H as [H _].
  unfold insert_at.
  rewrite find_app, H, length_take, permutation_length.
  simpl. rewrite <- beq_nat_refl, plus_0_r.
  assert (Hn' : n / fact s <= s).
  { replace (fact s + s * fact s) with (fact s * S s) in Hn by ring.
    apply Nat.div_lt_upper_bound in Hn; try apply fact_neq_0.
    omega. }
  rewrite Min.min_l; try omega.
  rewrite take_app, take_take, Min.min_idempotent, length_take, permutation_length,
          Min.min_l, minus_diag, app_nil_r; try omega.
  rewrite drop_app, length_take, permutation_length, Min.min_l, minus_plus; try omega.
  simpl.
  rewrite drop_all, take_drop, IH; try rewrite length_take, permutation_length, Min.min_l; trivial; try omega; simpl.
  - rewrite mult_comm, <- div_mod; trivial.
    apply fact_neq_0.
  - apply Nat.mod_upper_bound.
    apply fact_neq_0.
Qed.

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
