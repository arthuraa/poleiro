(* begin hide *)
Require Import NPeano.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Import ListNotations.
Require Import Psatz.

Set Implicit Arguments.
Open Scope bool_scope.
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

Lemma map_ext_in {A B} (f g : A -> B) (l : list A) :
  (forall a, In a l -> f a = g a) ->
  map f l = map g l.
Proof.
  induction l as [|a l IH]; intros Hfg; simpl; trivial.
  f_equal.
  - apply Hfg. simpl. auto.
  - apply IH. intros a' Ha'. apply Hfg. simpl. eauto.
Qed.

Definition insert_at {A} (l : list A) (n : nat) (a : A) :=
  take n l ++ a :: drop n l.

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

Definition apply_permutation (p : list nat) : list nat -> list nat :=
  map (fun n => nth n p 0).

Fixpoint insert (n : nat) (l : list nat) : list nat :=
  match l with
  | [] => [n]
  | n' :: l' => if leb n n' then n :: n' :: l'
                else n' :: insert n l'
  end.

Fixpoint sort (l : list nat) : list nat :=
  match l with
  | [] => []
  | n :: l' => insert n (sort l')
  end.

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

Inductive sorting_algorithm : Type :=
| Compare (n m : nat) (l r : sorting_algorithm)
| Done (p : list nat).

Fixpoint comparisons (s : sorting_algorithm) : nat :=
  match s with
  | Compare _ _ l r => S (max (comparisons l) (comparisons r))
  | Done _ => 0
  end.

Fixpoint execute (alg : sorting_algorithm) (xs : list nat) : list nat :=
  match alg with
  | Done res => res
  | Compare n m l r => if leb (nth n xs 0) (nth m xs 0) then
                         execute r xs
                       else
                         execute l xs
  end.

Definition algorithm_correct (alg : sorting_algorithm) (xs : list nat) : bool :=
  if list_eq_dec Nat.eq_dec
                 (apply_permutation (execute alg xs) xs)
                 (sort xs) then true
  else false.

Lemma algorithm_correct_compare n m l r xs :
  algorithm_correct (Compare n m l r) xs = true ->
  algorithm_correct l xs || algorithm_correct r xs = true.
Proof.
  unfold algorithm_correct. simpl.
  destruct (leb (nth n xs 0) (nth m xs 0)).
  - destruct (list_eq_dec Nat.eq_dec (apply_permutation (execute r xs) xs) (sort xs));
    try discriminate.
    now rewrite Bool.orb_true_r.
  - destruct (list_eq_dec Nat.eq_dec (apply_permutation (execute l xs) xs) (sort xs));
    try discriminate.
    reflexivity.
Qed.

Definition count {A} (f : A -> bool) (l : list A) : nat :=
  length (filter f l).

Lemma count_or A (f g : A -> bool) (l : list A) :
  count (fun a => f a || g a) l <= count f l + count g l.
Proof.
  unfold count.
  induction l as [|a l IH]; simpl; trivial.
  destruct (f a), (g a); simpl; omega.
Qed.

Lemma count_impl A (f g : A -> bool) (l : list A) :
  (forall a, f a = true -> g a = true) ->
  count f l <= count g l.
Proof.
  unfold count.
  intros H.
  induction l as [|a l IH]; simpl; trivial.
  destruct (f a) eqn:E.
  - rewrite (H _ E). simpl. omega.
  - destruct (g a); simpl; omega.
Qed.

Lemma count_ext A (f g : A -> bool) (l : list A) :
  (forall a, f a = g a) ->
  count f l = count g l.
Proof.
  intros H.
  cut (count f l <= count g l <= count f l); try solve [intuition lia].
  split; apply count_impl; intros a; specialize (H a); congruence.
Qed.

Lemma count_eq_seq : forall s l n, count (beq_nat n) (seq s l) <= 1.
Proof.
  intros s l n.
  cut (count (beq_nat n) (seq s l) =
       if leb s n && negb (leb (s + l) n) then 1 else 0);
  try solve [destruct (leb s n && negb (leb (s + l) n)); omega].
  generalize dependent s.
  induction l as [|l IH]; intros s; simpl.
  - rewrite plus_0_r.
    now destruct (leb s n).
  - unfold count in *. simpl.
    destruct (beq_nat n s) eqn:E; simpl.
    + rewrite IH.
      rewrite beq_nat_true_iff in E. subst n.
      rewrite (leb_correct_conv s (S s)); try omega. simpl.
      rewrite (leb_correct s s); try omega. simpl.
      now rewrite (leb_correct_conv s (s + S l)); try omega.
    + rewrite IH.
      rewrite beq_nat_false_iff in E.
      rewrite <- plus_n_Sm.
      cut (leb (S s) n = leb s n).
      { intros E'. now rewrite E'. }
      destruct (leb s n) eqn:LE.
      * rewrite leb_iff in *. omega.
      * rewrite leb_iff_conv in *. omega.
Qed.
