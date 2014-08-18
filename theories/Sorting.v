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

Lemma firstn_nil :
  forall A n, firstn n [] = [] :> list A.
Proof. now intros A [|?]. Qed.

Lemma firstn_firstn :
  forall A n m l,
    firstn n (firstn m l) = firstn (min n m) l :> list A.
Proof.
  intros A.
  induction n as [|n IH]; intros [|m] [|a l]; simpl; trivial.
  now rewrite IH.
Qed.

Lemma length_firstn :
  forall A n (l : list A),
    length (firstn n l) = min n (length l).
Proof.
  intros A.
  induction n as [|n IH]; intros [|a l]; simpl; trivial.
  now rewrite IH.
Qed.

Lemma firstn_app :
  forall A n (l1 l2 : list A),
    firstn n (l1 ++ l2) =
    firstn n l1 ++ firstn (n - length l1) l2.
Proof.
  intros A.
  induction n as [|n IH]; intros [|a1 l1] [|a2 l2]; simpl; trivial.
  - now rewrite firstn_nil, app_nil_r, app_nil_r.
  - now rewrite IH.
Qed.

Lemma skipn_app :
  forall A n (l1 l2 : list A),
    skipn n (l1 ++ l2) =
    skipn n l1 ++ skipn (n - length l1) l2.
Proof.
  intros A.
  induction n as [|n IH]; intros [|a1 l1] [|a2 l2]; simpl; trivial.
Qed.

Lemma skipn_all :
  forall A n (l : list A),
    length l <= n ->
    skipn n l = [].
Proof.
  intros A.
  induction n as [|n IH]; intros [|a l]; simpl; trivial; try omega.
  intros H.
  apply IH; omega.
Qed.

Definition insert_at {A} (l : list A) (n : nat) (a : A) :=
  firstn n l ++ a :: skipn n l.

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
  rewrite <- (firstn_skipn (n / fact s) (decode_permutation _ _)) at 3.
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
    rewrite <- (firstn_skipn (n / fact s) (decode_permutation (n mod fact s) s)) in H.
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
    encode_permutation (firstn pos p ++ skipn (pos + 1) p) len'
  end.

Lemma existsb_firstn_false A (f : A -> bool) (l : list A) (n : nat) :
  existsb f l = false ->
  existsb f (firstn n l) = false.
Proof.
  generalize dependent l.
  induction n as [|n IH]; intros [|a l]; trivial.
  simpl.
  destruct (f a); try discriminate.
  simpl. eauto.
Qed.

Hint Resolve Nat.mod_upper_bound.
Hint Resolve fact_neq_0.

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
  rewrite <- (firstn_skipn (n / fact s) _), existsb_app, Bool.orb_false_iff in H.
  destruct H as [H _].
  unfold insert_at.
  rewrite find_app, H, length_firstn, permutation_length.
  simpl. rewrite <- beq_nat_refl, plus_0_r.
  assert (Hn' : n / fact s <= s).
  { replace (fact s + s * fact s) with (fact s * S s) in Hn by ring.
    apply Nat.div_lt_upper_bound in Hn; try apply fact_neq_0.
    omega. }
  rewrite Min.min_l; try omega.
  rewrite firstn_app, firstn_firstn, Min.min_idempotent, length_firstn, permutation_length,
          Min.min_l, minus_diag, app_nil_r; try omega.
  rewrite skipn_app, length_firstn, permutation_length, Min.min_l, minus_plus; try omega.
  simpl.
  rewrite skipn_all, firstn_skipn, IH;
  try rewrite length_firstn, permutation_length, Min.min_l; trivial; try omega; simpl; eauto.
  rewrite mult_comm, <- div_mod; trivial.
Qed.

Definition apply_permutation (p l : list nat) : list nat :=
  map (fun n => nth n l 0) p.

Definition inv_p (p : list nat) : list nat :=
  map (fun i => find (beq_nat i) p) (seq 0 (length p)).

Lemma list_eq_ext :
  forall A l1 l2,
    length l1 = length l2 ->
    (forall x def, x < length l1 -> nth x l1 def = nth x l2 def) ->
    l1 = l2 :> list A.
Proof.
  intros A.
  induction l1 as [|a1 l1 IH]; intros [|a2 l2]; simpl; try congruence.
  intros Hlen Hnth.
  rewrite (Hnth 0 a1); try omega. f_equal.
  apply IH.
  - congruence.
  - intros x def Hx. apply (Hnth (S x)). omega.
Qed.

Lemma map_nth' :
  forall A B d d' (f : A -> B) l x,
    x < length l ->
    nth x (map f l) d =
    f (nth x l d').
Proof.
  intros A B d d' f.
  induction l as [|a l IH]; simpl; intros [|x] Hx; try omega; trivial.
  apply IH. omega.
Qed.

Lemma find_permutation :
  forall s n x,
    x < s ->
    find (beq_nat x) (decode_permutation n s) < s.
Proof.
  induction s as [|s IH]; intros n x Hx; try omega.
  simpl.
  unfold insert_at.
  assert (H : x = s \/ x < s) by omega. clear Hx.
  destruct H as [Hx | Hx].
  - subst x.
    rewrite find_app, existsb_firstn_false, length_firstn, permutation_length;
    try solve [apply permutation_range; eauto].
    simpl. rewrite <- beq_nat_refl, plus_0_r. lia.
  - rewrite find_app. simpl.
    specialize (IH (n mod fact s) x Hx).
    rewrite <- (firstn_skipn (n / fact s) (decode_permutation (n mod fact s) s)), find_app in IH.
    destruct (existsb (beq_nat x) (firstn (n / fact s) (decode_permutation (n mod fact s) s))); try omega.
    assert (E : beq_nat x s = false).
    { rewrite beq_nat_false_iff. omega. }
    rewrite E. clear E. omega.
Qed.

Lemma nth_find :
  forall A (f : A -> bool) l def,
    find f l < length l ->
    f (nth (find f l) l def) = true.
Proof.
  intros A f l def H.
  induction l as [|a l IH]; simpl in *.
  - omega.
  - destruct (f a) eqn:E; trivial.
    apply IH.
    omega.
Qed.

Lemma inv_p_correct :
  forall s n,
    n < fact s ->
    apply_permutation (inv_p (decode_permutation n s))
                      (decode_permutation n s) = seq 0 s.
Proof.
  intros s n H.
  apply list_eq_ext.
  - unfold apply_permutation, inv_p.
    repeat rewrite map_length.
    now rewrite permutation_length.
  - intros x def Hx.
    unfold apply_permutation, inv_p in *.
    repeat rewrite map_length in Hx.
    rewrite seq_length in Hx.
    rewrite permutation_length in *.
    repeat rewrite (map_nth' def def).
    + rewrite seq_nth; trivial. simpl.
      symmetry. apply beq_nat_true.
      apply nth_find.
      rewrite permutation_length.
      now apply find_permutation.
    + now rewrite seq_length.
    + now rewrite map_length, seq_length.
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

Inductive sorting_algorithm (s : nat) : Type :=
| Compare (n m : nat) (l r : sorting_algorithm s)
| Done (p : nat) (H : p < fact s).

Fixpoint comparisons s (alg : sorting_algorithm s) : nat :=
  match alg with
  | Compare _ _ l r => S (max (comparisons l) (comparisons r))
  | Done _ _ => 0
  end.

Fixpoint execute s (alg : sorting_algorithm s) (xs : list nat) : list nat :=
  match alg with
  | Done res _ => decode_permutation res s
  | Compare n m l r => if leb (nth n xs 0) (nth m xs 0) then
                         execute r xs
                       else
                         execute l xs
  end.

Definition algorithm_correct s (alg : sorting_algorithm s) (p : nat) : bool :=
  if list_eq_dec Nat.eq_dec
                 (execute alg (decode_permutation p s))
                 (decode_permutation p s)
  then true
  else false.

Lemma algorithm_correct_compare s n m (l r : sorting_algorithm s) p :
  algorithm_correct (Compare n m l r) p = true ->
  algorithm_correct l p || algorithm_correct r p = true.
Proof.
  unfold algorithm_correct. simpl.
  destruct (leb (nth n (decode_permutation p s) 0) (nth m (decode_permutation p s) 0)).
  - destruct (list_eq_dec Nat.eq_dec
                          (execute r (decode_permutation p s))
                          (decode_permutation p s));
    try discriminate.
    now rewrite Bool.orb_true_r.
  - destruct (list_eq_dec Nat.eq_dec
                          (execute l (decode_permutation p s))
                          (decode_permutation p s));
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
  (forall a, In a l -> f a = true -> g a = true) ->
  count f l <= count g l.
Proof.
  unfold count.
  intros H.
  induction l as [|a l IH]; simpl; trivial.
  specialize (IH (fun a' H1 H2 => H a' (or_intror H1) H2)).
  destruct (f a) eqn:E.
  - rewrite (H a (or_introl eq_refl) E); simpl; auto.
    omega.
  - destruct (g a); simpl; omega.
Qed.

Lemma count_ext A (f g : A -> bool) (l : list A) :
  (forall a, In a l -> f a = g a) ->
  count f l = count g l.
Proof.
  intros H.
  cut (count f l <= count g l <= count f l); try solve [intuition lia].
  split; apply count_impl; intros a H'; specialize (H a H'); congruence.
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

Lemma nth_in :
  forall A def a (l : list A),
    In a l ->
    exists i, i < length l /\
              nth i l def = a.
Proof.
  intros A def a l H.
  induction l as [|a' l IH].
  - destruct H.
  - destruct H as [H | H].
    + subst a'.
      exists 0.
      simpl. split; trivial.
      omega.
    + specialize (IH H).
      destruct IH as (i & H1 & H2).
      exists (S i). simpl. split; trivial.
      omega.
Qed.

Lemma comp_lb_1 s (alg : sorting_algorithm s) :
  count (algorithm_correct alg) (seq 0 (fact s)) <=
  2 ^ (comparisons alg).
Proof.
  induction alg as [n m l IHl r IHr|p H].
  - simpl.
    rewrite (count_impl _ _ _
                        (fun p _ => algorithm_correct_compare n m l r p)),
            count_or.
    rewrite (Nat.pow_le_mono_r _ _ (max (comparisons l) (comparisons r))) in IHl; try lia.
    rewrite (Nat.pow_le_mono_r _ _ (max (comparisons l) (comparisons r))) in IHr; try lia.
  - unfold algorithm_correct. simpl.
    rewrite (@count_ext _ _ (beq_nat p)).
    + apply count_eq_seq.
    + intros p' Hp'.
      destruct (beq_nat p p') eqn:E1,
               (list_eq_dec Nat.eq_dec
                            (decode_permutation p s)
                            (decode_permutation p' s)) as [E2 | NE]; trivial.
      * rewrite beq_nat_true_iff in E1. subst p'.
        congruence.
      * rewrite beq_nat_false_iff in E1. contradict E1.
        rewrite <- (@encode_decode p s H).
        rewrite <- (@encode_decode p' s); try congruence.
        apply (nth_in 0) in Hp'.
        destruct Hp' as (i & H1 & H2).
        rewrite seq_length in H1.
        rewrite <- H2, seq_nth; trivial.
Qed.

Lemma count_true A (l : list A) : count (fun _ => true) l = length l.
Proof.
  induction l as [|? l IH]; trivial.
  unfold count in *. simpl.
  now rewrite IH.
Qed.

Lemma comp_lb_2 s (alg : sorting_algorithm s) :
  forallb (algorithm_correct alg) (seq 0 (fact s)) = true ->
  s * log2 s / 2 <= comparisons alg.
Proof.
  intros H.
  rewrite log2_fact.
  rewrite <- (Nat.log2_pow2 (log2 (fact s))); try omega.
  rewrite <- (Nat.log2_pow2 (comparisons alg)); try omega.
  apply Nat.log2_le_mono.
  rewrite <- comp_lb_1.
  rewrite (@count_ext _ _ (fun _ => true)).
  - rewrite count_true, seq_length.
    pose proof (log2_spec (fact s) (lt_O_fact s)).
    omega.
  - now rewrite forallb_forall in H.
Qed.
