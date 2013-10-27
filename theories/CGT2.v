Require Import Coq.Lists.List.
Require Import Coq.Init.Wf.
Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Coq.Relations.Relation_Operators.
Require Import CGT.
Definition game_pair_order {cg1 cg2 : combinatorial_game} :=
  symprod _ _ (valid_move cg1) (valid_move cg2).
Definition game_pair_order_wf cg1 cg2 : well_founded game_pair_order :=
  wf_symprod _ _ _ _ (finite_game cg1) (finite_game cg2).

Program Definition sum_cg (cg1 cg2 : combinatorial_game)
                          : combinatorial_game :=
  {| position := (position cg1 * position cg2);
     moves p pos := map (fun pos1' => (pos1', snd pos))
                        (moves cg1 p (fst pos)) ++
                    map (fun pos2' => (fst pos, pos2'))
                        (moves cg2 p (snd pos)) |}.
Next Obligation.
  match goal with
    | |- well_founded ?R =>
      assert (EQ : RelationClasses.relation_equivalence R game_pair_order)
  end.
  { intros [pos1' pos2'] [pos1 pos2]. split.
    - intros [p H].
      apply in_app_or in H.
      repeat rewrite in_map_iff in H.
      destruct H as [(pos1'' & H1 & H2) | (pos2'' & H1 & H2)];
      simpl in *; inversion H1; subst; clear H1;
      constructor (solve [eexists; eauto]).
    - intros H.
      inversion H as [? ? [p H'] ?|? ? [p H'] ?]; subst; clear H;
      exists p; rewrite in_app_iff; repeat rewrite in_map_iff;
      simpl; eauto. }
  rewrite EQ.
  apply game_pair_order_wf.
Qed.

Fail Fixpoint sum (g1 g2 : game) : game :=
  match g1, g2 with
    | Game l1 r1, Game l2 r2 =>
      Game (map (fun g1 => sum g1 g2) l1 ++ map (fun g2 => sum g1 g2) l2)
           (map (fun g1 => sum g1 g2) r1 ++ map (fun g2 => sum g1 g2) r2)
  end.

Definition sum (g1 g2 : game) : game.
  refine (
    Fix (game_pair_order_wf game_as_cg game_as_cg) (fun _ => game)
        (fun gs =>
           match gs with
           | (g1, g2) =>
             fun sum =>
               let sum_fst g1' P := sum (g1', g2) _ in
               let sum_snd g2' P := sum (g1, g2') _ in
               Game (map_game game_as_cg g1 Left sum_fst ++
                     map_game game_as_cg g2 Left sum_snd)
                    (map_game game_as_cg g1 Right sum_fst ++
                     map_game game_as_cg g2 Right sum_snd)
           end) (g1, g2));
  clear - P; constructor; eauto.
Defined.

Lemma sum_eq (g1 g2 : game) :
  sum g1 g2 =
  Game (map (fun g1' => sum g1' g2) (left_moves g1) ++
        map (fun g2' => sum g1 g2') (left_moves g2))
       (map (fun g1' => sum g1' g2) (right_moves g1) ++
        map (fun g2' => sum g1 g2') (right_moves g2)).
Proof.
  unfold sum at 1.
  simpl.
  rewrite Fix_eq.
  - intros.
    do 2 f_equal; apply map_game_map; reflexivity.
  - clear. intros [g1 g2] f g EXT.
    do 2 f_equal; apply map_game_ext; eauto.
Qed.

Lemma map_ext_strong :
  forall {A B}
         (l : list A)
         (f g : A -> B)
         (EXT : forall x, In x l -> f x = g x),
    map f l = map g l.
Proof.
  intros.
  induction l as [|x l IH]; trivial.
  simpl.
  f_equal.
  - apply EXT. simpl. auto.
  - apply IH. intros. apply EXT. simpl. auto.
Qed.

Lemma sum_is_sum (cg1 cg2 : combinatorial_game)
                 (pos1 : position cg1) (pos2 : position cg2) :
  embed_in_game (sum_cg cg1 cg2) (pos1, pos2) =
  sum (embed_in_game cg1 pos1) (embed_in_game cg2 pos2).
Proof.
  remember (pos1, pos2) as pos.
  replace pos1 with (fst pos) by (destruct pos; simpl; congruence).
  replace pos2 with (snd pos) by (destruct pos; simpl; congruence).
  clear.
  induction pos as [[pos1 pos2] IH]
                using (well_founded_ind (game_pair_order_wf _ _)).
  rewrite embed_in_game_eq, sum_eq. simpl.
  repeat rewrite (embed_in_game_moves _ _ Left).
  repeat rewrite (embed_in_game_moves _ _ Right).
  repeat rewrite map_app. repeat rewrite map_map.
  do 2 f_equal;
  apply map_ext_strong; intros pos IN; apply IH; constructor; eexists; eauto.
Qed.
