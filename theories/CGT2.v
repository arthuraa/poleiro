Require Import Coq.Lists.List.
Require Import Coq.Init.Wf.
Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Coq.Relations.Relation_Operators.
Require Import CGT.

Fixpoint negate (g : game) : game :=
  match g with
    | Game l r =>
      Game (map negate r) (map negate l)
  end.

Lemma negate_involutive :
  forall g, negate (negate g) = g.
Proof.
  induction g as [l r IHl IHr] using game_ind'.
  simpl.
  f_equal.
  - clear IHr.
    induction IHl as [|g gs Hg _ IH]; simpl; eauto.
    rewrite Hg, IH.
    reflexivity.
  - clear IHl.
    induction IHr as [|g gs Hg _ IH]; simpl; eauto.
    rewrite Hg, IH.
    reflexivity.
Qed.

Fail Fixpoint sum (g1 g2 : game) : game :=
  match g1, g2 with
    | Game l1 r1, Game l2 r2 =>
      Game (map (fun g1 => sum g1 g2) l1 ++ map (fun g2 => sum g1 g2) l2)
           (map (fun g1 => sum g1 g2) r1 ++ map (fun g2 => sum g1 g2) r2)
  end.

Definition game_pair_order :=
  symprod _ _ (valid_move game_as_cg) (valid_move game_as_cg).
Definition game_pair_order_wf : well_founded game_pair_order :=
  wf_symprod _ _ _ _ (finite_game game_as_cg) (finite_game game_as_cg).

Definition sum_body (gs : game * game) :=
  match gs return (forall gs', game_pair_order gs' gs -> game) -> game with
    | (Game l1 r1, Game l2 r2) =>
      fun F =>
        {| left_moves :=
             map_In l1
                    (fun g1 p => F (g1, Game l2 r2)
                                   (left_sym game game
                                             (valid_move game_as_cg)
                                             (valid_move game_as_cg)
                                             g1 (Game l1 r1) (ex_intro _ Left p)
                                             (Game l2 r2))) ++
             map_In l2
                    (fun g2 p => F (Game l1 r1, g2)
                                   (right_sym game game
                                              (valid_move game_as_cg)
                                              (valid_move game_as_cg)
                                              g2 (Game l2 r2) (ex_intro _ Left p)
                                              (Game l1 r1)));
           right_moves :=
             map_In r1
                    (fun g1 p => F (g1, Game l2 r2)
                                   (left_sym game game
                                             (valid_move game_as_cg)
                                             (valid_move game_as_cg)
                                             g1 (Game l1 r1) (ex_intro _ Right p)
                                             (Game l2 r2))) ++
             map_In r2
                    (fun g2 p => F (Game l1 r1, g2)
                                   (right_sym game game
                                              (valid_move game_as_cg)
                                              (valid_move game_as_cg)
                                              g2 (Game l2 r2) (ex_intro _ Right p)
                                              (Game l1 r1))) |}
  end.

Definition sum (g1 g2 : game) : game :=
  Fix game_pair_order_wf (fun _ => game)
      sum_body (g1, g2).





(* Let's define a more interesting function on games: sum. As we've
seen, Coq rejects the direct definition of sum, because it's not
structurally recursive on a single argument. We use the trick here of
passing an additional parameter to sum. *)

Fixpoint height (g : game) :=
  S (max (fold_left max (map height (left_moves g)) 0)
         (fold_left max (map height (right_moves g)) 0)).

Fixpoint sum_aux (max_height : nat) (g1 g2 : game) :=
  match max_height with
    | 0 =>
      (* We'll never reach 0 normally, so we just return some arbitrary value here *)
      zero
    | S n =>
      match g1, g2 with
        | Game l1 r1, Game l2 r2 =>
          Game (map (fun g1 => sum_aux n g1 g2) l1 ++
                map (fun g2 => sum_aux n g1 g2) l2)
               (map (fun g1 => sum_aux n g1 g2) r1 ++
                map (fun g2 => sum_aux n g1 g2) r2)
      end
  end.

Definition sum (g1 g2 : game) : game :=
  sum_aux (max (height g1) (height g2)) g1 g2.

Lemma sum_aux_

Lemma sum_eq :
  forall g1 g2,
    sum g1 g2 =
    Game (map (fun g1 => sum g1 g2) (left_moves g1) ++
          map (fun g2 => sum g1 g2) (left_moves g2))
         (map (fun g1 => sum g1 g2) (right_moves g1) ++
          map (fun g2 => sum g1 g2) (right_moves g2)).
Proof.
  intros.
  unfold sum.
  generalize dependent


(* Using sum, we can define minus *)

Definition minus (g1 g2 : game) : game :=
  sum g1 (negate g2).

(* Now let's analyze the winning profile of games. We begin by
defining two (mutually recursive) functions that return true if left
can win if it plays first (resp. if it plays second) *)

Fixpoint left_wins_first (g : game) : bool :=
  existsb left_wins_second (left_moves g)
with left_wins_second (g : game) : bool :=
  forallb left_wins_first (right_moves g).

(* Defining if left always wins now is easy. *)

Definition left_wins (g : game) : bool :=
  match g with
    | Game l r =>
      existsb left_wins_second l &&
      forallb left_wins_first r
  end.

(* We can use the previous functions and negate to define similar
functions for the right player. *)

Definition right_wins_first (g : game) : bool :=
  left_wins_first (negate g).
Definition right_wins_second (g : game) : bool :=
  left_wins_second (negate g).
Definition right_wins (g : game) : bool :=
  left_wins (negate g).

(* Finally, two functions that return true iff the first (resp. the
second) player to play always wins *)

Fixpoint first_wins (g : game) : bool :=
  match g with
    | Game l r =>
      existsb left_wins_second l &&
      existsb left_wins_second r
  end.

Definition second_wins (g : game) : bool :=
  match g with
    | Game l r =>
      forallb right_wins_first l &&
      forallb left_wins_first r
  end.

(* We can check that these functions behave as expected on some arguments: *)

Lemma left_wins_test_1 : left_wins zero = false.
Proof. reflexivity. Qed.
Lemma left_wins_test_2 : left_wins one = true.
Proof. reflexivity. Qed.
Lemma left_wins_test_3 : left_wins two = true.
Proof. reflexivity. Qed.

Lemma right_wins_test_1 : right_wins zero = false.
Proof. reflexivity. Qed.
Lemma right_wins_test_2 : right_wins one = false.
Proof. reflexivity. Qed.
Lemma right_wins_test_3 : right_wins minus_one = true.
Proof. reflexivity. Qed.

Lemma first_wins_test_1 : first_wins zero = false.
Proof. reflexivity. Qed.
Lemma first_wins_test_2 : first_wins one = false.
Proof. reflexivity. Qed.
Lemma first_wins_test_3 : first_wins star = true.
Proof. reflexivity. Qed.

Lemma second_wins_test_1 : second_wins zero = true.
Proof. reflexivity. Qed.
Lemma second_wins_test_2 : second_wins one = false.
Proof. reflexivity. Qed.
Lemma second_wins_test_3 : second_wins star = false.
Proof. reflexivity. Qed.

(* Using those, we can finally define comparison functions between games. *)

Definition gt (g1 g2 : game) : bool := left_wins (minus g1 g2).
Definition lt (g1 g2 : game) : bool := right_wins (minus g1 g2).
Definition eq (g1 g2 : game) : bool := second_wins (minus g1 g2).
Definition incomp (g1 g2 : game) : bool := first_wins (minus g1 g2).

Lemma gt_test : gt one zero = true.
Proof. reflexivity. Qed.
Lemma lt_test : lt minus_one zero = true.
Proof. reflexivity. Qed.
Lemma eq_test : eq (sum star star) zero = true.
Proof. reflexivity. Qed.
Lemma incomp_test : incomp star zero = true.
Proof. reflexivity. Qed.

(* In case you're thinking this is too gross, you can abstract things
a little bit more. Let's define a datatype for representing players,
and a function for comparing members of that type. *)


Definition side_eq (s1 s2 : side) : bool :=
  match s1, s2 with
    | Left, Left => true
    | Right, Right => true
    | _, _ => false
  end.


(* And moves selects the moves of a player from a game *)

Definition moves (g : game) (s : side) :=
  match s with
    | Left => left_moves g
    | Right => right_moves g
  end.

(* We can now write a function [wins s first g] that returns true iff
player [s] always wins game [g] when player [first] begins playing. *)

Fixpoint wins (s first : side) (g : game) : bool :=
  if side_eq s first then
    existsb (wins s (other first)) (moves g first)
  else
    forallb (wins s (other first)) (moves g first).

(* Now, we can define left_wins and right_wins generically: *)

Definition always_wins s g := wins s s g && wins s (other s) g.
