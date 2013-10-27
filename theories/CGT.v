(* begin hide *)
Require Import Coq.Lists.List.
Notation "[]" := nil : list_scope.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) .. ) : list_scope.
Open Scope bool_scope.
(* end hide *)

(** In this post, I will begin to formalize a small part of #<a
href="http://en.wikipedia.org/wiki/Combinatorial_game_theory">#
combinatorial game theory#</a># using Coq. Combinatorial game theory
attempts to model sequential, deterministic games between two players,
both of which take turns causing the game state to change. It
restricts itself to _perfect information_ games, where the current
configuration of the game is known to both players. Thus, it can be
used to study games such as chess, tic-tac-toe, and go, but not games
such as poker or blackjack.

The power of combinatorial game theory comes from abstracting away
details that are too specific to each game, such as whether it is
played moving pieces on a board, how the pieces can move, etc. It
defines a single mathematical object that can represent all games
uniformily, allowing us to study general situations that could occur
in many kinds of games. In this post, I will present this
representation and discuss why it makes sense. I will start with a
more intuitive formalization of combinatorial games, and then show how
combinatorial game theory applies to all of those.

** Defining combinatorial games

In combinatorial games, players are traditionally called _left_ and
_right_. *)

Inductive player : Type := Left | Right.

(** Each combinatorial game has a set of _positions_. In chess, for
instance, a position is a chess board with black and white pieces on
it. The rules of the game determine which _moves_ are available to
each player at a given position. They also describe how the game ends,
and which player wins in that case. To simplify our analysis, we will
assume that games end when some player must play but has no moves
left, in which case the other player wins. This frees us from having
to model how matches end separately for each game. We will also
consider only _finite_ games, i.e. ones that can't be played
indefinitely. Notice that these two assumptions taken together,
strictly speaking, rule out many interesting games: chess can end in a
draw, something that can't happen in our model.

Translating the above requirements into code results in the following
definition: *)

Inductive combinatorial_game := CombinatorialGame {
  position : Type;
  moves : player -> position -> list position;
  valid_move next current := exists s, In next (moves s current);
  finite_game : well_founded valid_move
}.

(** To formalize how games are played, we define a predicate [Match cg
first winner m] that represents a match of game [cg] where player
[first] starts and player [winner] wins. [m] is the sequence of
positions traversed during the match, from first to last. *)

Definition other (s : player) : player :=
  match s with
    | Left => Right
    | Right => Left
  end.

Inductive Match cg : forall (first winner : player), list (position cg) -> Prop :=
| Match_end : forall pl pos,
                moves cg pl pos = [] ->
                Match cg pl (other pl) [pos]
| Match_move : forall pl winner pos next m,
                 In next (moves cg pl pos) ->
                 Match cg (other pl) winner (next :: m) ->
                 Match cg pl winner (pos :: next :: m).

(** In the [Match_end] clause, we check that the current player has no
moves left. In [Match_move], we check that the current player can make
a move and that the match can then proceed with the other positions.

** A universal game

We will now define a combinatorial game that is, in a precise sense to
be explained later, the most general one. This is what combinatorial
game theory uses to study combinatorial games.

The crucial observation is that in the definition of [Match] we only
care about the moves that can be made from a given position, but not
about what the positions themselves _are_. This suggests a definition
where each position is just a pair of sets, one for each player's
moves. This forms the type [game] of games. *)

Inductive game := Game {
  left_moves : list game;
  right_moves : list game
}.

(** Each position in this game can be pictured as an
arbitrarily-branching tree with two sets of children. On each player's
turn, they choose one child in their set of moves to be the new
position, and lose if they can't choose anything.

The simplest [game] is [zero], where both players have no moves
available. It is a game where the first player always loses. *)

Definition zero : game := Game [] [].

(** Using [zero] we can define [star], where the first player _always_
wins by making a move to [zero]. *)

Definition star : game := Game [zero] [zero].

(** A small variation gives us [one] and [minus_one], where [Left] and
[Right] always win, respectively. *)

Definition one : game := Game [zero] [].
Definition minus_one : game := Game [] [zero].

(** It should be possible to encapsulate [game] in a
[combinatorial_game] record. Defining [moves] is simple, but proving
that [game]s are finite requires some additional work. The nested
inductive in the definition of [game] makes Coq generate an induction
principle that is too weak to be useful:

[[
game_ind
     : forall P : game -> Prop,
       (forall left_moves right_moves : list game,
        P {| left_moves := left_moves; right_moves := right_moves |}) ->
       forall g : game, P g
]]

The usual solution is to define a new one by hand that gives us
induction hypotheses to use: *)

Lemma lift_forall :
  forall T (P : T -> Prop),
    (forall t, P t) ->
    forall l, Forall P l.
Proof. induction l; auto. Defined.

Definition game_ind' (P : game -> Prop)
                     (H : forall l r, Forall P l -> Forall P r -> P (Game l r)) :
  forall g : game, P g :=
  fix F (g : game) : P g :=
  match g with
    | Game l r =>
      H l r (lift_forall _ P F l) (lift_forall _ P F r)
  end.

(** Using this principle, we can now prove that [game]s always
terminate and define a [combinatorial_game] for [game]. *)

Definition game_as_cg : combinatorial_game.
  refine ({| position := game;
             moves s := if s then left_moves else right_moves |}).
  intros p1.
  induction p1 as [l r IHl IHr] using game_ind'.
  (* ... *)
  (* begin hide *)
  constructor.
  intros p2 [s H].
  destruct s; simpl in H.
  - rewrite Forall_forall in IHl.
    apply IHl.
    assumption.
  - rewrite Forall_forall in IHr.
    apply IHr.
    assumption.
  (* end hide *)
Defined.

(** ** Game embeddings

I claimed that [game] is the most general combinatorial game. One way
of seeing this is that we lose no information by representing each
position in a combinatorial game as the tree of all possible moves,
and such a tree can always be encoded as a [game]. To make this
intuition formal, we can define a notion of _game embedding_ between
two combinatorial games. This will be a mapping between the positions
of each combinatorial game that preserves matches. Thus, if we have an
embedding of [cg1] into [cg2], then we can study [cg1] matches by
regarding them as [cg2] matches. *)

Definition game_embedding (cg1 cg2 : combinatorial_game)
           (embedding : position cg1 -> position cg2) : Prop :=
  forall first winner (m : list (position cg1)),
    Match cg1 first winner m ->
    Match cg2 first winner (map embedding m).

(** With this notion of game embedding, combinatorial games form a
category. I will now show that every combinatorial game can be
embedded in [game], making [game] a terminal object in this category
and the most general combinatorial game. In this formulation, it is
only a _weakly_ terminal object (i.e., embeddings are not unique), as
we are using Coq lists to represent sets.

To embed an arbitrary combinatorial game into [game], we can define a
function by well-founded recursion over the proof that games are
finite. In order to do this, we need a higher-order function
[map_game] that allows us to perform a well-founded recursive call on
a list of next moves. [map_game] acts like [map], but passes to its
argument function a proof that the element is a [valid_move]. *)

Fixpoint map_In {A B} (l : list A) : (forall x, In x l -> B) -> list B :=
  match l with
    | [] => fun _ => []
    | x :: l' => fun f =>
                   f x (or_introl _ eq_refl)
                     :: map_In l' (fun x P => f x (or_intror _ P))
  end.

Definition map_game {A} (cg : combinatorial_game)
                    (pos : position cg) (p : player)
                    (f : forall pos', valid_move cg pos' pos -> A) : list A :=
  map_In (moves cg p pos) (fun pos' P => f pos' (ex_intro _ p P)).

(** Using this function and the [Fix] combinator in the standard
library, we write a generic embedding function [embed_in_game]. Like a
regular fixpoint combinator, [Fix] takes a function that does a
recursive call by applying its argument (here, [F]). The difference is
that this argument must take a _proof_ that shows that the recursive
call is valid.

The behavior of [embed_in_game] is simple: it calls itself recursively
for each possible next position, and includes that position in the set
of moves of the appropriate player. *)

Definition embed_in_game cg (pos : position cg) : game :=
  Fix (finite_game cg)
      (fun _ => position game_as_cg)
      (fun pos F =>
         Game (map_game cg pos Left F)
              (map_game cg pos Right F))
      pos.
(* begin hide *)
Lemma map_In_map :
  forall A B
         (l : list A)
         (f : forall x, In x l -> B)
         (g : A -> B)
         (H : forall x P, f x P = g x),
    map_In l f = map g l.
Proof.
  intros.
  induction l as [|x l IH]; auto.
  simpl.
  rewrite H. f_equal.
  apply IH.
  intros x' P.
  apply H.
Qed.

Lemma map_game_map :
  forall A
         (cg : combinatorial_game)
         (pos : position cg) (p : player)
         (f : forall pos', valid_move cg pos' pos -> A)
         (g : position cg -> A)
         (H : forall pos' P, f pos' P = g pos'),
    map_game cg pos p f = map g (moves cg p pos).
Proof. eauto using map_In_map. Qed.

Lemma map_In_ext :
  forall A B
         (l : list A)
         (f g : forall x, In x l -> B)
         (EXT : forall x P, f x P = g x P),
    map_In l f = map_In l g.
Proof.
  intros.
  induction l as [|x l IH]; auto.
  simpl. rewrite EXT.
  f_equal.
  apply IH.
  intros x' P.
  apply EXT.
Qed.

Lemma map_game_ext :
  forall A
         (cg : combinatorial_game)
         (pos : position cg) (p : player)
         (f g : forall pos', valid_move cg pos' pos -> A)
         (EXT : forall pos' P, f pos' P = g pos' P),
    map_game cg pos p f = map_game cg pos p g.
Proof. eauto using map_In_ext. Qed.

(* end hide *)
(** Definitions that use [Fix] can be hard to manipulate directly, so
we need to prove some equations that describe the reduction behavior
of the function. I've hidden some of the auxiliary lemmas and proofs
for clarity; as usual, you can find them in the original [.v] file.

The proof that we can unfold [embed_in_game] once uses the [Fix_eq]
lemma in the standard library. *)

Lemma embed_in_game_eq cg (pos : position cg) :
  embed_in_game cg pos =
  Game (map (embed_in_game cg) (moves cg Left pos))
       (map (embed_in_game cg) (moves cg Right pos)).
Proof.
  unfold embed_in_game in *.
  rewrite Fix_eq.
  (* ... *)
  (* begin hide *)
  - intros.
    f_equal; apply map_game_map; reflexivity.
  - intros.
    f_equal; apply map_game_ext; intros; eauto.
  (* end hide *)
Qed.

(** With this lemma, we can show that [moves] and [embed_in_game] commute. *)

Lemma embed_in_game_moves cg (p : position cg) :
  forall s, moves game_as_cg s (embed_in_game cg p) =
            map (embed_in_game cg) (moves cg s p).
Proof.
  intros.
  rewrite embed_in_game_eq.
  destruct s; reflexivity.
Qed.

(** We are now ready to state and prove our theorem: every
combinatorial game can be embedded in [game]. *)

Theorem embed_in_game_correct cg :
  game_embedding cg game_as_cg (embed_in_game cg).
Proof.
  unfold game_embedding.
  intros first winner m MATCH.
  induction MATCH as [winner p H|s winner p p' m IN MATCH IH];
  simpl; constructor; eauto.
  - rewrite embed_in_game_moves, H. reflexivity.
  - rewrite embed_in_game_moves. auto using in_map.
Qed.

(** ** Summary

We've developed the foundations of combinatorial game theory, showing
how it can model combinatorial games in a simple yet general way. We
haven't explored yet how to use this representation in practice to
study games, something I plan to do on future posts.

_Update_: I'll leave the list of posts in this series here.

- #<a href="/posts/2013-10-27-summing-combinatorial-games.html">#Summing combinatorial games#</a>#

*)
