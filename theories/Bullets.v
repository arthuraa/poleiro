(* begin hide *)
Open Scope bool_scope.
(* end hide *)

(** Ltac scripts are notoriously hard to maintain. One problem that
arises often is ensuring that

** Bullets to the rescue

Since version 8.4, Coq comes with a nice feature for better
structuring proof scripts. One can now use bullets ([-], [+] and [*])
and curly braces ([{}]) to delimit sections of a proof that correspond
to different subgoals. A similar feature was already present in the
#<a
href="http://www.msr-inria.com/projects/mathematical-components/">SSReflect</a>#
Coq plugin for some time, but the new version brings a significant
improvement: bullets are automatically checked for consistent
usage. Thus, besides making proofs more readable, bullets also guide
Coq when executing a proof script, making errors easier to understand.

Let's see how bullets work. When Coq spots a bullet during a proof, it
hides all other goals and focuses the proof on the current one.

*)

Lemma negb_involutive : forall b, negb (negb b) = b.
Proof.
  intros.
  destruct b.

(**
[[
2 subgoals, subgoal 1 (ID 7)

  ============================
   negb (negb true) = true

subgoal 2 (ID 8) is:
 negb (negb false) = false
]]
*)

  - (* Focus the proof *)

(**
[[
1 focused subgoals (unfocused: 1)
, subgoal 1 (ID 7)

  ============================
   negb (negb true) = true
]]

The proof can only be unfocused once the current subgoal is
solved. Then, we can proceed with the other subgoals by beginning each
of them with the _same_ bullet. Trying to use another bullet (or no
bullet at all) results in an error. *)

    simpl. reflexivity.

  - (* Begin other case *)
    simpl. reflexivity.
Qed.

(** It is possible to nest bullets in subcases by using a different
type for each level. The actual order doesn't matter, as long as we
don't use a bullet when a subgoal with that same bullet is still
unsolved. *)

Lemma andb_comm : forall b1 b2, b1 && b2 = b2 && b1.
Proof.
  intros b1 b2.
  destruct b1.
  - destruct b2.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - destruct b2.
    + simpl. reflexivity.
    + simpl. reflexivity.
Qed.

(** Curly braces are similar to bullets, but need to be explicitly
closed when a goal is solved. Because of this, they can be arbitrarily
nested, since no ambiguity arises. *)

Lemma andb_comm' : forall b1 b2, b1 && b2 = b2 && b1.
Proof.
  intros b1 b2.
  destruct b1.
  { destruct b2.
    { simpl. reflexivity. }
    { simpl. reflexivity. } }
  { destruct b2.
    { simpl. reflexivity. }
    { simpl. reflexivity. } }
Qed.

(** Curly braces also allow us to reuse bullets by "forgetting" which
ones were used before it: *)

Lemma andb_assoc : forall b1 b2 b3, b1 && (b2 && b3) = (b1 && b2) && b3.
Proof.
  intros b1 b2 b3.
  destruct b1.
  + destruct b2.
    { destruct b3.
      + simpl. reflexivity.
      + simpl. reflexivity. }
    { destruct b3.
      + simpl. reflexivity.
      + simpl. reflexivity. }
  + simpl. reflexivity.
Qed.

(** Finally, a pair of curly braces doesn't have to be followed by
another pair. This makes them great for proving assertions without
needing to nest the proof on the second subcase: *)

Lemma andb_permute : forall b1 b2 b3, b1 && (b2 && b3) = (b1 && b3) && b2.
Proof.
  intros b1 b2 b3.
  assert (H : b2 && b3 = b3 && b2).
  { (* Proof of assertion *)
    apply andb_comm. }
  rewrite H.
  apply andb_assoc.
Qed.

(** If we try to use the same bullet for different subcase levels, Coq
understands that the tactics we want to execute are meant for a
different subgoal, and raises an error.

When beginning a subcase with a bullet that is still _open_ (i.e.,
also used a subgoal that hasn't been completely solved yet), Coq
understands that you want to proceed to the next subgoal and raises an
error. This makes the hierarchical structure of the proof more robust,

First of all, it checks that bullets are used consistently. If you
start a subgoal with a bullet, Coq will require you to use the same
bullet in all corresponding subgoals. Also, trying to proceed to a new
bullet will fail if that bullet is still _open_, i.e. if it has been
used to introduce a subgoal that hasn't been solved yet. This ensures
that tactics will only run in the goal they were intended for, making
errors more local and tracktable. Another advantage is that opening a
bullet focuses the proof on the current subgoal *)
