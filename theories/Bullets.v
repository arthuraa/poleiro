(* begin hide *)
Open Scope bool_scope.
(* end hide *)
(** Ltac scripts are notoriously hard to maintain. One problem that
arises often is ensuring that each piece of Ltac code executes exactly
on the subgoal it was intended for. When refactoring Coq code, a proof
could start generating different sets of subgoals at some points,
causing the proof script to fail. Sometimes, these failures occur far
from the place that needs to be fixed, making it difficult to track
the actual cause.

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
type of bullet for each level. The actual order doesn't matter, as
long as we don't use a bullet when a subgoal with that same bullet is
still unsolved. *)

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
closed when a goal is solved. This allows us to nest curly braces
arbitrarily deep, since, unlike bullets, no ambiguity arises in those
cases. *)

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
other pairs when proceeding to other parts of the proof. This makes
them great for proving assertions or short secondary goals: *)

Lemma andb_permute : forall b1 b2 b3, b1 && (b2 && b3) = (b1 && b3) && b2.
Proof.
  intros b1 b2 b3.
  assert (H : b2 && b3 = b3 && b2).
  { (* Proof of assertion *)
    apply andb_comm. }
  rewrite H.
  apply andb_assoc.
Qed.

(** ** Update

Ssreflect also uses bullets to structure scripts. As pointed out in a
comment below, however, their behavior is slightly different there:
bullets don't focus on the current subgoal, and they are not checked
for consistency. To restore the default behavior, simply include the
following command on your script: *)
(* begin hide *)
Require Import Ssreflect.ssreflect.
(* end hide *)
Set Bullet Behavior "Strict Subproofs".
