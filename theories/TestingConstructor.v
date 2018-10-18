(** When writing tactics, there are situations where it would be useful to know
    whether a term begins with a constructor.  One possibility is to extract the
    head of the term and use the [is_constructor] tactic. *)

Ltac head t :=
  match t with
  | ?t' _ => head t'
  | _ => t
  end.

Ltac head_constructor t :=
  let t' := head t in is_constructor t'.

Goal True.
(* These calls succeed *)
head_constructor 0.
head_constructor 1.
(* ...but this one fails *)
Fail head_constructor (1 + 1).
(*
The command has indeed failed with message:
In nested Ltac calls to "head_constructor" and "is_constructor", last call failed.
Tactic failure: not a constructor.
*)
Abort.

(** As of version 8.8, the [is_constructor] tactic is undocumented, but this
    should hopefully be fixed soon.  Interestingly, we can achieve almost the
    same effect without [is_constructor], by observing that Coq does not reduce
    a fixpoint unless it is applied to a term that begins with a constructor.
    *)

Reset head_constructor.
Ltac head_constructor t :=
  match type of t with
  | ?T =>
    let r := eval cbn in ((fix loop (t' : T) {struct t'} := tt) t) in
    match r with tt => idtac end
  end.

Goal True.
(* Succeed *)
head_constructor 0.
head_constructor 1.
Abort.

(** Unlike the previous version, this one reduces the term using [cbn] before
    testing it. Thus, the following test succeeds, while the analogous one
    before failed: *)

Goal True.
(* Succeeds *)
head_constructor (1 + 1).
Abort.

(** #<b>Update</b># Anton Trunov pointed out that we can emulate the behavior of
    the first tactic with a fixpoint by adding a flag in the call to [eval]: *)

Reset head_constructor.
Ltac head_constructor t :=
  match type of t with
  | ?T =>
    let r := eval cbn fix in ((fix loop (t' : T) {struct t'} := tt) t) in
    match r with tt => idtac end
  end.

(** Now, only the outer fixpoint is reduced. *)

Goal True.
Fail head_constructor (1 + 1).
Abort.
