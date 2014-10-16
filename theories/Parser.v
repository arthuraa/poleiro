(* begin hide *)
Require Import Coq.Lists.List.
(* end hide *)

Section Parser.

(** Our parser will be parameterized by a few types and functions that
determine how it reads data, given in the following record: *)

Record parser_data := ParserData {
  state : Type;
  initial_state : state;
  token : state -> Type;
  next : forall s, token s -> state;
  result : state -> Type;
  initial_result : result initial_state;
  update_result : forall s t, result s -> result (next s t)
}.

(** Let's see what each field in this record means.

    - [state] represents the current parser state. We can use it for
      signaling that our parser has finished and produced a result, or
      that it encountered an error, or even that it is currently
      parsing some specific construct. The parser starts at state
      [initial_state].

    - [token] is the type of parsing tokens that the parser will
      read. Notice that it is allowed to depend on the current state,
      so we can use types to constrain our parser's behavior. Once a
      parser at state [s] reads some token [t], it will enter a new
      state [s'] given by the [next] function.

    - [result] is the type of values returned by the parser. It also
      tells the type of the partial result that our parser has read so
      far. It is initially set to [initial_result], and it is
      incrementally updated with each new token read, using
      [update_result].

Given such data, we can simulate a parsing process ourselves by doing
successive calls to [update_result]. *)

Variable pd : parser_data.

Definition read_three_tokens t1 t2 t3 :=
  update_result pd _ t3 (
    update_result pd _ t2 (
      update_result pd _ t1 (initial_result pd)
    )
  ).

(** Needless to say, this is not very convenient for extending Coq's
syntax. We can make this better by wrapping [parser_data] in another
type. *)

Record parser_state (s : state pd) : Type := ParserState {
  get_result : result pd s
}.

Definition read_token s (p : parser_state s) t :=
  ParserState _ (update_result pd s t (get_result s p)).

Definition reader := ParserState _ (initial_result pd).

End Parser.

Coercion reader : parser_data >-> parser_state.
Coercion read_token : parser_state >-> Funclass.

Notation "[ x ]" := (get_result _ _ x) (at level 0).

Module List.

Definition p (X : Type) := {|
  state := unit;
  token := fun _ => X;
  result := fun _ => list X;
  initial_state := tt;
  next := fun _ _ => tt;
  initial_result := nil;
  update_result := fun _ x l => app l (cons x nil)
|}.

End List.

Definition my_list : list nat := [List.p _ 1 2 3 4 5 6 7 8 9 10 11].

Module Exp.

Inductive binop := Plus | Minus | Mult.

Definition ap_binop (b : binop) :=
  match b with
  | Plus => plus
  | Minus => minus
  | Mult => mult
  end.

Inductive inst :=
| Binop (b : binop)
| Const (n : nat).

Module Exports.

Notation "''+'" := (Plus) (at level 0).
Notation "''-'" := (Minus) (at level 0).
Notation "''*'" := (Mult) (at level 0).

Coercion Binop : binop >-> inst.
Coercion Const : nat >-> inst.

End Exports.

Module Pre.

Inductive state :=
| Ok (n : nat)
| Error.

Definition token (s : state) : Type :=
  match s with
  | Ok (S _) => inst
  | _ => Empty_set
  end.

Fixpoint result' (n : nat) : Type :=
  match n with
  | 0 => nat
  | S n => nat -> result' n
  end.

Definition result (s : state) : Type :=
  match s with
  | Ok n => result' n
  | Error => Empty_set
  end.

Definition next (s : state) : token s -> state :=
  match s with
  | Ok (S n') => fun t =>
                   match t with
                   | Binop _ => Ok (S (S n'))
                   | Const _ => Ok n'
                   end
  | _ => fun _ => Error
  end.

Definition update_result s : forall t, result s -> result (next s t) :=
  match s with
  | Ok (S n') =>
    fun t =>
      match t with
      | Binop b => fun res n1 n2 => res (ap_binop b n1 n2)
      | Const n => fun res => res n
      end
  | _ => fun t _ => t
  end.

End Pre.

Definition pre := {|
  state := Pre.state;
  initial_state := Pre.Ok 1;
  token := Pre.token;
  result := Pre.result;
  next := Pre.next;
  initial_result := fun t => t;
  update_result := Pre.update_result
|}.

Module Post.

Inductive state :=
| Empty
| One
| More (n : nat).

Definition token (s : state) : Type :=
  match s with
  | Empty | One => nat
  | More _ => inst
  end.

Fixpoint result' (n : nat) : Type :=
  match n with
  | 0 => nat
  | S n => (result' n * nat)%type
  end.

Definition result (s : state) : Type :=
  match s with
  | Empty => unit
  | One => nat
  | More n => result' (S n)
  end.

Definition next s : token s -> state :=
  match s with
  | Empty => fun _ => One
  | One => fun _ => More 0
  | More 0 => fun t =>
                match t with
                | Binop _ => One
                | Const _ => More 1
                end
  | More (S n) => fun t =>
                    match t with
                    | Binop _ => More n
                    | Const _ => More (S (S n))
                    end
  end.

Definition update_result s : forall t, result s -> result (next s t) :=
  match s with
  | Empty => fun t _ => t
  | One => fun t r => (r, t)
  | More 0 => fun t res =>
                match res with
                | (n1, n2) =>
                  match t with
                  | Binop b => ap_binop b n1 n2
                  | Const n => (n1, n2, n)
                  end
                end
  | More (S n) => fun t res =>
                    match res with
                    | (res, n1, n2) =>
                      match t with
                      | Binop b => (res, ap_binop b n1 n2)
                      | Const n => (res, n1, n2, n)
                      end
                    end
  end.

End Post.

Definition post := {|
  state := Post.state;
  token := Post.token;
  result := Post.result;
  initial_state := Post.Empty;
  next := Post.next;
  initial_result := tt;
  update_result := Post.update_result
|}.

End Exp.

Export Exp.Exports.

Definition my_exp : nat := [Exp.pre '+ '- 1 2 '+ 4 4].
Definition my_exp' : nat := [Exp.post 4 4 '+ 2 1 '- '+].
