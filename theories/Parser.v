(* begin hide *)
Require Import Coq.Lists.List.
(* end hide *)

(** Our parser will be parameterized by a few types and functions that
determine how it reads data, given in the following record: *)

Record parser := Parser {
  state : Type;
  initial_state : state;
  token : state -> Type;
  next : forall s, token s -> state;
  result : state -> Type;
  initial_result : result initial_state;
  read_token : forall s, result s -> forall t, result (next s t)
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
      [read_token].

Given such data, we can simulate a parsing process ourselves by doing
successive calls to [read_token]. *)

Section WithParser.

Variable p : parser.

Definition read_three_tokens t1 t2 t3 :=
  read_token p _ (
    read_token p _ (
      read_token p _ (initial_result p) t1
    ) t2
  ) t3.

(** Needless to say, this is not very convenient as a way of extending
Coq's syntax. We can make it better by declaring [read_token] as a
coercion from [result] to [Funclass]. Then, we can read a stream of
tokens simply by applying [initial_result p] to each token
successively: *)

Coercion read_token : result >-> Funclass.

Definition read_three_tokens' t1 t2 t3 :=
  (initial_result p) t1 t2 t3.

(** This works because each application of [read_token] returns a
[result], so trying to apply that updated result to another token
triggers yet another coercion, allowing the process to continue
indefinitely. We can check that both definitions of
[read_three_tokens] yield the same function, meaning that the coercion
is behaving as expected: *)

Lemma read_three_tokens_same : read_three_tokens = read_three_tokens'.
Proof. reflexivity. Qed.

(** To make the mechanism more robust, we can wrap our parser in a new
type, ensuring that the Coq type checker will not fail to perform some
coercions by reducing [result] more than it should. *)

Record parser_wrapper (s : state p) : Type := ParserWrapper {
  get_result : result p s
}.

Definition read_token' s (w : parser_wrapper s) t :=
  ParserWrapper _ (read_token p s (get_result s w) t).
Coercion read_token' : parser_wrapper >-> Funclass.

End WithParser.

(** As a last tweak, we declare another coercion and a notation to
make using our embedded parsers more similar to usual quotations, like
in Template Haskell: *)

Definition init_parser p := ParserWrapper _ _ (initial_result p).
Coercion init_parser : parser >-> parser_wrapper.
Notation "[ x ]" := (get_result _ _ x) (at level 0).

(** Now, we can invoke a parser simply by writing [[name_of_parser
<list of tokens>]]: *)

Definition read_three_tokens'' (p : parser) t1 t2 t3 :=
  [p t1 t2 t3].

(** As a first test for our parsing infrastructure, we can define an
alternative syntax for Coq lists that doesn't need separators between
the elements. *)

Definition listp (X : Type) := {|
  state := unit;
  initial_state := tt;
  token := fun _ => X;
  next := fun _ _ => tt;
  result := fun _ => list X;
  initial_result := nil;
  read_token := fun _ l x => app l (cons x nil)
|}.

(** The [listp] parser is parameterized by [X], the type of the
elements on the list. We initialize the parser with an empty list, and
each token that we read is an element of [X], which will be
progressively added at the end of our list. *)

Definition my_nat_list : list nat := [listp nat 0 1 2 3 4 5 6 7 8 9 10].

(** For [listp], there is no need to use anything interesting for the
[state] type. For more complicated parsers, however, [state] comes in
handy. To see how, we will define parsers for prefix and postfix
arithmetic expressions.

Expressions can involve three operations: addition, subtraction and
multiplication. *)

Inductive op := Add | Sub | Mul.

(** The expression parsers will read tokens that can be natural
numbers or one of the above operations. Thus, we group those in a
common type [exp_token]. *)

Inductive exp_token :=
| Op (o : op)
| Const (n : nat).

Notation "''+'" := Add (at level 0).
Notation "''-'" := Sub (at level 0).
Notation "''*'" := Mul (at level 0).

Coercion Op : op >-> exp_token.
Coercion Const : nat >-> exp_token.

(** To compute the value of an expression, we map each operation to a
Coq function: *)

Definition ap_op (o : op) :=
  match o with
  | Add => plus
  | Sub => minus
  | Mul => mult
  end.

Module Pre.

Definition state := nat.

Definition token (s : state) : Type :=
  match s with
  | S _ => exp_token
  | _ => Empty_set
  end.

Fixpoint result (n : nat) : Type :=
  match n with
  | 0 => nat
  | S n => nat -> result n
  end.

Definition next (s : state) : token s -> state :=
  match s with
  | S n' => fun t =>
              match t with
              | Op _ => S (S n')
              | Const _ => n'
              end
  | _ => fun _ => 0
  end.

Definition read_token s : result s -> forall t, result (next s t) :=
  match s with
  | S n' =>
    fun res t =>
      match t with
      | Op o => fun n1 n2 => res (ap_op o n1 n2)
      | Const n => res n
      end
  | _ => fun _ t => match t with end
  end.

End Pre.

Definition pre := {|
  state := Pre.state;
  initial_state := 1;
  token := Pre.token;
  result := Pre.result;
  next := Pre.next;
  initial_result := fun t => t;
  read_token := Pre.read_token
|}.

Module Post.

Inductive state :=
| Empty
| One
| More (n : nat).

Definition token (s : state) : Type :=
  match s with
  | Empty | One => nat
  | More _ => exp_token
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
                | Op _ => One
                | Const _ => More 1
                end
  | More (S n) => fun t =>
                    match t with
                    | Op _ => More n
                    | Const _ => More (S (S n))
                    end
  end.

Definition read_token s : result s -> forall t, result (next s t) :=
  match s with
  | Empty => fun _ t => t
  | One => fun res t => (res, t)
  | More 0 => fun res t =>
                match res with
                | (n1, n2) =>
                  match t with
                  | Op o => ap_op o n1 n2
                  | Const n => (n1, n2, n)
                  end
                end
  | More (S n) => fun res t =>
                    match res with
                    | (res, n1, n2) =>
                      match t with
                      | Op o => (res, ap_op o n1 n2)
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
  read_token := Post.read_token
|}.

Definition my_exp : nat := [pre '+ '- 1 2 '+ 4 4].
Definition my_exp' : nat := [post 4 4 '+ 2 1 '- '+].
