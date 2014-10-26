(* begin hide *)
Require Import Coq.Lists.List.
(* end hide *)
(** Coq's built-in extensible parser, although quite convenient in
many cases, does have some limitations. On one hand, some syntax
extensions that one might like to write cannot be expressed in
it. Furthermore, the extensions are not first-class, having to be
defined outside of the core language. We will see how to implement
some interesting syntax extensions in Coq using just coercions and
regular Coq functions. Besides being first-class, we will see that the
mechanism can be used for defining extensions that cannot be expressed
just with Coq's extensible parser.

We want to describe each syntax extension with a few Coq types and
functions that determine how it should be parsed. Our first attempt
might look like this: *)

Module Simple.

Record parser := Parser {
  token : Type;
  result : Type;
  initial_result : result;
  read_token : result -> token -> result
}.

(** Our parser works by reading [token]s and returning a value of type
[result] at the end of the process. It does this by starting with some
value [initial_result] and updating that value with each token read,
using function [read_token]. For instance, here's a function that
returns the result of parsing three tokens: *)

Section WithParser.

Variable p : parser.

Definition read_three_tokens t1 t2 t3 :=
  read_token p (
    read_token p (
      read_token p (initial_result p) t1
    ) t2
  ) t3.

(** We can use this definition as a syntax extension by declaring
[read_token] as a coercion from [result] to [Funclass], allowing us to
use each [result] as if it were a function. Then, applying
[initial_result p] to a sequence of tokens will correspond to calling
our parser on that sequence. *)

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

(** To make the mechanism more robust, we wrap our parser in a new
type, ensuring that the Coq type checker will not fail to perform some
coercion by reducing [result] more than it should. *)

Record parser_wrapper : Type := ParserWrapper {
  get_result : result p
}.

Definition read_token' (w : parser_wrapper) t :=
  ParserWrapper (read_token p (get_result w) t).
Coercion read_token' : parser_wrapper >-> Funclass.

End WithParser.

(** As a last tweak, we declare another coercion and a notation to
make using our embedded parsers more similar to other systems, like in
Template Haskell: *)

Definition init_parser p := ParserWrapper _ (initial_result p).
Coercion init_parser : parser >-> parser_wrapper.
Notation "[ x ]" := (get_result _ x) (at level 0).

(** Now, we can invoke a parser simply by writing [[name_of_parser
<list of tokens>]]: *)

Definition read_three_tokens'' (p : parser) t1 t2 t3 :=
  [p t1 t2 t3].

(** As a first example, we can define an alternative syntax for Coq
lists that doesn't need separators between the elements. *)

Definition listp (X : Type) := {|
  token := X;
  result := list X;
  initial_result := nil;
  read_token l x := app l (cons x nil)
|}.

(** The [listp] parser is parameterized by [X], the type of the
elements on the list. We initialize the parser with an empty list, and
each token that we read is an element of [X], which will be
progressively added at the end of our list. *)

Definition list_exp : list nat := [listp nat 0 1 2 3 4 5 6 7 8 9 10].

End Simple.

(** ** More parsers

While nice, [listp] is not especially interesting as a parser, since
it doesn't really analyze the tokens it reads. In contrast, parsers
usually treat tokens differently, depending on what it has been read
so far. To take such dependencies into account, we introduce some new
fields to our record: *)

Module State.

Record parser := Parser {
  state : Type;
  initial_state : state;
  token : Type;
  next : state -> token -> state;
  result : Type;
  initial_result : result;
  read_token : state -> result -> token -> result
}.

End State.

(** The [state] field represents the internal state of our parser at a
given point. It is set initially set to [initial_state], and is
updated using function [next]. We also change [read_token] to pass it
the current state as an additional argument.

While more general, this version isn't quite good yet. We require our
parsers to carry around a complete result value that it can return
after having read _any_ sequence of tokens. Usually, however, parsing
can result in errors, and there is no meaningful value that can be
returned by the parser until it finishes its job. To solve this
problem, we introduce one last change to our definition: _dependent
types_. *)

Record parser := Parser {
  state : Type;
  initial_state : state;
  token : state -> Type;
  next : forall s, token s -> state;
  partial_result : state -> Type;
  initial_partial_result : partial_result initial_state;
  read_token : forall s, partial_result s -> forall t, partial_result (next s t)
}.
(* begin hide *)
Section WithParser.

Variable p : parser.

Record parser_wrapper (s : state p) : Type := ParserWrapper {
  get_partial_result : partial_result p s
}.

Definition read_token' s (w : parser_wrapper s) t :=
  ParserWrapper _ (read_token p s (get_partial_result s w) t).
Coercion read_token' : parser_wrapper >-> Funclass.

End WithParser.

Definition init_parser p := ParserWrapper _ _ (initial_partial_result p).
Coercion init_parser : parser >-> parser_wrapper.
Notation "[ x ]" := (get_partial_result _ _ x) (at level 0).
(* end hide *)

(** Now, the type of tokens expected by the parser, as well as its
type of partial results, can depend on the current parsing state, and
the parsing functions have been updated to take this dependency into
account.

With dependent types, the type of the value being built,
[partial_result], can change during the parsing process, allowing us
to distinguish a complete, successfully parsed result, from one that
still needs more tokens, or even from a message describing a parse
error. By making [token] depend on the current state, we can constrain
which tokens can be read at each parsing state, allowing us to expose
parse errors as type errors.

For [listp], there is no need to use anything interesting for the
[state] type. For more complicated parsers, however, [state] comes in
handy. To see how, we will define parsers for prefix and postfix
arithmetic expressions. This is also a nice example because prefix and
postfix expressions cannot be handled by Coq's extensible parser
alone.

Expressions can involve three operations: addition, subtraction and
multiplication. *)

Inductive op := Add | Sub | Mul.

(** The parsers will read tokens that can be natural numbers or one of
the above operations. We group those in a common type [exp_token]. *)

Inductive exp_token :=
| Op (o : op)
| Const (n : nat).

Notation "''+'" := Add (at level 0).
Notation "''-'" := Sub (at level 0).
Notation "''*'" := Mul (at level 0).

Coercion Op : op >-> exp_token.
Coercion Const : nat >-> exp_token.
(* begin hide *)
(* Denotation of an operation *)
Definition ap_op (o : op) :=
  match o with
  | Add => plus
  | Sub => minus
  | Mul => mult
  end.
(* end hide *)

(** Let's consider how to deal with prefix expressions first. At any
point during parsing, the parser is waiting for some number of
additional expressions it must read in order to complete the top-level
expression. We will use this number as the parser state. Initially,
the parser wants to read just one expression, so we will use that as
the initial state. Once the state reaches zero, there are no more
expressions to read, so we know that the parser is done. *)

Module Pre.

Definition state := nat.
Definition initial_state : state := 1.

(** If our current state is zero, any additional tokens fed to the
parser should result in a parse error. To implement this behavior, we
define the type of tokens for that state to be [Empty_set]. Trying to
feed an extra token to parser at that point will result in a type
error, signaling that a parse error just occurred. If the parser still
expects expressions (i.e., if the current state is greater than zero),
we just use [exp_token] for the token type. *)

Definition token (s : state) : Type :=
  match s with
  | S _ => exp_token
  | 0 => Empty_set
  end.

(** The value built by the parser will be a continuation that expects
[n] numbers, one for each expression that the parser still needs to
read. *)

Fixpoint partial_result (n : nat) : Type :=
  match n with
  | 0 => nat
  | S n => nat -> partial_result n
  end.

(** We must define how the parser actually interprets the tokens it
reads. If the parser expects [n] expressions, reading a constant will
make this number go down by one, since a constant is a complete
expression. If it reads an operation, on the other hand, that number
is increased by one. If [n = 0], there is no token to be read, hence
no next state, so we perform an empty pattern match to show that can't
happen. *)

Definition next (s : state) : token s -> state :=
  match s with
  | S n' => fun t =>
              match t with
              | Op _ => S (S n')
              | Const _ => n'
              end
  | 0 => fun t => match t with end
  end.

(** How do we update the result? If we read a constant, we just feed
it to the continuation. If we read an operation, we compose that
operation with the continuation, which has the net effect of adding
one argument to it. Here, [ap_op] is a function that maps each [op] to
the corresponding Coq function. *)

Definition read_token s : partial_result s -> forall t, partial_result (next s t) :=
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

(** We can now package our definitions as a complete parser and try it
on some examples: *)

Definition pre := {|
  state := Pre.state;
  initial_state := 1;
  token := Pre.token;
  partial_result := Pre.partial_result;
  next := Pre.next;
  initial_partial_result := fun t => t;
  read_token := Pre.read_token
|}.

Definition pre_exp1 : nat :=
  [pre '+ '- 1 2 '+ 4 4].
Definition pre_exp2 : nat :=
  [pre '+ '* 12 '* 12 12 '* 1 '* 1 1].

(** We can also see that invalid expressions are rejected, as expected. *)

Fail Definition pre_exp_wrong : nat :=
  [pre '+ 1 1 1].
(**
[[
Error: The term "1" has type "nat" while it is expected to have type
"token pre (next pre (next pre (next pre (initial_state pre) '+) 1) 1)".
]]

A parser for postfix expressions is in some sense the _dual_ of the
one we've just seen: instead of carrying around a continuation that
expects arguments, we construct a stack of numbers on which we can
perform our operations. Our state will also be a number, denoting the
number of elements on our stack. Since our stack start empty, the
initial state will be zero. *)

Module Post.

Definition state := nat.
Definition initial_state : state := 0.

(** Since our operations need at least two numbers on the stack, we
restrict our parser to accept only numbers if the stack doesn't have
the appropriate size: *)

Definition token (s : state) : Type :=
  match s with
  | 0 | 1 => nat
  | _ => exp_token
  end.

(** The [partial_result] type is a length-indexed list of natural
numbers with one small twist: we ensure that [partial_result 1 = nat]
definitionally, so that we can use postfix expressions as having type
[nat] without the need for any projections. *)

Fixpoint partial_result' (n : nat) : Type :=
  match n with
  | 0 => nat
  | S n => (partial_result' n * nat)%type
  end.

Definition partial_result (s : state) : Type :=
  match s with
  | 0 => unit
  | S n => partial_result' n
  end.

(** [next] and [read_token] are dual to the definitions of the
previous parser: reading a constant increases the stack size by one,
while reading an operation decreases the stack size by one. *)

Definition next s : token s -> state :=
  match s with
  | 0 => fun _ => 1
  | 1 => fun _ => 2
  | S (S n) => fun t =>
                 match t with
                 | Op _ => 1 + n
                 | Const _ => 3 + n
                 end
  end.

Definition read_token s : partial_result s -> forall t, partial_result (next s t) :=
  match s with
  | 0 => fun _ t => t
  | 1 => fun res t => (res, t)
  | 2 => fun res t =>
           match res with
           | (n1, n2) =>
             match t with
             | Op o => ap_op o n1 n2
             | Const n => (n1, n2, n)
             end
           end
  | S (S (S n)) => fun res t =>
                     match res with
                     | (res, n1, n2) =>
                       match t with
                       | Op o => (res, ap_op o n1 n2)
                       | Const n => (res, n1, n2, n)
                       end
                     end
  end.

End Post.

(** We now have a full parser for postfix expressions, which we can
test on some examples. *)

Definition post := {|
  state := Post.state;
  initial_state := 0;
  token := Post.token;
  next := Post.next;
  partial_result := Post.partial_result;
  initial_partial_result := tt;
  read_token := Post.read_token
|}.

Definition post_exp1 : nat := [post 4 4 '+ 2 1 '- '+].
Definition post_exp2 : nat := [post 9 9 '* 9 '* 10 10 '* 10 '* '+].

(** ** Summary

We've seen how we can use coercions to extend the syntax of Coq. While
useful, this technique is _complementary_ to Coq's own extensible
parser, having its own limitations. Despite being very programmable,
there are also syntax extensions that cannot be defined with this
technique in a seamless way, such as anything involving variable
binding. Being first class can also be a disadvantage, since the
parser and parsing functions are part of the resulting term, possibly
affecting conversion and unification. Finally, regular syntax
extensions are defined with a high-level declarative syntax, while
this mechanism requires one to write a custom parser for each
extension. *)
