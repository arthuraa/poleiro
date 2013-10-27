(* begin hide *)
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Numbers.Natural.Peano.NPeano.
(* end hide *)
(** Many languages provide mechanisms for formatted output, with C's
[printf] undoubtedly being the most influential one. Some of these
functions allow a format to be specified using a concise and intuitive
syntax, which is probably part of the reason for them being so
popular. For [printf], for instance, a format is described using just
a plain string.

Unfortunately, this convenience often comes with a price. In C, a
mismatch between the output format and the other arguments results in
incorrect behavior. This non-trivial dependency can't be expressed in
the language's type system and requires additional compiler checks to
be enforced. Other languages suffer from similar problems. Haskell's
standard [printf] also causes a run-time error when a format mismatch
occurs. OCaml is able to enforce that format and arguments are
compatible at compile-time, but at the cost of extending the language
with an _ad-hoc_ [format] type that is also represented as
strings. Other approaches solve the problem by adopting different
representations for the output format, which can make it slightly less
convenient to specify. In #<a
href="http://www.brics.dk/RS/98/12/BRICS-RS-98-12.pdf">Functional
Unparsing</a>#, Olivier Danvy showed how to implement an analogue of
[printf] using formatting combinators. More recently, Oleg Kieslyov
used delimited control operators to implement his own type-safe
version of [printf] in #<a
href="http://okmij.org/ftp/Haskell/ShiftResetGenuine.hs">Haskell</a>#,
an idea that has also been ported to #<a
href="http://mattam.org/repos/coq/misc/shiftreset/GenuineShiftReset.html">Coq</a>#
by Matthieu Sozeau.

It would be a shame if we had to extend our language in an _ad-hoc_
manner just to get safe and convenient formatting. We will see how we
can use Coq's expressive type system to describe the dependency
between a format string and the arguments it requires, and implement a
version of [sprintf] that doesn't suffer from the aforementioned
issues.

Let's begin by defining some useful notations for lists and
strings. *)

Notation "[ ]" := nil : list_scope.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..) : list_scope.
Notation "x ::: y" := (String x y)
                        (at level 60, right associativity) : string_scope.

Open Scope list_scope.
Open Scope char_scope.

(** ** Directives and format

Before working directly with strings, we will define a new data type
to describe an output format, and then use it to implement a
preliminary version of [sprintf]. As we shall see, this will help us
express the not-so-trivial type of [sprintf] and simplify our
implementation. Later, we will write a separate function to convert
[string]s to this new type, and combine both programs to obtain our
final result.

Our [format] type is inspired by [printf] formats in C, which can be
seen as a sequence of _directives_. Each directive can be either a
literal character, to be printed verbatim, or a _control sequence_,
which instructs the function to print one of its arguments in a
certain format. Thus, we begin by defining a [directive] type, loosely
based upon what is available in C: *)

Inductive directive : Type :=
| DLit : ascii -> directive
| DNum : option nat -> directive
| DBool : directive
| DString : directive
| DChar : directive.

(** Directive [DLit c] outputs the literal character [c], while [DNum
s], [DBool], [DString], and [DChar] take an argument of the
corresponding type and print it. The [s] field of [DNum s] controls
how its argument should be printed. If [s = Some n], then we output
exactly the [n] least-significant digits of the number, padding it
with zeros if necessary. Otherwise, if [s = None], we just print the
whole number. Thus, the number [4] should be printed as [4] using the
[DNum None], but as [04] using [DNum (Some 2)].

With the [directive] type in hand, defining [format] is
straightforward: *)

Definition format := list directive.

(** ** Relating format and arguments

As noted above, [sprintf f] should be a function that returns a
[string] and takes one argument for each directive in [f] that
requires one. For instance, [sprintf [DBool, DString]] should have
type [bool -> string -> string], whereas [sprintf [DLit "a", DLit "b",
DNum None]] should have type [nat -> string].

This relation is easy to express in Coq using dependent types. Since
types can be the result of computations, it is possible to write a
[formatType] function that takes a [format] [f] and returns the type
of [sprintf f]. Let's begin by defining a function that maps each
directive to the corresponding argument type. Notice that its result
type must be an [option], since [DLit] doesn't need arguments. *)

Definition directiveType (dir : directive) :=
  match dir with
    | DLit _ => None
    | DNum _ => Some nat
    | DBool => Some bool
    | DString => Some string
    | DChar => Some ascii
  end.

(** Now, [formatType] itself is just a direct translation of what we
stated above. *)

Fixpoint formatType (f : format) : Type :=
  match f with
    | [] => string
    | dir :: dirs =>
      match directiveType dir with
        | Some T => T -> formatType dirs
        | None => formatType dirs
      end
  end.

(** We can check if this definition makes sense on simple examples. *)

Example formatTypeTest1 : formatType [DBool, DString] =
                          (bool -> string -> string).
Proof. reflexivity. Qed.

Example formatTypeTest2 : formatType [DLit "a", DLit "b", DNum None] =
                          (nat -> string).
Proof. reflexivity. Qed.

(** ** The implementation

Now that we can express the type of [sprintf], we can try to implement
it. We might be tempted to try something like this:

[[
Fixpoint sprintf (f : format) : formatType f :=
  match f with
    | [] => ""
    | dir :: dirs =>
      match dir with
        | DLit c => c ::: sprintf dirs
        (* ... *)
      end
  end.
]]

Alas, this approach doesn't work. The problem here is that our
recursive call to [sprintf] returns a [formatType dirs] instead of
a [string], which means that we are unable to add character [c] in
front of it.

Instead of building the string directly on the body of the match, we
will add an auxiliary parameter [k] to [sprintf]. [k] will be a
_continuation_ of type [string -> string] that builds the final output
using the result of the recursive calls. The implementation uses some
auxiliary functions, such as [writeNat], that have been omitted in the
interest of space. Their definitions can be found in the original [.v]
file. *)

(* begin hide *)
Definition digitToNat (c : ascii) : option nat :=
  match c with
    | "0" => Some 0
    | "1" => Some 1
    | "2" => Some 2
    | "3" => Some 3
    | "4" => Some 4
    | "5" => Some 5
    | "6" => Some 6
    | "7" => Some 7
    | "8" => Some 8
    | "9" => Some 9
    | _   => None
  end.

Definition natToDigit (n : nat) : ascii :=
  match n with
    | 0 => "0"
    | 1 => "1"
    | 2 => "2"
    | 3 => "3"
    | 4 => "4"
    | 5 => "5"
    | 6 => "6"
    | 7 => "7"
    | 8 => "8"
    | _ => "9"
  end%char.

Open Scope string_scope.

Fixpoint writeNatAux (time n : nat) (crop : bool) (acc : string) : string :=
  match time with
    | 0 => acc
    | S time' =>
      let acc' := natToDigit (n mod 10) ::: acc in
      match n / 10 with
        | 0 => if crop then acc'
               else writeNatAux time' 0 crop acc'
        | n' => writeNatAux time' n' crop acc'
      end
  end.

Definition writeNat (n : nat) (acc : string) : string :=
  writeNatAux (S n) n true acc.

Definition writeNatSize (size : nat) (n : nat) (acc : string) : string :=
  writeNatAux size n false acc.

Definition writeBool (b : bool) : string :=
  if b then "true" else "false".
(* end hide *)

Module Internal.

Fixpoint sprintf (f : format) (k : string -> string) : formatType f :=
  match f with
    | [] => k ""
    | dir :: dirs =>
      match dir return formatType (dir :: dirs) with
        | DLit c => sprintf dirs (fun res => k (c ::: res))
        | DNum o =>
          fun n =>
            let k' := match o with
                        | Some size => fun res => k (writeNatSize size n res)
                        | None => fun res => k (writeNat n res)
                      end in
            sprintf dirs k'
        | DBool =>
          fun b =>
            sprintf dirs (fun res => k (writeBool b ++ res))
        | DString =>
          fun s =>
            sprintf dirs (fun res => k (s ++ res))
        | DChar =>
          fun c =>
            sprintf dirs (fun res => k (c ::: res))
      end
  end.

(** Most directives generate an additional argument to [sprintf] by
wrapping the recursive call with an anonymous function. Also, notice
the type annotation on the inner [match]: [return formatType (dir ::
dirs)]. As one could hope, this mysterious expression is telling Coq
which type is being returned on each branch of the [match]. Dependent
types require more sophisticated type inference, and in some cases it
is necessary to provide these annotations explicitly.

To use [sprintf], we just have to pass it the identity continuation
[fun res => res], which will receive the value built by [sprintf] and
return it as-is. *)

Example sprintfTest1 :
  sprintf [DNum None, DString] (fun res => res)
          42 "This is a string" = "42This is a string".
Proof. reflexivity. Qed.

Example sprintfTest2 :
  sprintf [DNum (Some 2), DLit "/", DNum (Some 2)] (fun res => res)
          2 4 = "02/04".
Proof. reflexivity. Qed.

End Internal.

(** ** Strings as format

Now that we have our first implementation, we will write the code
needed to parse the format from a [string]. Our format syntax is
inspired by C's own syntax. All characters are interpreted literally,
except for [%], which signals the beginning of a control sequence. As
in C, we can write [%<n>d], where [<n>] is a number, to specify how
many digits we want when printing a [nat].

The [parseFormat] function below tries to read a [format], returning
[Some f] if the [string] argument represents [f], and [None] if there
was a parse error. [parseFormatSize] is used to read the [%<n>d]
directives. The auxiliary function [addDir] adds a directive to an
[option format] when possible, returning [None] otherwise. *)

Definition addDir (o : option format) (dir : directive) : option format :=
  match o with
    | Some f => Some (dir :: f)
    | None => None
  end.

Fixpoint parseFormat (s : string) : option format :=
  match s with
    | "" => Some []
    | "%" ::: s' =>
      match s' with
        | "%" ::: s'' => addDir (parseFormat s'') (DLit "%")
        | "b" ::: s'' => addDir (parseFormat s'') DBool
        | "s" ::: s'' => addDir (parseFormat s'') DString
        | "c" ::: s'' => addDir (parseFormat s'') DChar
        | "d" ::: s'' => addDir (parseFormat s'') (DNum None)
        | _ => parseFormatSize s' 0
      end
    | c ::: s' =>
      addDir (parseFormat s') (DLit c)
  end

with parseFormatSize (s : string) (acc : nat) : option format :=
       match s with
         | "" => None
         | "d" ::: s' => addDir (parseFormat s') (DNum (Some acc))
         | c ::: s' =>
           match digitToNat c with
             | Some n => parseFormatSize s' (10 * acc + n)
             | None => None
           end
       end.

(** We can test our function in some simple cases. *)

Example parseFormatTest1 :
  parseFormat "%d%4da" = Some [DNum None, DNum (Some 4), DLit "a"].
Proof. reflexivity. Qed.

Example parseFormatTest2 :
  parseFormat "%ca%s%" = None.
Proof. reflexivity. Qed.

Example parseFormatTest3 :
  parseFormat "%s%b" = Some [DString, DBool].
Proof. reflexivity. Qed.

(** ** Putting the pieces together

Using [parseFormat], we can now write a convenient wrapper for our
first [sprintf]. Just as we did in the #<a
href="/posts/2013-04-03-parse-errors-as-type-errors.html">previous
post</a>#, we ensure that invalid format strings are detected right
away by producing a value of a different type when we hit a parse
error. *)

Inductive printfError := InvalidFormat.

Definition sprintfOpt (o : option format) : match o with
                                              | Some f => formatType f
                                              | None => printfError
                                            end :=
  match o with
    | Some f => Internal.sprintf f (fun res => res)
    | None => InvalidFormat
  end.

Definition sprintf (s : string) := sprintfOpt (parseFormat s).

(** Despite its intricate type, using our function is simple, as the
examples below show. *)

Definition greet name y m d : string :=
  sprintf "Hello %s, today is %d/%2d/%2d" name y m d.

Example greetTest1 : greet "readers" 2013 4 19 =
                     "Hello readers, today is 2013/04/19".
Proof. reflexivity. Qed.

Definition tableRow name value : string :=
  sprintf "<tr><td>%s</td><td>%b</td></tr>" name value.

Example tableRowTest1 : tableRow "x1" true =
                        "<tr><td>x1</td><td>true</td></tr>".
Proof. reflexivity. Qed.

(** Trying to pass the wrong number of arguments to [sprintf], or
giving it arguments of the wrong type, will result in a type error. *)

(* Example greetTest2 : string := greet 2013 4 19 "readers". *)

(* Error: The term "2013" has type "nat" while it is expected to have type
  "string". *)

(* Example tableRowTest2 : string := tableRow "x1". *)

(* Error: The term "tableRow "x1"" has type "bool -> string"
   while it is expected to have type "string". *)

(** ** Summary

We've seen how to implement a type-safe version of [sprintf] in
Coq. Unlike other approaches to the problem, our solution did not
require abandoning strings for specifying formats, nor relies on any
special extensions to the language. Type computation and dependent
types, the key ingredients in our implementation, are powerful
general-purpose features that lie at the heart of Coq. *)
