(* begin hide *)
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Notation "[ ]" := nil : list_scope.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..) : list_scope.
Notation "x ::: y" := (String x y)
                        (at level 60, right associativity) : string_scope.

Open Scope list_scope.
Open Scope char_scope.
(* end hide *)

(** The widespread [printf] family of functions offers a very
    convenient interface for formatted output. While the function
    itself originated in the C programming language, the idea of
    having formatted output controlled by a parameter predates it, and
    functions with similar interfaces are present in other
    languages, such as the [format] function in Common Lisp.

    In spite of being so popular, adding a [printf]-like function may
    be significantly challenging. The number and types of arguments
    expected by [printf] depend on the format parameter passed to it,
    something that is incompatible with many static type systems. In
    C, the problem is solved by allowing funcitons to take a variable
    number of arguments, but there is no way for the type system to
    ensure that the number and types of those arguments match the
    specification given in the format string. OCaml has its own
    version of [printf], which does track the dependencies between the
    format and the rest of the arguments, at the cost of extending the
    language with an _ad-hoc_ format type.

    In this post, we will see how we can use simple dependently typed
    programming in Coq to build a very nice and safe implementation of
    [printf]. *)

(** ** Directives and format

    The power of [printf] comes from how succint strings are for
    writing output formats. The format argument looks very similar to
    the final output that we expect, which makes calls to the function
    very easy to understand.

    Even though we want to use Coq [string]s for the format argument,
    it is more convenient to first implement [printf] using a separate
    [format] type. In the final implementation, we will parse the
    [string] argument as a [format] and pass it to that function.

    In C, a [printf] format is a sequence of _directives_. Each
    directive can be either a literal character, which will be printed
    verbatim, or a _control sequence_, which instructs the function to
    print one of its arguments in a certain format. For our version of
    [printf] we will consider a small set of control sequences, based
    roughly on the ones available in C. *)

Inductive directive : Type :=
| DLit : ascii -> directive
| DNum : option nat -> directive
| DBool : directive
| DString : directive
| DChar : directive.

Definition format := list directive.

(** Directive [DLit c] corresponds to the literal character
    [c]. [DBool], [DString] and [DChar] signal that we will output an
    element of the corresponding type.  More interestingly, [DNum s]
    is used to output numbers (i.e., Coq [nat]s). The [s] parameter
    controls the length of the number we will print. If [s = Some n],
    then we output exactly the [n] least-significant digits of the
    number, padding it with zeros if necessary. Otherwise, if [s =
    None], we just print the whole number.

    Given a format [f], we can compute the type that [printf f] should
    have as follows: *)

Fixpoint formatType (f : format) : Type :=
  match f with
    | [] => string
    | dir :: dirs =>
      match dir with
        | DLit _ => formatType dirs
        | DNum _ => nat -> formatType dirs
        | DBool => bool -> formatType dirs
        | DString => string -> formatType dirs
        | DChar => ascii -> formatType dirs
      end
  end%list.

(** Notice that all directives except [DLit] add an argument to the
    type.

    ** The implementation

    Now that we can express the type for a [format], we can try to
    implement [printf]. As a first attempt, we might try something
    like this:

[[
Fixpoint printfImpl (f : format) : formatType f :=
  match f with
    | [] => ""
    | dir :: dirs =>
      match dir with
        | DLit c => c :: printfImpl dirs
        (* ... *)
      end
  end.
]]

    Alas, this approach doesn't work. The problem here is that our
    recursive call to [printfImpl] returns a [formatType dirs] instead
    of a [string], which means that we are unable to add character [c]
    in front of it.

    Instead of building the string directly on the body of the match,
    we will add an auxiliary parameter [k] to [printfImpl]. To make it
    more efficient, this parameter will be a _continuation_ of type
    [string -> string] that builds the final output from the result of
    the recursive calls. For brevity, I've omitted the definition of
    some auxiliary functions, such as [writeNat], but they can be
    found in the original [.v] file. *)

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

Fixpoint printfImpl (f : format) (k : string -> string) : formatType f :=
  match f with
    | [] => k ""
    | dir :: dirs =>
      match dir return formatType (dir :: dirs) with
        | DLit c => printfImpl dirs (fun res => k (c ::: res))
        | DNum o =>
          fun n =>
            let k' := match o with
                        | Some size => fun res => k (writeNatSize size n res)
                        | None => fun res => k (writeNat n res)
                      end in
            printfImpl dirs k'
        | DBool =>
          fun b =>
            printfImpl dirs (fun res => k (writeBool b ++ res))
        | DString =>
          fun s =>
            printfImpl dirs (fun res => k (s ++ res))
        | DChar =>
          fun c =>
            printfImpl dirs (fun res => k (c ::: res))
      end
  end.

(** Our implementation mimics the definition of [formatType], to
    ensure that the types will match accordingly. Notice that it is
    still necessary to annotate the return type of the second [match]
    explicitly, because Coq is not able to infer it.

    To use [printfImpl], we just have to pass it the identity
    continuation [fun res => res], that will receive the value built
    by [printfImpl] and return it as-is. *)

Example printfImpl1 :
  printfImpl [DNum None, DString] (fun res => res)
             42 "This is a string" = "42This is a string".
Proof. reflexivity. Qed.

Example printfImpl2 :
  printfImpl [DNum (Some 2), DLit "/", DNum (Some 2)] (fun res => res)
             2 4 = "02/04".
Proof. reflexivity. Qed.

(** ** Strings as format

    Now that we have our first implementation, we will write the code
    needed to parse the format from a [string]. Our format syntax is
    inspired by C's own syntax. All characters are interpreted
    literally, except for [%], which signals the beginning of a
    control sequence. As in C, we can write [%<n>d], where [<n>] is a
    number, to specify how many digits we want when printing a [nat].

    The [parseFormat] function below tries to read a [format],
    returning [Some f] if the [string] argument represents [f], and
    [None] if there was a parse error. [parseFormatSize] is used to
    read the [%<n>d] directives. *)

Definition snocK (k : format -> format) (dir : directive) : format -> format :=
  fun res => k (dir :: res).

Fixpoint parseFormat (s : string) (k : format -> format) : option format :=
  match s with
    | "" => Some (k [])
    | "%" ::: s' =>
      match s' with
        | "%" ::: s'' => parseFormat s'' (snocK k (DLit "%"))
        | "b" ::: s'' => parseFormat s'' (snocK k DBool)
        | "s" ::: s'' => parseFormat s'' (snocK k DString)
        | "c" ::: s'' => parseFormat s'' (snocK k DChar)
        | "d" ::: s'' => parseFormat s'' (snocK k (DNum None))
        | _ => parseFormatSize s' k 0
      end
    | c ::: s' => parseFormat s' (snocK k (DLit c))
  end

with parseFormatSize (s : string) (k : format -> format) (acc : nat) : option format :=
       match s with
         | "" => None
         | "d" ::: s' => parseFormat s' (snocK k (DNum (Some acc)))
         | c ::: s' =>
           match digitToNat c with
             | Some n => parseFormatSize s' k (10 * acc + n)
             | None => None
           end
       end.

(** We can test our function in some simple cases. *)

Example parseFormat1 :
  parseFormat "%d%4da" (fun res => res) =
  Some [DNum None, DNum (Some 4), DLit "a"].
Proof. reflexivity. Qed.

(** ** Putting the pieces together

    Using [parseFormat], we can write a convenient wrapper for
    [printfImpl]. We can use the same trick as
    #<a href="/posts/2013-04-03-parse-errors-as-type-errors.html">before</a># to
    ensure that invalid format strings will be noticed right away. *)

Inductive printfError := InvalidFormat.

Definition printfT (s : string) : Type :=
  match parseFormat s (fun res => res) with
    | Some f => formatType f
    | None => printfError
  end.

Definition printf (s : string) : printfT s :=
  match parseFormat s (fun res => res) as o
                      return match o with
                               | Some f => formatType f
                               | None => printfError
                             end
  with
    | Some f => printfImpl f (fun res => res)
    | None => InvalidFormat
  end.

Definition greet s d m y :=
  printf "Hello %s, your birthday is %2d/%2d/%d." s d m y : string.

Eval compute in greet "Arthur" 2 12 2012.

Eval vm_compute in printf "Hello, I'm %s and I am %2d years old" "Arthur" 2.
