(* begin hide *)
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Notation "[ ]" := nil : list_scope.
Notation "x :: y" := (String x y) : string_scope.

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
    expected by [printf] depends on the format parameter passed to it,
    something that is incompatible with most static type systems. In
    C, the problem is solved by allowing funcitons to take a variable
    number of arguments, but there is no way of the type system to
    ensure that the number and types of those arguments match the
    specification given in the format string. OCaml has its own
    version of [printf], which does track the dependencies between the
    format and the rest of the arguments, at the cost of extending the
    language with an _ad-hoc_ format type.

    In this post, we will see how we can use simple dependently typed
    programming in Coq to build a very nice and safe implementation of
    [printf]. *)

(** ** Directives and format

    We will begin our implementation by expressing what a [printf]
    format is. In C, a [printf] format is just a string, which makes
    writing them very easy. As a crude approximation to the C
    interface, a [printf] format is just a string with a sequence of
    directives marked by [%] characters. We will model literal strings
    and directives as a separate data type, and a format will be just
    a sequence of directives. *)

Inductive directive : Type :=
| DLit : ascii -> directive
| DNum : option nat -> directive
| DBool : directive
| DString : directive
| DChar : directive.

Definition format := list directive.

(** Constructors [DBool], [DString] and [DChar] just signal that we
    will output an element of the corresponding type. [DLiteral c]
    just prints the constant character [c]. Finally, [DNum s] is used
    to output numbers (i.e., Coq [nat]s) according to the [s]
    parameter. If [s = Some n], then we output exactly the [n]
    least-significant digits of the number, padding it with zeros if
    necessary. Otherwise, we just print the whole number.

    Given that definition, we can write a Coq function that takes a
    [format] (i.e., a sequence of directives) and computes the
    corresponding Coq type. *)

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

(** All directives add an additional argument to the type, except for
    [DLit], whose behavior is already fully determined by its
    immediate argument. *)

(** ** A first implementation

    Now that we can express the type for a [format], we can code a
    first implementation of [printf]. *)

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
      let acc' := natToDigit (n mod 10) :: acc in
      match n / 10 with
        | 0 => if crop then acc'
               else writeNatAux time' 0 crop acc'
        | n' => writeNatAux time' n' crop acc'
      end
  end.

Definition writeNat (n : nat) : string :=
  writeNatAux (S n) n true "".

Definition writeNatSize (size : nat) (n : nat) : string :=
  writeNatAux size n false "".

Definition writeBool (b : bool) : string :=
  if b then "true" else "false".
(* end hide *)

Fixpoint printfImpl (f : format) (acc : string) : formatType f :=
  match f with
    | [] => acc
    | (dir :: dirs)%list =>
      match dir return formatType (dir :: dirs)%list with
        | DLit c => printfImpl dirs (acc ++ c :: "")
        | DNum o => fun n =>
                      printfImpl dirs
                                 match o with
                                   | Some size => acc ++ writeNatSize size n
                                   | None => acc ++ writeNat n
                                 end
        | DBool => fun b => printfImpl dirs (acc ++ writeBool b)
        | DString => fun s => printfImpl dirs (acc ++ s)
        | DChar => fun c => printfImpl dirs (acc ++ c :: "")
      end
  end.

(** The first argument [f] is just the format that we are using,
    whereas the extra [acc] argument is just an auxiliary variable to
    store the [string] produced so far. The result of the function,
    [formatType f], ensures that the function will be able to take the
    arguments we want it to depending on which format was passed to
    it.

    Notice how the structure of the pattern-matching is very close to
    the one used to define [formatType]. This is done to make it
    easier for Coq to infer and check the types. Unfortunately,
    inference is not powerful enough to figure out everything on its
    own, so we need to add a type annotation for the second
    pattern-matching. *)

Definition consOpt {A} (x : A) (o : option (list A)) : option (list A) :=
  match o with
    | Some xs => Some (x :: xs)%list
    | None => None
  end.

Fixpoint parseFormat (s : string) : option format :=
  match s with
    | "" => Some []
    | "%" :: s' =>
      match s' with
        | "%" :: s'' => consOpt (DLit "%"%char) (parseFormat s'')
        | "b" :: s'' => consOpt DBool (parseFormat s'')
        | "s" :: s'' => consOpt DString (parseFormat s'')
        | "c" :: s'' => consOpt DChar (parseFormat s'')
        | _ => parseFormatSize s' 0
      end
    | c :: s' =>
      consOpt (DLit c) (parseFormat s')
  end

with parseFormatSize (s : string) (acc : nat) : option format :=
       match s with
         | "" => None
         | "d" :: s' => consOpt (DNum (Some acc)) (parseFormat s')
         | c :: s' =>
           match digitToNat c with
             | Some n => parseFormatSize s' (10 * acc + n)
             | None => None
           end
       end.

Inductive printfError := InvalidFormat.

Definition printfT (s : string) : Type :=
  match parseFormat s with
    | Some f => formatType f
    | None => printfError
  end.

Definition printf (s : string) : printfT s :=
  match parseFormat s as o
                      return match o with
                               | Some f => formatType f
                               | None => printfError
                             end
  with
    | Some f => printfImpl f ""
    | None => InvalidFormat
  end.

Eval compute in printf "Hello, I'm %s and I am %2d years old" "Arthur" 2.
