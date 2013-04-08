Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Notation "[ ]" := nil : list_scope.
Notation "x :: y" := (String x y) : string_scope.

Open Scope list_scope.
Open Scope char_scope.

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

Inductive directive : Type :=
| DLit : ascii -> directive
| DNum : option nat -> directive
| DBool : directive
| DString : directive
| DChar : directive.

Definition format := list directive.

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
