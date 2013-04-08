Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Notation "x :: y" := (String x y) : string_scope.

Open Scope string_scope.

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

Fixpoint writeNatAux (time n : nat) (acc : string) : string :=
  let acc' := String (natToDigit (n mod 10)) acc in
  match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => writeNatAux time' n' acc'
      end
  end.

Definition writeNat (n : nat) : string :=
  writeNatAux n n "".

Definition writeBool (b : bool) : string :=
  if b then "true" else "false".

Module FirstTry.

Fixpoint printfT (s : string) : Type :=
  match s with
    | "" => string
    | "%" :: s' => printfEscT s'
    | c :: s' => printfT s'
  end
with
printfEscT (s : string) : Type :=
  match s with
    | "" => string
    | "d" :: s' => nat -> printfT s'
    | c :: s' => printfT s'
  end.

Fixpoint printfAux (s : string) (acc : string) {struct s} : printfT s :=
  match s with
    | "" => acc
    | "%" :: s' => printfEscAux s' acc
    | c :: s' => printfAux s' (acc ++ (c :: ""))
  end
with
printfEscAux (s : string) (acc : string) : printfEscT s :=
  match s with
    | "" => (acc ++ "%")
    | "d" :: s' => fun n => printfAux s' (acc ++ writeNat n)
    | c :: s' => printfAux s' (acc ++ (c :: ""))
  end.

End FirstTry.

Inductive printfError := InvalidFormat.

Fixpoint printfT (s : string) : Type :=
  match s with
    | "" => string
    | c :: s' =>
      match c with
        | "%"%char =>
          match s' with
            | "d" :: s'' => nat -> printfT s''
            | "b" :: s'' => bool -> printfT s''
            | "s" :: s'' => string -> printfT s''
            | "c" :: s'' => ascii -> printfT s''
            | "%" :: s'' => printfT s''
            | _ => printfError
          end
        | _ => printfT s'
      end
  end.

Fixpoint printfAux (s : string) (k : string -> string) : printfT s :=
  match s return printfT s with
    | "" => k ""
    | c :: s' =>
      match c return printfT (c :: s') with
        | "%"%char =>
          match s' with
            | "d" :: s'' => fun n => printfAux s'' (fun acc => k (writeNat n ++ acc))
            | "b" :: s'' => fun b => printfAux s'' (fun acc => k (writeBool b ++ acc))
            | "s" :: s'' => fun s => printfAux s'' (fun acc => k (s ++ acc))
            | "c" :: s'' => fun c => printfAux s'' (fun acc => k (c :: acc))
            | "%" :: s'' => printfAux s'' (fun acc => k ("%" ++ acc))
            | _ => InvalidFormat
          end
        | _ => printfAux s' (fun s => k (c :: s))
      end
  end.

Definition printf (s : string) : printfT s :=
  printfAux s (fun s => s).

Eval compute in printfT "asdf%d = %c%%".

Definition s : string := printf "asdf%d = %b" 42 false.

Eval compute in s.
