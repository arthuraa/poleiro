Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Open Scope char_scope.

Definition hexDigitToNat (c : ascii) : option nat :=
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
    | "a" | "A" => Some 10
    | "b" | "B" => Some 11
    | "c" | "C" => Some 12
    | "d" | "D" => Some 13
    | "e" | "E" => Some 14
    | "f" | "F" => Some 15
    | _   => None
  end.

Open Scope string_scope.

Fixpoint readHexNatAux (s : string) (acc : nat) : option nat :=
  match s with
    | "" => Some acc
    | String c s' =>
      match hexDigitToNat c with
        | Some n => readHexNatAux s' (16 * acc + n)
        | None => None
      end
  end.

Definition readHexNat (s : string) : option nat :=
  readHexNatAux s 0.

Example readHexNat1 : readHexNat "ff" = Some 255.
Proof. reflexivity. Qed.

Definition r (s : string) : nat :=
  match readHexNat s with
    | Some n => n
    | None => 0
  end.

Example e1 : r "ff" = 255.
Proof. reflexivity. Qed.

Example e2 : r "1o" = 0.
Proof. reflexivity. Qed.

Definition forceOption {A} (o : option A) : match o with
                                              | Some _ => A
                                              | None => unit
                                            end :=
  match o with
    | Some a => a
    | None => tt
  end.

Definition r' (s : string) :=
  forceOption (readHexNat s).

Example e3 : r' "ff" = 255.
Proof. reflexivity. Qed.

(* Example e4 : r' "1o" = 10. *)
