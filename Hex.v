Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

(** Many programming languages have built-in support for string
    processing. Coq is no exception. The standard library provides us
    with its own definition of strings. Unlike other languages,
    though, strings in Coq are not special in any way: they are just
    members of another inductive data type. *)

Print string.

(** As we can see, strings are much like the list type, but contain
    ascii elements. *)

Print ascii.

(** asciis, on the other hand, are just eightuples of bools.

    Sure enough, if we had to use constructors explicitly for building
    strings, using them in Coq wouldn't be much
    practical. Fortunately, Coq provides a convenient notation for
    strings and ascii, much like the built-in notation for
    numbers. They are defined in string_scope and char_scope,
    respectively. *)

Open Scope string_scope.

Check "This is a string".

Open Scope char_scope.

Check "b".

Check "1".

(** Let's see what kind of string-processing functions we can
    write. One could certainly hope that we'd be able to write a
    function to read numbers. First, we'll write a function to convert
    from asciis to nat. Since not every character corresponds to a
    digit, our function will be partial -- i.e., the result will be an
    option nat. *)

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

(** We can now use this function to read numbers. The easiest way is
    probably to do it tail recursively: *)

Fixpoint readNatAux (s : string) (acc : nat) : option nat :=
  match s with
    | EmptyString => Some acc
    | String c s' =>
      match digitToNat c with
        | Some n => readNatAux s' (10 * acc + n)
        | None => None
      end
  end.

Definition readNat (s : string) : option nat :=
  readNatAux s 0.

Example readNat1 : readNat "1234" = Some 1234.
Proof. reflexivity. Qed.

Example readNat2 : readNat "asdf" = None.
Proof. reflexivity. Qed.

(** Since we have a function for reading numbers, we should now write
    one for printing them. How could we proceed? The natural approach
    would be to divide the number by 10, print it recursively, and
    then append the remainder of that division at the
    end. Unfortunately, we can't translate this idea directly as a Coq
    fixpoint, since we wouldn't be calling the function recursively on
    a subterm of the original argument. *)

Open Scope string_scope.

Definition natToDigit (n : nat) : string :=
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
  end.

Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Omega.

Fixpoint writeNatAux (n time : nat) : string :=
  match time with
    | 0 => "0"
    | S time' =>
      match n / 10 with
        | 0 => natToDigit (n mod 10)
        | n' => writeNatAux n' time' ++ natToDigit (n mod 10)
      end
  end.

Definition writeNat (n : nat) : string :=
  writeNatAux n n.

Example writeNat1 : writeNat 12 = "12".
Proof. reflexivity. Qed.

Example writeNat2 : writeNat 0 = "0".
Proof. reflexivity. Qed.

Theorem readNatAuxApp : forall s1 s2 n m,
  readNatAux s1 n = Some m ->
  readNatAux (s1 ++ s2) n = readNatAux s2 m.
Proof.
  induction s1 as [|c s1 IHs1]; intros s2 n m H.
  - inversion H. reflexivity.
  - simpl in *.
    destruct (digitToNat c) as [n'|];
    inversion H; eauto.
Qed.

Arguments div !x !y.
Arguments modulo x y : simpl never.

Theorem readNatAuxNatToDigit : forall (n m : nat),
  n < 10 -> readNatAux (natToDigit n) m = Some (10 * m + n).
Proof.
  intros n m H.
  repeat match goal with
          | n : nat |- _ =>
            destruct n; [reflexivity|try omega]
         end.
Qed.

Theorem readNatWriteNatAux :
  forall time n,
    n <= time ->
    readNat (writeNatAux n time) = Some n.
Proof.
  induction time as [|time' IHtime]; intros n H.
  - compute. f_equal. omega.
  - simpl. unfold readNat.
    destruct (n / 10) as [|n'] eqn:En10.
    + { rewrite readNatAuxNatToDigit;
        try apply Nat.mod_upper_bound; try omega.
        rewrite <- En10 at 2.
        rewrite <- div_mod; try omega; trivial. }
    + { unfold readNat.
        erewrite readNatAuxApp; try eapply IHtime.
        + rewrite readNatAuxNatToDigit.
          { rewrite <- En10.
            rewrite <- div_mod; try omega; trivial. }
          apply Nat.mod_upper_bound; omega.
        + assert (n / 10 < n); try omega.
          apply Nat.div_lt; try omega.
          destruct n; simpl in *; try omega. }
Qed.

Theorem readNatWriteNat :
  forall n, readNat (writeNat n) = Some n.
Proof.
  intros n.
  unfold writeNat.
  rewrite readNatWriteNatAux; trivial.
Qed.
