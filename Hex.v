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
  end.

Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Omega.

Open Scope string_scope.

Fixpoint writeNatAux (time n : nat) (acc : string) : string :=
  match time with
    | 0 => acc
    | S time' =>
      let acc' := String (natToDigit (n mod 10)) acc in
      match n / 10 with
        | 0 => acc'
        | n' => writeNatAux time' n' acc'
      end
  end.

Definition writeNat (n : nat) : string :=
  match n with
    | 0 => "0"
    | _ => writeNatAux n n ""
  end.

Example writeNat1 : writeNat 12 = "12".
Proof. reflexivity. Qed.

Example writeNat2 : writeNat 1 = "1".
Proof. reflexivity. Qed.

Arguments div !x !y.
Arguments modulo x y : simpl never.

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

Theorem digitToNatNatToDigit : forall n : nat,
  n < 10 ->
  digitToNat (natToDigit n) = Some n.
Proof.
  intros n H.
  repeat match goal with
          | n : nat |- _ =>
            destruct n; [reflexivity|try omega]
         end.
Qed.

Theorem writeNatAuxApp :
  forall time n acc1 acc2,
    writeNatAux time n (acc1 ++ acc2) =
    writeNatAux time n acc1 ++ acc2.
Proof.
  induction time as [|time' IH]; intros n acc1 acc2. reflexivity.
  simpl.
  destruct (n / 10) as [|n']. reflexivity.
  rewrite <- IH. reflexivity.
Qed.

Theorem writeNatAuxEmptyString :
  forall time n acc,
    writeNatAux time n acc =
    writeNatAux time n "" ++ acc.
Proof.
  intros time n acc. rewrite <- writeNatAuxApp.
  reflexivity.
Qed.

Theorem readNatAuxWriteNatAux :
  forall time n,
    n <= time ->
    readNatAux (writeNatAux time n "") 0 =
    Some n.
Proof.
  induction time as [|time' IHtime]; intros n H.
  - compute. f_equal. omega.
  - rewrite (div_mod n 10) at 2; try omega.
    cbv delta [writeNatAux] iota beta zeta.
    destruct (n / 10) as [|n'] eqn:En10.
    + { cbv delta [readNatAux] iota beta.
        rewrite digitToNatNatToDigit;
        try apply Nat.mod_upper_bound; try omega.
        trivial. }
    + { rewrite writeNatAuxEmptyString.
        erewrite readNatAuxApp; try eapply IHtime.
        + cbv delta [readNatAux] iota beta.
          rewrite digitToNatNatToDigit. trivial.
          apply Nat.mod_upper_bound; omega.
        + assert (n / 10 < n); try omega.
          apply Nat.div_lt; try omega.
          destruct n; simpl in *; try omega. }
Qed.

Theorem readNatWriteNat :
  forall n, readNat (writeNat n) = Some n.
Proof.
  intros [|n]. reflexivity.
  unfold writeNat, readNat.
  rewrite readNatAuxWriteNatAux; trivial.
Qed.
