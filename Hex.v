Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Omega.

(** Many programming languages have built-in support for string
    processing. Coq is no exception. The standard library provides us
    with its own definition of strings. Unlike other languages,
    though, strings in Coq are not special in any way: they are just
    members of another inductive data type. *)

Print string.

(** As we can see, [string]s are much like the [list] type, but
    contain [ascii] elements instead of an arbitrary type. *)

Print ascii.

(** [ascii]s, on the other hand, are just eightuples of [bool]s.

    Sure enough, if we had to use constructors explicitly for building
    [string]s, using them in Coq wouldn't be much
    practical. Fortunately, Coq provides a convenient notation for
    [string]s and [ascii], much like the built-in notation for
    numbers. They are defined in [string_scope] and [char_scope],
    respectively. *)

Open Scope string_scope.

Check "This is a string".

Open Scope char_scope.

Check "b".

Check "1".

(** Let's see what kind of string-processing functions we can
    write. One could certainly hope that we'd be able to write a
    function to read numbers. To do this, we will need a function to
    convert [ascii]s to [nat]s: if the character is a digit, we return
    the corresponding number. Otherwise, the whole parsing should
    fail. As in other functional programming languages, we model this
    by making our function return an [option] instead -- in this case,
    [option nat]. *)

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

(** We can now use this function to read numbers. To make it more
    efficient, we can add an [acc] parameter to store the intermediate
    results of the computation -- i.e., the number we've read so far. *)

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

(** Since we have a function for reading numbers, we should now be
    able to write one for printing them. As a first step, let's write
    a function that converts [nat]s to their corresponding digits. *)

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

(** One might think that we should make this function return an
    [option ascii] instead of a plain [ascii], just like we did in our
    previous digitToNat function. After all, it doesn't make any sense
    to associate any digit to, say, 10. *)

(** The natural approach would be to divide the number by 10, print it
    recursively, and then append the remainder of that division at the
    end.

    Unfortunately, we can't translate this idea directly as a Coq
    fixpoint, since we wouldn't be calling the function recursively on
    a subterm of the original argument. There are several tricks *)

Open Scope string_scope.

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

Example writeNat1 : writeNat 12 = "12".
Proof. reflexivity. Qed.

Example writeNat2 : writeNat 0 = "0".
Proof. reflexivity. Qed.

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

Theorem digitToNatNatToDigitMod : forall n : nat,
  digitToNat (natToDigit (n mod 10)) = Some (n mod 10).
Proof.
  intros n. apply digitToNatNatToDigit. apply Nat.mod_upper_bound.
  congruence.
Qed.

Lemma div_10_le : forall n m,
  n <= S m -> n / 10 <= m.
Proof.
  intros [|n] m H. simpl. omega.
  assert (S n / 10 < S n); try omega.
  apply Nat.div_lt; omega.
Qed.

Theorem readNatAuxWriteNatAux :
  forall time n acc,
    n <= time ->
    readNatAux (writeNatAux time n acc) 0 =
    readNatAux acc n.
Proof.
  induction time as [|time' IHtime]; intros n acc H.
  - simpl. inversion H. reflexivity.
  - apply div_10_le in H.
    unfold writeNatAux.
    destruct (n / 10) as [|n'] eqn:En';
    [|rewrite IHtime; auto];
    unfold readNatAux;
    try rewrite digitToNatNatToDigitMod;
    try erewrite (div_mod n 10) at 2; try omega;
    try congruence.
Qed.

Theorem readNatWriteNat :
  forall n, readNat (writeNat n) = Some n.
Proof.
  intros [|n]. reflexivity.
  unfold writeNat, readNat.
  rewrite readNatAuxWriteNatAux; trivial.
Qed.
