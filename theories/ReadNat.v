(* begin hide *)
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Omega.
(* end hide *)
(** Many programming languages have built-in support for string
    processing. Coq is no exception. The standard library provides us
    with its own definition of strings. Unlike other languages,
    though, strings in Coq are not fundamentally different from other
    data types: they are defined as an inductive type. *)

Print string.

(* Inductive string : Set :=
      EmptyString : string | String : ascii -> string -> string *)

(** As we can see, [string]s are much like the [list] type, but
    contain [ascii] elements instead of elements of an arbitrary
    type. [ascii]s, on the other hand, are just eightuples of
    [bool]s. *)

Print ascii.

(* Inductive ascii : Set :=
      Ascii : bool ->
              bool -> bool -> bool -> bool -> bool -> bool -> bool -> ascii *)

(** Sure enough, if we had to use constructors explicitly for building
    [string]s, using them in Coq wouldn't be very
    practical. Fortunately, Coq provides a convenient notation for
    [string]s and [ascii], much like the built-in notation for
    numbers. They are defined in [string_scope] and [char_scope],
    respectively. *)

Open Scope string_scope.
Example stringEx : string := "This is a string".

Open Scope char_scope.
Example asciiEx : ascii := "a".

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

Open Scope string_scope.

Fixpoint readNatAux (s : string) (acc : nat) : option nat :=
  match s with
    | "" => Some acc
    | String c s' =>
      match digitToNat c with
        | Some n => readNatAux s' (10 * acc + n)
        | None => None
      end
  end.

Definition readNat (s : string) : option nat :=
  readNatAux s 0.

(** We can write some unit tests to make sure our function behaves as
    expected. *)

Example readNat1 : readNat "1234" = Some 1234.
Proof. reflexivity. Qed.

Example readNat2 : readNat "asdf" = None.
Proof. reflexivity. Qed.

(** Since we have a function for reading numbers, we should now be
    able to write one for printing them. Again, as a first step, let's
    write a function that converts [nat]s to their corresponding
    digits. *)

Open Scope char_scope.

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

(** In all rigor, [natToDigit] should return an [option ascii] instead
    of a plain [ascii], just like we did in our previous digitToNat
    function. After all, it doesn't make any sense to associate any
    digit to, say, 10. However, if we make sure that we only use this
    function on numbers less than 10, we don't have to do an explicit
    conversion from [option ascii] to [ascii] later on, and our
    function will still be correct. As a matter of fact, we can now
    prove a theorem that tells us when it's safe to use [natToDigit]. *)

Theorem digitToNatNatToDigit : forall n : nat,
  n < 10 ->
  digitToNat (natToDigit n) = Some n.
Proof.
  intros n H.

  (* H ensures that we only have to check the cases from n = 0 to
     9. We can do this very easily by using a "repeat match" where we
     do a case analysis on n until the H hypothesis becomes
     contradictory. *)

  repeat match goal with
          | n : nat |- _ =>
            destruct n; [reflexivity|try omega]
         end.

Qed.

(** In particular, we get the following consequence, which will be
    particularly useful later: *)

Theorem digitToNatNatToDigitMod : forall n : nat,
  digitToNat (natToDigit (n mod 10)) = Some (n mod 10).
Proof.
  intros n. apply digitToNatNatToDigit.
  apply Nat.mod_upper_bound.
  congruence.
Qed.

(** Now that we can convert numbers to digits, let's see how we could
    write our printing function. One idea would be to add a parameter
    to our function to accumulate the paritially printed number:

[[
    Fixpoint writeNatAux (n : nat) (acc : string) : string :=
      let acc' := String (natToDigit (n mod 10)) acc in
      match n / 10 with
        | 0 => acc'
        | n' => writeNatAux n' acc'
      end.
]]

    The algorithm is straightforward. We print the least signigicant
    digit of the number, adding it to the string we've printed so far
    (recall that the [String] constructor adds a character to the
    front of a [string]). Then, we divide the number by 10 and print
    it recursively, until we reach zero.

    Unfortunately, Coq doesn't accept this definition, since the
    recursive call is not done on structurally smaller terms. There
    are lots of ways to make this definition work, such as using the
    [Program] command. We will use the somewhat simpler, but standard,
    trick of adding an explicit "timeout" parameter to our
    function. *)


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

(** At each step, we do a pattern match on the timeout parameter. If
    we reach 0, our computation must stop, and we just give back the
    [string] we've printed so far. Otherwise, we have a structurally
    smaller argument we can use to do a recursive call, which will
    make Coq accept the definition.

    Now, in order to effectively print a number, we need to find a
    timeout value that is big enough to perform the entire
    computation. In this case, as it turns out, we can use the very
    the number we're printing for the timeout parameter. *)

Open Scope string_scope.

Definition writeNat (n : nat) : string :=
  writeNatAux n n "".

(** Let's test our definition on some simple examples. *)

Example writeNat1 : writeNat 12 = "12".
Proof. reflexivity. Qed.

Example writeNat2 : writeNat 0 = "0".
Proof. reflexivity. Qed.

(** It seems clear that [readNat] is indeed the inverse of [writeNat],
    but can we prove this rigorously in Coq? Formally, we can state
    the theorem we want as *)

Definition readNatWriteNatStatement :=
  forall n, readNat (writeNat n) = Some n.

(** Since both functions are defined in terms of auxiliary fixpoints,
    it is better to prove something about them first and then use that
    fact to get the result we want as a consequence. Here's one such
    possibility: *)

Definition readNatAuxWriteNatAuxStatement :=
  forall time n acc,
    n <= time ->
    readNatAux (writeNatAux time n acc) 0 =
    readNatAux acc n.

(** Notice the precondition [n <= time] in the above statement. As
    mentioned before, we must give enough time to [writeNatAux] for it
    to function correctly. This precondition is just stating this fact
    explicitly.

    It is easy to prove that this lemma will suffice. *)

Theorem readNatWriteNat' :
  readNatAuxWriteNatAuxStatement ->
  readNatWriteNatStatement.
Proof.
  unfold readNatAuxWriteNatAuxStatement, readNatWriteNatStatement.
  unfold readNat, writeNat.
  intros H n.
  rewrite H; trivial.
Qed.

(** Now, we are ready to prove our intermediate lemma. As usual, since
    [writeNatAux] is defined by recursion on [time], trying the proof
    by induction on [time] seems a good guess. Let's begin with a
    simple lemma that will be useful later. It states that if the
    precondition for our lemma is satisfied, then it'll also be
    satisfied for the recursive call, which will allow us to apply the
    induction hypothesis. *)

Lemma div_10_le : forall n time,
  n <= S time -> n / 10 <= time.
Proof.
  intros [|n] time H. simpl. omega.
  assert (S n / 10 < S n); try omega.
  apply Nat.div_lt; omega.
Qed.

(** We can proceed with our proof. *)

Lemma readNatAuxWriteNatAux : readNatAuxWriteNatAuxStatement.
Proof.

  induction time as [|time' IHtime]; intros n acc H.

  (* The base case is where the inductive hypothesis is crucial, since it
     forces n to be 0. *)

  - simpl. inversion H. reflexivity.

  (* The inductive case is slightly trickier, but not too hard. We
     start by applying our previous lemma. *)

  - apply div_10_le in H. unfold writeNatAux.

    (* To simplify the goal, we need to do some case analysis on (n /
       10). *)

    destruct (n / 10) as [|n'] eqn:En';

    (* We do a recursive call in the non-zero case, and that's where we will
       need our induction hypothesis. *)

    [|rewrite IHtime; auto]; unfold readNatAux;

    (* Finally, we need the digitToNatNatToDigitMod lemma to show that
       readNatAux doesn't fail, and the div_mod theorem (defined in the
       standard library) to express n in terms of (n / 10) and (n mod 10).
       omega and congruence can easily take care of the end. *)

    try rewrite digitToNatNatToDigitMod;
    try rewrite (div_mod n 10) at 2; try omega;
    congruence.

Qed.

(** The final result follows easily. *)

Theorem readNatWriteNat : readNatWriteNatStatement.
Proof.
  apply readNatWriteNat'.
  apply readNatAuxWriteNatAux.
Qed.
