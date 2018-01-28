(* begin hide *)
From Coq Require Import ssreflect ssrfun.
(* end hide *)
(** Coq views truth through the lens of provability.  The hypotheses it
    manipulates are not mere assertions of truth, but _formal proofs_ of the
    corresponding statements -- data structures that can be inspected to build
    other proofs.  It is not a coincidence that function types and logical
    implication use the same notation, [A -> B], because proofs of implication
    in Coq _are_ functions: they take proofs of the precondition as inputs and
    return a proof of the consequent as the output.  Such proofs are written
    with the same language we use for programming in Coq; tactics are but
    scripts that build such programs for us.  A proof that implication is
    transitive, for example, amounts to function composition. *)

Definition implication_is_transitive (A B C : Prop) :
  (A -> B) -> (B -> C) -> (A -> C) :=
  fun HAB HBC HA => HBC (HAB HA).

(** Similarly, inductive propositions in Coq behave just like algebraic data
    types in typical functional programming languages.  With pattern matching,
    we can check which constructor was used in a proof and act accordingly. *)

Definition or_false_r (A : Prop) : A \/ False -> A :=
  fun (H : A \/ False) =>
    match H with
    | or_introl HA     => HA
    | or_intror contra => match contra with end
    end.

(** Disjunction [\/] is an inductive proposition with two constructors,
    [or_introl] and [or_intror], whose arguments are proofs of its left and
    right sides.  In other words, a proof of [A \/ B] is either a proof of [A]
    or a proof of [B].  Falsehood, on the other hand, is an inductive
    proposition with no constructors.  Matching on a proof of [False] does not
    require us to consider any cases, thus allowing the expression to have any
    type we please.  This corresponds to the so-called #<a
    href="https://en.wikipedia.org/wiki/Principle_of_explosion">principle of
    explosion</a>#, which asserts that from a contradiction, anything follows.

    The idea of viewing proofs as programs is known as the #<a
    href="https://en.wikipedia.org/wiki/Curry-Howard_correspondence">Curry-Howard
    correspondence</a>#.  It has been a fruitful source of inspiration for the
    design of many other logics and programming languages beyond Coq, other
    noteworthy examples including #<a
    href="https://en.wikipedia.org/wiki/Agda_(programming_language)">Agda</a>#
    and #<a href="https://en.wikipedia.org/wiki/Nuprl">Nuprl</a>#.  I will
    discuss a particular facet of this correspondence in Coq: the meaning of a
    proof of equality.

    ** Defining equality

    The Coq standard library defines equality as an indexed inductive
    proposition. (The familiar [x = y] syntax is provided by the standard
    library using Coq's notation mechanism.) *)

(* begin hide *)
Module HideEquality.
(* end hide *)
Inductive eq (T : Type) (x : T) : T -> Prop :=
| eq_refl : eq T x x.
(* begin hide *)
End HideEquality.
(* end hide *)

(** This declaration says that the most basic way of showing [x = y] is when [x]
    and [y] are the "same" term -- not in the strict sense of syntactic
    equality, but in the more lenient sense of equality "up to computation" used
    in Coq's theory.  For instance, we can use [eq_refl] to show that [1 + 1 =
    2], because Coq can simplify the left-hand side using the definition of [+]
    and arrive at the right-hand side.

    To prove interesting facts about equality, we generally use the [rewrite]
    tactic, which in turn is implemented by pattern matching.  Matching on
    proofs of equality is more complicated than for typical data types because
    it is a _non-uniform_ indexed proposition -- that is, the value of its last
    argument is not fixed for the whole declaration, but depends on the
    constructor used.  (This non-uniformity is what allows us to put two
    occurrences of [x] on the type of [eq_refl].)

    Concretely, suppose that we have elements [x] and [y] of a type [T], and a
    predicate [P : T -> Prop].  We want to prove that [P y] holds assuming that
    [x = y] and [P x] hold.  This can be done with the following program: *)

Definition rewriting
  (T : Type) (P : T -> Prop) (x y : T) (p : x = y) (H : P x) : P y :=
  match p in _ = z return P z with
  | eq_refl => H
  end.

(** Compared to common match expressions, this one has two extra clauses. The
    first, [in _ = z], allows us to provide a name to the non-uniform argument
    of the type of [p].  The second, [return P z], allows us to declare what the
    return type of the match expression is as a function of [z].  At the top
    level, [z] corresponds to [y], which means that the whole [match] has type
    [P y].  When checking each individual branch, however, Coq requires proofs
    of [P z] using values of [z] that correspond to the constructors of that
    branch.  Inside the [eq_refl] branch, [z] corresponds to [x], which means
    that we have to provide a proof of [P x].  This is why the use of [H] there
    is valid.

    To illustrate, here are proofs of two basic facts about equality:
    transitivity and symmetry. *)

Definition etrans {T} {x y z : T} (p : x = y) (q : y = z) : x = z :=
  match p in _ = w return w = z -> x = z with
  | eq_refl => fun q' : x = z => q'
  end q.

Definition esym {T} {x y : T} (p : x = y) : y = x :=
  match p in _ = z return z = x with
  | eq_refl => eq_refl
  end.

(** Notice the return clause in the first proof, which uses a function type.  We
    cannot use [w = z] alone, as the final type of the expression would be [y =
    z].  The other reasonable guess, [x = z], wouldn't work either, since we
    would have nothing of that type to return in the branch -- [q] has type [y =
    z], and Coq does not automatically change it to [x = z] just because we know
    that [x] and [y] ought to be equal inside the branch.  The practice of
    returning a function is so common when matching on dependent types that it
    even has its own name: the _convoy pattern_, a term coined by Adam Chlipala
    in his #<a href="http://adam.chlipala.net/cpdt/html/MoreDep.html">CDPT
    book</a>#.

    In addition to functions, pretty much any type expression can go in the
    return clause of a [match].  This flexibility allows us to derive many basic
    reasoning principles -- for instance, the fact that constructors are
    disjoint and injective. *)

Definition eq_Sn_m (n m : nat) (p : S n = m) :=
  match p in _ = k return match k with
                          | 0    => False
                          | S m' => n = m'
                          end with
  | eq_refl => eq_refl
  end.

Definition succ_not_zero n : S n <> 0 :=
  eq_Sn_m n 0.

Definition succ_inj n m : S n = S m -> n = m :=
  eq_Sn_m n (S m).

(** In the [eq_refl] branch, we know that [k] is of the form [S n].  By
    substituting this value in the return type, we find that the result of the
    branch must have type [n = n], which is why [eq_refl] is accepted.  Since
    this is only value of [k] we have to handle, it doesn't matter that [False]
    appears in the return type of the [match]: that branch will never be used.
    The more familiar lemmas [succ_not_zero] and [succ_inj] simply correspond to
    special cases of [eq_Sn_m].  A similar trick can be used for many other
    inductive types, such as booleans, lists, and so on.

    ** Mixing proofs and computation

    Proofs can be used not only to build other proofs, but also in more
    conventional programs.  If we know that a list is not empty, for example, we
    can write a function that extracts its first element. *)

From mathcomp Require Import seq.

Definition first {T} (s : seq T) (Hs : s <> [::]) : T :=
  match s return s <> [::] -> T with
  | [::]   => fun Hs : [::] <> [::] => match Hs eq_refl with end
  | x :: _ => fun _ => x
  end Hs.

(** Here we see a slightly different use of dependent pattern matching: the
    return type depends on the analyzed value [s], not just on the indices of
    its type.  The rules for checking that this expression is valid are the
    same: we substitute the pattern of each branch for [s] in the return type,
    and ensure that it is compatible with the result it produces.  On the first
    branch, this gives a contradictory hypothesis [[::] <> [::]], which we can
    discard by pattern matching as we did earlier.  On the second branch, we can
    just return the first element of the list.

    Proofs can also be stored in regular data structures.  Consider for instance
    the subset type [{x : T | P x}], which restricts the elements of the type
    [T] to those that satisfy the predicate [P].  Elements of this type are of
    the form [exist x H], where [x] is an element of [T] and [H] is a proof of
    [P x].  Here is an alternative version of [first], which expects the
    arguments [s] and [Hs] packed as an element of a subset type. *)

Definition first' {T} (s : {s : seq T | s <> [::]}) : T :=
  match s with
  | exist s Hs => first s Hs
  end.

(** While powerful, this idiom comes with a price: when reasoning about a term
    that mentions proofs, the proofs must be explicitly taken into account.  For
    instance, we cannot show that two elements [exist x H1] and [exist x H2] are
    equal just by reflexivity; we must explicitly argue that the proofs [H1] and
    [H2] are equal.  Unfortunately, there are many cases in which this is not
    possible -- for example, two proofs of a disjunction [A \/ B] need to use
    the same constructor to be considered equal.

    The situation is not as bad as it might sound, because Coq was designed to
    allow a _proof irrelevance_ axiom without compromising its soundness.  This
    axiom says that any two proofs of the same proposition are equal. *)

Axiom proof_irrelevance : forall (P : Prop) (p q : P), p = q.

(** If we are willing to extend the theory with this axiom, much of the pain of
    mixing proofs and computation goes away; nevertheless, it is a bit upsetting
    that we need an extra axiom to make the use of proofs in computation
    practical.  Fortunately, much of this convenience is already built into
    Coq's theory, thanks to the structure of proofs of equality.

    ** Proof irrelevance and equality

    A classical result of type theory says that equalities between elements of a
    type [T] are proof irrelevant _provided that_ [T] has decidable equality.
    Many useful properties can be expressed in this way; in particular, any
    boolean function [f : S -> bool] can be seen as a predicate [S -> Prop]
    defined as [fun x : S => f x = true].  Thus, if we restrict subset types to
    _computable_ predicates, we do not need to worry about the proofs that
    appear in its elements.

    You might wonder why any assumptions are needed in this result -- after all,
    the definition of equality only had a single constructor; how could two
    proofs be different?  Let us begin by trying to show the result without
    relying on any extra assumptions. We can show that general proof irrelevance
    can be reduced to irrelevance of "reflexive equality": all proofs of [x = x]
    are equal to [eq_refl x]. *)

Section Irrelevance.

Variable T : Type.
Implicit Types x y : T.

Definition almost_irrelevance :
  (forall x   (p   : x = x), p = eq_refl x) ->
  (forall x y (p q : x = y), p = q) :=
  fun H x y p q =>
    match q in _ = z return forall p' : x = z, p' = q with
    | eq_refl => fun p' => H x p'
    end p.

(** This proof uses the extended form of dependent pattern matching we have seen
    in the definition of [first]: the return type mentions [q], the very element
    we are matching on.  It also uses the convoy pattern to "update" the type of
    [p] with the extra information gained by matching on [q].

    The [almost_irrelevance] lemma may look like progress, but it does not
    actually get us anywhere, because there is no way of proving its premise
    without assumptions. Here is a failed attempt.  *)

Fail Definition irrelevance x (p : x = x) : p = eq_refl x :=
  match p in _ = y return p = eq_refl x with
  | eq_refl => eq_refl
  end.

(** Coq complains that the return clause is ill-typed: its right-hand side has
    type [x = x], but its left-hand side has type [x = y].  That is because when
    checking the return type, Coq does not use the original type of [p], but the
    one obtained by generalizing the index of its type according to the [in]
    clause.

    It took many years to understand that, even though the inductive definition
    of equality only mentions one constructor, it is possible to extend the type
    theory to allow for provably different proofs of equality between two
    elements. #<a href="https://homotopytypetheory.org/book/">Homotopy type
    theory</a>#, for example, introduced a _univalence principle_ that says that
    proofs of equality between two types correspond to isomorphisms between
    them.  Since there are often many different isomorphisms between two types,
    [irrelevance] cannot hold in full generality.

    To obtain an irrelevance result, we must assume that [T] has decidable
    equality. *)

Hypothesis eq_dec : forall x y, x = y \/ x <> y.

(** The argument roughly proceeds as follows.  We use decidable equality to
    define a normalization procedure that takes a proof of equality as input and
    produces a canonical proof of equality of the same type as output.
    Crucially, the output of the procedure does not depend on its input.  We
    then show that the normalization procedure has an inverse, allowing us to
    conclude -- all proofs must be equal to the canonical one.

    Here is the normalization procedure. *)

Definition normalize {x y} (p : x = y) : x = y :=
  match eq_dec x y with
  | or_introl e => e
  | or_intror _ => p
  end.

(** If [x = y] holds, [eq_dec x y] must return something of the form [or_introl
    e], the other branch being contradictory.  This implies that [normalize] is
    constant. *)

Lemma normalize_const {x y} (p q : x = y) : normalize p = normalize q.
Proof. by rewrite /normalize; case: (eq_dec x y). Qed.

(** The inverse of [normalize] is defined by combining transitivity and symmetry
    of equality. *)

Notation "p * q" := (etrans p q).

Notation "p ^-1" := (esym p)
  (at level 3, left associativity, format "p ^-1").

Definition denormalize {x y} (p : x = y) := p * (normalize (eq_refl y))^-1.

(** As the above notation suggests, we can show that [esym] is the inverse of
    [etrans], in the following sense. *)

Definition etransK x y (p : x = y) : p * p^-1 = eq_refl x :=
  match p in _ = y return p * p^-1 = eq_refl x with
  | eq_refl => eq_refl (eq_refl x)
  end.

(** This proof avoids the problem that we encountered in our failed proof of
    [irrelevance], resulting from generalizing the right-hand side of [p]. In
    this return type, [p * p^-1] has type [x = x], which matches the one of
    [eq_refl x].  Notice why the result of the [eq_refl] branch is valid: we
    must produce something of type [eq_refl x * (eq_refl x)^-1 = eq_refl x], but
    by the definitions of [etrans] and [esym], the left-hand side computes
    precisely to [eq_refl x].

    Armed with [etransK], we can now relate [normalize] to its inverse, and
    conclude the proof of irrelevance.  *)

Definition normalizeK x y (p : x = y) :
  normalize p * (normalize (eq_refl y))^-1 = p :=
  match p in _ = y return normalize p * (normalize (eq_refl y))^-1 = p with
  | eq_refl => etransK x x (normalize (eq_refl x))
  end.

Lemma irrelevance x y (p q : x = y) : p = q.
Proof.
by rewrite -[LHS]normalizeK -[RHS]normalizeK (normalize_const p q).
Qed.

End Irrelevance.

(** ** Irrelevance of equality in practice

    The #<a href="http://math-comp.github.io/math-comp/">Mathematical
    Components</a># library provides excellent support for types with decidable
    equality in its [eqtype] #<a
    href="http://math-comp.github.io/math-comp/htmldoc/mathcomp.ssreflect.eqtype.html">module</a>#,
    including a generic result of proof irrelevance like the one I gave above
    ([eq_irrelevance]).  The class structure used by [eqtype] makes it easy for
    Coq to infer proofs of decidable equality, which considerably simplifies the
    use of this and other lemmas.  The #<a
    href="https://coq.inria.fr/library/Coq.Logic.Eqdep_dec.html">Coq standard
    library</a># also provides a proof of this lemma ([eq_proofs_unicity_on]),
    though it is a bit harder to use, since it does not make use of any
    mechanisms for inferring results of decidable equality. *)
