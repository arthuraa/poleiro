(* begin hide *)
From mathcomp
  Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq bigop path.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* end hide *)
(** One important aspect of Coq's logic is the special status given to
_computation_: while some systems require one to apply explicit
deductive steps to show that two given terms are equal, Coq's logic
considers any two terms that _evaluate_ to the same result to be equal
automatically, without the need for additional reasoning.

Without getting into too much detail, we can illustrate this idea with
some simple examples. Russell and Whitehead's seminal _Principia
Mathematica_ had to develop #<a
href="http://quod.lib.umich.edu/cgi/t/text/pageviewer-idx?c=umhistmath&cc=umhistmath&idno=aat3201.0001.001&frm=frameset&view=image&seq=401">hundreds
of pages</a># of foundational mathematics before being able to prove
that [1 + 1 = 2]. In contrast, here's what this proof looks like in
Coq: *)

Definition one_plus_one : 1 + 1 = 2 := erefl.

(** [erefl] is the only constructor of the [eq] type; its type,
[forall A (a : A), a = a], tells us that we can use it to prove that
given term [a] is equal to itself. Coq accepts [one_plus_one] as a
valid proof because, even though the two sides of the equation are not
syntactically the same, it is able to use the definition of [+] to
compute the left-hand side and check that the result is the same as
the right-hand side. This also works for some statements with
variables in them, for instance *)

Definition zero_plus_n n : 0 + n = n := erefl.

(** The same principle applies here: [+] is defined by case analysis
on its first argument, and doesn't even need to inspect the second
one. Since the first argument on the left-hand side is a constructor
([0]), Coq can reduce the expression and conclude that both sides are
equal.

Unfortunately, not every equality is a direct consequence of
computation. For example, this proof attempt is rejected: *)

Fail Definition n_plus_zero n : n + 0 = n := erefl.

(** What happened here? As mentioned before, [+] is defined by case
analysis on the first argument; since the first argument of the
left-hand side doesn't start with a constructor, Coq doesn't know how
to compute there. As it turns out, one actually needs an inductive
argument to prove this result, which might end up looking like this,
if we were to check the proof term that Coq produces: *)

Fixpoint n_plus_zero n : n + 0 = n :=
  match n with
  | 0 => erefl
  | n.+1 => let: erefl := n_plus_zero n in erefl
  end.

(** It seems that, although interesting, computation inside Coq isn't
of much use when proving something. Or is it?

In this post, I will show how computation in Coq can be used to write
certified automation tactics with a technique known as _proof by
reflection_. Reflection is extensively used in Coq and in other proof
assistants as well; it is at the core of powerful automation tactics
such as [ring], and played an important role in the formalization of
the #<a
href="http://en.wikipedia.org/wiki/Four_color_theorem">Four-color
theorem</a>#. As a matter of fact, the name #<a
href="http://ssr.msr-inria.inria.fr/">Ssreflect</a># stands for
_small-scale reflection_, due to the library's pervasive use of
reflection and computation.

Let's see how reflection works by means of a basic example: a tactic
for checking equalities between simple expressions involving natural
numbers.

** Arithmetic with reflection

Imagine that we were in the middle of a proof and needed to show that
two natural numbers are equal: *)

Lemma lem n m p : (n + m) * p = p * m + p * n.

(** [ring] is powerful enough to solve this goal by itself, but just
for the sake of the example, suppose that we had to prove it by
hand. We could write something like *)

Proof. by rewrite mulnDl (mulnC n) (mulnC m) addnC. Qed.

(** This was not terribly complicated, but there's certainly room for
improvement. In a paper proof, a mathematician would probably assume
that the reader is capable of verifying this result on their own,
without any additional detail. But how exactly would the reader
proceed?

In the case of the simple arithmetic expression above, it suffices to
apply the distributivity law as long as possible, until both
expressions become a sum of monomials. Then, thanks to associativity
and commutativity, we just have to reorder the factors and terms and
check that both sides of the equation match.

The idea of proof by reflection is to reduce a the validity of a
logical statement to a _symbolic computation_, usually by proving a
theorem of the form [thm : b = true -> P] with [b : bool]. If [b] can
be computed explicitly and reduces to [true], then Coq recognizes
[erefl] as a proof of [b = true], which means that [thm erefl] becomes
a proof of [P].

To make things concrete, let's go back to our example. The idea that
we described above for checking whether two numbers are equal can be
used whenever we have expressions involving addition, multiplication,
and variables. We will define a Coq data type for representing such
expressions, as we will need to compute with them: *)

Inductive expr :=
| Var of nat
| Add of expr & expr
| Mul of expr & expr.

(** Variables are represented by natural numbers using the [Var]
constructor, and [Add] and [Mul] can be used to combine
expressions. The following term, for instance, represents the
expression [n * (m + n)]: *)

Example expr_ex :=
  Mul (Var 0) (Add (Var 1) (Var 0)).

(** where [Var 0] and [Var 1] denote [n] and [m], respectively.

If we are given a function [vals] assigning variables to numbers, we
can compute the value of an expression with a simple recursive
function: *)

Fixpoint nat_of_expr vals e :=
  match e with
  | Var v => vals v
  | Add e1 e2 => nat_of_expr vals e1 + nat_of_expr vals e2
  | Mul e1 e2 => nat_of_expr vals e1 * nat_of_expr vals e2
  end.

(** Now, since every expression of that form can be written as a sum
of monomials, we can define a function for converting an [expr] to
that form: *)

Fixpoint monoms e :=
  match e with
  | Var v => [:: [:: v] ]
  | Add e1 e2 => monoms e1 ++ monoms e2
  | Mul e1 e2 => [seq m1 ++ m2 | m1 <- monoms e1, m2 <- monoms e2]
  end.

(** Here, each monomial is represented by a list enumerating all
variables that occur in it, counting their multiplicities. Hence, a
sum of monomials is represented as a list of lists. For example,
here's the result of normalizing [expr_ex]: *)

Example monoms_expr_ex :
  monoms expr_ex = [:: [:: 0; 1]; [:: 0; 0]].
Proof. by []. Qed.

(** To prove that [monoms] has the intended behavior, we show that the
value of an expression is preserved by it. By using the big operations
[\sum] and [\prod] from the MathComp library, we can compute the value
of a sum of monomials very easily: *)

Lemma monomsE vals e :
  nat_of_expr vals e = \sum_(m <- monoms e) \prod_(v <- m) vals v.
Proof.
elim: e=> [v|e1 IH1 e2 IH2|e1 IH1 e2 IH2] /=.
- by rewrite 2!big_seq1.
- by rewrite big_cat IH1 IH2.
rewrite {}IH1 {}IH2 big_distrlr /=.
elim: (monoms e1) (monoms e2)=> [|v m1 IH] m2 /=; first by rewrite 2!big_nil.
rewrite big_cons big_cat /= IH; congr addn.
by rewrite big_map; apply/eq_big=> //= m3 _; rewrite big_cat.
Qed.

(** Hence, to check that two expressions are equivalent, it suffices
to compare the results of [monoms], modulo the ordering. We can do
this by sorting the variable names on each monomial and then testing
whether one list of monomials is a permutation of the other: *)

Definition normalize := map (sort leq) \o monoms.

Lemma normalizeE vals e :
  nat_of_expr vals e = \sum_(m <- normalize e) \prod_(v <- m) vals v.
Proof.
rewrite monomsE /normalize /=; elim: (monoms e)=> [|m ms IH] /=.
  by rewrite big_nil.
rewrite 2!big_cons IH; congr addn.
by apply/perm_big; rewrite perm_sym perm_sort.
Qed.

Definition expr_eq e1 e2 := perm_eq (normalize e1) (normalize e2).

Lemma expr_eqP vals e1 e2 :
  expr_eq e1 e2 ->
  nat_of_expr vals e1 = nat_of_expr vals e2.
Proof. rewrite 2!normalizeE; exact/perm_big. Qed.

(** To see how this lemma works, let's revisit our original
example. Here's a new proof that uses [expr_eqP]: *)

Lemma lem' n m p : (n + m) * p = p * m + p * n.
Proof.
exact: (@expr_eqP (nth 0 [:: n; m; p])
                  (Mul (Add (Var 0) (Var 1)) (Var 2))
                  (Add (Mul (Var 2) (Var 1)) (Mul (Var 2) (Var 0)))
                  erefl).
Qed.

(** The first argument to our lemma assigns "real" variables to
variable numbers: [0] corresponds to [n] (the first element of the
list), [1] to [m], and [2] to [p]. The second and third argument are
symbolic representations of the left and right-hand sides of our
equation. The fourth argument is the most interesting one: the
[expr_eq] was defined as a _boolean_ function that returns [true] when
its two arguments are equivalent expressions. As we've seen above,
this means that whenever [expr_eq e1 e2] computes to [true], [erefl]
is a valid proof of it. Finally, when Coq tries to check whether the
conclusion of [expr_eqP] can be used on our goal, it computes
[nat_of_expr] on both sides, realizing that the conclusion and the
goal are exactly the same. For instance: *)

Lemma expr_eval n m p :
  nat_of_expr (nth 0 [:: n; m; p]) (Mul (Add (Var 0) (Var 1)) (Var 2))
  = (n + m) * p.
Proof. reflexivity. Qed.

(** Of course, [expr_eqP] doesn't force its first argument to always
return actual Coq variables, so it can be applied even in some cases
where the expressions contain other operators besides [+] and [*]: *)

Lemma lem'' n m : 2 ^ n * m = m * 2 ^ n.
Proof.
exact: (@expr_eqP (nth 0 [:: 2 ^ n; m])
                  (Mul (Var 0) (Var 1)) (Mul (Var 1) (Var 0))
                  erefl).
Qed.

(** At this point, it may seem that we haven't gained much from using
[expr_eqP], since the second proof of our example was much bigger than
the first one. This is just an illusion, however, as the proof term
produced on the first case is actually quite big:

[[
lem =
fun n m p : nat =>
(fun _evar_0_ : n * p + m * p = p * m + p * n =>
 eq_ind_r (eq^~ (p * m + p * n)) _evar_0_ (mulnDl n m p))
  ((fun _evar_0_ : p * n + m * p = p * m + p * n =>
    eq_ind_r
      (fun _pattern_value_ : nat => _pattern_value_ + m * p = p * m + p * n)
      _evar_0_ (mulnC n p))
     ((fun _evar_0_ : p * n + p * m = p * m + p * n =>
       eq_ind_r
         (fun _pattern_value_ : nat =>
          p * n + _pattern_value_ = p * m + p * n) _evar_0_
         (mulnC m p))
        ((fun _evar_0_ : p * m + p * n = p * m + p * n =>
          eq_ind_r (eq^~ (p * m + p * n)) _evar_0_ (addnC (p * n) (p * m)))
           (erefl (p * m + p * n)))))
     : forall n m p : nat, (n + m) * p = p * m + p * n
]]

By using reflection, we were able to transform the explicit reasoning
steps of the first proof into implicit computation that is carried out
by the proof assistant. And since proof terms have to be stored in
memory or included into the compiled [vo] file, it is good to make
them smaller if we can.

Nevertheless, even with a smaller proof term, having to manually type
in that proof term is not very convenient. The problem is that Coq's
unification engine is not smart enough to infer the symbolic form of
an expression, forcing us to provide it ourselves. Fortunately, we can
use some code to fill in the missing bits.

** Reification

To _reify_ something means to produce a representation of that object
that can be directly manipulated in computation. In our case, that
object is a Gallina expression of type [nat], and the representation
we are producing is a term of type [expr].

Reification is ubiquitous in proofs by reflection. The Coq standard
library comes with a #<a
href="https://coq.inria.fr/distrib/current/refman/Reference-Manual012.html##sec480">plugin</a>#
for reifying formulas, but it is not general enough to accommodate our
use case. Therefore, we will program our own reification tactic in
ltac.

We will begin by writing a function that looks for a variable on a
list and returns its position. If the variable is not present, we add
it to the end of the list and return the updated list as well: *)

Ltac intern vars e :=
  let rec loop n vars' :=
    match vars' with
    | [::] =>
      let vars'' := eval simpl in (rcons vars e) in
      constr:((n, vars''))
    | e :: ?vars'' => constr:((n, vars))
    | _ :: ?vars'' => loop (S n) vars''
    end in
  loop 0 vars.

(** Notice the call to [eval simpl] on the first branch of
[loop]. Remember that in ltac everything is matched almost purely
syntactically, so we have to explicitly evaluate a term when we are
just interested on its value, and not on how it is written.

We can now write a tactic for reifying an expression. [reify_expr]
takes two arguments: a list [vars] to be used with [intern] for
reifying variables, plus the expression [e] to be reified. It returns
a pair [(e',vars')] contained the reified expression [e'] and an
updated variable list [vars']. *)

Ltac reify_expr vars e :=
  match e with
  | ?e1 + ?e2 =>
    let r1 := reify_expr vars e1 in
    match r1 with
    | (?qe1, ?vars') =>
      let r2 := reify_expr vars' e2 in
      match r2 with
      | (?qe2, ?vars'') => constr:((Add qe1 qe2, vars''))
      end
    end
  | ?e1 * ?e2 =>
    let r1 := reify_expr vars e1 in
    match r1 with
    | (?qe1, ?vars') =>
      let r2 := reify_expr vars' e2 in
      match r2 with
      | (?qe2, ?vars'') => constr:((Mul qe1 qe2, vars''))
      end
    end
  | _ =>
    let r := intern vars e in
    match r with
    | (?n, ?vars') => constr:((Var n, vars'))
    end
  end.

(** Again, because this is an ltac function, we can traverse our
Gallina expression syntactically, as if it were a data
structure. Notice how we thread though the updated variable lists
after each call; this is done to ensure that variables are named
consistently.

Finally, using [reify_expr], we can write [solve_nat_eq], which
reifies both sides of the equation on the goal and applies [expr_eqP]
with the appropriate arguments. *)

Ltac solve_nat_eq :=
  match goal with
  | |- ?e1 = ?e2 =>
    let r1 := reify_expr (Nil nat) e1 in
    match r1 with
    | (?qe1, ?vm') =>
      let r2 := reify_expr vm' e2 in
      match r2 with
      | (?qe2, ?vm'') => exact: (@expr_eqP (nth 0 vm'') qe1 qe2 erefl)
      end
    end
  end.

(** We can check that our tactic works on our original example: *)

Lemma lem''' n m p : (n + m) * p = p * m + p * n.
Proof. solve_nat_eq. Qed.

(** With [solve_nat_eq], every equation of that form becomes very easy
to solve, including cases where a human prover might have trouble at
first sight! *)

Lemma complicated n m p r t :
  (n + 2 ^ r * m) * (p + t) * (n + p)
  = n * n * p + m * 2 ^ r * (p * n + p * t + t * n + p * p)
  + n * (p * p + t * p + t * n).
Proof. solve_nat_eq. Qed.

(** ** Summary

We have seen how we can use internal computation in Coq to write
powerful tactics. Besides generating small proof terms, tactics that
use reflection have another important benefit: they are mostly written
in Gallina, a typed language, and come with correctness proofs. This
contrasts with most custom tactics written in ltac, which tend to
break quite often due to the lack of static guarantees (and to how
unstructure the tactic language is). For [solve_nat_eq], we only had
to write the reification engine in ltac, which results in a more
manageable code base.

If you want to learn more about reflection, Adam Chlipala's #<a
href="http://adam.chlipala.net/cpdt/">CPDT</a># book has #<a
href="http://adam.chlipala.net/cpdt/html/Reflection.html">an entire
chapter</a># devoted to the subject, which I highly recommend. *)
