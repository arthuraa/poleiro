(* begin hide *)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool.
Require Import Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq.
Require Import MathComp.bigop MathComp.path.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* end hide *)
(** One important aspect of Coq's logic is the special status it gives
to _computation_: while some systems require one to apply explicit
reasoning steps to show that two given terms are equal, Coq's logic
considers any two terms that _evaluate_ to the same result to be equal
automatically, without the need for additional reasoning steps.

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
given term [a] is equal to itself. Coq accepts this proof because,
even though the two sides of the equation are not syntactically the
same, it is able to use the definition of [+] to compute the left-hand
side and check that the result is the same as the right-hand
side. This also works for some statements with variables in them, for
instance *)

Definition zero_plus_n n : 0 + n = n := erefl.

(** The same principle applies here: [+] is defined by case analysis
on its first argument, and doesn't even need to inspect the second
one. Since the first argument on the left-hand side is a constructor
([0]), Coq can use this definition to reduce it to [n].

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
certified tactics for automating certain reasoning steps. This
technique, known as _proof by reflection_, played an important role in
the Coq formalization of the #<a
href="http://en.wikipedia.org/wiki/Four_color_theorem">Four-color
theorem</a>#, and has been used for many other developments, even in
other proof assistants. As a matter of fact, the name #<a
href="http://ssr.msr-inria.inria.fr/">Ssreflect</a># stands for
_small-scale reflection_, due to the pervasive use of reflection and
computation. Let's see how reflection works by means of a basic (but
interesting) example: a tactic for checking equalities between simple
expressions involving natural numbers.

** Arithmetic with reflection

Imagine that we were in the middle of a proof and needed to show that
two natural numbers are equal: *)

Lemma lem n m p : (n + m) * (2 ^ p) = (2 ^ p) * m + (2 ^ p) * n.

(** This lemma is simple enough so that Coq's own [ring] tactic can
solve it automatically for us, but just for the sake of the example,
suppose that we had to prove this by hand. We could write something
like *)

Proof. by rewrite mulnDl (mulnC n) (mulnC m) addnC. Qed.

(** This was not terribly complicated, but there's certainly room for
improvement. In a paper proof, a mathematician would probably assume
that the reader would be able to verify this result on their own,
without needing any additional detail. But how exactly would the
reader proceed?

In the case of the simple arithmetic expression above, one strategy is
to apply the distributivity law as long as we can, until both
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
constructor, and we can add and multiply expressions together with the
[Add] and [Mul] constructors. The following term, for instance,
represents the expression [n + (m * n)]: *)

Example expr_ex :=
  Add (Var 0) (Mul (Var 1) (Var 0)).

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

(** Now, we know that every expression of that form can be written as
a sum of monomials. We can then define a function [monoms] for
converting an [expr] to that form: *)

Fixpoint monoms e :=
  match e with
  | Var v => [:: [:: v]]
  | Add e1 e2 => monoms e1 ++ monoms e2
  | Mul e1 e2 => allpairs cat (monoms e1) (monoms e2)
  end.

(** Here, we represent a sum of monomials with a list of lists of
variable numbers; for example, here's the result of normalizing
[expr_ex]: *)

Example monoms_expr_ex :
  monoms expr_ex = [:: [:: 0]; [:: 1; 0]].
Proof. by []. Qed.

(** (The [allpairs] function in the body of [monoms] comes from
the [seq] Ssreflect library, and outputs all possible combinations of
elements of two given lists using some binary function (in this case,
list concatenation)). *)

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

Definition normalize := map (sort leq) \o monoms.

Lemma normalizeE vals e :
  nat_of_expr vals e = \sum_(m <- normalize e) \prod_(v <- m) vals v.
Proof.
rewrite monomsE /normalize /=; elim: (monoms e)=> [|m ms IH] /=.
  by rewrite big_nil.
rewrite 2!big_cons IH; congr addn.
by apply/eq_big_perm; rewrite perm_eq_sym perm_sort.
Qed.

Definition expr_eq e1 e2 := perm_eq (normalize e1) (normalize e2).

Lemma expr_eqP vm e1 e2 :
  expr_eq e1 e2 ->
  nat_of_expr vm e1 = nat_of_expr vm e2.
Proof. rewrite 2!normalizeE; exact/eq_big_perm. Qed.

Ltac intern vm e :=
  let rec loop n vm' :=
    match vm' with
    | [::] =>
      let vm'' := eval simpl in (rcons vm e) in
      constr:(n, vm'')
    | e :: ?vm'' => constr:(n, vm)
    | _ :: ?vm'' => loop (S n) vm''
    end in
  loop 0 vm.

Ltac quote_expr vm e :=
  match e with
  | ?e1 + ?e2 =>
    let r1 := quote_expr vm e1 in
    match r1 with
    | (?qe1, ?vm') =>
      let r2 := quote_expr vm' e2 in
      match r2 with
      | (?qe2, ?vm'') => constr:(Add qe1 qe2, vm'')
      end
    end
  | ?e1 * ?e2 =>
    let r1 := quote_expr vm e1 in
    match r1 with
    | (?qe1, ?vm') =>
      let r2 := quote_expr vm' e2 in
      match r2 with
      | (?qe2, ?vm'') => constr:(Mul qe1 qe2, vm'')
      end
    end
  | _ =>
    let r := intern vm e in
    match r with
    | (?n, ?vm') => constr:(Var n, vm')
    end
  end.

Ltac quote_eq :=
  match goal with
  | |- ?e1 = ?e2 =>
    let r1 := quote_expr (Nil nat) e1 in
    match r1 with
    | (?qe1, ?vm') =>
      let r2 := quote_expr vm' e2 in
      match r2 with
      | (?qe2, ?vm'') => apply (@expr_eqP (nth 0 vm'') qe1 qe2 erefl)
      end
    end
  end.

Lemma l1' n m p : (n + m) * (2 ^ p) = (2 ^ p) * m + (2 ^ p) * n.
Proof. quote_eq. Qed.
