From mathcomp Require Import ssreflect ssrfun ssrbool.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition cast T S (e : T = S) : T -> S :=
  match e with erefl => id end.

Arguments cast {_ _} e _.

Definition congr1CE (T S : Type) (a : S) x y (e : x = y) :
  congr1 (fun _ : T => a) e = erefl :=
  match e with erefl => erefl end.

Lemma val_inj (T : Type) (P : T -> Prop) : injective (@sval T P).
Proof.
case=> [x xP] [y yP] /= exy; case: y / exy yP => xP'.
congr exist; exact: proof_irrelevance.
Qed.

Axiom uchoice : forall T (P : T -> Prop), (exists! x, P x) -> {x | P x}.

Section Quotient.

Context (T : Type) (R : relation T) (RP : Equivalence R).

Unset Elimination Schemes.
Record quot : Type :=
  Quot_ {of_quot : {P : T -> Prop | exists x, P = R x}}.
Set Elimination Schemes.

Definition Quot (x : T) : quot := Quot_ (exist _ (R x) (ex_intro _ x erefl)).

Lemma QuotE x y : R x y -> Quot x = Quot y.
Proof.
move=> e; congr Quot_; apply: val_inj.
apply: functional_extensionality=> z.
apply: propositional_extensionality.
by rewrite /= e.
Qed.

Lemma Quot_inj x y : Quot x = Quot y -> R x y.
Proof.
move=> e; rewrite -[R x y]/(sval (of_quot (Quot x)) y) e //=; reflexivity.
Qed.

Section Elim.

Context (S : quot -> Type) (f : forall x, S (Quot x)).
Context (fP : forall x y (exy : R x y), cast (congr1 S (QuotE exy)) (f x) = f y).

Lemma quot_rect_subproof (q : quot) :
  exists! a, exists x (exq : Quot x = q), a = cast (congr1 S exq) (f x).
Proof.
have {q} [x ->]: exists x, q = Quot x.
  by case: q=> [[P [x xP]]]; exists x; congr Quot_; apply: val_inj.
exists (f x); split=> [|a]; first by exists x, erefl.
case=> y [eyx -> {a}].
by rewrite (proof_irrelevance _ eyx (QuotE (Quot_inj eyx))) fP.
Qed.

Definition quot_rect q := sval (uchoice (quot_rect_subproof q)).

Lemma quot_rectE x : quot_rect (Quot x) = f x.
Proof.
rewrite /quot_rect; case: uchoice=> _ [y [eyx /= ->]].
by rewrite (proof_irrelevance _ eyx (QuotE (Quot_inj eyx))) fP.
Qed.

End Elim.

Section Rec.

Context S (f : T -> S) (fP : forall x y, R x y -> f x = f y).

Definition quot_rec :=
  @quot_rect (fun=> S) f
    (fun x y exy => etrans
      (congr1 (fun p => cast p (f x)) (congr1CE S (QuotE exy)))
      (fP exy)).

Lemma quot_recE x : quot_rec (Quot x) = f x.
Proof. by rewrite /quot_rec quot_rectE. Qed.

End Rec.

End Quotient.
