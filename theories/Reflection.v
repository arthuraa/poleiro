Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool.
Require Import Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq.
Require Import MathComp.bigop MathComp.path.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive expr :=
| Var of nat
| Add of expr & expr
| Mul of expr & expr.

Fixpoint nat_of_expr vm e :=
  match e with
  | Var v => nth 0 vm v
  | Add e1 e2 => nat_of_expr vm e1 + nat_of_expr vm e2
  | Mul e1 e2 => nat_of_expr vm e1 * nat_of_expr vm e2
  end.

Fixpoint normalize_int e :=
  match e with
  | Var v => [:: [:: v]]
  | Add e1 e2 => normalize_int e1 ++ normalize_int e2
  | Mul e1 e2 => allpairs cat (normalize_int e1) (normalize_int e2)
  end.

Definition normalize := map (sort leq) \o normalize_int.

Lemma normalizeE vm e :
  nat_of_expr vm e = \sum_(s <- normalize e) \prod_(n <- s) nth 0 vm n.
Proof.
transitivity (\sum_(s <- normalize_int e) \prod_(n <- s) nth 0 vm n).
  elim: e=> [v|e1 IH1 e2 IH2|e1 IH1 e2 IH2] /=.
  - by rewrite 2!big_seq1.
  - by rewrite big_cat IH1 IH2.
  rewrite {}IH1 {}IH2 big_distrlr /=.
  elim: (normalize_int e1) (normalize_int e2)=> [|v s1 IH] s2 /=.
    by rewrite 2!big_nil.
  rewrite big_cons big_cat /= IH; congr addn.
  by rewrite big_map; apply/eq_big=> //= s3 _; rewrite big_cat.
rewrite /normalize /=; elim: (normalize_int e)=> [|s ss IH] /=.
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
      | (?qe2, ?vm'') => apply (@expr_eqP vm'' qe1 qe2 erefl)
      end
    end
  end.

Lemma l1 n m p : (n + m) * (2 ^ p) = (2 ^ p) * m + (2 ^ p) * n.
Proof.
by rewrite mulnDl (mulnC n) (mulnC m) addnC.
Qed.

Lemma l1' n m p : (n + m) * (2 ^ p) = (2 ^ p) * m + (2 ^ p) * n.
Proof. quote_eq. Qed.
