Inductive parser_data := ParserData {
  state : Type;
  token : Type;
  result : state -> Type;
  initial_state : state;
  next : state -> token -> state;
  initial_result : result initial_state;
  build_result : forall s t, result s -> result (next s t)
}.

Section Parser.

Variable pd : parser_data.

CoInductive parser (s : state pd) : Type := Parser {
  read :> forall t, parser (next pd s t);
  get_result : result pd s
}.

CoFixpoint reader' s (r : result pd s) : parser s :=
  Parser _ (fun t => reader' _ (build_result pd s t r)) r.

Definition reader := Parser _ (reader' _ (initial_result pd)) (initial_result pd).

End Parser.

Definition exp_state := nat.

Inductive exp_token :=
| Plus
| Minus
| Times
| Const (n : nat).

Notation "!+" := (Plus) (at level 0).
Notation "!-" := (Minus) (at level 0).
Notation "!*" := (Times) (at level 0).
Notation "! n" := (Const n) (at level 0).

Fixpoint exp_result' (n : nat) : Type :=
  match n with
  | 0 => nat
  | S n => nat -> exp_result' n
  end.

Definition exp_result (n : exp_state) : Type :=
  match n with
  | 0 => unit
  | S n => exp_result' n
  end.

Definition exp_next (n : exp_state) (t : exp_token) : exp_state :=
  match n with
  | S (S n') => match t with
                | Plus | Minus | Times => S n
                | Const _ => S n'
                end
  | _ => 0
  end.

Definition exp_build_result n t : exp_result n -> exp_result (exp_next n t) :=
  match n with
  | S (S n') =>
    match t with
    | Plus => fun res n1 n2 => res (n1 + n2)
    | Minus => fun res n1 n2 => res (n1 - n2)
    | Times => fun res n1 n2 => res (n1 * n2)
    | Const n => fun res => res n
    end
  | _ => fun _ => tt
  end.

Definition exp_parser_data := {|
  state := exp_state;
  initial_state := 2;
  token := exp_token;
  result := exp_result;
  next := exp_next;
  initial_result := fun t => t;
  build_result := exp_build_result
|}.

Definition my_exp : nat := get_result _ _ (reader exp_parser_data !+ !- !1 !2 !+ !4 !4).
