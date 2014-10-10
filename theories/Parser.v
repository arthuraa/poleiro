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

Module ListParser.

Definition parser_data (X : Type) := {|
  state := unit;
  token := X;
  result := fun _ => list X -> list X;
  initial_state := tt;
  next := fun _ _ => tt;
  initial_result := fun t => t;
  build_result := fun _ x f l => f (cons x l)
|}.

Definition my_list : list nat := get_result _ _ (reader (parser_data nat) 1 2 3 4 5 6 7 8 9 10 11) nil.

End ListParser.

Module ExpParser.

Module Internal.

Definition state := nat.

Inductive token :=
| Plus
| Minus
| Times
| Const (n : nat).

Fixpoint result' (n : nat) : Type :=
  match n with
  | 0 => nat
  | S n => nat -> result' n
  end.

Definition result (n : state) : Type :=
  match n with
  | 0 => unit
  | S n => result' n
  end.

Definition next (n : state) (t : token) : state :=
  match n with
  | S (S n') => match t with
                | Plus | Minus | Times => S n
                | Const _ => S n'
                end
  | _ => 0
  end.

Definition build_result n t : result n -> result (next n t) :=
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

End Internal.

Definition parser_data := {|
  state := Internal.state;
  initial_state := 2;
  token := Internal.token;
  result := Internal.result;
  next := Internal.next;
  initial_result := fun t => t;
  build_result := Internal.build_result
|}.

Notation "!+" := (Internal.Plus) (at level 0).
Notation "!-" := (Internal.Minus) (at level 0).
Notation "!*" := (Internal.Times) (at level 0).
Notation "! n" := (Internal.Const n) (at level 0).

Definition my_exp : nat := get_result _ _ (reader parser_data !+ !- !1 !2 !+ !4 !4).

End ExpParser.
