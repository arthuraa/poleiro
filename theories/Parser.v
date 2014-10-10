Inductive parser_data := ParserData {
  state : Type;
  token : state -> Type;
  result : state -> Type;
  initial_state : state;
  next : forall s, token s -> state;
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

Definition reader := reader' _ (initial_result pd).

End Parser.

Coercion reader : parser_data >-> parser.

Notation "[ x ]" := (get_result _ _ x) (at level 0).

Module List.

Definition p (X : Type) := {|
  state := unit;
  token := fun _ => X;
  result := fun _ => list X -> list X;
  initial_state := tt;
  next := fun _ _ => tt;
  initial_result := fun t => t;
  build_result := fun _ x f l => f (cons x l)
|}.

End List.

Definition my_list : list nat := [List.p _ 1 2 3 4 5 6 7 8 9 10 11] nil.

Module Exp.

Module Internal.

Definition state := nat.

Inductive token' :=
| Plus
| Minus
| Times
| Const (n : nat).

Definition token (n : state) : Type :=
  match n with
  | S (S _) => token'
  | _ => Empty_set
  end.

Fixpoint result' (n : nat) : Type :=
  match n with
  | 0 => nat
  | S n => nat -> result' n
  end.

Definition result (n : state) : Type :=
  match n with
  | 0 => Empty_set
  | S n => result' n
  end.

Definition next (n : state) : token n -> state :=
  match n with
  | S (S n') => fun t =>
                  match t with
                  | Plus | Minus | Times => S n
                  | Const _ => S n'
                  end
  | _ => fun _ => 0
  end.

Definition build_result n : forall t, result n -> result (next n t) :=
  match n with
  | S (S n') =>
    fun t =>
      match t with
      | Plus => fun res n1 n2 => res (n1 + n2)
      | Minus => fun res n1 n2 => res (n1 - n2)
      | Times => fun res n1 n2 => res (n1 * n2)
      | Const n => fun res => res n
      end
  | _ => fun t _ => t
  end.

End Internal.

Definition p := {|
  state := Internal.state;
  initial_state := 2;
  token := Internal.token;
  result := Internal.result;
  next := Internal.next;
  initial_result := fun t => t;
  build_result := Internal.build_result
|}.

Module Exports.

Notation "!+" := (Internal.Plus) (at level 0).
Notation "!-" := (Internal.Minus) (at level 0).
Notation "!*" := (Internal.Times) (at level 0).
Coercion Internal.Const : nat >-> Internal.token'.

End Exports.

End Exp.

Export Exp.Exports.

Definition my_exp : nat := [Exp.p !+ !- 1 2 !+ 4 4].
