Require Import Coq.Lists.List.

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
  result := fun _ => list X;
  initial_state := tt;
  next := fun _ _ => tt;
  initial_result := nil;
  build_result := fun _ x l => app l (cons x nil)
|}.

End List.

Definition my_list : list nat := [List.p _ 1 2 3 4 5 6 7 8 9 10 11].

Module Exp.

Inductive op :=
| Plus
| Minus
| Times
| Const (n : nat).

Module Exports.

Notation "!+" := (Plus) (at level 0).
Notation "!-" := (Minus) (at level 0).
Notation "!*" := (Times) (at level 0).
Coercion Const : nat >-> op.

End Exports.

Module Pre.

Inductive state :=
| Ok (n : nat)
| Error.

Definition token (s : state) : Type :=
  match s with
  | Ok (S _) => op
  | _ => Empty_set
  end.

Fixpoint result' (n : nat) : Type :=
  match n with
  | 0 => nat
  | S n => nat -> result' n
  end.

Definition result (s : state) : Type :=
  match s with
  | Ok n => result' n
  | Error => Empty_set
  end.

Definition next (s : state) : token s -> state :=
  match s with
  | Ok (S n') => fun t =>
                   match t with
                   | Plus | Minus | Times => Ok (S (S n'))
                   | Const _ => Ok n'
                   end
  | _ => fun _ => Error
  end.

Definition build_result s : forall t, result s -> result (next s t) :=
  match s with
  | Ok (S n') =>
    fun t =>
      match t with
      | Plus => fun res n1 n2 => res (n1 + n2)
      | Minus => fun res n1 n2 => res (n1 - n2)
      | Times => fun res n1 n2 => res (n1 * n2)
      | Const n => fun res => res n
      end
  | _ => fun t _ => t
  end.

End Pre.

Definition pre := {|
  state := Pre.state;
  initial_state := Pre.Ok 1;
  token := Pre.token;
  result := Pre.result;
  next := Pre.next;
  initial_result := fun t => t;
  build_result := Pre.build_result
|}.

Module Post.

Inductive state :=
| Empty
| One
| More (n : nat).

Definition token (s : state) : Type :=
  match s with
  | Empty | One => nat
  | More _ => op
  end.

Fixpoint result' (n : nat) : Type :=
  match n with
  | 0 => nat
  | S n => (result' n * nat)%type
  end.

Definition result (s : state) : Type :=
  match s with
  | Empty => unit
  | One => nat
  | More n => result' (S n)
  end.

Definition next s : token s -> state :=
  match s with
  | Empty => fun _ => One
  | One => fun _ => More 0
  | More 0 => fun t =>
                match t with
                | Plus | Minus | Times => One
                | Const _ => More 1
                end
  | More (S n) => fun t =>
                    match t with
                    | Plus | Minus | Times => More n
                    | Const _ => More (S (S n))
                    end
  end.

Definition build_result s : forall t, result s -> result (next s t) :=
  match s with
  | Empty => fun t _ => t
  | One => fun t r => (r, t)
  | More 0 => fun t res =>
                match res with
                | (n1, n2) =>
                  match t with
                  | Plus => n1 + n2
                  | Minus => n1 - n2
                  | Times => n1 * n2
                  | Const n => (n1, n2, n)
                  end
                end
  | More (S n) => fun t res =>
                    match res with
                    | (res, n1, n2) =>
                      match t with
                      | Plus => (res, n1 + n2)
                      | Minus => (res, n1 - n2)
                      | Times => (res, n1 * n2)
                      | Const n => (res, n1, n2, n)
                      end
                    end
  end.

End Post.

Definition post := {|
  state := Post.state;
  token := Post.token;
  result := Post.result;
  initial_state := Post.Empty;
  next := Post.next;
  initial_result := tt;
  build_result := Post.build_result
|}.

End Exp.

Export Exp.Exports.

Definition my_exp : nat := [Exp.pre !+ !- 1 2 !+ 4 4].
Definition my_exp' : nat := [Exp.post 4 4 !+ 2 1 !- !+].
