Inductive parser_data := ParserData {
  state : Type;
  initial_state : state;
  token : Type;
  result : Type;
  next : state -> token -> option state;
  partial_result : option state -> Type;
  initial_partial_result : partial_result (Some initial_state);
  get_result : partial_result None -> result;
  build_result : forall s t, partial_result (Some s) -> partial_result (next s t)
}.

Section Parser.

Variable pd : parser_data.

CoInductive parser' : option (state pd) -> Type :=
| PRead (s : state pd) (read : forall t, parser' (next pd s t)) : parser' (Some s)
| PDone (res : result pd) : parser' None.

Definition caseD (p : parser' None) : result pd :=
  match p with
  | PDone res => res
  end.

Definition caseR (s : state pd) (p : parser' (Some s)) : forall t, parser' (next pd s t) :=
  match p with
  | PRead _ read => read
  end.

Inductive parser s := Parser (p : parser' (Some s)).

Definition read s (p : parser s) :=
  fun t =>
    match next pd s t as s' return parser' s' ->
                                   match s' with
                                   | Some s' => parser s'
                                   | None => result pd
                                   end
    with
    | Some s' => fun p => Parser _ p
    | None => caseD
    end match p with Parser p => caseR s p t end.

Coercion read : parser >-> Funclass.

CoFixpoint reader' s : partial_result pd s -> parser' s :=
  match s with
  | Some s => fun res => PRead s (fun t => reader' _ (build_result pd s t res))
  | None   => fun res => PDone (get_result pd res)
  end.

Definition reader := Parser _ (reader' _ (initial_partial_result pd)).

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

Definition exp_result := nat.

Definition exp_next :=
  (fun (s : nat) (t : exp_token) =>
     match t with
     | Plus | Minus | Times => Some (S s)
     | Const _ => match s with
                  | 0 => None
                  | S s => Some s
                  end
     end).

Fixpoint exp_partial_result' (n : nat) : Type :=
  match n with
  | 0 => nat
  | S n' => nat -> exp_partial_result' n'
  end.

Definition exp_partial_result (s : option exp_state) : Type :=
  match s with
  | Some n => nat -> exp_partial_result' n
  | None => nat
  end.

Definition exp_get_result (r : exp_partial_result None) : exp_result := r.

Definition exp_build_result s t : exp_partial_result (Some s) -> exp_partial_result (exp_next s t) :=
  match t with
  | Plus => fun res n1 n2 => res (n1 + n2)
  | Minus => fun res n1 n2 => res (n1 - n2)
  | Times => fun res n1 n2 => res (n1 * n2)
  | Const n => match s return exp_partial_result (Some s) ->
                              exp_partial_result (exp_next s (Const n))
               with
               | 0 => fun res => res n
               | S _ => fun res => res n
               end
  end.

Definition exp_parser_data := {|
  state := exp_state;
  initial_state := 0;
  token := exp_token;
  result := exp_result;
  next := exp_next;
  partial_result := exp_partial_result;
  initial_partial_result := fun t => t;
  get_result := exp_get_result;
  build_result := exp_build_result
|}.

Definition reader_exp := Eval compute in reader exp_parser_data.

Definition my_exp : nat := reader_exp !+ !- !1 !2 !+ !4 !4.
