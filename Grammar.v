Require Import Base.
Require Import List.

Inductive chomsky_rule (U: Type): Type :=
  |   nonterm_rule : U -> U -> U -> chomsky_rule U
  |   terminal_rule : U -> ter -> chomsky_rule U.


Record chomsky_grammar (U: Type): Type :=
  make_chomsky_grammar {
      grammar_start : U;
      grammar_rules : list (chomsky_rule U)             
    }.


Inductive der (U: Type) (rules: list (chomsky_rule U)) (r: U): word -> Prop :=
  | nonterm_rule_app : forall
                     (r1 : U) (w1 : word)
                     (r2 : U) (w2 : word),
      (In (nonterm_rule U r r1 r2) rules) ->
      (der U rules r1 w1) -> (der U rules r2 w2) -> der U rules r (w1 ++ w2)  
  | terminal_rule_app : forall (t : ter),
      (In (terminal_rule U r t) rules) -> der U rules r (t :: nil).


Definition chomsky_language (U: Type) (g: chomsky_grammar U) (w : word) : Prop :=
  der U (grammar_rules U g) (grammar_start U g) w.

