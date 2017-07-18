Require Import Base.
Require Import Grammar.
Require Import List.

Require Import Coq.Arith.Le.
Require Import Coq.Arith.Lt.



Import ListNotations.

Lemma in_single_list (U : Type) (v1 v2 : U):
      In v1 [v2] -> v1 = v2.
Proof.
  intro.
  destruct H.
  auto.
  simpl in H.
  contradiction.
Qed.

Inductive chomsky_union_var (U : Type): Type :=
  |   start_rule : chomsky_union_var U
  |   un_rule : nat -> U -> chomsky_union_var U.  

Definition chomsky_rule_conv (U : Type) (n : nat)
           (r : chomsky_rule U) : chomsky_rule (chomsky_union_var U):=
  match r with
  |   nonterm_rule _ r r1 r2 => nonterm_rule _ (un_rule U n r) (un_rule U n r1) (un_rule U n r2)
  |   terminal_rule _ r te => terminal_rule _ (un_rule U n r) te
  end.


Definition chomsky_rules_s_conv (U : Type) (n : nat)
           (eqb : U -> U -> bool) (s: U)
           (rule : chomsky_rule U) :
           list (chomsky_rule (chomsky_union_var U)):=
  match rule with
  | nonterm_rule _ r r1 r2 =>
    if eqb s r then [nonterm_rule _ (start_rule U) (un_rule U n r1) (un_rule U n r2)] else  nil
  | terminal_rule _ r te =>
    if eqb s r then [terminal_rule _ (start_rule U) te] else nil
  end.                              


Definition chomsky_rules_conv (U : Type) (n : nat)
           (eqb : U -> U -> bool) (s: U)
           (l : list (chomsky_rule U)) :
           list (chomsky_rule (chomsky_union_var U)):=
  flat_map (fun r => chomsky_rule_conv U n r :: chomsky_rules_s_conv U n eqb s r) l.

Definition chomsky_grammar_cov (U : Type) (n : nat)
           (eqb : U -> U -> bool)
           (g : chomsky_grammar U) :
           list (chomsky_rule (chomsky_union_var U)):=
  chomsky_rules_conv U n eqb (grammar_start U g) (grammar_rules U g)                  
.

Fixpoint enumerate (U U1 : Type)
                     (f : U -> nat -> list U1)
                     (l : list U): (list U1) :=
  match l with
  | nil => nil
  | h :: t => (f h (length t)) ++ (enumerate _ _ f t)
  end.  

Definition chomsky_rules_union (U : Type)
           (eqb : U -> U -> bool) 
           (l : list (chomsky_grammar U)) :
  list (chomsky_rule (chomsky_union_var U)) :=
   enumerate _ _ (fun g n => chomsky_grammar_cov U n eqb g) l. 

Definition chomsky_grammar_union (U : Type)
           (eqb : U -> U -> bool) 
           (l : list (chomsky_grammar U)) :
           chomsky_grammar (chomsky_union_var U) :=
  {|
      grammar_start := start_rule U;
      grammar_rules := chomsky_rules_union U eqb l 
  |}.

Record isBoolEq (U: Type) :=  {
      eqb : U -> U -> bool; 
      eqb_eq : forall x y, eqb x y = true <-> eq x y           
}.

Lemma redundant_rules (U : Type) (start : U)
      (rules : list (chomsky_rule U))
      (big_rules : list (chomsky_rule U))
      (w : word):
    (forall a : (chomsky_rule U), In a rules -> In a big_rules) ->      
    der U rules start w ->
    der U big_rules start w.
Proof.
  intros H D.
  induction D.
  apply nonterm_rule_app with (r1 := r1) (r2 := r2).
  apply H.
  apply H0.
  apply IHD1.
  apply IHD2.
  apply terminal_rule_app.
  apply H.
  apply H0.
Qed.

Lemma chomsky_union_lemma_fwd_0:
  forall (U : Type) (H : isBoolEq U)
         (start : U) (rules : list (chomsky_rule U))
         (r : U) (n : nat)
         (w: word)
         (H0 : der U rules r w),
    der (chomsky_union_var U)
        (chomsky_rules_conv U n (eqb U H) start rules)
        (un_rule U n r) w.
Proof.
  intros.
  induction H0.
  apply nonterm_rule_app with (r1 := (un_rule U n r1)) (r2 := (un_rule U n r2)).
  clear H0_ H0_0 IHder1 IHder2.
  induction rules.
  simpl in H0.
  contradiction.
  simpl in H0.
  destruct H0.
  simpl.
  left.
  rewrite H0.
  simpl.
  reflexivity.
  right.
  apply in_app_iff.
  right.
  apply IHrules.
  exact H0.
  exact IHder1.
  exact IHder2.
  apply terminal_rule_app.
  induction rules.
  simpl in H0.
  contradiction.
  simpl in H0.
  destruct H0.
  simpl.
  left.
  rewrite H0.
  reflexivity.
  simpl.
  right.
  apply in_app_iff.
  right.
  apply IHrules.
  exact H0.
Qed.


Lemma chomsky_union_lemma_fwd_1 (U : Type) (H : isBoolEq U)
      (start : U) (rules : list (chomsky_rule U))
      (n : nat)
      (w: word)
      (H0 : der U rules start w)
      (other : list (chomsky_rule (chomsky_union_var U))):  
    der (chomsky_union_var U)
        ((chomsky_rules_conv U n (eqb U H) start rules) ++ other)
        (start_rule U) w.
Proof.
  apply redundant_rules with (rules := chomsky_rules_conv U n (eqb U H) start rules).
  intros.
  apply in_app_iff.
  left.
  exact H1.  
  assert (H1: eqb U H start start = true).
  destruct H.
  simpl.
  apply eqb_eq0.
  reflexivity.

  destruct H0.
  - apply nonterm_rule_app with (r1 := (un_rule U n r1)) (r2 := (un_rule U n r2)).
    clear H0_.
    clear H0_0.
    induction rules.
    simpl in H0.
    contradiction.
    destruct H0.
    + apply in_app_iff.
      left.
      simpl.
      right.
      rewrite H0.
      unfold chomsky_rules_s_conv.
      rewrite H1.
      apply in_eq.
    + simpl.
      right.
      apply in_app_iff.
      right.
      apply IHrules.
      exact H0.
    + apply chomsky_union_lemma_fwd_0.
      exact H0_.
    + apply chomsky_union_lemma_fwd_0.
      exact H0_0.
  - apply terminal_rule_app.
    induction rules.
    simpl in H0.
    contradiction.
    simpl.
    simpl in H0.
    destruct H0.
    + right.
      apply in_app_iff.
      left.
      rewrite H0.
      unfold chomsky_rules_s_conv.
      rewrite H1.
      apply in_eq.
    + right.
      apply in_app_iff.
      right.
      apply IHrules.
      exact H0.
Qed.  
    
Lemma chomsky_union_lemma_fwd:
  forall (U : Type) (H : isBoolEq U) (l : list (chomsky_grammar U)) (w: word),
  language_list_union (map (chomsky_language U) l) w ->
  chomsky_language (chomsky_union_var U) (chomsky_grammar_union U (eqb U H) l) w.
Proof.
  intros.
  induction l.
  simpl in H0.
  contradiction.
  simpl in H0.
  destruct H0.
  - clear IHl.
    unfold chomsky_language in H0.
    destruct a.
    simpl in H0.
    unfold chomsky_grammar_union.
    simpl.
    unfold chomsky_grammar_cov.
    simpl.
    unfold chomsky_language.
    simpl.
    apply chomsky_union_lemma_fwd_1.
    exact H0.  
  - remember (start_rule U) as new_sart.
    unfold chomsky_grammar_union.
    unfold chomsky_language.
    simpl.
    apply redundant_rules with (rules := enumerate (chomsky_grammar U) (chomsky_rule (chomsky_union_var U))
       (fun (g : chomsky_grammar U) (n : nat) => chomsky_grammar_cov U n (eqb U H) g)
       l).
    intros.
    apply in_app_iff.
    right.
    exact H1.
    apply IHl.
    exact H0.
Qed.


Inductive is_un_rule (U : Type)
          (start : U)
          (rules: list (chomsky_rule U)):
  (chomsky_rule (chomsky_union_var U)) -> Prop :=
|  mk_noterm_un_rule : forall (n : nat) (r: U) (r1: U) (r2: U),
    In (nonterm_rule U r r1 r2) rules ->
    is_un_rule U start rules
               (nonterm_rule (chomsky_union_var U)
                             (un_rule U n r) (un_rule U n r1) (un_rule U n r2))

|  mk_noterm_un_rule_start : forall (n : nat) (r1: U) (r2: U),
    In (nonterm_rule U start r1 r2) rules ->
    is_un_rule U start rules
               (nonterm_rule (chomsky_union_var U)
                             (start_rule U) (un_rule U n r1) (un_rule U n r2))       
|  mk_terminal_un_rule : forall (n : nat) (r: U) (t: ter),
    In (terminal_rule U r t) rules ->
    is_un_rule U start rules 
               (terminal_rule (chomsky_union_var U)
                              (un_rule U n r) t)
|  mk_terminal_un_rule_start : forall (t: ter),
    In (terminal_rule U start t) rules ->
    is_un_rule U start rules 
               (terminal_rule (chomsky_union_var U)
                   (start_rule U) t).

Definition rule_left_part U (r : chomsky_rule U): U :=
  match r with
  |  nonterm_rule _ v _ _ => v
  |  terminal_rule _ v _ => v
  end.

Lemma chomsky_union_lemma_bkw_sublemma
      (U : Type) (H : isBoolEq U)
      (a : chomsky_grammar U)
      (r : chomsky_union_var U)
      (n0 : nat)
      (r3 : U)
      (w : word):
 (un_rule U n0 r3) = r ->
 (exists (n1 : nat) (r2 : U),
          un_rule U n1 r2 = r /\ der U (grammar_rules U a) r2 w) ->
 der U (grammar_rules U a) r3 w.
Proof.
  intros.
  elim H1.
  intros.
  elim H2.
  intros.
  clear H1 H2.
  destruct H3.
  rewrite <- H0 in H1.
  assert (Heq : x0 = r3).
  congruence.
  rewrite Heq in H2.
  exact H2.
Qed.

Lemma rule_conv_lemma (U : Type) (H : isBoolEq U)
      (a : chomsky_grammar U)
      (r : chomsky_rule (chomsky_union_var U))
      (n : nat):
             In r (chomsky_grammar_cov U n (eqb U H) a) ->
             is_un_rule U (grammar_start U a) (grammar_rules U a) r.
Proof.
  intros.
  destruct a.
  simpl.
  unfold chomsky_grammar_cov in H0.
  simpl in H0.
  induction grammar_rules.
  simpl in H0.
  contradiction.
  simpl in H0.
  destruct H0.
  - destruct a.
    + simpl in H0.
      rewrite <- H0.
      apply mk_noterm_un_rule.
      apply in_eq.
    + simpl in H0.
      rewrite <- H0.
      apply mk_terminal_un_rule.
      apply in_eq.
  - apply in_app_iff in H0.
    destruct H0.
    + destruct a.
      simpl in H0.
      remember (eqb U H grammar_start u) as b in H0.
      destruct b.
      simpl in H0.
      destruct H0.
      rewrite <- H0.
      apply mk_noterm_un_rule_start.
      destruct H.
      simpl in Heqb.
      apply eq_sym in Heqb.
      apply eqb_eq0 in Heqb.
      rewrite Heqb.
      apply in_eq.
      contradiction.
      simpl in H0.
      contradiction.
      simpl in H0.
      remember (eqb U H grammar_start u) as b in H0.
      destruct b.
      simpl in H0.
      destruct H0.
      rewrite <- H0.
      apply mk_terminal_un_rule_start.
      destruct H.
      simpl in Heqb.
      apply eq_sym in Heqb.
      apply eqb_eq0 in Heqb.
      rewrite Heqb.
      apply in_eq.
      contradiction.
      simpl.
      contradiction.        
    + assert (is_un_rule U grammar_start grammar_rules r).
      apply (IHgrammar_rules H0).
      clear IHgrammar_rules H0.
      destruct H1.
      apply mk_noterm_un_rule.
      simpl; right.
      exact H0.
      apply mk_noterm_un_rule_start.
      simpl; right.
      exact H0.
      apply mk_terminal_un_rule.
      simpl; right.
      exact H0.
      apply mk_terminal_un_rule_start.
      simpl; right.
      exact H0.
Qed.
  
Lemma chomsky_union_lemma_bkw_0
      (U : Type) (H : isBoolEq U)
      (a : chomsky_grammar U)
      (r : chomsky_union_var U)
      (n : nat)
      (l : list (chomsky_grammar U)) (w: word)
      (n1 : nat) (r1 : U):
  (un_rule U n1 r1) = r ->
  der (chomsky_union_var U) (chomsky_grammar_cov U n (eqb U H) a) r w ->
  der U (grammar_rules U a) r1 w.
Proof.
  intros.
  revert H0.
  revert r1 n1.
 
  induction H1.
  intros.
  assert (IS: is_un_rule U (grammar_start U a) (grammar_rules U a) 
                          (nonterm_rule (chomsky_union_var U) r r1 r2)).
  apply rule_conv_lemma with (H := H) (n:=n).
  exact H0.
  remember (nonterm_rule (chomsky_union_var U) r r1 r2) as rule.  
  destruct IS.
  apply nonterm_rule_app with (r1 := r4) (r2 := r5).
  rewrite <- H1 in Heqrule.
  assert (r0 = r3).
  congruence.
  rewrite H3.
  exact H2.
  apply (IHder1 r4 n0).
  congruence.
  apply (IHder2 r5 n0).
  congruence.

  rewrite <- H1 in Heqrule.
  discriminate Heqrule.
  discriminate Heqrule.
  discriminate Heqrule.

  intros.
  assert (IS: is_un_rule U (grammar_start U a) (grammar_rules U a) 
                        (terminal_rule (chomsky_union_var U) r t)).
  apply rule_conv_lemma with (H := H) (n:=n).
  exact H0.
  remember (terminal_rule (chomsky_union_var U) r t) as rule.  
  destruct IS.
  discriminate Heqrule.
  discriminate Heqrule.
  apply terminal_rule_app.
  assert (t = t0).
  congruence.
  assert (r1 = r0).
  congruence.
  rewrite H3.
  rewrite H4.
  exact H2.
  rewrite <- H1 in Heqrule.
  discriminate Heqrule.  
Qed.



Lemma len_is_n (U : Type) (H : isBoolEq U)
      (a : chomsky_grammar U)
      (n0 n : nat)
      (r0 : U)
      (r1 r2: chomsky_union_var U):
  In (nonterm_rule (chomsky_union_var U) (un_rule U n r0) r1 r2)
     (chomsky_grammar_cov U n0 (eqb U H) a) ->
  n = n0.
Proof.
  intros.
  destruct a.
  unfold chomsky_grammar_cov in H0.
  simpl in H0.
  induction grammar_rules.
  - simpl in H0.
    contradiction.
  - simpl in H0.
    destruct H0.
    destruct a.
    simpl in H0.
    congruence.
    simpl in H0.
    discriminate H0.
    apply in_app_iff in H0.
    destruct H0.
    destruct a.
    simpl in H0.
    destruct (eqb U H grammar_start u) in H0.
    apply in_single_list in H0.
    discriminate H0.
    simpl in H0.
    contradiction.
    simpl in H0.
    destruct (eqb U H grammar_start u) in H0.
    apply in_single_list in H0.
    discriminate H0.
    simpl in H0.
    contradiction.
    apply (IHgrammar_rules H0).
Qed.  

Lemma le_contr (n : nat):
        S n <= n -> False.
Proof.
  apply lt_not_le.
  apply le_lt_n_Sm.
  exact (le_n n).
Qed.    
  
Lemma too_big_n (U : Type) (H : isBoolEq U)
      (l : list (chomsky_grammar U))
      (n : nat)
      (r0 : U)
      (r1 r2 : chomsky_union_var U):
  (length l <= n) ->
  In (nonterm_rule (chomsky_union_var U) (un_rule U n r0) r1 r2)
     (chomsky_rules_union _ (eqb U H) l) -> False.
Proof.
  intros.
  induction l.
  simpl in H1.
  contradiction.
  unfold chomsky_rules_union in H1.
  simpl in H1.
  apply in_app_iff in H1.
  destruct H1.
  apply len_is_n in H1.
  simpl in H0.
  rewrite <- H1 in H0.
  apply le_contr in H0.
  contradiction.
  apply IHl.
  simpl in H0.
  apply le_Sn_le.
  exact H0.
  exact H1.
Qed.

Lemma chomsky_union_lemma_bkw_one (U : Type) (H : isBoolEq U)
      (a : chomsky_grammar U)
      (l : list (chomsky_grammar U))
      (n : nat)
      (r0 : U)
      (r : chomsky_union_var U) (w: word):
  ((un_rule U n r0) = r) -> (n = length l) ->
  der (chomsky_union_var U) (chomsky_rules_union U (eqb U H) (a :: l)) r w ->
  der (chomsky_union_var U) (chomsky_grammar_cov U n (eqb U H) a) r w.
Proof.
  intros.
  remember (chomsky_rules_union U (eqb U H) (a :: l)) as rules.
  revert H0.
  revert r0.
  induction H2.
  rewrite Heqrules in H0.
  unfold chomsky_rules_union in H0.
  simpl in H0.
  apply in_app_iff in H0.
  destruct H0.
  intros.
 
  remember (nonterm_rule (chomsky_union_var U) r r1 r2) as rule.

  assert(IS : is_un_rule U (grammar_start U a) (grammar_rules U a) rule).
  apply rule_conv_lemma with (H := H) (n := n).
  rewrite H1.
  exact H0.  
  rewrite <- H2 in Heqrule. 
  destruct IS. 
  
  apply nonterm_rule_app with (r1 := r1) (r2 := r2).
  rewrite H1.
  rewrite <- H2.
  rewrite <- Heqrule.
  exact H0.
  apply (IHder1 r4).
  congruence.
  apply (IHder2 r5).
  congruence.
  discriminate Heqrule.
  discriminate Heqrule.
  discriminate Heqrule.
  intros.
  rewrite <- H2 in H0.
  apply too_big_n in H0.
  contradiction.
  rewrite H1.
  apply le_n.
  
  rewrite Heqrules in H0.
  
  simpl in H0.
  remember (terminal_rule (chomsky_union_var U) r t) as rule.
  unfold chomsky_rules_union in H0.
  simpl in H0.
  apply in_app_iff in H0.
  destruct H0.

  assert(IS : is_un_rule U (grammar_start U a) (grammar_rules U a) rule).
  apply rule_conv_lemma with (H := H) (n := n).
  rewrite H1.
  exact H0.
  destruct IS. 


  

Lemma chomsky_union_lemma_bkw_one (U : Type) (H : isBoolEq U)
         (l : list (chomsky_grammar U)) (w: word):
  der (chomsky_union_var U)
      (chomsky_rules_union U (eqb U H) l)
      (start_rule U) w ->
    exists (a : chomsky_grammar U),
      In a l /\ der U (grammar_rules U a) (grammar_start U a) w.
Proof.
  intros.
  destruct H0.
  induction l.
  simpl in H0.
  contradiction.
  simpl in H0.
  unfold chomsky_rules_union in H0.
  simpl in H0.
  apply in_app_iff in H0.
  destruct H0.
  clear IHl.
  exists a.
  split.
  apply in_eq.
  remember (nonterm_rule (chomsky_union_var U) (start_rule U) r1 r2) as rule.
  assert (IS : is_un_rule U (grammar_start U a) (grammar_rules U a) rule).
  apply rule_conv_lemma with (H := H) (n:=length l).
  exact H0.
  destruct IS.
  discriminate Heqrule.
  apply nonterm_rule_app with (r1 := r0) (r2 := r3).
  exact H1.
  apply chomsky_union_lemma_bkw_0 with (H := H) (r := r1) (n := n) (n1 := n).
  exact l.
  congruence.
  apply len_is_n in h1.
  
  
  
  

Lemma chomsky_union_lemma_bkw_1:
  forall (U : Type) (H : isBoolEq U)
         (a : chomsky_grammar U)
         (l : list (chomsky_grammar U)) (w: word),
    der (chomsky_union_var U) (chomsky_rules_union U (eqb U H) (a :: l))
         (start_rule U) w ->
    der U (grammar_rules U a) (grammar_start U a) w  \/
    der (chomsky_union_var U) (chomsky_rules_union U (eqb U H) l) 
          (start_rule U) w.
Proof.
  enough (clean_der: forall (U : Type) (H : isBoolEq U)
         (a : chomsky_grammar U)
         (l : list (chomsky_grammar U))
         (n : nat)
         (r0 : U)
         (r : chomsky_union_var U)
         (w: word),
  (r = un_rule U n r0) ->
  (der _ (chomsky_rules_union U (eqb U H) (a :: l)) r w)->
  (der _ (chomsky_grammar_cov U n (eqb U H) a) r w)
      ).
  intros.
  remember (chomsky_rules_union U (eqb U H) (a :: l)) as rules in H0.
  
  destruct H0.
  - rewrite Heqrules in H0.
    unfold chomsky_rules_union in H0.
    simpl.
    simpl in H0.
    apply in_app_iff in H0.
    destruct H0.
    + left.
      remember (nonterm_rule (chomsky_union_var U) (start_rule U) r1 r2) as rule.  
      apply rule_conv_lemma in H0.
      destruct H0.
      discriminate Heqrule.
      apply nonterm_rule_app with (r1 := r0) (r2 := r3).
      exact H0.
      apply chomsky_union_lemma_bkw_0 with (H := H) (r := r1) (n := n) (n1 := n) . 
      exact l.
      congruence.
      apply clean_der with (l := l) (r0 := r0).
      congruence.
      rewrite <- Heqrules. 
      exact H0_.

      apply chomsky_union_lemma_bkw_0 with (H := H) (r := r2) (n := n) (n1 := n) . 
      exact l.
      congruence.
      apply clean_der with (l := l) (r0 := r3).
      congruence.
      rewrite <- Heqrules. 
      exact H0_0.
      discriminate Heqrule.
      discriminate Heqrule.
    + right.
      assert (D1 : der (chomsky_union_var U) rules (start_rule U) (w1 ++ w2)).
      apply nonterm_rule_app with (r1 := r1) (r2 := r2).
      rewrite Heqrules.
      apply in_app_iff.
      right.
      exact H0.
      exact H0_.
      exact H0_0.
      remember (nonterm_rule (chomsky_union_var U) (start_rule U) r1 r2) as rule.
      apply nonterm_rule_app with (r1 := r1) (r2 := r2).
      rewrite <- Heqrule.
      exact H0.
      apply chomsky_union_lemma_bkw_0 with (H := H) (r := r1) (n := length l) (n1 := length l) . 




    
  
Lemma chomsky_union_lemma_bkw:
  forall (U : Type) (H : isBoolEq U) (l : list (chomsky_grammar U)) (w: word),
    chomsky_language (chomsky_union_var U) (chomsky_grammar_union U (eqb U H) l) w ->
    language_list_union (map (chomsky_language U) l) w.
Proof.
  unfold chomsky_grammar_union.
  unfold chomsky_language .
  simpl.
  intros.
  induction l.
  - unfold chomsky_grammar_union in H0.
    simpl in H0.
    destruct H0.
    + simpl in H0.
      contradiction.
    + simpl in H0.
      contradiction.
  - simpl in H0.
    simpl.
    
  
Lemma chomsky_union_lemma:
  forall (U : Type) (H : isBoolEq U) (l : list (chomsky_grammar U)),
  language_list_union (map (chomsky_language U) l) [==]
  chomsky_language (chomsky_union_var U) (chomsky_grammar_union U (eqb U H) l).
Proof.
  intros.

Qed.