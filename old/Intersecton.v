Require Import Base.
Require Import List.
Require Import Fin.
Require Import DFA.


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


Inductive tr (U : Type) (n : nat) :=
    | mk_triple : (t n) -> U -> (t n) -> tr U n. 


Theorem lt_Sn_lt (m : nat) (n : nat) (prop : S m < n): m < n.
Proof.
  induction prop.
  auto.
  auto.
Qed.


Fixpoint values_list (n : nat) : list (t n) :=
  match  n with
  | O => nil
  | S n' => F1 :: (map FS (values_list n'))
  end.     

Theorem map_f : forall (U : Type) (U2 : Type) (v : U) (l : list U) (f : U -> U2),
    In v l -> In (f v) (map f l).
Proof.
  intros.
  induction l.
  simpl in H.
  auto.
  simpl.
  simpl in H.
  destruct H. 
  left.    
  exact (f_equal f H). 
  right.
  exact (IHl H).
Qed.
     
Theorem all_values_in_list : forall (n : nat) (f : t n), In f (values_list n).
Proof.    
  intros n f.
  induction f.
  simpl.
  auto.
  simpl.
  right.
  apply map_f.
  exact IHf.   
Qed.


Definition convert_nonterm_rule_2
         (U : Type) (n : nat) 
         (r: U) (r1: U) (r2: U)
         (s1 : t n) (s2 : t n): list (chomsky_rule (tr U n)) :=
   map (fun s3 => nonterm_rule (tr U n)
                   (mk_triple U n s1 r s3)
                   (mk_triple U n s1 r1 s2)
                   (mk_triple U n s2 r2 s3)   
       ) (values_list n).
   
Definition convert_nonterm_rule_1
         (U : Type) (n : nat) 
         (r: U) (r1: U) (r2: U)
         (s1 : t n): list (chomsky_rule (tr U n)) :=
  flat_map (convert_nonterm_rule_2 U n r r1 r2 s1) (values_list n).

Definition convert_nonterm_rule
         (U : Type) (n : nat) 
         (r: U) (r1: U) (r2: U) : list (chomsky_rule (tr U n)) :=
  flat_map ( convert_nonterm_rule_1 U n r r1 r2) (values_list n).


Definition convert_terminal_rule
         (U : Type) (n : nat) (next : (t n) -> ter -> (t n))
         (r: U) (t: ter): list (chomsky_rule (tr U n)) :=
 map (fun s1 =>
       terminal_rule (tr U n)
                     (mk_triple U n s1 r (next s1 t))
                     t         
     ) (values_list n).
                                                     
Definition convert_rule (U : Type) (n : nat) (next : (t n) -> ter -> (t n))
           (r : chomsky_rule U): list (chomsky_rule (tr U n)) :=
  match r with
  |   nonterm_rule _ r r1 r2 => convert_nonterm_rule U n r r1 r2
  |   terminal_rule _ r t => convert_terminal_rule U n next r t
  end.


Definition convert_rules
           (U : Type) (n : nat) (next : (t n) -> ter -> (t n))
           (g : list (chomsky_rule U)): list (chomsky_rule (tr U n)) :=
    (flat_map (convert_rule U n next) g).

Definition convert_grammar
           (U : Type) (n : nat) (d : s_dfa n)
           (g : chomsky_grammar U): (chomsky_grammar (tr U n)) :=
  make_chomsky_grammar (tr U n)
    (mk_triple U n (s_start n d) (grammar_start U g) (s_final n d))
    (convert_rules U n (s_next n d) (grammar_rules U g)).
  

Theorem test0: forall (n : nat)
                      (w1 w2 : word)
                      (next : (t n) -> ter -> (t n))
                      (from to: (t n))
                      (H0 : final_state next from (w1 ++ w2) = to),
     final_state next (final_state next from w1) w2 = to.
Proof.
  intros n w1 w2 next.
  induction w1.
  simpl.
  auto.
  simpl.
  intros from to.
  apply IHw1.  
Qed.

Inductive rule_conversion (U : Type)
          (n : nat)
          (rules : list (chomsky_rule U))
          (next : (t n) -> ter -> (t n)): (chomsky_rule (tr U n)) -> Prop :=
| nonterm_rule_conversion : forall (r r1 r2: U) (s1 s2 s3: t n),  
     In (nonterm_rule U r r1 r2) rules ->
     rule_conversion U n rules next (nonterm_rule (tr U n)
                                            (mk_triple U n s1 r s3)
                                            (mk_triple U n s1 r1 s2)
                                            (mk_triple U n s2 r2 s3))
| term_rule_conversion : forall (r: U) (s1: t n) (te : ter),
    In (terminal_rule U r te) rules ->
    rule_conversion U n rules next (terminal_rule (tr U n)
                                            (mk_triple U n s1 r (next s1 te)) te).


Lemma conversion_nonterm_lemma_2 : forall (U : Type) (n : nat)
                                   (rules : list (chomsky_rule U))
                                   (next : t n -> ter -> t n)
                                   (r_n: chomsky_rule (tr U n))
                                   (r: U) (r1: U) (r2: U)
                                   (s1 s2: t n),
    In (nonterm_rule U r r1 r2) rules ->
    In r_n (convert_nonterm_rule_2 U n r r1 r2 s1 s2) ->
    rule_conversion U n rules next r_n.
Proof.  
  intros U n rules next r_n r0 r1 r2 s1 s2 H_in H0.
  unfold convert_nonterm_rule_2 in H0.
  set (vals := (values_list n)) in H0.
  induction vals.
  simpl in H0.
  contradiction.
  simpl in H0.
  destruct H0.
  rewrite <- H.
  exact (nonterm_rule_conversion U n rules next r0 r1 r2 s1 s2 a H_in).
  apply IHvals.
  exact H.
Qed.

Lemma conversion_nonterm_lemma_1 : forall (U : Type) (n : nat)
                                   (rules : list (chomsky_rule U))
                                   (next : t n -> ter -> t n)
                                   (r_n: chomsky_rule (tr U n))
                                   (r: U) (r1: U) (r2: U)
                                   (s1 : t n),
    In (nonterm_rule U r r1 r2) rules ->
    In r_n (convert_nonterm_rule_1 U n r r1 r2 s1) ->
    rule_conversion U n rules next r_n.
Proof.
  intros U n rules next r_n r0 r1 r2 s1 H_in H0.
  unfold convert_nonterm_rule_1 in H0.
  set (vals := (values_list n)) in H0.
  induction vals.
  simpl in H0.
  contradiction.
  simpl in H0.
  assert (H1: In r_n (convert_nonterm_rule_2 U n r0 r1 r2 s1 a) \/
              In r_n (flat_map (convert_nonterm_rule_2 U n r0 r1 r2 s1) vals)).
  apply in_app_or.
  exact H0.
  clear H0.
  destruct H1.
  exact (conversion_nonterm_lemma_2 U n rules next r_n r0 r1 r2 s1 a H_in H).
  apply IHvals.
  exact H.
Qed.


Lemma conversion_nonterm_lemma : forall (U : Type) (n : nat)
                                   (rules : list (chomsky_rule U))
                                   (next : t n -> ter -> t n)
                                   (r_n: chomsky_rule (tr U n))
                                   (r: U) (r1: U) (r2: U),
     In (nonterm_rule U r r1 r2) rules ->
     In r_n (convert_nonterm_rule U n r r1 r2) ->
     rule_conversion U n rules next r_n.
Proof.
  intros U n rules next r_n r0 r1 r2 H_in H0.
  unfold convert_nonterm_rule in H0.
  set (vals := (values_list n)) in H0.
  induction vals.
  simpl in H0.
  contradiction.
  simpl in H0.
  assert (H1: In r_n (convert_nonterm_rule_1 U n r0 r1 r2 a) \/
              In r_n (flat_map (convert_nonterm_rule_1 U n r0 r1 r2) vals)).
  apply in_app_or.
  exact H0.
  clear H0.
  destruct H1.
  exact (conversion_nonterm_lemma_1 U n rules next r_n r0 r1 r2 a H_in H).
  apply IHvals.
  exact H.   
Qed.


Lemma conversion_term_lemma : forall (U : Type) (n : nat)
  (u : U) (te : ter) (rules : list (chomsky_rule U))
  (next : t n -> ter -> t n)
  (r : chomsky_rule (tr U n)),

    In (terminal_rule U u te) rules ->
  (In r (convert_terminal_rule U n next u te)) ->
  rule_conversion U n rules next r.
Proof.
  intros U n u te rules next r H_in H0.
  unfold convert_terminal_rule in H0.
  set (vals := (values_list n)) in H0.
  induction vals.
  simpl in H0.
  contradiction.
  simpl in H0.
  destruct H0.
  rewrite <- H.
  exact (term_rule_conversion U n rules next u a te H_in).
  apply IHvals.
  exact H.
Qed.

Lemma conversion_update : forall (U : Type) (n : nat)
                                 (a : chomsky_rule U)
                                 (rules : list (chomsky_rule U))
                                 (next : t n -> ter -> t n)
                                 (r : chomsky_rule (tr U n)),
    rule_conversion U n rules next r -> rule_conversion U n (a :: rules) next r.
Proof.
  intros U n a rules next r H0.
  destruct H0.
  apply nonterm_rule_conversion.
  apply in_cons; exact H.
  apply term_rule_conversion.
  apply in_cons; exact H.
Qed.       

Lemma conversion_lemma : forall (U : Type) (n : nat)
                                   (rules : list (chomsky_rule U))
                                   (next : t n -> ter -> t n)
                                   (r : chomsky_rule (tr U n)),
                        In r (convert_rules U n next rules) ->
                        rule_conversion U n rules next r.
Proof.
  intros U n rules next r H0.
  induction rules.
  simpl in H0.
  contradiction.
  simpl in H0.
  assert (H1: In r (convert_rule U n next a) \/ In r (convert_rules U n next rules)).
  apply in_app_or.
  exact H0.
  clear H0.  
  destruct H1.
  destruct a.
  simpl in H.
  apply conversion_nonterm_lemma with (r := u) (r1 := u0) (r2 := u1).
  apply in_eq.
  exact H.
  simpl in H.
  apply conversion_term_lemma with (u := u) (te := t).
  apply in_eq.
  exact H.
  apply conversion_update.
  apply IHrules.
  exact H.
Qed.


Lemma new_rule_2: forall (U : Type) (n : nat)
                         (next : (t n) -> ter -> (t n))
                         (from m to: (t n))
                         (r r1 r2: U),
    (In (nonterm_rule (tr U n)
                      (mk_triple U n from r to)
                      (mk_triple U n from r1 m)
                      (mk_triple U n m r2 to))
        (convert_nonterm_rule_2 U n r r1 r2 from m)).
Proof.
  intros U n next from m to r r1 r2.
  set (rule := nonterm_rule (tr U n)
                            (mk_triple U n from r to)
                            (mk_triple U n from r1 m)
                            (mk_triple U n m r2 to)).
  unfold convert_nonterm_rule_2.
  set (vals := (values_list n)).
  assert (H2: In to vals).
  apply all_values_in_list.  
  induction vals.
  simpl in H2.
  contradiction.
  simpl.  
  simpl in H2.
  destruct H2.
  left.
  rewrite H.
  auto.
  right.
  apply IHvals.
  exact H.
Qed.

Lemma new_rule_1: forall (U : Type) (n : nat)
                         (next : (t n) -> ter -> (t n))
                         (from m to: (t n))
                         (r r1 r2: U),
    (In (nonterm_rule (tr U n)
                      (mk_triple U n from r to)
                      (mk_triple U n from r1 m)
                      (mk_triple U n m r2 to))
        (convert_nonterm_rule_1 U n r r1 r2 from)).
Proof.
  intros U n next from m to r r1 r2.
  set (rule := nonterm_rule (tr U n)
                            (mk_triple U n from r to)
                            (mk_triple U n from r1 m)
                            (mk_triple U n m r2 to)).
  unfold convert_nonterm_rule_1.
  set (vals := (values_list n)).
  assert (H2: In m vals).
  apply all_values_in_list.
  induction vals.
  simpl in H2.
  contradiction.
  simpl.  
  simpl in H2.
  apply in_or_app.
  destruct H2.
  left.
  rewrite H.
  apply new_rule_2.
  exact next.
  right.
  apply IHvals.
  apply H.
Qed.

Lemma new_rule_0: forall (U : Type) (n : nat)
                         (next : (t n) -> ter -> (t n))
                         (from m to: (t n))
                         (rules : list (chomsky_rule U))
                         (r r1 r2: U),
    (In (nonterm_rule U r r1 r2) rules) ->
    (In (nonterm_rule (tr U n) (mk_triple U n from r to) (mk_triple U n from r1 m) (mk_triple U n m r2 to)) (convert_rules U n next rules)).
Proof.
  intros U n next from m to rules r r1 r2 H0.
  induction rules.
  simpl.  
  auto.
  simpl.
  simpl in H0.
  destruct H0.
  apply in_or_app.
  left.
  clear IHrules.
  rewrite H.
  simpl.
  set (rule := nonterm_rule (tr U n)
                            (mk_triple U n from r to)
                            (mk_triple U n from r1 m)
                            (mk_triple U n m r2 to)).
  unfold convert_nonterm_rule.
  set (vl := (values_list n)).
  assert (H2: In from vl).
  apply all_values_in_list.  
  induction vl.
  simpl in H2.
  contradiction.  
  simpl in H2.
  destruct H2.  
  simpl.
  apply in_or_app.
  left.
  rewrite H0.
  apply new_rule_1.
  exact next.
  simpl.
  apply in_or_app.
  right.
  apply IHvl.  
  apply H0.
  apply in_or_app.
  right.
  apply IHrules.
  apply H.
Qed.


Lemma in_terminal: forall
    (U : Type) (n : nat)
    (rules : list (chomsky_rule U))
    (r : U)
    (te : ter)
    (next : t n -> ter -> t n)
    (from to : t n),
    (In (terminal_rule U r te) rules) ->  
    (next from te = to) ->
    In (terminal_rule (tr U n) (mk_triple U n from r to) te) (convert_rules U n next rules).
  intros U n rules r te next from to H0 H1.
  induction rules.
  simpl in H0.
  contradiction.
  simpl in H0.
  destruct H0.
  simpl.
  apply in_or_app.
  left.
  rewrite H.
  simpl.
  unfold convert_terminal_rule.
  set (vals := (values_list n)).
  assert (H2: In from vals).
  apply all_values_in_list.
  induction vals.
  simpl in H2.
  contradiction.
  simpl in H2.
  destruct H2.
  simpl.
  left.
  rewrite H0.
  rewrite H1.
  reflexivity.
  simpl.
  right.
  apply IHvals.
  apply H0.
  simpl.
  apply in_or_app.
  right.
  apply IHrules.
  apply H.
Qed.

Theorem main_theorem: forall (U : Type)
                      (n : nat)
                      (w : word)
                      (rules : list (chomsky_rule U))
                      (r : U)
                      (gr : der U rules r w)
                      (next : (t n) -> ter -> (t n))
                      (from to: (t n))
                      (H0 : (final_state next from w = to)),
    der (tr U n) (convert_rules U n next rules) (mk_triple U n from r to) w.
Proof.
  intros U n w rules r gr next.
  set (new_rules := convert_rules U n next rules).
  induction gr.               
  intros from0 to0 H0.
  set (m := final_state next from0 w1).
  assert (new_gr1 : der (tr U n) new_rules (mk_triple U n from0 r1 m) w1).
  apply IHgr1.
  auto.
  assert (new_gr2 : der (tr U n) new_rules (mk_triple U n m r2 to0) w2).
  apply IHgr2.
  apply test0.
  exact H0.
  
  assert (in_H : In (nonterm_rule (tr U n)
                           (mk_triple U n from0 r to0)
                           (mk_triple U n from0 r1 m)
                           (mk_triple U n m r2 to0)) new_rules).
  apply new_rule_0.
  exact H.
  exact (nonterm_rule_app (tr U n) new_rules (mk_triple U n from0 r to0)
                          (mk_triple U n from0 r1 m) w1
                          (mk_triple U n m r2 to0) w2
                          in_H
                          new_gr1 new_gr2).
  simpl.  
  intros from to H0.
  apply terminal_rule_app.
  apply in_terminal.
  exact H.
  exact H0.
Qed.

Theorem main_forward: forall (U : Type) (n : nat)
                     (d : s_dfa n) (g : chomsky_grammar U) (w : word),
    (s_dfa_language d) w /\ (chomsky_language U g) w ->
                (chomsky_language (tr U n) (convert_grammar U n d g) w).
Proof.
  intros.
  destruct H as [H1 H2].
  unfold chomsky_language in H2.
  unfold s_dfa_language in H1.
  unfold s_accepts in H1.
  unfold chomsky_language.
  apply main_theorem.
  exact H2.
  exact H1.
Qed.

Definition from_tr (U : Type) (n : nat) (t1: tr U n): (t n) :=
    match t1 with
      mk_triple _ _ from r to => from
    end.                            

Definition rule_tr (U : Type) (n : nat) (t1: tr U n): U :=
    match t1 with
      mk_triple _ _ from r to => r
    end.  

Definition to_tr (U : Type) (n : nat) (t1: tr U n): (t n) :=
    match t1 with
      mk_triple _ _ from r to => to
    end.                            

Lemma middle_lemma : forall (U : Type) (n : nat)
                            (rules : list (chomsky_rule U))
                            (next : t n -> ter -> t n)
                            (r r1 r2 : tr U n),
    In (nonterm_rule (tr U n) r r1 r2) (convert_rules U n next rules) ->
    (from_tr U n r = from_tr U n r1) /\ (to_tr U n r1) = (from_tr U n r2) /\ (to_tr U n r = to_tr U n r2).
Proof.
  intros U n rules next r r1 r2 H0.
  remember (nonterm_rule (tr U n) r r1 r2) as rule in H0.
  assert (H1 :rule_conversion U n rules next rule).
  apply (conversion_lemma U n rules).
  exact H0.
  destruct H1. 
  assert (H1: mk_triple U n s1 r0 s3 = r).
  congruence.
  assert (H2: mk_triple U n s1 r3 s2 = r1).
  congruence.
  assert (H3: mk_triple U n s2 r4 s3 = r2).
  congruence.
  rewrite <- H1.
  rewrite <- H2.
  rewrite <- H3.
  simpl.
  split.
  reflexivity.
  split.
  reflexivity.
  reflexivity.
  discriminate Heqrule.
Qed.
 
Theorem test0_1: forall (n : nat)
                      (w1 w2 : word)
                      (next : (t n) -> ter -> (t n))
                      (from to: (t n)),
     final_state next (final_state next from w1) w2 = to ->
                       final_state next from (w1 ++ w2) = to.
Proof.
  intros n w1 w2 next.
  induction w1.
  simpl.
  auto.
  simpl.
  intros from to.
  apply IHw1.  
Qed.


Lemma main_backward_1_0_0 : forall (U : Type) (n : nat)
  (rules : list (chomsky_rule U))
  (next : t n -> ter -> t n)
  (r : tr U n)
  (te : ter),
    In (terminal_rule (tr U n) r te) (convert_rules U n next rules) ->
    (next (from_tr U n r) te) = (to_tr U n r).
Proof.    
  intros U n rules next r te H0.
  remember (terminal_rule (tr U n) r te) as rule in H0.
  assert (H1 :rule_conversion U n rules next rule).  
  apply (conversion_lemma U n rules).
  exact H0.
  destruct H1.
  discriminate Heqrule.
  assert (H1: (mk_triple U n s1 r0 (next s1 te0)) = r).
  congruence.
  assert (H2: (te0 = te)).
  congruence.
  rewrite <- H1.
  rewrite <- H2.
  simpl.
  reflexivity.
Qed.

Lemma main_backward_1_0 : forall (U : Type) (n : nat)
    (w : word)
    (rules : list (chomsky_rule U))
    (next : (t n) -> ter -> (t n))
    (t1 : tr U n),
    der (tr U n) (convert_rules U n next rules) t1 w ->
    (final_state next (from_tr U n t1) w = (to_tr U n t1)).
Proof.
  intros U n w rules next t1 H0.
  induction H0.
  assert (H2 : (from_tr U n r = from_tr U n r1) /\ (to_tr U n r1) = (from_tr U n r2) /\ (to_tr U n r = to_tr U n r2)).
  exact (middle_lemma U n rules next r r1 r2 H).
  destruct H2.
  destruct H1.
  apply test0_1.
  rewrite H0.
  rewrite -> IHder1.
  rewrite H1.
  rewrite H2.
  exact  IHder2.
  simpl.
  apply (main_backward_1_0_0 U n rules).
  exact H.
Qed.

Theorem main_backward_1: forall (U : Type)
                      (n : nat)
                      (w : word)
                      (rules : list (chomsky_rule U))
                      (r : U)
                      (next : (t n) -> ter -> (t n))
                      (from to: (t n)),
    (der (tr U n) (convert_rules U n next rules) (mk_triple U n from r to)) w ->
    (final_state next from w = to).
Proof.
  intros U n w rules r next from to.
  set (rule := (mk_triple U n from r to)).
  intros H.
  assert (from = from_tr U n rule).
  simpl.
  reflexivity.
  assert (to = to_tr U n rule).
  simpl.
  reflexivity.
  rewrite H0.
  rewrite H1.
  apply (main_backward_1_0 U n w rules).
  exact H.
Qed.

Theorem main_backward_2_1: forall (U : Type) (n : nat)
  (s_next0 : t n -> ter -> t n)
  (grammar_rules : list (chomsky_rule U))
  (s : tr U n)
  (w : word),  
  der (tr U n) (convert_rules U n s_next0 grammar_rules) s w ->
  der U grammar_rules (rule_tr U n s) w.
Proof.
  intros U n next g_rules s w H.
  induction H.
  remember (nonterm_rule (tr U n) r r1 r2) as rule in H.
  assert (H2 :rule_conversion U n g_rules next rule).
  apply (conversion_lemma U n g_rules).
  exact H.
  apply (nonterm_rule_app U g_rules
                          (rule_tr U n r)
                          (rule_tr U n r1) w1
                          (rule_tr U n r2) w2).
  destruct H2.
  assert (r = (mk_triple U n s1 r0 s3)).
  congruence.
  assert (r1 = (mk_triple U n s1 r3 s2)).
  congruence.
  assert (r2 = (mk_triple U n s2 r4 s3)).
  congruence.
  rewrite H3.
  rewrite H4.
  rewrite H5.
  simpl.  
  exact H2.
  discriminate Heqrule.
  exact IHder1.
  exact IHder2.
  remember (terminal_rule (tr U n) r t) as rule in H.
  assert (H2 : rule_conversion U n g_rules next rule).
  apply (conversion_lemma U n g_rules).
  exact H.
  destruct H2.
  discriminate Heqrule.
  apply (terminal_rule_app U g_rules).
  assert (r = mk_triple U n s1 r0 (next s1 te)).
  congruence.
  rewrite H1.
  simpl.
  assert (te = t).
  congruence.
  rewrite <- H2.
  exact H0.
Qed.

Theorem main_backward_2: forall (U : Type) (n : nat)
  (s_start0 s_final0 : t n)
  (s_next0 : t n -> ter -> t n)
  (grammar_start0 : U)
  (grammar_rules0 : list (chomsky_rule U))
  (w : word),  
  der (tr U n) (convert_rules U n s_next0 grammar_rules0) 
        (mk_triple U n s_start0 grammar_start0 s_final0) w ->
  der U grammar_rules0 grammar_start0 w.
Proof.
  intros U n start final next g_start g_rules w H.
  set (s0 := (mk_triple U n start g_start final)).
  assert (g_start = rule_tr U n s0).
  simpl.  
  reflexivity.
  rewrite H0.
  apply (main_backward_2_1 U n next).
  exact H.
Qed.  
  
Theorem main_backward: forall (U : Type) (n : nat)
                     (d : s_dfa n) (g : chomsky_grammar U) (w : word),
    (chomsky_language (tr U n) (convert_grammar U n d g) w) ->
    (s_dfa_language d) w /\ (chomsky_language U g) w.
Proof.
  intros.
  unfold chomsky_language in H.
  unfold convert_grammar in H.
  simpl in H.
  destruct d.
  simpl in H.
  split.
  unfold s_dfa_language.
  unfold s_accepts.
  simpl.
  set (rules := (grammar_rules U g)) in H.
  apply (main_backward_1 U n w rules (grammar_start U g)).
  exact H.
  unfold chomsky_language.
  destruct g.
  simpl.
  simpl in H.
  apply (main_backward_2 U n s_start s_final s_next).
  exact H.
Qed.


Theorem main: forall (U : Type) (n : nat)
                     (d : s_dfa n) (g : chomsky_grammar U),
    ((s_dfa_language d) [/\] (chomsky_language U g)) [==]
                (chomsky_language (tr U n) (convert_grammar U n d g)).
Proof.
  intros. 
  apply mk_laguage_eq.
  apply main_forward.
  apply main_backward.
Qed.

