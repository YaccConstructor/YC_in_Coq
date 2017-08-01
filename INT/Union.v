Require Import List.
Require Import Fin.

Add LoadPath "../".

Require Import CFG.Base CFG.Definitions CFG.Binarize CFG.Chomsky.
Require Import INT.Base INT.DFA INT.ChomskyInduction.

Module Union.
  Import ListNotations Definitions Derivation
         INT.Base.Base INT.Base ChomskyInduction.

  Section Definitions. 

  Variable Tt Vt: Type.

  Inductive labeled_Vt : Type :=
  |  start : labeled_Vt
  |  lV : nat -> Vt -> labeled_Vt.

  Definition update_var (n : nat) (v: @var Vt): (@var labeled_Vt) :=
    match v with
    | V v => V (lV n v)
    end.
  
  Definition update_symbol (n : nat) (s: @symbol Tt Vt): (@symbol Tt labeled_Vt) :=
    match s with
    | Ts t => Ts t
    | Vs (V v) => Vs (V (lV n v))
    end.
    
  
  Definition update_rule (n : nat) (r : @rule Tt Vt): (@rule Tt labeled_Vt) :=
     match r with
     |  R (V v) p => R (V (lV n v)) (map (update_symbol n) p)
     end.

  Definition update_grammar (n : nat) (g : (@grammar Tt Vt) * Vt): @grammar Tt labeled_Vt :=
    match g with
      (gr, st) => (R (V start) [Vs (V (lV n st))]) :: (map (update_rule n) gr)
    end.

  Fixpoint grammar_union (l : list ((@grammar Tt Vt) * Vt)): @grammar Tt labeled_Vt :=
    match l with
    |  [] => []
    |  (g::t) => update_grammar (length t) g ++ (grammar_union t)
    end.

  (* TODO remove duplicate *)
  Fixpoint to_phrase (w: word): @phrase Tt Vt :=
    match w with
    | s::sx => Ts s :: to_phrase sx
    | _ => []
    end.

  Fixpoint to_word (p: @phrase Tt Vt): list ter :=
          match p with
            | Ts x :: sx => x :: to_word sx
            | _ => []
          end.

  End Definitions.

  Variable Tt Vt: Type.
  
  Definition grammar_to_languange {Vl : Type} (g : (@grammar Tt Vl) * Vl) : language :=
    match g with
      (gr, st) => fun w => (der gr (V st) (to_phrase Vl w)) 
    end.                                                  

  (*Definition ex_language (l : (@language Tt labeled_Vt)): (@language Tt Vt) :=
   *)


  Definition tranform_phrase (n : nat) (p : @phrase Tt Vt) : phrase :=
    map (update_symbol n) p.

  Lemma in_app : forall A (v : A) (l1 l2 : list A),
      In v l1 -> In v (l1 ++ l2).
  Proof.
    intros.
    induction l1.
    simpl in H; contradiction.
    simpl in H.
    destruct H.
    left.
    rewrite H.
    reflexivity.
    right.
    apply (IHl1 H).
  Qed.                                 

  (* TODO Import*)
  Definition unVar (v: var): Vt := let '(V e) := v in e.

  Lemma trasform_app : forall (n : nat) (p1 p2 : phrase),
                 tranform_phrase n (p1 ++ p2) =
                 (tranform_phrase n p1) ++ (tranform_phrase n p2).
  Proof.
    intros.
    induction p1.
    reflexivity.
    simpl.
    rewrite IHp1; reflexivity.
  Qed.
  
  Lemma same_union_0 : forall (g : grammar) (vst: Vt) (v : var)
     (l : list (grammar * Vt))
     (p : phrase)
     (d : der g v p),
      der (grammar_union (Tt:=Tt) ((g, vst) :: l)) (update_var (length l) v)
          (tranform_phrase (length l) p).
  Proof.
    intros.
    induction d.
    - destruct A.
      simpl.
      apply vDer.
        
    - apply rDer.
      simpl.
      right.
      apply in_app.
      induction g.
      simpl in H ; contradiction.
      simpl in H.
      destruct H.
      simpl.
      left.
      rewrite H.
      destruct A.
      simpl.
      reflexivity.
      simpl; right. 
      apply (IHg H).
    - rewrite trasform_app.
      rewrite trasform_app.
      apply (replN (B := (update_var (length l) B))
                   (G := (grammar_union (Tt:=Tt) ((g, vst) :: l)))
            ).
      enough (tr_eq :[Vs (update_var (length l) B)] = (tranform_phrase (length l) [Vs B])).
      rewrite tr_eq.
      rewrite <- trasform_app.
      rewrite <- trasform_app.
      apply IHd1.
      destruct B.
      simpl.
      reflexivity.
      apply IHd2.     
  Qed.  

  
  Lemma tranform_phrase_for_word : forall (n : nat) (w : word),
      to_phrase (Tt:=Tt) (labeled_Vt Vt) w =
      tranform_phrase n (to_phrase (Tt:=Tt) Vt w).
  Proof.
    intros.
    induction w.
    simpl.
    reflexivity.
    simpl.
    rewrite IHw.
    reflexivity.
  Qed.  

   Lemma in_app_2 : forall A (v : A) (l1 l2 : list A),
      In v l2 -> In v (l1 ++ l2).
  Proof.
    intros.
    induction l1.
    simpl in H; apply H.
    simpl.
    right.
    apply IHl1.
  Qed.      
  
  Lemma grammar_extention : forall (g1 g2 : @grammar Tt (labeled_Vt Vt))
                                   (v : var) (p : phrase),
      (der g2 v p) -> (der (g1 ++ g2) v p).
  Proof.
    intros.
    induction H.
    apply vDer.
    apply rDer.
    apply in_app_2.
    apply H.
    apply (replN (B := B)).
    apply IHder1.
    apply IHder2.
  Qed.
  
  Lemma same_union_fwd : forall (l : list (grammar * Vt)) (w : word),
     language_list_union (map grammar_to_languange l) w ->
     grammar_to_languange (grammar_union l, start Vt) w.
  Proof.
    intros l w H1.
    induction l.  
    simpl in H1.
    contradiction.
    simpl in H1.
    destruct H1.
    clear IHl.
    destruct a.
    unfold grammar_to_languange in H.
    unfold grammar_to_languange.
    remember (to_phrase (Tt:=Tt) Vt w) as p.
    assert  (eq1 : (to_phrase (Tt:=Tt) (labeled_Vt Vt) w) = (tranform_phrase (length l) p)).
    { rewrite Heqp;  apply tranform_phrase_for_word. }
    
    rewrite eq1.
    assert (eq2 : (tranform_phrase (length l) p) = [] ++ (tranform_phrase (length l) p) ++ []).
    { rewrite Heqp.
      simpl.
      rewrite app_nil_r.
      reflexivity. }
    
    rewrite eq2.
    apply (replN (B := (V (lV (length l) v)))).
    apply rDer.
    simpl.
    left.
    reflexivity.
    assert (eq3 : (V (lV (length l) v)) = update_var (length l) (V v)).
    { simpl ; reflexivity. }
    rewrite eq3.
    apply same_union_0.
    exact H.                 
    simpl.
    apply grammar_extention.
    apply IHl.
    apply H.
  Qed.

  Lemma empty_grammar: (forall (st : var) (p : @phrase Tt (labeled_Vt Vt)),
                           (der [] st p) -> p = [Vs st]).
  Proof.
    intros.
    induction H.
    reflexivity.
    contradiction.
    rewrite <- IHder1.
    rewrite IHder2.
    reflexivity.
  Qed.
(*
  Lemma same_union_bkw_0 : forall
    (g : grammar) (v : Vt)
    (l : list (grammar * Vt))
    (n : nat)
    (p : phrase)
    (H : der (grammar_union (Tt:=Tt) ((g, v) :: l)) (V (lV n v))
        (tranform_phrase n p)),
      der g (V v) p \/ (der (grammar_union (Tt:=Tt) l) (V (lV n v)) (tranform_phrase n p)).
*)    
(*
  Lemma der_start :
    forall (l : list (grammar * Vt)) (p : @phrase Tt (labeled_Vt Vt)),
      der (grammar_union l) (V (start Vt)) p -> p <> [(Vs (V (start Vt)))] ->
      exists n0 v0, der (grammar_union l) (V (lV n0 v0)) p.
  Proof.
    intros.
    remember (V (start Vt)) as st in H.
    induction H.
    rewrite Heqst in H0.
    contradiction.
    admit.
    enough (u ++ [Vs B] ++ w <> [Vs (V (start Vt))]).
    assert (exists (n0 : nat) (v0 : Vt),
               der (grammar_union (Tt:=Tt) l) (V (lV n0 v0)) (u ++ [Vs B] ++ w)).
    apply IHder1.
    apply Heqst.
    apply H2.
    destruct H3.
    destruct H3.
    exists x, x0.
    apply (replN (B := B)).
    exact H3.
    exact H1.
  Qed.
 *)

  Lemma grammar_cut : forall (l1 l2 : list rule) (p : @phrase Tt (labeled_Vt Vt)) (v0 : var)
      (P : symbol -> Prop), 
      der (l1 ++ l2) v0 p ->
      (forall s pf, der (l1 ++ l2) v0 pf -> In s pf -> P s -> False) ->
      (forall s p, In (R s p) l1 -> P (Vs s)) ->
      der l2 v0 p.
  Proof.
    intros.
    induction H.
    apply vDer.
    admit.
    
  

  Lemma der_exchange : forall (l1 l2 : list rule) (p : @phrase Tt (labeled_Vt Vt)) (v0 : var),
      der (l1 ++ l2) v0 p -> der (l2 ++ l1) v0 p.
  Proof.
    intros.
    induction H.
    apply vDer.
    apply rDer.
    apply in_or_app.
    apply or_comm.
    apply in_app_or.
    exact H.
    apply (replN (B:=B)).
    exact IHder1.
    exact IHder2.
  Qed.

  
  
  Lemma same_union_bkw_0 : forall (l : list (grammar * Vt)) (w : word) (n : nat) (v0 : Vt),
  der (grammar_union (Tt:=Tt) l) (V (lV n v0)) (to_phrase (Tt:=Tt) (labeled_Vt Vt) w) ->
  language_list_union (map grammar_to_languange l) w.
  Proof.
    intros.
    induction l.
    simpl in H.
    admit.
    simpl.
    simpl in H.
    enough (n <= (length l)).
    assert (n < (length l) \/ n = (length l)).
    apply le_lt_or_eq.
    apply H0.
    clear H0.
    destruct H1.
    right.
    apply IHl.
    admit.
    left.
  Qed.
  
  Lemma same_union_bkw : forall (l : list (grammar * Vt)) (w : word),
      grammar_to_languange (grammar_union l, start Vt) w ->
      language_list_union (map grammar_to_languange l) w.
  Proof.
    intros.
    unfold grammar_to_languange in H.

    enough (der_start :
    forall (l : list (grammar * Vt)) (p : @phrase Tt (labeled_Vt Vt)),
      der (grammar_union l) (V (start Vt)) p -> p <> [(Vs (V (start Vt)))] ->
      exists n0 v0, der (grammar_union l) (V (lV n0 v0)) p).

    assert (exists (n0 : nat) (v0 : Vt), der (grammar_union (Tt:=Tt) l) (V (lV n0 v0)) (to_phrase (Tt:=Tt) (labeled_Vt Vt) w)).
    apply der_start.
    exact H.
    admit.
    destruct H0.
    destruct H0. 
    remember (V (start Vt)) as st.
    remember (to_phrase (Tt:=Tt) (labeled_Vt Vt) w) as p.
    destruct H.
    destruct w.
    simpl in Heqp.
    discriminate.
    simpl in Heqp.
    discriminate.
    admit.
    destruct B.
    destruct l0.
    admit.
    
    induction l.
    - simpl in H.
      exfalso.
      remember (V (start Vt)) as st.
      remember (to_phrase (Tt:=Tt) (labeled_Vt Vt) w) as p.
      
      assert (p = [Vs st]).
      apply empty_grammar.
      apply H.
      rewrite Heqp in H0.
      destruct w.
      simpl in H0.
      discriminate.
      simpl in H0.
      discriminate.
    - simpl.
      destruct a. 
      unfold grammar_to_languange.
      enough (same_union_bkw_0 : forall
    (g : grammar) (v : Vt)
    (l : list (grammar * Vt))
    (n : nat)
    (p : phrase)
    (H : der (grammar_union (Tt:=Tt) ((g, v) :: l)) (V (lV n v))
        (tranform_phrase n p)),
                 der g (V v) p \/ (der (grammar_union (Tt:=Tt) l) (V (lV n v)) (tranform_phrase n p))).
    

  Qed.
 
  
  Lemma same_union: forall (l : list ((@grammar Tt Vt) * Vt)),
      language_eq (language_list_union (map grammar_to_languange l)) 
                  (grammar_to_languange ((grammar_union l), start Vt)).
  Proof.
    intro l.
    apply mk_laguage_eq.
    apply same_union_fwd.
        
  Qed.
    
    