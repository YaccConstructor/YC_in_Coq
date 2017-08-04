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
  
  Definition grammar_to_language {Vl : Type} (g : (@grammar Tt Vl) * Vl) : language :=
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
     language_list_union (map grammar_to_language l) w ->
     grammar_to_language (grammar_union l, start Vt) w.
  Proof.
    intros l w H1.
    induction l.  
    simpl in H1.
    contradiction.
    simpl in H1.
    destruct H1.
    clear IHl.
    destruct a.
    unfold grammar_to_language in H.
    unfold grammar_to_language.
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
  Lemma grammar_close : forall (l: list rule) (p : @phrase Tt (labeled_Vt Vt)) (v0 : var)
      (P : var -> Prop), 
      der l v0 p ->
      (P v0) ->
      (forall r pr v1, In (R r pr) l -> (P r) -> In (Vs v1) pr -> P v1) ->
      (forall vp, In (Vs vp) p -> P vp).
  Proof.
    intros l p v0 P d is_p H0.
    induction d.
    - intros.
      simpl in H.
      destruct H.
      simplify_eq H.
      intro.
      rewrite <- H1.
      exact is_p.
      contradiction.
    - intros.
      apply (H0 A l0).
      exact H.
      exact is_p.
      exact H1.
    - intros.
      assert (In (Vs vp) v \/ In (Vs vp) u \/ In (Vs vp) w).
      { apply in_app_or in H.
      destruct H.
      right; left; exact H.
      apply in_app_or in H.
      destruct H.
      left; exact H.
      right; right; exact H.
      }
      clear H.
      destruct H1.
      + apply IHd2.
        apply IHd1.
        exact is_p.
        apply in_or_app.
        right.
        apply in_or_app.
        left.
        auto.
        exact H.
      + apply IHd1.
        exact is_p.
        destruct H.
        apply in_or_app.
        left.
        auto.
        apply in_or_app.
        right.
        apply in_or_app.
        right.
        auto.
  Qed.

  Lemma grammar_cut_l1 : forall (l1 l2 : list rule) (p : @phrase Tt (labeled_Vt Vt)) (v0 : var)
      (P : var -> Prop), 
      der (l1 ++ l2) v0 p ->
      (P v0) ->
      (forall r pr v1, In (R r pr) (l1 ++ l2) -> (P r) -> In (Vs v1) pr -> P v1) ->
      (forall r pr, In (R r pr) l1 -> (P r) -> False) ->
      der l2 v0 p.
  Proof.
    intros.
    induction H.
    - apply vDer.
    - apply rDer.
      apply in_app_or in H.
      destruct H.
      exfalso.
      apply (H2 A l).
      exact H.
      exact H0.
      exact H.
    - apply (replN (B := B)).
      apply (IHder1 H0).
      apply IHder2.
      apply (grammar_close H).
      exact H0.
      exact H1.
      apply in_or_app.
      right.
      apply in_or_app.
      left.
      auto.
  Qed.

  Lemma grammar_cut_l2 : forall (l1 l2 : list rule) (p : @phrase Tt (labeled_Vt Vt)) (v0 : var)
      (P : var -> Prop), 
      der (l1 ++ l2) v0 p ->
      (P v0) ->
      (forall r pr v1, In (R r pr) (l1 ++ l2) -> (P r) -> In (Vs v1) pr -> P v1) ->
      (forall r pr, In (R r pr) l2 -> (P r) -> False) ->
      der l1 v0 p.
  Proof.
    intros.
    induction H.
    - apply vDer.
    - apply rDer.
      apply in_app_or in H.
      destruct H.
      exact H.
      exfalso.
      apply (H2 A l).
      exact H.
      exact H0.
      
    - apply (replN (B := B)).
      apply (IHder1 H0).
      apply IHder2.
      apply (grammar_close H).
      exact H0.
      exact H1.
      apply in_or_app.
      right.
      apply in_or_app.
      left.
      auto.
  Qed.
            
  
  Definition get_n (l : @var (labeled_Vt Vt)) : nat :=
    match l with 
    |  V (start _) => 0
    |  V (lV n _) => S n
    end.

  Lemma grammar_cutable : forall (l : list (grammar * Vt))
                                 (pr : phrase)
                                 (P : nat -> Prop)
                                 (P_0 : P 0 -> False)
                                 (r : var)
                                 (v1 : var), 
    In (R r pr) (grammar_union (Tt:=Tt) l) -> (P (get_n r)) -> In (Vs v1) pr -> (P (get_n v1)).
  Proof.
    intros l pr P P_0 r v1.
    induction l.
    simpl.
    contradiction.
    intros.
    simpl in H.
    apply in_app_or in H.
    destruct H.
    clear IHl.
    assert (n_start : forall v, (R (V (start Vt)) [Vs (V (lV (length l) v))] = R r pr -> False)).
    { intros.
    simplify_eq H2.
    intros.
    rewrite <- H3 in H0.
    simpl in H0.
    exact (P_0 H0).
    }
    
    destruct a.
    induction g.
    simpl in H.
    destruct H.
    exfalso.
    apply (n_start v H).
    contradiction.
    simpl in H.
    destruct H.
    exfalso.
    apply (n_start v H).
    destruct H.
    destruct a.
    destruct v0.
    simpl in H.
    simplify_eq H.
    intros.
    clear H.
    rewrite <- H2 in H0.
    simpl in H0.
    rewrite <- H3 in H1.
    clear H2 H3 n_start IHg v0 v.
    induction p.
    simpl in H1.
    contradiction.
    simpl in H1.
    destruct H1.
    destruct a.
    simpl in H.
    discriminate.
    destruct v.
    simpl in H.
    simplify_eq H.
    intros.
    rewrite <- H1.
    simpl.
    exact H0.
    apply (IHp H).
    apply IHg.
    simpl.
    right.
    exact H.
    apply (IHl H H0 H1).    
  Qed.

  Lemma z_le_n : forall n, 0 <= n.
  Proof.
    intro.
    induction n.
    auto.
    auto.
  Qed.

  Lemma m_le_n : forall m n,
    m = S n -> m <= n -> False.
  Proof.
    intros.
    revert m H H0.
    induction n.
    intros.
    apply le_n_0_eq in H0.
    rewrite H in H0.
    discriminate.
    intros.
    destruct m.
    discriminate.
    apply (IHn m).
    injection H.
    auto.
    apply le_S_n.
    apply H0.
  Qed.
 
  Lemma сut_grammar_0 : forall
      (g : grammar * Vt)
      (l : list (grammar * Vt))
      (p : phrase (Tt := Tt))
      (n : nat)
      (v0 : Vt)
      (H0 : n = length l)
      (D : der (update_grammar (length l) g ++ grammar_union l) (V (lV n v0)) p),
      (der (update_grammar (length l) g) (V (lV n v0)) p).
  Proof.
    intros.
    apply grammar_cut_l2 with
        (P := fun s => (get_n s = S n))
        (l2 := grammar_union l).
    exact D.
    simpl; reflexivity.
    intros r pr v1 is_in.
    apply grammar_cutable with (l := g::l) (P := fun m => m = S n).
    discriminate.
    simpl.
    exact is_in.
    rewrite H0.
    intros.
    clear D H0 n p g v0.
    assert (get_n r <= length l).
    clear H1.
    induction l.
    simpl in H.
    contradiction.
    simpl in H.
    apply in_app_or in H.
    destruct H.
    destruct a.
    assert (get_n r = 0 \/ get_n r = S (length l)).
    {
      destruct g.
      simpl in H.
      destruct H.
      left.
      injection H as H_eq.
      rewrite <- H_eq.
      reflexivity.
      contradiction.
      simpl in H.
      destruct H.
      injection H as H_eq.
      rewrite <- H_eq.
      left.
      reflexivity.
      destruct H.
      destruct r0.
      destruct v0.
      simpl in H.
      injection H as H_eq; rewrite <- H_eq. 
      right.
      simpl.
      reflexivity.
      right.
      induction g.
      simpl in H.
      contradiction.
      simpl in H.
      destruct H.
      destruct a.
      destruct v0.
      simpl in H.
      injection H as H_eq; rewrite <- H_eq.
      simpl.
      reflexivity.
      apply (IHg H).
    }
    destruct H0.
    rewrite H0.
    apply z_le_n.
    rewrite H0.
    apply le_n.
    simpl.
    apply le_S.
    apply (IHl H).
    apply m_le_n with (m := (get_n r)) (n := (length l)).
    exact H1.
    exact H0.
  Qed.  
(*
   g : grammar
  v : Vt
  l : list (grammar * Vt)
  w : word
  n : nat
  v0 : Vt
  H : der (update_grammar (Tt:=Tt) (length l) (g, v) ++ grammar_union (Tt:=Tt) l) (V (lV n v0)) (to_phrase (Tt:=Tt) (labeled_Vt Vt) w)
  IHl : der (grammar_union (Tt:=Tt) l) (V (lV n v0)) (to_phrase (Tt:=Tt) (labeled_Vt Vt) w) -> language_list_union (map grammar_to_language l) w
  H0 : n = length l
  H1 : der (update_grammar (Tt:=Tt) (length l) (g, v)) (V (lV n v0)) (to_phrase (Tt:=Tt) (labeled_Vt Vt) w)
  ============================
  der g (V v) (to_phrase (Tt:=Tt) Vt w)
 *)
  (*
  Lemma same_union_bkw_0 : forall (l : list (grammar * Vt)) (w : word) (n : nat) (v0 : Vt),
  der (grammar_union (Tt:=Tt) l) (V (lV n v0)) (to_phrase (Tt:=Tt) (labeled_Vt Vt) w) ->
  language_list_union (map grammar_to_language l) w.
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
    destruct a.
    unfold grammar_to_language.
    assert (der (update_grammar (Tt:=Tt) (length l) (g, v)) (V (lV n v0)) (to_phrase (Tt:=Tt) (labeled_Vt Vt) w)).
    apply сut_grammar_0.
    exact H0.
    exact H.
       
  Qed.
   *)
  
  Lemma same_union_bkw : forall (l : list (grammar * Vt)) (w : word),
      grammar_to_language (grammar_union l, start Vt) w ->
      language_list_union (map grammar_to_language l) w.
  Proof.
    intros.
    unfold grammar_to_language in H.

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
   
    induction l.
    - simpl in H.
      exfalso.
      assert (p = [Vs st]).
      apply empty_grammar.
      apply H.
      rewrite Heqp in H1.
      destruct w.
      simpl in H1.
      discriminate.
      simpl in H1.
      discriminate.
    - simpl.
      destruct a. 
      unfold grammar_to_language.
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
    
    