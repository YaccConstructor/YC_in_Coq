Require Export Lists.

Module Definitions.

  Import Base Lists. 
  (** * Definitions of grammars *)
  Section Defs.
    
    Context {Tt Vt: Type}.
    Context {Tt_eqdec: eq_dec Tt}.
    Context {Vt_eqdec: eq_dec Vt}.
    
    Inductive ter : Type :=
    | T : Tt -> ter.
    
    Inductive var : Type :=
    | V : Vt -> var.
    
    Inductive symbol : Type :=
    | Ts : ter -> symbol
    | Vs : var -> symbol.
    
    Definition phrase := list symbol.

    Inductive rule : Type :=
    | R : var -> phrase -> rule.

    Definition grammar := list rule.

  End Defs.

  (** * Decidability instances *)
  Section DecidabilityInstances.

    Context {Tt Vt: Type}.
    Context {Tt_eqdec: eq_dec Tt}.
    Context {Vt_eqdec: eq_dec Vt}.
    
    Global Instance var_eq_dec : eq_dec (@var Vt).
    Proof.
      intros A B. unfold dec. repeat decide equality. apply Vt_eqdec. Defined. 

    Global Instance rule_eq_dec : eq_dec (@rule Tt Vt).
    Proof.
      intros A B. unfold dec. repeat decide equality.
      apply Tt_eqdec. apply Vt_eqdec. apply Vt_eqdec. Defined.

    Global Instance symbol_eq_dec : eq_dec (@symbol Tt Vt).
    Proof.
      intros A B. unfold dec. repeat decide equality.
      apply Tt_eqdec. apply Vt_eqdec.
    Defined.
    
    Global Instance exists_rule_dec G p {D : forall A u, dec (p A u)} : dec (exists A u, @R Tt Vt A u el G /\ p A u).
    Proof.
      induction G as [| [A u] Gr IHGr].
      - right. intros [A [u [H0 H1]]]. destruct H0.
      - destruct IHGr as [IH | IH].
        + left. destruct IH as [A' [u' [H0 H1]]].
          exists A', u'. auto.
        + destruct (D A u) as [D' | D'].
          * left. exists A, u. auto.
          * right. intros [A' [u' [H0 H1]]].
            destruct H0 ; try now inv H.
            apply IH. exists A', u'. auto.
    Defined.

    Global Instance exists_phrase_dec G A p : (forall x, dec (p x)) -> dec (exists u , @R Tt Vt A u el G /\ p u).
    Proof with (intros H1 ; destruct H1 as [u [[H1 | H1] H2]] ; [inv H1 |] ; firstorder).
      intros H.
      induction G as [| [B v] Gr IHGr] ; try (now right ; intros [u [H0 H1]] ; destruct H0).
      destruct IHGr as [IHGr | IHGr] ; try now (left ; firstorder).
      decide (A = B) as [D | D] ; subst.
      - decide (p v) as [D0 | D0].
        + left. exists v. split ; auto.
        + right...
      - right...
    Defined.

    Global Instance symbol_ter_dec : forall s, dec (exists a, s = @Ts Tt Vt a).
    Proof.
      intros [s|s] ; [ left ; now exists s | right ; intros [a H] ; inv H].
    Defined.

    Global Instance phrase_var_dec u : dec (exists A, u = [@Vs Tt Vt A]).
    Proof with (try now (right ; intros [? H] ; inv H)).
      destruct u as [| [t | A] ur]...
      destruct ur as [| s ur]...
      left. now (exists A).
    Defined.

    Global Instance phrase_char_dec u : dec (exists a, u = [@Ts Tt Vt a]).
    Proof.
      destruct u as [| [a | A] [| s u]] ; try now (right ; intros [b H] ; inv H).
      left. exists a. auto.
    Qed.

    Global Instance filter_rule_dec (p : @phrase Tt Vt -> Prop) {D : forall u, dec (p u)} : forall r, (dec ((fun r => match r with R A u => p u end) r)).
    Proof.
      destruct r ; auto.
    Defined.

  End DecidabilityInstances.
  
End Definitions.