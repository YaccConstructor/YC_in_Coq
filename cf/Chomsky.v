Require Export Basics Separate Binarize ElimE ElimU.
Local Open Scope program_scope.

Definition chomsky G := efree G /\ uniform G /\ binary G /\ unitfree G.
Definition normalize := elimU ∘ elimE ∘ sep ∘ bin.

(** * Normalization yields Chomsky normal form *)

Lemma substG_preservesLength G s s' :
  binary G -> binary (substG G s [s']).
Proof.
  intros H. induction G as [| [A u] G IHG] ; simpl ; auto.
  intros B v [E | E].
  - inv E. rewrite <- substL_length_unit ; eauto.
  - eapply IHG ; eauto.
    intros B' v' E'. eapply H ; eauto.
Qed.

(** ** Preservation of binarity *)

Lemma binary_sep G : binary G -> binary (sep G).
Proof.
  intros H.
  unfold sep.
  apply it_ind ; auto.
  intros G' Bi.
  unfold Separate.step.
  destruct (pickCharRule G') as [[a [B [v [H0 [H1 H2]]]]] | H0 ] ; auto.
  destruct (pickFresh G') as [C N].
  cut (binary (substG G' (Ts a) [Vs C])) ; auto using substG_preservesLength.
  intros Bin A u E. destruct E ; [inv H3 | ] ; eauto.
Qed.

Lemma binary_elimE G : binary G -> binary (elimE G).
Proof.
  intros H A u H0.
  apply delE_rules, closure_slist in H0.
  destruct H0 as [u' [H0 H1]].
  apply slist_length in H1.
  specialize (H A u' H0). omega.
Qed.  

Lemma binary_unit G : binary G -> binary (elimU G).
Proof.
  intros H A u H0.
  apply rule_ranG, ran_elimU_G, ranG_rule in H0.
  destruct H0 as [B H0].
  apply (H B u H0).
Qed.

(** ** Preservation of uniformness *)

Lemma excluded_free G : uniform G -> uniform (elimE G).
Proof.
  intros H A u H0 a E.
  apply delE_rules in H0.
  apply closure_slist in H0.
  destruct H0 as [u' [H1 H2]].
  assert (H4 : Ts a el u') by (apply slist_subsumes in H2 ; auto).
  specialize (H A u' H1 a H4).
  subst. inv H2.
  - inv H6. destruct E.
  - now inv H3.
Qed.

Lemma excluded_unit G : uniform G -> uniform (elimU G).
Proof.
  intros H A u Ru.
  apply rule_ranG, ran_elimU_G, ranG_rule in Ru.
  destruct Ru as [B H0].
  apply (H B u H0).
Qed.  

(** ** Preservation of epsilon-freeness *)

Lemma efree_unit G : efree G -> efree (elimU G).
Proof.
  intros H A u Ru.
  apply rule_ranG, ran_elimU_G, ranG_rule in Ru.
  destruct Ru as [B H0].
  apply (H B u H0).
Qed.

Lemma chomsky_normalform G :
  chomsky (normalize G).
Proof.
  repeat split.
  - apply efree_unit, efree_elimE.
  - apply excluded_unit, excluded_free, sep_uniform.
  - apply binary_unit, binary_elimE, binary_sep, bin_binary.
  - apply unitfree_elimU.
Qed.

(** * Normalization preserves languages *)

Lemma bin_dom G :
  dom G <<= dom (bin G).
Proof.
  unfold bin.
  apply it_ind ; auto.
  intros G' H.
  setoid_transitivity (dom G') ; auto.
  apply Binarize.step_dom.
Qed.

Lemma language_normalform G A u :
  Vs A el dom G -> u <> [] -> (language G A u <-> language (normalize G) A u).
Proof.
  intros Do U.
  unfold normalize.
  rewrite bin_language ; auto.
  rewrite sep_language ; try now apply bin_dom.
  rewrite elimE_language ; auto.
  now rewrite unit_language.
Qed.

