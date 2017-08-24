Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.

Add LoadPath "~/Git/YC_in_Coq/". 
Require Import CFG.Definitions CFG.Derivation INT.Intersection.
Require Import GLL.GLL.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq bigop fintype fingraph finfun finset choice.

Section RA.
  
  Import Definitions.

  (* TODO: new file? *)
  Section CanonicalStructures.
    
    Section CanonicalStructureTer.
      
      Section EqTer.
        
        Variable T: eqType.
        
        Fixpoint eqter (t1 t2: @ter T) :=
          match t1, t2 with
            | Definitions.T x1, Definitions.T x2 => x1 == x2
          end.
        
        Lemma eqterP: Equality.axiom eqter.
        Proof.
          move => t1 t2; apply: (iffP idP) => [| <-]; last by elim: t1 => //= t ->.
          intros; destruct t1, t2.
            by inversion H as [H']; move: H' => /eqP H'; subst.
        Defined. 

        Canonical ter_eqMixin := Eval hnf in EqMixin eqterP.
        Canonical ter_eqType := Eval hnf in EqType ter ter_eqMixin.

      End EqTer. 
      
      Section ChoiceTypeTer.

        Variable T: choiceType.
        
        Definition to_ter (x: T) := Definitions.T x.
        Definition from_ter t: T := match t with Definitions.T x => x end.
        
        Lemma hz_of_terK : cancel from_ter to_ter.
        Proof.
            by intros t; destruct t.
        Qed.
        
        Definition ter_choiceMixin := CanChoiceMixin hz_of_terK.
        Canonical ter_choiceType := Eval hnf in ChoiceType ter ter_choiceMixin.

      End ChoiceTypeTer.

      Section CountTypeTer.

        Variable T: countType.
        
        Definition ter_countMixin := CanCountMixin (@hz_of_terK T).
        Canonical ter_countType := Eval hnf in CountType ter ter_countMixin.
        
      End CountTypeTer.

      Section FinTypeTer.
        
        Variable T: finType.
        
        Definition ter_enum := map (@Definitions.T _) (Finite.enum T).
        
        Lemma ter_enumP: Finite.axiom ter_enum.
        Proof.
          intros x; destruct x as [t].
            by rewrite //= count_map enumP.
        Qed.
        
        Definition ter_finMixin := FinMixin ter_enumP.
        Canonical ter_finType := Eval hnf in FinType ter ter_finMixin.
        
      End FinTypeTer.

    End CanonicalStructureTer.

    Section CanonicalStructureVar.

      Section EqVar.
        
        Variable T: eqType.
        
        Fixpoint eqvar (v1 v2: @var T) :=
          match v1, v2 with
            | Definitions.V x1, Definitions.V x2 => x1 == x2
          end.
        
        Lemma eqvarP: Equality.axiom eqvar.
        Proof.
          move => v1 v2; apply: (iffP idP) => [| <-]; last by elim: v1 => //= t ->.
          intros; destruct v1, v2.
            by inversion H as [H']; move: H' => /eqP H'; subst.
        Defined. 

        Canonical var_eqMixin := Eval hnf in EqMixin eqvarP.
        Canonical var_eqType := Eval hnf in EqType var var_eqMixin.

      End EqVar. 
      
      Section ChoiceTypeVar.

        Variable T: choiceType.
        
        Definition to_var (x: T) := Definitions.V x.
        Definition from_var v: T := match v with Definitions.V x => x end.
        
        Lemma hz_of_varK : cancel from_var to_var.
        Proof. by intros t; destruct t. Qed.
        
        Definition var_choiceMixin := CanChoiceMixin hz_of_varK.
        Canonical var_choiceType := Eval hnf in ChoiceType var var_choiceMixin.

      End ChoiceTypeVar.

      Section CountTypeVar.

        Variable T: countType.
        
        Definition var_countMixin := CanCountMixin (@hz_of_varK T).
        Canonical var_countType := Eval hnf in CountType var var_countMixin.
        
      End CountTypeVar.

      Section FinTypeVar.
        
        Variable T: finType.
        
        Definition var_enum := map (@Definitions.V _) (Finite.enum T).
        
        Lemma var_enumP: Finite.axiom var_enum.
        Proof.
          intros x; destruct x as [t].
            by rewrite //= count_map enumP.
        Qed.
        
        Definition var_finMixin := FinMixin var_enumP.
        Canonical var_finType := Eval hnf in FinType var var_finMixin.
        
      End FinTypeVar.      

    End CanonicalStructureVar.

  End CanonicalStructures.

  Section Definitions.

    (* TODO: add epsilon edge *)

    Record ra: Type :=
      mkRA {
          ra_state :> finType;
          ra_term :> finType;
          
          ra_s: ra_state;
          ra_f: pred ra_state;

          ra_step: ra_state * ((*TODO: eps + *) ra_term + ra_state) -> pred ra_state
        }.

    (* Acceptance on RAs *)
    Section Acceptance.

      (* Assume some automaton *)
      Variable A: ra.

      Inductive Accept: _ -> _ -> Prop :=
      | Emp : Accept [::] [::]
      | Fin : forall w s sl, ra_f s -> Accept w sl -> Accept w (s::sl)
      | Ter: forall a w (s s1: ra_state A) sl, ra_step (s, (inl a)) s1 -> Accept w (s1::sl) -> Accept (a::w) (s::sl) 
      | Non: forall w (s s1 s2: ra_state A) sl, ra_step (s, (inr s1)) s2 -> Accept w (s1::s2::sl) -> Accept w (s::sl).

      Definition ra_lang w := Accept w [:: ra_s A].  

    End Acceptance.

    Section Examples.
     
      Variable States T: finType.
      Let Ters := Eval hnf in [finType of (@ter T)].

      Variable t1: T.
      Let ter_t1: Ters := Definitions.T t1.

     
      Variable (s0 s1 s2 s3: States) (a b: Ters).

      (* Important! *)
      (* TODO: Should we use finSet? *)
      Hypothesis Neq: s0 == s1 = false /\ s0 == s2 = false /\ s0 == s3 = false /\
                      s1 == s2 = false /\ s1 == s3 = false /\
                      s2 == s3 = false.

(*
        ⊳0          1
         ↓         ↙↓
         ↓       ↙  ↓
       1 ↓   a ↙    ↓ 1
         ↓   ↙      ↓
         ↓ ↙        ↓
        ►3  ← ← ← ← 2        
               b               
*)
   
      
      Let ra :=
        @mkRA
          States Ters
          s0 (fun st => st == s3)
          (fun pair =>
             let '(st, sym) := pair in
             if (st == s0) && (sym == inr s1) then (fun s => s == s3)
             else
               if (st == s1) && (sym == inr s1) then (fun s => s == s2)
               else
                 if (st == s1) && (sym == inl a) then (fun s => s == s3)
                 else
                   if (st == s2) && (sym == inl b) then (fun s => s == s3)
                   else (fun _ => false)).

      Goal @ra_lang ra [::a;b;b] .
      Proof.
        destruct Neq as [H1 [H2 [H3 [H4 [H5 H6]]]]]. 
        unfold ra_lang.
        apply Non with (s1 := s1) (s2 := s3).
        { by simpl; rewrite !eq_refl Bool.andb_true_l. }
        
        apply Non with (s1 := s1) (s2 := s2).
        { by simpl; rewrite !eq_refl eq_sym H1; simpl. }

        apply Non with (s1 := s1) (s2 := s2).
        { by simpl; rewrite !eq_refl eq_sym H1; simpl. }

        apply Ter with (s1 := s3); simpl.
        { by simpl; rewrite !eq_refl eq_sym H1; simpl. }

        apply Fin. by simpl.  
        apply Ter with (s1 := s3); simpl.
        {  simpl; rewrite !eq_refl eq_sym H2; simpl.
             by rewrite eq_sym H4; simpl. }

        apply Fin. by simpl.  
        apply Ter with (s1 := s3); simpl.
        {  simpl; rewrite !eq_refl eq_sym H2; simpl.
             by rewrite eq_sym H4; simpl. }        
        apply Fin. by simpl.  
        apply Fin. by simpl.  
        apply Emp.
      Qed.
        
    End Examples.

  End Definitions.

  (* TODO: fix ⇓⇓⇓⇓⇓⇓⇓⇓⇓⇓⇓⇓⇓⇓⇓⇓⇓*)
  Section SectionName.

    Context {T'': Type}.
    
    Variable ra : @RA T''.

    (* State type *)
    Local Definition Q : Type := @Q' _ ra.
    Definition states : Ensemble Q := Full_set Q.
    Variable state'count : nat.
    Axiom states_is_finite : cardinal Q states state'count.
    
    (* Terminal type *)
    Local Definition T : Type := T' ra.
    Definition terminals : Ensemble T := Full_set T.
    Variable terminal'count : nat.
    Axiom terminals_is_finite : cardinal T terminals terminal'count.
    
    (* Nonterminal type *)
    Local Definition N : Type := N' ra.
    Definition nonterminals : Ensemble N := Full_set N.
    Variable nonterminal'count : nat.
    Axiom nonterminals_is_finite : cardinal N nonterminals nonterminal'count.

    (* TODO: comment *)
    Definition call : (N -> Q * Q) := @call' _ ra.
    
    (* Symbol *)
    Definition S : Type := option (T + N).
    Definition symbols : Ensemble S := Full_set S.
    Definition symbol'count : nat := terminal'count + nonterminal'count.
    
    (* Edges *)
    Definition edges : Ensemble (Q * Q) := @edges' _ ra.
    Variable edge'count : nat.
    
    Axiom edges_is_state_pair :
      forall (x y : Q), In (Q * Q) _ _ edges (x, y) -> In Q states x /\ In Q states y.

    Axiom edges_is_finite : cardinal (Q * Q) edges edge'count.

    Definition edge'relation: relation Q := fun x y => In (Q * Q) edges (x, y).
    
    (* Edge -> Symbol *)
    Definition edge'symbol (s : S): relation Q := edge'symbol' ra s.
    
    (* Paths *)
    Variable path'count : nat.
    Definition paths'relation : relation Q := clos_refl_trans Q edge'relation.
    Definition paths : Ensemble (Q * Q) := fun xy => paths'relation (fst xy) (snd xy).
    Axiom paths_is_state_pair : forall x y : Q, In (Q * Q) paths (x, y) -> In Q states x /\ In Q states y.
    Axiom paths_is_finite : cardinal (Q * Q) paths path'count.




    Section Lemmas.
      
      Lemma unpair : forall A B : Type, forall x : A * B, (fst x, snd x) = x.
      Proof.
        intros.
        elim x.
        intros.
        unfold fst.
        unfold snd.
        auto.
      Qed.
      
      Lemma unpair_call : forall A B : Type, forall f : A * B -> Prop, forall x : A * B, f x -> f (fst x, snd x).
      Proof.
        unfold fst.
        unfold snd.
        intro.
        intro.
        intro.
        intro.
        elim x.
        intros.
        exact H.
      Qed.
      
      Lemma edges_is_path'subpath : Included (Q * Q) edges paths.
      Proof.
        unfold Included.
        unfold In.
        unfold paths.
        unfold paths'relation.
        intros.
        unfold edge'relation.
        apply rt_step.
        unfold In.
        apply unpair_call.
        exact H.
      Qed.
      
      Lemma paths'relation_is_reflexive : reflexive Q paths'relation.
      Proof.
        unfold reflexive.
        apply rt_refl.
      Qed.
      
      Lemma paths'relation_is_transitive : transitive Q paths'relation.
      Proof.
        unfold transitive.
        apply rt_trans.
      Qed.
      
      Lemma paths_is_reflexive: forall x, In (Q * Q) paths (x, x).
      Proof.
        assert (reflexive Q paths'relation <-> forall x, In (Q * Q) paths (x, x)) as eval'reflexive.
        tauto.
        apply paths'relation_is_reflexive.
      Qed.
      
      (* Subpath relation *)
      Inductive subpath: relation (Q * Q) :=
      | edge: forall (ab: Q * Q), In (Q * Q) edges ab -> subpath ab ab
      | refl: forall (ab: Q * Q), subpath ab ab
      | trans: forall x y z : Q * Q, subpath x y -> subpath y z -> subpath x z
      | concat_l: forall (ab: Q * Q), forall x y z : Q, subpath ab (x, y) /\ subpath (y, z) (y, z) -> subpath ab (x, z)
      | concat_r: forall (ab: Q * Q), forall x y z : Q, subpath (x, y) (x, y) /\ subpath ab (y, z) -> subpath ab (x, z).
      
      Theorem subpath_is_reflexive : reflexive (Q * Q) subpath.
      Proof.
        intro.
        apply refl.
      Qed.
      
      Theorem subpath_is_transitive : transitive (Q * Q) subpath.
      Proof.
        intro.
        intro.
        intro.
        apply trans.
      Qed.
      
      Theorem subpath_edges : forall x y : Q, In (Q * Q) edges (x, y) -> subpath (x, y) (x, y).
      Proof.
        intros.
        apply edge.
        exact H.
      Qed.
      
      Theorem subpath_concat_l :
        forall a b x y z : Q,
          subpath (a, b) (x, y) ->
          subpath (y, z) (y, z) ->
          subpath (a, b) (x, z).
      Proof.
        intros.
        intro.
        intro.
        intro.
        intro.
        apply concat_l.
      Qed.
      
      Theorem subpath_concat_r :
        forall a b x y z : Q,
          subpath (x, y) (x, y) ->
          subpath (a, b) (y, z) ->
          subpath (a, b) (x, z).
      Proof.
        intro.
        intro.
        intro.
        intro.
        intro.
        apply concat_r.
      Qed.

    End Lemmas.
    
    (* Path -> [Symbol] *)
    Definition path'symbols (s: S): relation Q := fun z w : Q => exists x y : Q, edge'symbol s x y /\ subpath (x, y) (z, w).

    (* Calls *)
    Definition calls : relation N := fun n m : N => exists x y, subpath (call n) (x, y) /\ path'symbols (Some (inr m)) x y.
    Definition closcalls := clos_trans N calls.

    (* TODO: comment *)
    Definition is_nonrecursive_RA := forall x, ~ closcalls x x.
    
    Definition fsa_path'symbol (t: option T) :=
      match t with
        | None => path'symbols None
        | Some x => path'symbols (Some (inl x))
      end.
    
  End RA_Definition.


  Section Input_Definition.
    
    Variable Char : Type.
    
    Record LinearInput :=
      {
        current : nat -> Char;
        next : nat -> nat;
      }.
    
  End Input_Definition.

  Section GLL_Definition.
    
    Variable GrammarState : Type.
    Variable StackPos : Type.
    Variable SPPFPos : Type.
    
    Record GLL_Hundler :=
      {
                           position : nat;
                           state : GrammarState;
                           stack_pos : StackPos;
                           sppf : SPPFPos;
                         }.
  End GLL_Definition.

  Section RA_Operations.
    Section FSA_Intersection.
      
      Context {newT:Type}.
      
      Variable ra1 ra2 : @RA newT.
      
      Definition fsa_paths_intersection (t: option newT) (x1: Q ra1) (x2: Q ra2) (y1: Q ra1) (y2: Q ra2) :=
        fsa_path'symbol ra1 t x1 y1 /\ fsa_path'symbol ra2 t x2 y2.
      
    End FSA_Intersection.
    
    
    Section FSA_Image.
      
      Context {sT:Type}.
      
      Variable ra : @RA sT.
      
      Inductive newT :=
      | term (t : sT)
      | bbr (n : N ra) (ctx : Q ra * Q ra)
      | ebr (n : N ra) (ctx : Q ra * Q ra).
      
      Inductive Empty : Type :=.
      
      Inductive fsa_relation_image: option (newT + Empty) -> relation (Q ra) :=
      | fer_eps_edge:
          forall x y:Q ra, edge'symbol ra None x y -> fsa_relation_image None x y
      | fer_ter_edge (t: T ra):
          forall x y : Q ra, edge'symbol ra (Some (inl t)) x y -> fsa_relation_image (Some (inl (term t))) x y
      | begin_br (n : N ra):
          forall x y : Q ra, edge'symbol ra (Some (inr n)) x y -> fsa_relation_image (Some (inl (bbr n (x, y)))) x (fst (call ra n))
      | end_br (n : N ra):
          forall x y : Q ra, edge'symbol ra (Some (inr n)) x y -> fsa_relation_image (Some (inl (ebr n (x, y)))) (snd (call ra n)) y.
      
      Definition fsa_image : @RA newT :=
        mkRA newT (Q ra) Empty (edges ra) (fun _ => start' ra) fsa_relation_image (start' ra).
      
    End FSA_Image.
    
  End RA_Operations.

End RA.