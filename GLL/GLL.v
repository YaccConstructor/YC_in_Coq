Require Import List.

Add LoadPath "~/Git/YC_in_Coq/". 
Require Import CFG.Definitions CFG.Derivation INT.Intersection.

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module GLLMain.
  
  Import Base Definitions Derivation Intersection.

  Section Definitions.

    Context {Tt Vt: eqType}.

    
    (* TODO: comment *)
    Inductive Grammar_Slot: Type := Sl: @var Vt -> @phrase Tt Vt * @phrase Tt Vt -> Grammar_Slot.
    Notation "x ::= y ∙ z" := (Sl x (y, z)) (at level 95, no associativity).
    

    Definition to_slot rule :=
      let '(R v rhs) := rule in Sl v (nil, rhs).

    Definition next_slot slot :=
      match slot with
        | v ::= l ∙ [] => Sl v (l, []) (* fix *)
        | Sl v (l, r::rs) => Sl v (l ++ [r], rs)
      end.
    

    Section MakingEqType.
      
      Section EqTer.
        
        Fixpoint eqter (t1 t2: @ter Tt) :=
          match t1, t2 with
            | T x1, T x2 => x1 == x2
          end.
        
        Lemma eqterP: Equality.axiom eqter.
        Proof.
          move => t1 t2; apply: (iffP idP) => [| <-]; last by elim: t1 => //= t ->.
          intros.
          destruct t1, t2.
          inversion H.
          move: H1 => /eqP H1; subst.
            by done.
        Defined.
        
        Canonical ter_eqMixin := EqMixin eqterP.
        Canonical ter_eqType := Eval hnf in EqType ter ter_eqMixin.

      End EqTer.

      Section EqVar.

        Fixpoint eqvar (v1 v2: @var Vt) :=
          match v1, v2 with
            | V x1, V x2 => x1 == x2
          end.

        Lemma eqvarP: Equality.axiom eqvar.
        Proof.
          move => t1 t2; apply: (iffP idP) => [| <-]; last by elim: t1 => //= t ->.
          intros.
          destruct t1, t2.
          inversion H.
            by move: H1 => /eqP H1; subst.
        Defined.
        
        Canonical var_eqMixin := EqMixin eqvarP.
        Canonical var_eqType := Eval hnf in EqType var var_eqMixin.

      End EqVar.

      Section EqSymbol.

        Fixpoint eqsymbol (s1 s2: symbol) :=
          match s1, s2 with
            | Ts t1, Ts t2 => t1 == t2
            | Vs v1, Vs v2 => v1 == v2
            | _, _ => false
          end.

        Lemma eqsymbolP: Equality.axiom eqsymbol.
        Proof.
          move => t1 t2; apply: (iffP idP) => [| <-]; last by elim: t1 => //= t ->.
          intros.
          destruct t1, t2; try done; inversion H.
            by move: H1 => /eqP H1; subst.
              by move: H1 => /eqP H1; subst.
        Defined.
        
        Canonical symbol_eqMixin := EqMixin eqsymbolP.
        Canonical symbol_eqType := Eval hnf in EqType symbol symbol_eqMixin.

      End EqSymbol.
      
      Section EqGrammarSlot.

        Fixpoint eqGrammarSlot (gs1 gs2: Grammar_Slot) :=
          match gs1, gs2 with
            | Sl v1 (ph11,ph12), Sl v2 (ph21,ph22) => (v1 == v2) && (ph11 == ph21) && (ph12 == ph22)
          end.

        Lemma eqGrammarSlotP: Equality.axiom eqGrammarSlot.
        Proof.
          move => g1 g2; apply: (iffP idP) => [| <-].
          { intros.
            destruct g1, g2, p, p0.
            inversion H.
              by move: H1 => /andP [/andP [/eqP H1 /eqP H2] /eqP H3]; subst. }
          { destruct g1, p; simpl.
            apply/andP; split; last by done.
              by apply/andP; split. }
        Defined.
        
        Canonical grammar_slot_eqMixin := EqMixin eqGrammarSlotP.
        Canonical grammar_slot_eqType := Eval hnf in EqType Grammar_Slot grammar_slot_eqMixin.

      End EqGrammarSlot.
      
    End MakingEqType.


    
    Let ter := @ter Tt.
    Let var := @var Vt.
    Let symbol := @symbol Tt Vt.
    Let rule := @rule Tt Vt.
    Let grammar := @grammar Tt Vt.
    
    Variable G: grammar.

    
    (* None for now. *)
    Definition SPPF: Type := option bool.
    Let Temp: SPPF := None.


    
    
    
    (* TODO: comment *)
    Definition Position: Type := nat.
    
    (* TODO: comment *)
    (* TODO: better structure *)
    Definition GSS_Node: Type := (var * Position).
    Definition GSS_Edge: Type := (GSS_Node * (Grammar_Slot * Position) * GSS_Node).
    Definition GSS: Type := (list GSS_Node * seq GSS_Edge).

    (* TODO: comment *)
    Definition Descriptor: Type := (Grammar_Slot * GSS_Node * Position).


    (* Temp *)
    (* Definition getNodeP: (Grammar_Slot * SPPF * SPPF) -> SPPF := fun _ => None. *)
    (* Definition getNodeT *)    

    (* TODO: comment *)
    Definition Pending_Descriptors: Type := seq Descriptor.
    Definition Created_Descriptors: Type := seq Descriptor.
    Definition Pop_Calls: Type := seq (GSS_Node * Position).


    
    Let State: Type := (Pending_Descriptors * Pop_Calls * Created_Descriptors * GSS).


    

    Section Add.

      Section Definitions.

        (* *)
        Definition add (state: State) (d: Descriptor): State :=
          let '(Rs, P, U, GSS) := state in
          if (d \in U) then state else (Rs ++ [d], P, d::U, GSS).

      End Definitions.

      Section Lemmas.

        Variable R: Pending_Descriptors.
        Variable P: Pop_Calls.
        Variable U: Created_Descriptors.
        Variable GSS: GSS.
        Let state := (R,P,U,GSS).

        
        Hypothesis H_R_is_a_seq: uniq R.
        Hypothesis H_U_is_a_seq: uniq U.

        Lemma remains_uniq:
          forall d,
            let '(nR,_,nU,_) := add state d in
            uniq nR /\ uniq nU.
        Proof.
          intros.
        Admitted.
        
      End Lemmas.

    End Add.
    
    
    

    (* TODO: comment *)
    Section GetAllPairs.

      Variable pairs: Pop_Calls.
      Variable u: GSS_Node.
      
      Definition get_all_pairs :=
        [seq pair <- pairs | let '(node,_) := pair in node == u].
      
    End GetAllPairs.
    

    Section GetAllAlternatives.

      Variable state: State.
      Variable v: var.
      
      Definition get_all_alternatives :=
        [seq rule <- G | let 'R lhs _ := rule in lhs == v].
      
      Definition add_all_descriptors node pos :=
        foldl (
            fun st rule =>
              add st (to_slot rule, node, pos)
          ) state (get_all_alternatives).
      
    End GetAllAlternatives.
    
    
    Let R: Pending_Descriptors := nil.
    Let P: Pop_Calls := nil. 
    Let U: Created_Descriptors := nil.


    Section Create.
      
      Definition create (state: State) (d: Descriptor) (nt: var): ( State) :=
        let '(L,u,i) := d in
        let '(R, P, U, (GSSN, GSSE)) := state in
        let v := (nt,i) in
        
        let newState :=
            if v \in GSSN then
              if ~~ ((v,(L,i),u) \in GSSE) then
                let GSSE := ((v,(L,i),u)::GSSE) in
                foldl (
                    fun st pair =>
                      let '(u,z) := pair in
                      add st (L,v,i) 
                  ) (R,P,U,(GSSN,GSSE)) (get_all_pairs P u)
              else state
            else
              let GSSN: list GSS_Node := v::GSSN in
              let GSSE: list GSS_Edge := (v,(L,i),u)::GSSE in
              add_all_descriptors (R,P,U,(GSSN,GSSE)) nt v i in
                  
       add_all_descriptors newState nt (nt, i) i.                      
            
    End Create.

    Section GetAllEdges.

      Variable gss: GSS.
      Variable gss_node: GSS_Node.
      
      Definition get_all_edges :=
        let '(_, gss_es) := gss in
        [seq edge <- gss_es | let '(from, (_, _), _) := edge in from == gss_node].
      
    End GetAllEdges.

    Section Pop.
      
      Definition pop (state: State) (d: Descriptor): State :=
        let '(_,u,i) := d in
        let '(R, P, U, GSS) := state in
        
        if ~~ ((u,i) \in P) then
          let P := (u,i)::P in
          
          foldl (
              fun st edge =>
                let '(_,(L,w),v) := edge in
                add st (L,v,i)
            ) (R,P,U,GSS) (get_all_edges GSS u)
                
        else
          state.
 
    End Pop.

    Definition term_slot (state: State) (D: Descriptor) (word: list ter) (t: ter): State :=
      let '(L,cu,ci) := D in
      match nth_error word ci with
        | None => state
        | Some c => if c == t then add state (next_slot L, cu, ci + 1) else state
      end.
    
    
    Definition nonterm_slot (state: State) (D: Descriptor) (nt: var): State :=
      let '(L,cu,ci) := D in
      create state (next_slot L,cu,ci) nt.
    
    
    
    
    Definition do_very_important_stuff word (state: State) (D: Descriptor): State :=
      let '(L,cu,ci) := D in
      match L with
        | v ::= _ ∙          [] => pop state D
        | v ::= _ ∙  (Ts t::rs) => term_slot state D word t
        | v ::= _ ∙ (Vs nt::rs) => nonterm_slot state D nt 
      end.


    Fixpoint parse_iter
             (n: nat)
             (st: GSS_Node)
             (string: list ter)
             (state: State)
    : option bool :=
      let '(R, P, U, GSS) := state in
      match n, R with
        | 0, _ => None
        | S n, [] => Some (
                        has (fun d =>
                               let '(Sl _ (_,ph) ,node,pos) := d in
                               (node == st) && (length string == pos) && (ph == [::]))
                            U)
        | S n, d::R => parse_iter n st string (do_very_important_stuff string (R,P,U,GSS) d)
      end.

    Definition parse_gll st n string :=
      let start_node := (st, 0) in 
      parse_iter
        n start_node string
            (add_all_descriptors ([::],nil,nil,([start_node],nil)) st start_node 0).
            
    
  End Definitions.
 
  
  Section Lemmas.

    Context {T V: eqType}.
 
    Variable (G: @grammar T V) (A: @var V).
    Variable string: @phrase T V.

    (* Complexity of alg *)
    Variable f: @grammar T V -> @phrase T V -> nat.
    
    Theorem correctness_of_gll:
      language G A string <-> parse_gll G A (f G string) (to_word string).
    Proof.
      (* We have to do so many things to get it *)
    Admitted.
    
  End Lemmas.
  

  Section Examples.

    Section Grammar_Simple.

      Let a := T 1.
      Let A := V 1.
            
      Let G: grammar :=
        [
          R A [Ts a; Ts a; Ts a]
        ].


      Example test1:
        forall n,
          n >= 10 -> 
          parse_gll G A n [a;a;a] = Some true.
      Proof.      
        intros.
        unfold parse_gll, add_all_descriptors; simpl.
        destruct n; simpl; [inversion H | ]; rewrite ?add0n ?addn1.
        destruct n; simpl; [inversion H | ]; rewrite ?add0n ?addn1.
        destruct n; simpl; [inversion H | ]; rewrite ?add0n ?addn1.
        destruct n; simpl; [inversion H | ]; rewrite ?add0n ?addn1.
        destruct n; simpl; [inversion H | ]; rewrite ?add0n ?addn1.
        destruct n; simpl; [inversion H | ]; rewrite ?add0n ?addn1.
        destruct n; simpl; [inversion H | ]; rewrite ?add0n ?addn1.
        destruct n; simpl; [inversion H | ]; rewrite ?add0n ?addn1.
          by done.
      Qed.

      Example test2:
        forall n,
          n >= 10 ->
          parse_gll G A n [a;a;a;a] = Some false.
      Proof.      
        intros.
        unfold parse_gll, add_all_descriptors; simpl.     
        repeat (destruct n; simpl; [inversion H | ]; rewrite ?add0n ?addn1; try done).
      Qed.
      

      Example test3:
        forall n,
          n >= 10 ->
          parse_gll G A n [a;a] = Some false.
      Proof.      
        intros.
        repeat (destruct n; simpl; [inversion H | ]; rewrite ?add0n ?addn1; try done).
      Qed.
      
      
    End Grammar_Simple.
    
    Section Grammar_111.
 
      Let a := T 1.
      Let A := V 1.
            
      Let G: grammar :=
        [
          R A [Vs A; Ts a; Ts a];
          R A [Ts a]
        ].


      Example test1:
        forall n,
          n >= 10 -> 
          parse_gll G A n [a;a;a].
      Proof.      
        intros.
        unfold parse_gll, add_all_descriptors; simpl.
        destruct n; simpl; [inversion H | ]; rewrite ?add0n ?addn1.
        destruct n; simpl; [inversion H | ]; rewrite ?add0n ?addn1.
        destruct n; simpl; [inversion H | ]; rewrite ?add0n ?addn1.
        destruct n; simpl; [inversion H | ]; rewrite ?add0n ?addn1.
        destruct n; simpl; [inversion H | ]; rewrite ?add0n ?addn1.
        destruct n; simpl; [inversion H | ]; rewrite ?add0n ?addn1.
        destruct n; simpl; [inversion H | ]; rewrite ?add0n ?addn1.
        destruct n; simpl; [inversion H | ]; rewrite ?add0n ?addn1.
          by done.
      Qed.

      Example test2:
        forall n,
          n >= 10 ->
          parse_gll G A n [a;a;a;a] = Some false.
      Proof.      
        intros.
        unfold parse_gll, add_all_descriptors; simpl.     
        repeat (destruct n; simpl; [inversion H | ]; rewrite ?add0n ?addn1; try done).
      Qed.
      

      Example test3:
        forall n,
          n >= 10 ->
          parse_gll G A n [a;a] = Some false.
      Proof.      
        intros.
        repeat (destruct n; simpl; [inversion H | ]; rewrite ?add0n ?addn1; try done).
      Qed.
      
      
    End Grammar_111.

    (* TODO: name *)
    Section Grammar_name.

      Let a := T 1.
      Let A := V 1.
      
      Let G: @grammar nat nat :=
        [
          R A [Vs A; Vs A; Vs A];
          R A [Vs A; Vs A];
          R A [Vs A];
          R A [Ts a]
        ].


      Example test2:
        forall n,
          n >= 200 ->
          parse_gll G A n [a;a;a;a] = Some true.
      Proof.      
        intros.
        unfold parse_gll, add_all_descriptors; simpl.
       
        
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
        destruct n; [admit | ]; simpl; rewrite /add_all_descriptors ?add0n ?addn1; simpl.
      Qed.

    End Grammar_111.
    
    Section Grammar_Fig1_Izmaylova.

      Let a := T 1.
      Let b := T 2.
      Let c := T 3.
      Let A := V 1.

      Let G: @grammar nat nat :=
        [
          R A [Ts a; Vs A; Ts b];
          R A [Ts a; Vs A; Ts c];
          R A [Ts a]
        ].


      Example test:
        forall n,
          parse_iter
            G n (A, 0) [a; a; c]
            (add_all_descriptors G ([::],nil,nil,([(A, 0)],nil)) A (A, 0) 0) = Some true.
      Proof.      
        intros.
        destruct n; simpl; [admit | ]; rewrite /getNodeP ?add0n ?addn1.
        destruct n; simpl; [admit | ]; rewrite /getNodeP ?add0n ?addn1.
        destruct n; simpl; [admit | ]; rewrite /getNodeP ?add0n ?addn1.
        destruct n; simpl; [admit | ]; rewrite /getNodeP ?add0n ?addn1.
        destruct n; simpl; [admit | ]; rewrite /getNodeP ?add0n ?addn1.
        destruct n; simpl; [admit | ]; rewrite /getNodeP ?add0n ?addn1.
        destruct n; simpl; [admit | ]; rewrite /getNodeP ?add0n ?addn1.
        destruct n; simpl; [admit | ]; rewrite /getNodeP ?add0n ?addn1.
        destruct n; simpl; [admit | ]; rewrite /getNodeP ?add0n ?addn1.
        destruct n; simpl; [admit | ]; rewrite /getNodeP ?add0n ?addn1.
        destruct n; simpl; [admit | ]; rewrite /getNodeP ?add0n ?addn1.
        destruct n; simpl; [admit | ]; rewrite /getNodeP ?add0n ?addn1.
        destruct n; simpl; [admit | ]; rewrite /getNodeP ?add0n ?addn1.
        destruct n; simpl; [admit | ]; rewrite /getNodeP ?add0n ?addn1.
        destruct n; simpl; [admit | ]; rewrite /getNodeP ?add0n ?addn1.
        destruct n; simpl; [admit | ]; rewrite /getNodeP ?add0n ?addn1.
        destruct n; simpl; [admit | ]; rewrite /getNodeP ?add0n ?addn1.
        destruct n; simpl; [admit | ]; rewrite /getNodeP ?add0n ?addn1.
        destruct n; simpl; [admit | ]; rewrite /getNodeP ?add0n ?addn1.
      Admitted.

    End Grammar_111.
    
  End Examples.
  

End 