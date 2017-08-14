Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.

Section RA_Definition.
  Record RA := {
    Q' : Type;
    T' : Type;
    N' : Type;
    edges' : Ensemble (Q' * Q');
    subpath' : relation (Q' * Q');
    call' : N' -> Q' * Q';
    edge'symbol' : forall e : Q' * Q', In (Q' * Q') edges' e -> option (T' + N');
  }.
  
  Variable ra : RA.

  (* State type *)
  Local Definition Q : Type := Q' ra.
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
  
  (* N -> Q * Q *)
  Definition call : N -> Q * Q := call' ra.
  
  (* Symbol *)
  Definition S : Type := option (T + N).
  Definition symbols : Ensemble S := Full_set S.
  Definition symbol'count : nat := terminal'count + nonterminal'count.
  
  (* Edges *)
  Definition edges : Ensemble (Q * Q) := edges' ra.
  Variable edge'count : nat.
  Axiom edges_is_state_pair : forall x y : Q, In (Q * Q) edges (x, y) -> In Q states x /\ In Q states y.
  Axiom edges_is_finite : cardinal (Q * Q) edges edge'count.
  Definition edge'relation: relation Q := fun x y => In (Q * Q) edges (x, y).
  
  (* Edge -> Symbol *)
  Definition edge'symbol : forall e : Q * Q, In (Q * Q) edges e -> S := edge'symbol' ra.
  
  (* Paths *)
  Variable path'count : nat.
  Definition paths'relation : relation Q := clos_refl_trans Q edge'relation.
  Definition paths : Ensemble (Q * Q) := fun xy => paths'relation (fst xy) (snd xy).
  Axiom paths_is_state_pair : forall x y : Q, In (Q * Q) paths (x, y) -> In Q states x /\ In Q states y.
  Axiom paths_is_finite : cardinal (Q * Q) paths path'count.
  Lemma edges_is_path'subpath : Included (Q * Q) edges paths.
  Proof.
    intro.
    intro.
    unfold paths.
    unfold paths'relation.
    unfold edge'relation.
    apply rt_step.
  Admitted.
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
  Definition subpath : relation (Q * Q) := subpath' ra.
  Axiom subpath_is_reflexive : reflexive (Q * Q) subpath.
  Axiom subpath_is_transitive : transitive (Q * Q) subpath.
  Axiom subpath_id : forall x : Q * Q, subpath x x.
  Axiom subpath_edges : forall x y : Q, In (Q * Q) edges (x, y) -> subpath (x, y) (x, y).
  Axiom subpath_concat : forall x y z : Q, subpath (x, y) (x, y) /\ subpath (y, z) (y, z) -> subpath (x, y) (x, z) /\ subpath (y, z) (x, z).
  
  (* Path -> [Symbol] *)
  Definition spath'symbols : forall e : Q * Q, In (Q * Q) edges e -> Ensemble S := fun e i => Singleton S (edge'symbol e i).
  Variable path'symbols : forall e : Q * Q, In (Q * Q) paths e -> Ensemble S.
  Axiom spath_is_path'subpath : forall e i j, Included S (path'symbols e i) (spath'symbols e j).
  Axiom subpath'symbols : forall x y i j, subpath x y -> Included S (path'symbols x i) (path'symbols y j).
  
  (* Calls *)
  Definition calls : relation N := fun n m : N => exists q, subpath (call n) q /\ forall i : In (Q * Q) paths q, In S (path'symbols q i) (Some (inr m)).
  Definition closcalls := clos_trans N calls.
  Definition is_nonrecursive := forall x, ~ closcalls x x.
End RA_Definition.

Section Input_Definition.
  Variable Char : Type.
  Record LinearInput := {
    current : nat -> Char;
    next : nat -> nat;
  }.
End Input_Definition.

Section GLL_Definition.
  Variable GrammarState : Type.
  Variable StackPos : Type.
  Variable SPPFPos : Type.
  Record GLL_Hundler := {
    position : nat;
    state : GrammarState;
    stack_pos : StackPos;
    sppf : SPPFPos;
  }.
End GLL_Definition.
