(* ================================================================
   CERTIFIED PROOF (Coq)
   "Core Logic is not Paraconsistent"
   J. Vidal-Rosset, Universite de Lorraine, 2026
   Submitted to the Journal of Automated Reasoning
   ----------------------------------------------------------------
   This file mechanically certifies the central argument of the
   paper. The mathematical content (statement, motivation,
   dialectic) is in the paper. The comments here address only
   what the Coq commands do.

   Final theorem: claim1_false : nat -> nat -> False.
   Print Assumptions claim1_false returns two axioms:
     - Claim1_Tennant: the antisequent posited by Tennant in
       Core Logic, p. 156.
     - min_antisequent_rule_to_core: the transfer of antisequent
       rules from minimal_F to core_logic (structural property
       of F as a shared fragment).

   The file compiles in Coq 8.18 without warnings. To check
   online: paste it into https://jscoq.github.io/scratchpad.html
   and step through with the green arrows.
   ================================================================ *)
From Coq Require Import List ListSet.
Import ListNotations.
(* ----------------------------------------------------------------
   THE LANGUAGE (paper Sec. 2.1)

   "Inductive T : Type := ..." declares a new type T with the listed
   constructors. Coq enforces that constructors are distinct (Var,
   Neg, Impl produce distinct values), a fact used later by the tactic
   "discriminate".
   ---------------------------------------------------------------- *)
Inductive formula : Type :=
  | Var  : nat -> formula
  | Neg  : formula -> formula
  | Impl : formula -> formula -> formula.
(* ----------------------------------------------------------------
   THE FRAGMENT PARAMETER AND THE DERIVABILITY PREDICATE

   F has two readings: minimal_F (the rules shared with M) and
   core_logic (the rules of C, which adds R->_C). We encode this by a
   parameter f : fragment_F.

   Sequents are encoded with contexts as lists (with an Ex constructor
   for adjacent exchange, the only structural move the argument uses)
   and right-hand sides as "option formula" (Some A for a single
   formula, None for the empty succedent).

   The first five constructors quantify over f, so they exist in both
   readings. The sixth constructor R_arrow_core has f = core_logic
   fixed in its signature, restricting it to the Core reading of
   F. Antisequents are written directly as "derivable f G C -> False"
   without a separate definition.
   ---------------------------------------------------------------- *)
Inductive fragment_F : Type := minimal_F | core_logic.

Inductive derivable : fragment_F -> set formula -> option formula -> Prop :=
  | Ax           : forall f G A,
                     In A G ->
                     derivable f G (Some A)
  | L_neg        : forall f G A,
                     derivable f G (Some A) ->
                     derivable f (Neg A :: G) None
  | R_arrow      : forall f G A B,
                     derivable f (A :: G) (Some B) ->
                     derivable f G (Some (Impl A B))
  | L_arrow      : forall f G A B C,
                     derivable f G (Some A) ->
                     derivable f (B :: G) C ->
                     derivable f (Impl A B :: G) C
  | Exchange     : forall f x y C,
                     derivable f [x; y] C ->
                     derivable f [y; x] C
  | R_arrow_core : forall G A B,
                     derivable core_logic (A :: G) None ->
                     derivable core_logic G (Some (Impl A B)).
(* ----------------------------------------------------------------
   MIN-DERIVATIONS ARE CORE-DERIVATIONS

   By induction on the derivation. Each constructor instance at f =
   minimal_F is re-applied at f = core_logic; the case R_arrow_core is
   impossible because the inductive hypothesis is typed at minimal_F,
   contradicting the constructor's signature.
   ---------------------------------------------------------------- *)
Lemma MinToCore : forall G C,
  derivable minimal_F G C -> derivable core_logic G C.
Proof.
  intros G C H.
  remember minimal_F as f eqn:Hf.
  induction H.
  - apply Ax. assumption.
  - apply L_neg. apply IHderivable. assumption.
  - apply R_arrow. apply IHderivable. assumption.
  - apply L_arrow.
    + apply IHderivable1. assumption.
    + apply IHderivable2. assumption.
  - apply Exchange. apply IHderivable. assumption.
  - discriminate Hf.
Qed.
(* ----------------------------------------------------------------
   THE CORE-DERIVABLE ABSURDITY  (paper Sec. 2.5, left subtree)
   ---------------------------------------------------------------- *)
Lemma absurdity_core : forall (a : nat),
  derivable core_logic [Var a; Neg (Var a)] None.
Proof.
  intros a.
  apply (Exchange core_logic (Neg (Var a)) (Var a)).
  apply L_neg.
  apply Ax. left. reflexivity.
Qed.
(* ----------------------------------------------------------------
   DNS.1 IS A DERIVED RULE OF minimal_F  (paper Table 2)
   ---------------------------------------------------------------- *)
Theorem DNS1_instantiated : forall (a b : nat),
  derivable minimal_F [Var a; Neg (Var a)] (Some (Var b)) ->
  derivable minimal_F [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)]
                       (Some (Var b)).
Proof.
  intros a b H.
  apply (L_arrow minimal_F _ (Impl (Var a) (Var b)) (Var b) (Some (Var b))).
  - apply R_arrow. assumption.
  - apply Ax. left. reflexivity.
Qed.
(* ----------------------------------------------------------------
   DNS.2 IS A DERIVED RULE OF core_logic  (paper Table 2)
   ---------------------------------------------------------------- *)
Theorem DNS2_instantiated : forall (a b : nat),
  derivable core_logic [Var a; Neg (Var a)] None ->
  derivable core_logic [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)]
                       (Some (Var b)).
Proof.
  intros a b H.
  apply (L_arrow core_logic _ (Impl (Var a) (Var b)) (Var b) (Some (Var b))).
  - apply R_arrow_core. assumption.
  - apply Ax. left. reflexivity.
Qed.
(* ----------------------------------------------------------------
   DNS.1 IS INVERTIBLE IN minimal_F (paper Sec. 2.3)

   Structural induction on the derivation. The R_arrow_core case is
   eliminated by "discriminate Hf" because R_arrow_core has f =
   core_logic in its signature while the induction is at f =
   minimal_F. This is the Coq counterpart of Remark 1 of the paper.

   The "remember ... eqn:..." idiom freezes specific terms as fresh
   variables (with equations recording what they stand for), so that
   "induction" does not destroy them. After "revert ...; induction H;
   intros ...", each inductive case has the equations available for
   analysis.

   Two-step proof: (1) sub-lemma for the singleton context; (2) main
   theorem, generalised over both orderings of the doubleton context
   to absorb Exchange.
   ---------------------------------------------------------------- *)
Lemma R_arrow_inv_NegA_min : forall (a b : nat),
  derivable minimal_F [Neg (Var a)] (Some (Impl (Var a) (Var b))) ->
  derivable minimal_F [Var a; Neg (Var a)] (Some (Var b)).
Proof.
  intros a b H.
  remember minimal_F as f eqn:Hf.
  remember [Neg (Var a)] as G eqn:HG.
  remember (Some (Impl (Var a) (Var b))) as C eqn:HC.
  revert Hf HG HC.
  induction H; intros Hf HG HC.
  - subst. injection HC as HC'. subst.
    simpl in H. destruct H as [Heq | []]. discriminate Heq.
  - discriminate HC.
  - injection HC as HA HB. subst. assumption.
  - injection HG as Hhead Htail. discriminate Hhead.
  - discriminate HG.
  - discriminate Hf.
Qed.

Theorem DNS1_inv_instantiated : forall (a b : nat),
  derivable minimal_F [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)]
                       (Some (Var b)) ->
  derivable minimal_F [Var a; Neg (Var a)] (Some (Var b)).
Proof.
  intros a b H.
  assert (Hgen : forall f G C,
    derivable f G C ->
    f = minimal_F ->
    (G = [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)] \/
     G = [Neg (Var a); Impl (Impl (Var a) (Var b)) (Var b)]) ->
    C = Some (Var b) ->
    derivable minimal_F [Var a; Neg (Var a)] (Some (Var b))).
  { clear H. intros f G C HD. induction HD; intros Hf HG HC.
    - injection HC as HC'. subst.
      destruct HG as [HG|HG]; subst; simpl in H;
        destruct H as [Heq|[Heq|[]]]; discriminate Heq.
    - discriminate HC.
    - discriminate HC.
    - destruct HG as [HG|HG].
      + injection HG as HA HB HG0. subst.
        apply R_arrow_inv_NegA_min. assumption.
      + injection HG as Hhead Htail. discriminate Hhead.
    - destruct HG as [HG|HG].
      + injection HG as Hy Hx. subst.
        apply IHHD; [reflexivity | right; reflexivity | reflexivity].
      + injection HG as Hy Hx. subst.
        apply IHHD; [reflexivity | left; reflexivity | reflexivity].
    - discriminate Hf.
  }
  apply (Hgen _ _ _ H eq_refl).
  - left. reflexivity.
  - reflexivity.
Qed.
(* ----------------------------------------------------------------
   DNS.1-ANTI BY CONTRAPOSITION  (paper Sec. 2.4)
   ---------------------------------------------------------------- *)
Theorem DNS1_anti_instantiated : forall (a b : nat),
  (derivable minimal_F [Var a; Neg (Var a)] (Some (Var b)) -> False) ->
  (derivable minimal_F [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)]
     (Some (Var b)) -> False).
Proof.
  intros a b H1 H2.
  apply H1. apply DNS1_inv_instantiated. assumption.
Qed.
(* ----------------------------------------------------------------
   AXIOM I: Tennant's Claim 1, posited in core_logic
   ---------------------------------------------------------------- *)
Axiom Claim1_Tennant :
  forall (a b : nat),
  derivable core_logic [Var a; Neg (Var a)] (Some (Var b)) -> False.
(* ----------------------------------------------------------------
   AXIOM II: transfer of antisequent rules from minimal_F to
   core_logic.
   ---------------------------------------------------------------- *)
Axiom min_antisequent_rule_to_core :
  forall (G G' : set formula) (C C' : option formula),
    ((derivable minimal_F G C -> False) ->
     (derivable minimal_F G' C' -> False)) ->
    ((derivable core_logic G C -> False) ->
     (derivable core_logic G' C' -> False)).
(* ----------------------------------------------------------------
   THE CONTRADICTION  (paper Sec. 2.5)

   Four steps:
     (1) "assert" introduces an intermediate proposition (the
         lifted DNS.1-anti rule in core_logic), proved by applying
         the axiom of rule transfer to DNS1_anti_instantiated.
     (2) The lifted rule is applied to Claim1_Tennant, yielding
         the fatal antisequent in core_logic.
     (3) "apply DNS2_instantiated" reduces the goal to deriving
         the absurdity in core_logic.
     (4) "apply absurdity_core" closes it.
   ---------------------------------------------------------------- *)
Theorem claim1_false : forall (a b : nat), False.
Proof.
  intros a b.
  assert (Hanti_core :
    (derivable core_logic [Var a; Neg (Var a)] (Some (Var b)) -> False) ->
    (derivable core_logic [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)]
                          (Some (Var b)) -> False)).
  { apply min_antisequent_rule_to_core.
    apply DNS1_anti_instantiated. }
  apply (Hanti_core (Claim1_Tennant a b)).
  apply DNS2_instantiated.
  apply absurdity_core.
Qed.
(* ================================================================
   COROLLARY  (paper Sec. 3): Claim 2 entails the same contradiction
   by substituting Neg (Var b) for Var b throughout. The proof
   script is identical modulo that substitution.
   ================================================================ *)
