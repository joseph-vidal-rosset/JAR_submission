(*
  =====================================================================
  core_logic_is_not_paraconsistent_curried_commented.v
  ---------------------------------------------------------------------
  A Coq verification of:
  "Core Logic is NOT Paraconsistent -- A Certified Proof"

  This file follows the same curried encoding as the PhoX version.
  It is written in ordinary propositional Coq, without defining
  sequents as a separate datatype.

  The intended audience is a reader who may know logic, but does not
  know Coq.
  =====================================================================
*)

Section CoreLogicNotParaconsistent.

(*
  "Section" opens a local context.

  Everything declared inside this section is understood as depending
  on the assumptions introduced here. When the section is closed,
  Coq automatically generalizes over those assumptions.

  So if we declare propositional variables here, every theorem proved
  below will implicitly depend on them.
*)

Variables A B : Prop.

(*
  "Prop" is Coq's type of logical propositions.

  So A and B are arbitrary propositions.

  In the paper's informal reading:
    - A is the antecedent formula
    - B is the succedent formula used in Claim 1
  but the proofs below are schematic and work for arbitrary formulas.
*)

(* ------------------------------------------------------------------ *)
(*  ENCODING CONVENTION                                               *)
(* ------------------------------------------------------------------ *)

(*
  We use the curried encoding of sequents.

  In ordinary sequent notation:

      D, A |- C

  is represented in Coq as:

      D -> A -> C

  This is a standard higher-order encoding:
  multiple premises are written as nested implications.

  Likewise:

      D, (A -> C) -> C |- C

  becomes:

      D -> ((A -> C) -> C) -> C

  Negated sequents (antisecquents) are represented by ordinary
  propositional negation "~".

  For example:

      D, A |/- C

  is represented as:

      ~(D -> A -> C)
*)

(* ------------------------------------------------------------------ *)
(*  1.1 DNS.1                                                         *)
(* ------------------------------------------------------------------ *)

Theorem dns1 :
  forall D C : Prop, (D -> A -> C) -> (D -> ((A -> C) -> C) -> C).
Proof.
  intros D C H HD HK.
  (*
    "intros" moves assumptions from the goal into the context.

    Before "intros", the goal is:

      forall D C : Prop, (D -> A -> C) -> (D -> ((A -> C) -> C) -> C)

    After "intros D C H HD HK", we are proving C under the assumptions:

      D  : Prop
      C  : Prop
      H  : D -> A -> C
      HD : D
      HK : (A -> C) -> C

    Intuitively:
      - H says that from D and A, we can derive C.
      - HD says that D is available.
      - HK says that if we can produce A -> C, then we get C.
  *)

  apply HK.
  (*
    "apply HK" means:
    "to prove C, it is enough to prove the premise of HK."

    Since HK has type:

      (A -> C) -> C

    Coq replaces the current goal C with the new goal:

      A -> C
  *)

  intro HA.
  (*
    "intro HA" assumes A and names that assumption HA.

    Since the goal was A -> C, after introducing HA,
    the remaining goal is simply:

      C

    under the new assumption:

      HA : A
  *)

  apply H; assumption.
  (*
    H has type:

      D -> A -> C

    So "apply H" says:
    "to prove C, it is enough to prove D and A."

    Those are already available as:
      HD : D
      HA : A

    The tactic "assumption" tells Coq to solve a goal by using an
    assumption already present in the context.
  *)
Qed.

(* ------------------------------------------------------------------ *)
(*  1.2 DNS.2                                                         *)
(* ------------------------------------------------------------------ *)

Theorem dns2 :
  forall D C : Prop, (D -> A -> False) -> (D -> ((A -> C) -> C) -> C).
Proof.
  intros D C H HD HK.
  (*
    Context:
      H  : D -> A -> False
      HD : D
      HK : (A -> C) -> C

    Goal:
      C
  *)

  apply HK.
  (*
    As in dns1, to prove C using HK : (A -> C) -> C,
    it is enough to prove:

      A -> C
  *)

  intro HA.
  (*
    Assume:
      HA : A

    Goal:
      C
  *)

  exfalso.
  (*
    "exfalso" changes the current goal from an arbitrary proposition C
    to the goal False.

    This is justified by the principle of explosion:
    once False is proved, any proposition follows.
  *)

  apply H; assumption.
  (*
    H : D -> A -> False

    So applying H reduces the goal False to proving D and A,
    which are already available as HD and HA.
  *)
Qed.

(* ------------------------------------------------------------------ *)
(*  1.3 Inversion of DNS.1                                            *)
(* ------------------------------------------------------------------ *)

Theorem dns1_inv :
  forall D C : Prop, (D -> ((A -> C) -> C) -> C) -> (D -> A -> C).
Proof.
  intros D C H HD HA.
  (*
    Context:
      H  : D -> ((A -> C) -> C) -> C
      HD : D
      HA : A

    Goal:
      C

    The idea is:
    use H, which needs:
      1. D
      2. a proof of ((A -> C) -> C)
  *)

  apply H; try assumption.
  (*
    "apply H" uses H to reduce the goal C to its premises.

    The first required premise is D, and "try assumption" asks Coq to
    solve such premises automatically if possible.

    So after this line, only the second premise remains:

      (A -> C) -> C
  *)

  intro HAC.
  (*
    Assume:
      HAC : A -> C

    Goal:
      C
  *)

  apply HAC.
  (*
    Since HAC : A -> C, to prove C it is enough to prove A.
  *)

  exact HA.
  (*
    "exact HA" finishes the goal by providing the term HA : A exactly.
  *)
Qed.

(* ------------------------------------------------------------------ *)
(*  1.4 DNS.1-anti (contrapositive form)                              *)
(* ------------------------------------------------------------------ *)

Theorem dns1_anti :
  forall D C : Prop, ~(D -> A -> C) -> ~(D -> ((A -> C) -> C) -> C).
Proof.
  intros D C Hneg Hpos.
  (*
    Here:
      Hneg : ~(D -> A -> C)
      Hpos :  D -> ((A -> C) -> C) -> C

    Goal:
      False

    Why False? Because "~X" is notation for "X -> False".
    So after introducing Hpos, we are proving the contradiction
    required by the negation.
  *)

  apply Hneg.
  (*
    Hneg says that any proof of D -> A -> C leads to contradiction.

    Therefore, to prove False, it is enough to produce:

      D -> A -> C
  *)

  apply dns1_inv.
  (*
    dns1_inv transforms a proof of:

      D -> ((A -> C) -> C) -> C

    into a proof of:

      D -> A -> C
  *)

  exact Hpos.
Qed.

(* ------------------------------------------------------------------ *)
(*  1.5 Refutation of Claim 1                                         *)
(* ------------------------------------------------------------------ *)

Theorem claim1_refuted_full :
  ((((forall D C : Prop, (D -> A -> C) -> (D -> ((A -> C) -> C) -> C)) /\
      (forall D C : Prop, (D -> ((A -> C) -> C) -> C) -> (D -> A -> C)))
      -> (forall D C : Prop, ~(D -> A -> C) -> ~(D -> ((A -> C) -> C) -> C)))
    /\
    (forall D C : Prop, (D -> A -> False) -> (D -> ((A -> C) -> C) -> C))
    /\
    ~(~A -> A -> B))
  -> False.
Proof.
  intro H.
  (*
    The whole theorem says:
    if we assume
      1. from DNS.1 and its inverse we may derive DNS.1-anti,
      2. DNS.2,
      3. Claim 1, namely ~(~A -> A -> B),
    then we can derive False.

    After "intro H", the full conjunction is available as one
    hypothesis H.
  *)

  destruct H as [Hanti_builder Hrest].
  (*
    "destruct" breaks a conjunction into its components.

    Now we have:
      Hanti_builder : ((dns1-form /\ dns1_inv-form) -> dns1_anti-form)
      Hrest         : DNS.2 /\ Claim1
  *)

  destruct Hrest as [Hdns2 Hclaim1].
  (*
    So now:
      Hdns2   : forall D C, (D -> A -> False) -> (D -> ((A -> C) -> C) -> C)
      Hclaim1 : ~(~A -> A -> B)
  *)

  assert
    (Hpair :
      (forall D C : Prop, (D -> A -> C) -> (D -> ((A -> C) -> C) -> C)) /\
      (forall D C : Prop, (D -> ((A -> C) -> C) -> C) -> (D -> A -> C))).
  {
    (*
      "assert" creates an intermediate lemma inside the proof.

      Here we package together the two theorems already proved above:
      dns1 and dns1_inv.
    *)
    split.
    (*
      "split" is used when the goal is a conjunction P /\ Q.
      It creates two subgoals: first P, then Q.
    *)
    - exact dns1.
    - exact dns1_inv.
  }

  assert
    (Hanti :
      forall D C : Prop, ~(D -> A -> C) -> ~(D -> ((A -> C) -> C) -> C)).
  {
    apply Hanti_builder.
    exact Hpair.
  }
  (*
    We now obtain the contrapositive rule explicitly from
    Hanti_builder by feeding it the pair (dns1, dns1_inv).
  *)

  specialize (Hanti (~A) B).
  (*
    "specialize" instantiates universal variables.

    Hanti was:
      forall D C, ...

    After specializing with D := ~A and C := B, we get:

      Hanti : ~(~A -> A -> B) -> ~(~A -> ((A -> B) -> B) -> B)
  *)

  assert (HNAF : ~A -> A -> False).
  {
    intros HnA HA.
    exact (HnA HA).
  }
  (*
    This is the obvious contradiction pattern:
      from ~A and A, derive False.

    It is the curried encoding of the "inconsistent context"
    used to trigger DNS.2.
  *)

  assert (Hdns2inst : ~A -> ((A -> B) -> B) -> B).
  {
    apply Hdns2.
    exact HNAF.
  }
  (*
    Instantiating DNS.2 with:
      D := ~A
      C := B

    gives exactly:

      ~A -> ((A -> B) -> B) -> B
  *)

  apply (Hanti Hclaim1).
  (*
    Since:
      Hanti  : ~(~A -> A -> B) -> ~(~A -> ((A -> B) -> B) -> B)
      Hclaim1 : ~(~A -> A -> B)

    we get:

      ~(~A -> ((A -> B) -> B) -> B)

    and applying that negation means that it remains to show:

      ~A -> ((A -> B) -> B) -> B
  *)

  exact Hdns2inst.
  (*
    But this is exactly what DNS.2 provided.
    Hence contradiction.
  *)
Qed.

(* ------------------------------------------------------------------ *)
(*  2. Refutation of Claim 2                                          *)
(* ------------------------------------------------------------------ *)

Theorem claim2_refuted_full :
  ((((forall D C : Prop, (D -> A -> C) -> (D -> ((A -> C) -> C) -> C)) /\
      (forall D C : Prop, (D -> ((A -> C) -> C) -> C) -> (D -> A -> C)))
      -> (forall D C : Prop, ~(D -> A -> C) -> ~(D -> ((A -> C) -> C) -> C)))
    /\
    (forall D C : Prop, (D -> A -> False) -> (D -> ((A -> C) -> C) -> C))
    /\
    ~(~A -> A -> ~B))
  -> False.
Proof.
  intro H.
  destruct H as [Hanti_builder Hrest].
  destruct Hrest as [Hdns2 Hclaim2].

  assert
    (Hpair :
      (forall D C : Prop, (D -> A -> C) -> (D -> ((A -> C) -> C) -> C)) /\
      (forall D C : Prop, (D -> ((A -> C) -> C) -> C) -> (D -> A -> C))).
  {
    split.
    - exact dns1.
    - exact dns1_inv.
  }

  assert
    (Hanti :
      forall D C : Prop, ~(D -> A -> C) -> ~(D -> ((A -> C) -> C) -> C)).
  {
    apply Hanti_builder.
    exact Hpair.
  }

  specialize (Hanti (~A) (~B)).
  (*
    This is the crucial point for Claim 2.

    We do NOT instantiate C with B.
    We instantiate C with ~B.

    So we obtain:

      Hanti : ~(~A -> A -> ~B) -> ~(~A -> ((A -> ~B) -> ~B) -> ~B)

    This exactly matches the shape of Claim 2.
  *)

  assert (HNAF : ~A -> A -> False).
  {
    intros HnA HA.
    exact (HnA HA).
  }

  assert (Hdns2inst : ~A -> ((A -> ~B) -> ~B) -> ~B).
  {
    apply Hdns2.
    exact HNAF.
  }
  (*
    Here DNS.2 is instantiated with:
      D := ~A
      C := ~B
  *)

  apply (Hanti Hclaim2).
  exact Hdns2inst.
Qed.

End CoreLogicNotParaconsistent.

(*
  =====================================================================
  END OF FILE
  ---------------------------------------------------------------------
  Summary of what has been certified in Coq:

    dns1                DNS.1 is derivable
    dns2                DNS.2 is derivable
    dns1_inv            DNS.1 is invertible
    dns1_anti           the contrapositive form of DNS.1 holds
    claim1_refuted_full Claim 1 leads to contradiction
    claim2_refuted_full Claim 2 leads to contradiction

  The crucial benefit of the generalized succedent parameter C is that
  Claim 1 and Claim 2 become two instances of exactly the same logical
  pattern:
    - Claim 1 uses C := B
    - Claim 2 uses C := ~B

  This makes the Coq development both clean and structurally faithful
  to the PhoX argument.
  =====================================================================
*)