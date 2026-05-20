(*
  =====================================================================
  core_logic_is_not_paraconsistent.v
  ---------------------------------------------------------------------
  A Coq verification of the paper:

    "A Coq Proof that Core Logic is NOT Paraconsistent"
       (web edition, derived from the JAR submission
        "Core Logic is Not Paraconsistent -- A Certified Proof")

  ---------------------------------------------------------------------
  ENCODING

  This file follows the same higher-order propositional (curried)
  encoding as the companion PhoX and Athena files. A sequent

      Delta, A |- C

  is encoded as the Coq implication

      D -> A -> C

  where D, A, C are propositional variables (type Prop). Multiple
  premisses on the left of the turnstile become nested implications.
  An antisequent

      Delta, A |/- C

  is encoded as the negation

      ~(D -> A -> C),       i.e.       (D -> A -> C) -> False.

  This curried encoding operationalises the Arkoudas thesis that
  natural deduction IS sequent calculus: a sequent calculus rule
  becomes a natural deduction step at the level of Coq's
  intuitionistic propositional implication.

  ---------------------------------------------------------------------
  ON EX FALSO

  The script uses `exfalso` exactly once, in the proof of dns2, and it
  is *encapsulated under the implication A -> C* via a prior `intro HA`.
  This is precisely the position where Tennant himself accepts ex falso
  (under an implication), and not at the turnstile level (where he
  rejects it). The mechanisation is therefore philosophically faithful
  to Core logic's discipline on ex falso.

  ---------------------------------------------------------------------
  ANCHORS

  Each main theorem is preceded by a marker of the form

      (* ANCHOR: name *)

  so that a URL ending in  #name  opens the file at that theorem in
  waCoq. Anchors used:
     #dns1            DNS.1 derivable
     #dns2            DNS.2 derivable
     #dns1_inv        DNS.1 invertible
     #dns1_anti       DNS.1-anti (contrapositive)
     #claim1_refuted  Claim 1 refuted
     #claim2_refuted  Claim 2 refuted

  ---------------------------------------------------------------------
  AUDIENCE

  This file is written so that a reader who knows logic but not Coq
  can follow each line. The proofs are short (3-7 tactics each),
  and every tactic is explained in the comments.
  =====================================================================
*)

Section CoreLogicNotParaconsistent.

(*
  "Section" opens a local scope. Variables declared here are
  automatically generalised when the section is closed: every theorem
  proved inside the section is implicitly parameterised by them.
*)

Variables A B : Prop.

(*
  "Prop" is Coq's type of logical propositions. So A and B are
  arbitrary propositions (the schematic letters of the paper).

  Within each theorem below, we also quantify over auxiliary
  variables D and C universally (via `forall D C : Prop, ...`).
  Quantifying C explicitly lets Claim 1 and Claim 2 become two
  instances of the SAME schematic theorem, with C := B for Claim 1
  and C := ~B for Claim 2.
*)


(* ================================================================= *)
(*  1.1  DNS.1  -- derivable rule                                    *)
(* ================================================================= *)

(*
  In sequent notation:

      Delta, A |- C                      (premiss)
      -----------------------------       DNS.1
      Delta, (A -> C) -> C |- C          (conclusion)

  Curried:    (D -> A -> C) -> (D -> ((A -> C) -> C) -> C)
*)

(* ANCHOR: dns1 *)
Theorem dns1 :
  forall D C : Prop, (D -> A -> C) -> (D -> ((A -> C) -> C) -> C).
Proof.
  intros D C H HD HK.
  (*
    "intros" moves the hypotheses from the goal into the local
    context. Before this line, the goal is the entire formula. After
    "intros D C H HD HK", the context becomes:

      D  : Prop
      C  : Prop
      H  : D -> A -> C            (the premiss of DNS.1, curried)
      HD : D
      HK : (A -> C) -> C

    and the remaining goal is just  C.

    Intuitively:
      H  says: from D and A, we get C.
      HD says: D is available.
      HK says: if we can produce A -> C, then we get C.
  *)

  apply HK.
  (*
    "apply HK" reads HK : (A -> C) -> C  as a rule that produces C
    from a proof of (A -> C). So Coq replaces the goal  C  by the
    new goal  A -> C.
  *)

  intro HA.
  (*
    "intro HA" assumes the antecedent A and names this assumption HA.
    After this line, the context has the extra assumption  HA : A
    and the goal becomes simply  C.
  *)

  apply H; assumption.
  (*
    "apply H" uses H : D -> A -> C  to reduce the goal C to two
    subgoals: D and A. The semicolon-assumption  ";assumption"
    closes each subgoal automatically by finding HD : D and HA : A
    already in the context.
  *)
Qed.


(* ================================================================= *)
(*  1.2  DNS.2  -- the Core-specific derived rule                    *)
(* ================================================================= *)

(*
  In sequent notation:

      Delta, A |-                        (empty succedent;
                                          here encoded as
                                          D -> A -> False)
      -----------------------------       DNS.2
      Delta, (A -> C) -> C |- C

  The empty succedent  |-  is the formal mark of an inconsistent
  context, conventionally identified with  |- False  in the
  intuitionistic/minimal reading made explicit by David, Nour and
  Raffalli.

  DNS.2 is what makes the contradiction of Claims 1 and 2 possible.
  It is licensed by Core's rule R->_C: from an inconsistent left
  context, derive  C  for arbitrary C, but only under the implication
  built by "intro HA" below -- never at the turnstile level.
*)

(* ANCHOR: dns2 *)
Theorem dns2 :
  forall D C : Prop, (D -> A -> False) -> (D -> ((A -> C) -> C) -> C).
Proof.
  intros D C H HD HK.
  (*
    Context after intros:
      H  : D -> A -> False       (D extended with A is inconsistent)
      HD : D
      HK : (A -> C) -> C
    Goal: C.
  *)

  apply HK.
  (*
    As in dns1, reduce the goal C to the goal A -> C, using
    HK : (A -> C) -> C.
  *)

  intro HA.
  (*
    Assume A (name it HA). The goal is now C, with HA : A added
    to the context. NOTICE: from this point on, we are constructing
    the implication A -> C; the use of "exfalso" below is therefore
    ENCAPSULATED under this implication, never at the turnstile.
  *)

  exfalso.
  (*
    "exfalso" replaces the current goal C by the goal False.
    This is justified by the principle of explosion (ex falso
    quodlibet): once False is established, any proposition follows.
    Here, this is the move that Core's R->_C licenses, and it is
    licit because we are under the scope of HA : A introduced
    above -- not at the level of the global turnstile.
  *)

  apply H; assumption.
  (*
    H : D -> A -> False reduces the goal False to producing D and A.
    Both are already in context (HD and HA), closed automatically
    by "assumption".
  *)
Qed.


(* ================================================================= *)
(*  1.3  DNS.1 is invertible                                         *)
(* ================================================================= *)

(*
  In sequent notation:

      Delta, (A -> C) -> C |- C         (premiss = conclusion of DNS.1)
      -----------------------------      DNS.1-inv
      Delta, A |- C                     (consequence)

  Curried:   (D -> ((A -> C) -> C) -> C) -> (D -> A -> C)

  The proof recovers the antecedent A by feeding back the implication
  A -> C constructed on the fly from the assumption HA : A.
*)

(* ANCHOR: dns1_inv *)
Theorem dns1_inv :
  forall D C : Prop, (D -> ((A -> C) -> C) -> C) -> (D -> A -> C).
Proof.
  intros D C H HD HA.
  (*
    Context:
      H  : D -> ((A -> C) -> C) -> C    (the inverse premiss)
      HD : D
      HA : A
    Goal: C.

    Plan: apply H, which needs D (already available as HD) and a
    proof of (A -> C) -> C. The first need is settled automatically;
    the second is settled by introducing A -> C and applying it to
    HA : A.
  *)

  apply H; try assumption.
  (*
    "apply H" reduces the goal to producing each premiss of H.
    The first premiss is D, immediately discharged by HD via
    "try assumption". The remaining goal is  (A -> C) -> C.
  *)

  intro HAC.
  (*
    Assume A -> C (name it HAC). The goal becomes C.
  *)

  apply HAC.
  (*
    Reduce the goal C to producing A, using HAC : A -> C.
  *)

  exact HA.
  (*
    "exact HA" closes the goal by exhibiting HA : A directly.
  *)
Qed.


(* ================================================================= *)
(*  1.4  DNS.1-anti  -- the contrapositive of invertibility          *)
(* ================================================================= *)

(*
  In sequent notation:

      Delta, A |/- C                    (antisequent)
      -----------------------------      DNS.1-anti
      Delta, (A -> C) -> C |/- C        (antisequent)

  Curried:    ~(D -> A -> C) -> ~(D -> ((A -> C) -> C) -> C)

  This is the rule we use to convert Claim 1 (and Claim 2) into the
  negative side of the contradiction. Its proof is just the
  contrapositive of dns1_inv.
*)

(* ANCHOR: dns1_anti *)
Theorem dns1_anti :
  forall D C : Prop, ~(D -> A -> C) -> ~(D -> ((A -> C) -> C) -> C).
Proof.
  intros D C Hneg Hpos.
  (*
    Context:
      Hneg : ~(D -> A -> C)              (i.e. (D -> A -> C) -> False)
      Hpos :  D -> ((A -> C) -> C) -> C
    Goal: False.

    Why False as the goal? Because the conclusion of the theorem
    is the negation ~(D -> ((A->C)->C) -> C), which unfolds to
    (D -> ((A->C)->C) -> C) -> False. After "intros ... Hpos", we
    are precisely required to derive False.
  *)

  apply Hneg.
  (*
    Hneg says: any proof of (D -> A -> C) leads to False. So to
    derive False, it is enough to produce (D -> A -> C).
  *)

  apply dns1_inv.
  (*
    dns1_inv transforms a proof of (D -> ((A -> C) -> C) -> C)
    into a proof of (D -> A -> C). So it is enough to produce
    (D -> ((A -> C) -> C) -> C).
  *)

  exact Hpos.
  (*
    Hpos has exactly the required type.
  *)
Qed.


(* ================================================================= *)
(*  END OF PART 1: the four basic theorems are certified.            *)
(*                                                                   *)
(*  Part 2 instantiates them to obtain the contradiction.            *)
(* ================================================================= *)


(* ================================================================= *)
(*  2.1  Refutation of Claim 1                                       *)
(* ================================================================= *)

(*
  Claim 1 (Tennant): the antisequent  ~A, A |/- B  holds in Core.
  Curried:           ~(~A -> A -> B).

  Statement of claim1_refuted_full: under the conjunction of

    (a) DNS.1-anti is derivable from DNS.1 and DNS.1-inv, that is
        (((D -> A -> C) -> (D -> ((A->C)->C) -> C)) /\
         ((D -> ((A->C)->C) -> C) -> (D -> A -> C)))
        -> ~(D -> A -> C) -> ~(D -> ((A->C)->C) -> C)
        (quantified over D, C);

    (b) DNS.2, quantified over D, C;

    (c) Claim 1: ~(~A -> A -> B);

  we derive False.

  The argument:
    - Instantiate DNS.1-anti with D := ~A, C := B, applied to Claim 1
      to obtain  ~(~A -> ((A -> B) -> B) -> B).
    - Instantiate DNS.2 with D := ~A, C := B, applied to the trivial
      inconsistency  ~A -> A -> False, to obtain
      ~A -> ((A -> B) -> B) -> B.
    - The two contradict. Conclusion: False.
*)

(* ANCHOR: claim1_refuted *)
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
    H bundles together: (Hanti_builder, Hdns2, Hclaim1).
    "intro H" introduces this whole conjunction.
  *)

  destruct H as [Hanti_builder Hrest].
  (*
    "destruct" splits a conjunction. After this line:
      Hanti_builder : (dns1-form /\ dns1_inv-form) -> dns1_anti-form
      Hrest         : DNS.2-form /\ Claim 1
  *)

  destruct Hrest as [Hdns2 Hclaim1].
  (*
    Split Hrest:
      Hdns2   : forall D C, (D -> A -> False) -> (D -> ((A->C)->C) -> C)
      Hclaim1 : ~(~A -> A -> B)
  *)

  assert
    (Hpair :
      (forall D C : Prop, (D -> A -> C) -> (D -> ((A -> C) -> C) -> C)) /\
      (forall D C : Prop, (D -> ((A -> C) -> C) -> C) -> (D -> A -> C))).
  {
    (*
      "assert" creates an auxiliary lemma. Here we package together
      dns1 and dns1_inv (both already proved above) into a single
      conjunction, in the exact form that Hanti_builder expects.
    *)
    split.
    (*
      "split" turns the goal P /\ Q into two subgoals P and Q.
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
    Apply Hanti_builder to Hpair to obtain DNS.1-anti in usable form,
    quantified over D and C.
  *)

  specialize (Hanti (~A) B).
  (*
    "specialize" instantiates universally quantified variables.
    Before: Hanti : forall D C, ~(D -> A -> C) -> ~(D -> ((A->C)->C) -> C).
    After:  Hanti : ~(~A -> A -> B) -> ~(~A -> ((A -> B) -> B) -> B).

    We chose D := ~A and C := B, matching the curried form of Claim 1.
  *)

  assert (HNAF : ~A -> A -> False).
  {
    intros HnA HA.
    exact (HnA HA).
  }
  (*
    The trivial inconsistency: from ~A (= A -> False) and A, derive
    False by direct application. This is the curried counterpart of
    the inconsistent context  {A, ~A}.

    NB: ~X is Coq's notation for X -> False. So ~A applied to HA : A
    yields False.
  *)

  assert (Hdns2inst : ~A -> ((A -> B) -> B) -> B).
  {
    apply Hdns2.
    exact HNAF.
  }
  (*
    Instantiate Hdns2 (= DNS.2) with D := ~A, C := B, fed with HNAF
    (the inconsistency). Result:  ~A -> ((A -> B) -> B) -> B,
    the POSITIVE side of the contradiction (Core-derivable).
  *)

  apply (Hanti Hclaim1).
  (*
    Hanti instantiated to Claim 1 yields  ~(~A -> ((A->B)->B) -> B).
    Applying this negation to the goal (which is False) leaves the
    goal:  ~A -> ((A -> B) -> B) -> B.
  *)

  exact Hdns2inst.
  (*
    But this is exactly Hdns2inst. Contradiction; QED.
  *)
Qed.


(* ================================================================= *)
(*  2.2  Refutation of Claim 2                                       *)
(* ================================================================= *)

(*
  Claim 2 (Tennant): the antisequent  ~A, A |/- ~B  holds in Core.
  Curried:           ~(~A -> A -> ~B).

  Exactly the same pattern as claim1_refuted_full, with C := ~B
  instead of C := B. The structural identity reflects the paper's
  observation: Claims 1 and 2 are refuted by THE SAME MECHANISM,
  with B and ~B playing schematic roles.
*)

(* ANCHOR: claim2_refuted *)
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
  (*
    Same destructuring as for Claim 1, but the last component is
    Hclaim2 instead of Hclaim1.
  *)

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
    Crucial difference with Claim 1: HERE we instantiate
       D := ~A      (as before)
       C := ~B      (NOT B)

    After specialize:
      Hanti : ~(~A -> A -> ~B) -> ~(~A -> ((A -> ~B) -> ~B) -> ~B)

    This matches the shape of Claim 2 exactly.
  *)

  assert (HNAF : ~A -> A -> False).
  {
    intros HnA HA.
    exact (HnA HA).
  }
  (*
    Same trivial inconsistency as before.
  *)

  assert (Hdns2inst : ~A -> ((A -> ~B) -> ~B) -> ~B).
  {
    apply Hdns2.
    exact HNAF.
  }
  (*
    DNS.2 instantiated with D := ~A, C := ~B, fed HNAF. Result:
    the Core-derivable positive side, now with ~B instead of B.
  *)

  apply (Hanti Hclaim2).
  exact Hdns2inst.
  (*
    Contradiction by the same modus ponens pattern as in Claim 1.
  *)
Qed.

End CoreLogicNotParaconsistent.

(*
  =====================================================================
  END OF FILE
  ---------------------------------------------------------------------
  Summary of what has been certified in Coq:

    dns1                 DNS.1 is derivable
    dns2                 DNS.2 is derivable (Core-specific; uses
                         exfalso ENCAPSULATED under an implication,
                         never at the turnstile level)
    dns1_inv             DNS.1 is invertible
    dns1_anti            the contrapositive form of DNS.1 holds
    claim1_refuted_full  Claim 1 leads to contradiction
    claim2_refuted_full  Claim 2 leads to contradiction

  ---------------------------------------------------------------------
  No classical principle is used. The script lives entirely in the
  intuitionistic fragment of Coq's propositional logic. Tennant's
  own conventions on ex falso are respected throughout: it appears
  only once, in dns2, inside the scope of "intro HA" -- exactly the
  position licensed by Core's rule R->_C.

  ---------------------------------------------------------------------
  Each main theorem is anchored: the URL  ...test.html?...#name
  opens the file at that theorem. Anchors:
     #dns1   #dns2   #dns1_inv   #dns1_anti
     #claim1_refuted   #claim2_refuted
  =====================================================================
*)
