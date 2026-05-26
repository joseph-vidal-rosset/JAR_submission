(* ════════════════════════════════════════════════════════════════
   Proof in Coq that Core Logic is not Paraconsistent
   ════════════════════════════════════════════════════════════════

   This Coq file certifies the argument according to which Tennant's
   two foundational claims about Core logic ℂ — that ℂ is
   paraconsistent (Claim 1), and that ℂ merely overlaps minimal logic
   𝐌 rather than including it (Claim 2) — cannot be sustained without
   contradiction. The proof is done inside a small fragment ℱ of ℂ,
   using only rules that Tennant himself accepts.

   The file compiles in Coq 8.18 without warnings. A short glossary at
   the foot of the file points to the relevant sections of the Coq
   8.18 reference manual.
   ════════════════════════════════════════════════════════════════ *)

(* The language of ℱ is the usual propositional language built from
   atomic variables, negation, and implication. In ℂ, contexts are
   sets, hence the first line of this script.  Propositional variables
   are indexed by natural numbers via the constructor Var : nat →
   formula, providing a countably infinite supply of distinct atoms.*)

From Coq Require Import List ListSet.
Import ListNotations.

Inductive formula : Type :=
  | Var  : nat -> formula
  | Neg  : formula -> formula
  | Impl : formula -> formula -> formula.

(* ── Local note ──
   The three constructors are distinct by construction, which the
   tactic "discriminate" will use silently throughout the file to
   close cases where an equation between two of them would have
   to hold. *)

(* Fragment ℱ contains five rules: Ax., L¬, R→, L→, and the
  Core-specific rule R→ℂ. The first four rules are exactly those of
  minimal logic 𝐌 in fragment ℱ. The fifth, R→ℂ, derives an
  implication from an inconsistent context and is the single rule that
  distinguishes ℂ from 𝐌 in ℱ.

  To represent both readings of ℱ in a single inductive predicate, we
  introduce a fragment indicator f : fragment_F taking two values,
  minimal_F and core_logic. The first five rules quantify universally
  over f and therefore exist in both readings; the sixth,
  R_arrow_core, fixes f = core_logic in its signature and is
  restricted by typing to the Core reading.

  Sequents are encoded with contexts as lists of formulas. An explicit
  Exchange constructor is added to permit swapping two adjacent
  formulas in a doubleton context — the only structural move the
  argument requires (obviously allowed in a logical system where
  contexts are sets of formulas). Right-hand sides are encoded as
  "option formula": "Some A" represents a single succedent formula,
  "None" the empty succedent (used in inconsistency sequents Γ ⊢).

   An antisequent Γ ⊬ C is written directly as the type

                       derivable f Γ C → False

   An antisequent is, by the propositions-as-types correspondence, a
   function from a would-be derivation to absurdity. No separate
   "unprovable" predicate is introduced.*)

Inductive fragment_F : Type := minimal_F | core_logic.

Inductive derivable :
  fragment_F -> set formula -> option formula -> Prop :=
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

(* ── Local note ──
   The signature of R_arrow_core is the key typing constraint of
   this file: by fixing f = core_logic in both premiss and
   conclusion, the constructor refuses to exist for f = minimal_F.
   In any induction at f = minimal_F, the case R_arrow_core is
   therefore eliminated by "discriminate" on the equation
   f = minimal_F that "remember" has frozen. This typing trick is
   what allows minimal_F and core_logic to share a single
   inductive predicate while preserving their asymmetry. *)

(* Since ℱ shares its first four rules between 𝐌 and ℂ, every
   derivation built in minimal_F can be replayed verbatim in
   core_logic. The lemma below makes this inclusion mechanically
   explicit. It is the formal expression of ℱ as a shared fragment:
   nothing is imported from outside ℱ when one moves from the minimal
   reading to the Core reading. *)

Lemma MinToCore :
  forall G C,
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

(* ── Local note ──
   "remember minimal_F as f eqn:Hf" freezes minimal_F as a fresh
   variable f together with the equation Hf : f = minimal_F. This
   freezing is what preserves, inside the inductive cases, the
   information that the induction takes place at the minimal
   reading: without it, the case R_arrow_core (whose constructor
   demands f = core_logic) could no longer be discharged. The
   sixth case is then closed by "discriminate Hf", which exploits
   the impossibility of f = minimal_F ∧ f = core_logic. *)

(* The sequent ¬A, A ⊢ is the left subtree of the final
   contradiction (paper §2.5). It expresses the inconsistency of
   the context {¬A, A} and is derivable by a single application
   of L¬ preceded by an Exchange to bring ¬A into head position. *)

Lemma absurdity_core :
  forall (a : nat),
  derivable core_logic [Var a; Neg (Var a)] None.
Proof.
  intros a.
  apply (Exchange core_logic (Neg (Var a)) (Var a)).
  apply L_neg.
  apply Ax. left. reflexivity.
Qed.

(* ── Local note ──
   The Exchange step is needed because L_neg requires ¬A to be at
   the head of the context, while the convention adopted in the
   rest of the file places ¬A in second position. *)

(* Following Slaney [Slaney 1994], we call DNS (Double Negation
   à la Slaney) two rules central to the argument:

         A, ∆ ⊢ B                          A, ∆ ⊢
     ─────────────────── DNS.1     ─────────────────── DNS.2
     (A → B) → B, ∆ ⊢ B            (A → B) → B, ∆ ⊢ B

   DNS.1 is derivable in 𝐌 using R→ and L→. DNS.2 is derivable
   in ℂ using R→ℂ and L→: it requires the Core-specific rule
   because its premiss has an empty succedent. Both derivations
   live entirely inside ℱ (see paper, Table 2). We instantiate
   both rules at the specific contexts that appear in the final
   argument, namely A = Var a, ∆ = [Neg (Var a)], and B = Var b.*)

Theorem DNS1_instantiated :
  forall (a b : nat),
  derivable minimal_F [Var a; Neg (Var a)] (Some (Var b)) ->
  derivable minimal_F [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)]
                       (Some (Var b)).
Proof.
  intros a b H.
  apply (L_arrow minimal_F _ (Impl (Var a) (Var b)) (Var b) (Some (Var b))).
  - apply R_arrow. assumption.
  - apply Ax. left. reflexivity.
Qed.

(* ── Local note ──
   The script transcribes the derivation of DNS.1 (paper, Table 2)
   from root to top. The explicit arguments passed to L_arrow
   instantiate the schematic A, B, C of the rule to the specific
   formulas of the target sequent. *)

Theorem DNS2_instantiated :
  forall (a b : nat),
  derivable core_logic [Var a; Neg (Var a)] None ->
  derivable core_logic [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)]
                       (Some (Var b)).
Proof.
  intros a b H.
  apply (L_arrow core_logic _ (Impl (Var a) (Var b)) (Var b) (Some (Var b))).
  - apply R_arrow_core. assumption.
  - apply Ax. left. reflexivity.
Qed.

(* ── Local note ──
   Structurally identical to DNS1_instantiated, except that the
   rule used to derive ∆ ⊢ A → B from A, ∆ ⊢ is R_arrow_core
   rather than R_arrow. This is where the Core-specific rule R→ℂ
   enters the argument. *)

(* DNS.1 is invertible: from the derivability of its conclusion,
   the derivability of its premiss follows. This is the formal
   counterpart of the syntactic and semantic proofs given in the
   paper (§2.3). The semantic proof, in particular, is independent
   of any classical commitment and applies under the minimal
   reading of ⊥ as a nonlogical constant.

   The mechanisation proceeds in two steps. First, a sub-lemma
   inverts R→ over the singleton context [¬A]. Then the main
   theorem inverts DNS.1 over the doubleton context, generalised
   over both orderings to absorb the Exchange constructor.*)

Lemma R_arrow_inv_NegA_min :
  forall (a b : nat),
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

(* ── Local note ── The three "remember" invocations freeze the three
   specific instances (minimal_F, the singleton context, the
   implication succedent) so that they survive the "induction" tactic
   and remain available for case analysis. The pattern "revert ...;
   induction H; intros ..." reintroduces the equations inside each
   inductive case. Of the six branches, only R_arrow yields the
   inverted derivation directly; the other five are closed as
   impossible by "discriminate" or "injection ... discriminate" on the
   context, succedent, or fragment equations. *)

Theorem DNS1_inv_instantiated :
  forall (a b : nat),
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

(* ── Local note ──
   The auxiliary lemma Hgen is generalised over both orderings of
   the doubleton context. This generalisation is needed because
   the Exchange case of the induction yields a derivation on the
   permuted context: only a disjunction in the hypothesis allows
   the induction hypothesis to apply to either ordering. *)

(* The invertibility of DNS.1 means that conclusion-derivability
   entails premiss-derivability. Contraposing: premiss-non-
   derivability entails conclusion-non-derivability. This is exactly
   the antisequent form of DNS.1:

               A, ∆ ⊬ B
      ──────────────────── DNS.1-anti
      (A → B) → B, ∆  ⊬ B

   Note that, pace Tennant, antisequents are encoded by sequent
   implying False, only to avoid to code "unprovable" as being the
   negation of "provable".*)

Theorem DNS1_anti_instantiated :
  forall (a b : nat),
  (derivable minimal_F [Var a; Neg (Var a)] (Some (Var b)) -> False) ->
  (derivable minimal_F [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)]
     (Some (Var b)) -> False).
Proof.
  intros a b H1 H2.
  apply H1. apply DNS1_inv_instantiated. assumption.
Qed.

(* The derivation of contradiction needs two axioms that the file
   makes explicit and traceable. The first encodes Tennant's Claim 1
   (Core Logic, p. 156): the antisequent ¬A, A ⊬ B is posited as
   holding in ℂ. The second encodes the structural property of ℱ as a
   fragment shared by 𝐌 and ℂ: any antisequent rule established by
   induction on the rules of ℱ shared by 𝐌 and ℂ belongs to both
   readings. To deny this axiom would amount to claiming that the
   shared rules of ℱ produce consequences in 𝐌 that they do not
   produce in ℂ — which would contradict the very notion of a shared
   fragment. *)

Axiom Claim1_Tennant :
  forall (a b : nat),
  derivable core_logic [Var a; Neg (Var a)] (Some (Var b)) -> False.

Axiom min_antisequent_rule_to_core :
  forall (G G' : set formula) (C C' : option formula),
    ((derivable minimal_F G C -> False) ->
     (derivable minimal_F G' C' -> False)) ->
    ((derivable core_logic G C -> False) ->
     (derivable core_logic G' C' -> False)).

(*   (1) DNS.1-anti, established in minimal_F (§7), is lifted to
         core_logic by the rule-transfer axiom (§8). This yields
         a Core-level antisequent rule
                 ¬A, A ⊬ B  ⇒  ¬A, (A → B) → B ⊬ B.
     (2) The lifted rule is applied to Tennant's Claim 1, yielding
         the fatal antisequent ¬A, (A → B) → B ⊬ B in ℂ.
     (3) DNS.2, derivable in ℂ from the absurdity ¬A, A ⊢ via
         R→ℂ (§5), yields the sequent ¬A, (A → B) → B ⊢ B in ℂ.
     (4) (2) and (3) directly contradict each other, producing
         False.
   Therefore Claim 1 cannot be maintained in ℂ without
   contradiction: if ℂ is consistent, it cannot be
   paraconsistent. ∎  *)

Theorem claim1_false :
  forall (a b : nat), False.
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

(* ── Local note ──
   "assert" introduces the intermediate proposition Hanti_core,
   the Core-lifted DNS.1-anti rule, proved by applying the
   rule-transfer axiom to DNS1_anti_instantiated. The remaining
   three "apply" lines execute steps (2)–(4) of the schema above.
   To verify the axiom budget, add  Print Assumptions claim1_false.
   after the Qed: the output will list exactly Claim1_Tennant and
   min_antisequent_rule_to_core, and nothing else.

  Final theorem: claim1_false : ∀ a b : nat, False.  "Print
   Assumptions claim1_false" returns exactly two axioms: •
   Claim1_Tennant — Tennant's antisequent ¬A, A ⊬ B (Core Logic,
   p. 156).  • min_antisequent_rule_to_core — the transfer of
   antisequent rules from minimal_F to core_logic, i.e.  the
   structural property of ℱ as a fragment shared by 𝐌 and ℂ. *)

(* COROLLARY: Claim 2 — the antisequent ¬A, A ⊬ ¬B — entails exactly the
   same contradiction, by substituting ¬B for B throughout the
   statements and proofs of DNS1_instantiated, DNS2_instantiated,
   R_arrow_inv_NegA_min, DNS1_inv_instantiated,
   DNS1_anti_instantiated, and Claim1_Tennant. The substitution
   is purely textual; the proof scripts are identical modulo this
   renaming. The explicit re-instantiation is omitted. *)

(* ════════════════════════════════════════════════════════════════
   GLOSSARY — Coq 8.18 reference manual
   ════════════════════════════════════════════════════════════════
   The local notes above explain why each tactic is used at the
   point where it appears. For the general behaviour of the
   commands and tactics employed in this file, the reader may
   consult the corresponding sections of the Coq 8.18 reference
   manual:

   Commands
     • Inductive   — declaration of inductive types and their
                     constructors.
                     https://rocq-prover.org/doc/v8.18/refman/
                     language/core/inductive.html
     • Lemma, Theorem, Axiom, Qed
                   — assertion commands and proof termination.
                     https://rocq-prover.org/doc/V8.18.0/refman/
                     language/core/definitions.html
     • Print Assumptions
                   — list the axioms a theorem ultimately depends
                     on.
                     https://rocq-prover.org/doc/V8.18.0/refman/
                     proof-engine/vernacular-commands.html

   Tactics on inductive types and equality
     • induction, discriminate, injection
                   — structural induction, refutation by clashing
                     constructors, extraction of subterm equality.
                     https://rocq-prover.org/doc/V8.18.0/refman/
                     proofs/writing-proofs/reasoning-inductives.html

   General-purpose tactics
     • intros, apply, assert, remember, revert, subst,
       destruct, simpl, reflexivity, left, assumption
                   — basic proof-engine tactics.
                     https://rocq-prover.org/doc/V8.18.0/refman/
                     proof-engine/tactics.html

   Reference manual (entry point)
     • https://rocq-prover.org/doc/v8.18/refman/
   ════════════════════════════════════════════════════════════════ *)
