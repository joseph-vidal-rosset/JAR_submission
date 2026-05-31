/- ════════════════════════════════════════════════════════════════
   Proof in Lean 4 that Core Logic is not Paraconsistent
   ════════════════════════════════════════════════════════════════

   This Lean 4 file certifies the argument according to which
   Tennant's two foundational claims about Core logic ℂ — that ℂ is
   paraconsistent (Claim 1), and that ℂ merely overlaps minimal logic
   𝐌 rather than including it (Claim 2) — cannot be sustained without
   contradiction. The proof is done inside a small fragment ℱ of ℂ,
   using only rules that Tennant himself accepts.

   This file is a port of the Coq script
   `core_logic_is_not_paraconsistent.v`. It uses only core Lean 4
   (no Mathlib dependency).

   ════════════════════════════════════════════════════════════════ -/

/- The language of ℱ is the usual propositional language built from
   atomic variables, negation, and implication. Propositional
   variables are indexed by natural numbers via the constructor
   `Var : Nat → Formula`, providing a countably infinite supply of
   distinct atoms. -/

inductive Formula : Type
  | Var  : Nat → Formula
  | Neg  : Formula → Formula
  | Impl : Formula → Formula → Formula
  deriving DecidableEq, Repr

open Formula

/- ── Local note ──
   The three constructors are distinct by construction. In Lean 4,
   what Coq does with `discriminate` and `injection` is subsumed by
   `cases`, `injection`, and the `injection`/`noConfusion` machinery
   triggered by pattern matching. -/

/- Fragment ℱ contains five rules: Ax., L¬, R→, L→, and the
   Core-specific rule R→ℂ. The first four rules are exactly those of
   minimal logic 𝐌 in fragment ℱ. The fifth, R→ℂ, derives an
   implication from an inconsistent context and is the single rule
   that distinguishes ℂ from 𝐌 in ℱ.

   To represent both readings of ℱ in a single inductive predicate,
   we introduce a fragment indicator `f : FragmentF` taking two
   values, `minimal_F` and `core_logic`. The first five rules
   quantify universally over `f` and therefore exist in both
   readings; the sixth, `R_arrow_core`, fixes `f = core_logic` in
   its signature and is restricted by typing to the Core reading.

   Sequents are encoded with contexts as `List Formula`. An explicit
   `Exchange` constructor is added to permit swapping two adjacent
   formulas in a doubleton context. Right-hand sides are encoded as
   `Option Formula`: `some A` represents a single succedent formula,
   `none` the empty succedent (used in inconsistency sequents Γ ⊢).

   An antisequent Γ ⊬ C is written directly as the type

                Derivable f Γ C → False

   No separate "unprovable" predicate is introduced. -/

inductive FragmentF : Type
  | minimal_F  : FragmentF
  | core_logic : FragmentF
  deriving DecidableEq, Repr

open FragmentF

inductive Derivable : FragmentF → List Formula → Option Formula → Prop
  | Ax           : ∀ {f : FragmentF} {G : List Formula} {A : Formula},
                     A ∈ G →
                     Derivable f G (some A)
  | L_neg        : ∀ {f : FragmentF} {G : List Formula} {A : Formula},
                     Derivable f G (some A) →
                     Derivable f (Neg A :: G) none
  | R_arrow      : ∀ {f : FragmentF} {G : List Formula} {A B : Formula},
                     Derivable f (A :: G) (some B) →
                     Derivable f G (some (Impl A B))
  | L_arrow      : ∀ {f : FragmentF} {G : List Formula} {A B : Formula}
                     {C : Option Formula},
                     Derivable f G (some A) →
                     Derivable f (B :: G) C →
                     Derivable f (Impl A B :: G) C
  | Exchange     : ∀ {f : FragmentF} {x y : Formula} {C : Option Formula},
                     Derivable f [x, y] C →
                     Derivable f [y, x] C
  | R_arrow_core : ∀ {G : List Formula} {A B : Formula},
                     Derivable core_logic (A :: G) none →
                     Derivable core_logic G (some (Impl A B))

/- ── Local note ──
   The signature of `R_arrow_core` is the key typing constraint of
   this file: by fixing `core_logic` in both premiss and conclusion,
   the constructor refuses to exist for `f = minimal_F`. In any
   induction at `f = minimal_F`, the case `R_arrow_core` is therefore
   eliminated by `cases` on the frozen equation `minimal_F = f`. -/

/- Since ℱ shares its first four rules between 𝐌 and ℂ, every
   derivation built in `minimal_F` can be replayed verbatim in
   `core_logic`. The lemma below makes this inclusion mechanically
   explicit. It is the formal expression of ℱ as a shared fragment:
   nothing is imported from outside ℱ when one moves from the minimal
   reading to the Core reading. -/

theorem MinToCore {G : List Formula} {C : Option Formula} :
    Derivable minimal_F G C → Derivable core_logic G C := by
  intro h
  -- Freeze `minimal_F` as a fresh variable `f`, so that the
  -- induction on `h` preserves the information that we started in
  -- the minimal reading. `generalize` plays the role of Coq's
  -- `remember`.
  generalize hf : (minimal_F : FragmentF) = f at h
  induction h with
  | Ax hin              => exact Derivable.Ax hin
  | L_neg _ ih          => exact Derivable.L_neg (ih hf)
  | R_arrow _ ih        => exact Derivable.R_arrow (ih hf)
  | L_arrow _ _ ih1 ih2 => exact Derivable.L_arrow (ih1 hf) (ih2 hf)
  | Exchange _ ih       => exact Derivable.Exchange (ih hf)
  | R_arrow_core _ _    =>
      -- Impossible: this constructor demands `f = core_logic`,
      -- contradicting `hf : minimal_F = f`.
      cases hf

/- ── Local note ──
   `generalize hf : minimal_F = f at h` freezes `minimal_F` as a
   fresh variable `f` together with the equation
   `hf : minimal_F = f`. Without this freezing, the case
   `R_arrow_core` would no longer be discharged. That sixth case is
   closed by `cases hf`, which exploits the impossibility of
   `minimal_F = core_logic` (two distinct constructors of
   `FragmentF`). -/

/- The sequent ¬A, A ⊢ is the left subtree of the final contradiction
   (paper §2.5). It expresses the inconsistency of the context
   {¬A, A} and is derivable by a single application of L¬ preceded by
   an Exchange to bring ¬A into head position. -/

theorem absurdity_core (a : Nat) :
    Derivable core_logic [Var a, Neg (Var a)] none := by
  -- We aim at `[Var a, Neg (Var a)]`. `Exchange` swaps the doubleton,
  -- so we derive `[Neg (Var a), Var a]` first, by `L_neg` from
  -- `[Var a] ⊢ Var a` (the axiom A ∈ {A}).
  exact Derivable.Exchange
          (Derivable.L_neg
            (Derivable.Ax (by simp : Var a ∈ [Var a])))

/- ── Local note ──
   The Exchange step is needed because `L_neg` requires ¬A at the
   head of the context, while the convention adopted in the rest of
   the file places ¬A in second position. The `by simp` discharges
   the membership obligation `Var a ∈ [Var a, Neg (Var a)]`. -/

/- Following Slaney [Slaney 1994], we call DNS (Double Negation
   à la Slaney) two rules central to the argument:

         A, ∆ ⊢ B                          A, ∆ ⊢
     ─────────────────── DNS.1     ─────────────────── DNS.2
     (A → B) → B, ∆ ⊢ B            (A → B) → B, ∆ ⊢ B

   DNS.1 is derivable in 𝐌 using R→ and L→. DNS.2 is derivable in
   ℂ using R→ℂ and L→: it requires the Core-specific rule because
   its premiss has an empty succedent. Both derivations live entirely
   inside ℱ (see paper, Table 2). We instantiate both rules at the
   specific contexts that appear in the final argument, namely
   A = Var a, ∆ = [Neg (Var a)], B = Var b. -/

theorem DNS1_instantiated (a b : Nat) :
    Derivable minimal_F [Var a, Neg (Var a)] (some (Var b)) →
    Derivable minimal_F
      [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
      (some (Var b)) := by
  intro h
  -- L_arrow with A = Impl (Var a) (Var b), B = Var b:
  --   left premiss   : [Neg (Var a)] ⊢ Impl (Var a) (Var b)
  --                    via R_arrow from h
  --   right premiss  : [Var b, Neg (Var a)] ⊢ Var b  via Ax
  exact Derivable.L_arrow
          (Derivable.R_arrow h)
          (Derivable.Ax (by simp : Var b ∈ [Var b, Neg (Var a)]))

/- ── Local note ──
   The script transcribes the derivation of DNS.1 (paper, Table 2)
   from root to top. -/

theorem DNS2_instantiated (a b : Nat) :
    Derivable core_logic [Var a, Neg (Var a)] none →
    Derivable core_logic
      [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
      (some (Var b)) := by
  intro h
  -- Structurally identical to DNS1_instantiated, with R_arrow_core
  -- in place of R_arrow.
  exact Derivable.L_arrow
          (Derivable.R_arrow_core h)
          (Derivable.Ax (by simp : Var b ∈ [Var b, Neg (Var a)]))

/- ── Local note ──
   Structurally identical to `DNS1_instantiated`, except that the
   rule used to derive ∆ ⊢ A → B from A, ∆ ⊢ is `R_arrow_core`.
   This is where the Core-specific rule R→ℂ enters the argument. -/

/- DNS.1 is invertible: from the derivability of its conclusion, the
   derivability of its premiss follows. This is the formal counterpart
   of the syntactic and semantic proofs given in the paper (§2.3).
   The semantic proof, in particular, is independent of any classical
   commitment and applies under the minimal reading of ⊥ as a
   nonlogical constant.

   The mechanisation proceeds in two steps. First, a sub-lemma
   inverts R→ over the singleton context [¬A]. Then the main theorem
   inverts DNS.1 over the doubleton context, generalised over both
   orderings to absorb the `Exchange` constructor. -/

theorem R_arrow_inv_NegA_min (a b : Nat) :
    Derivable minimal_F [Neg (Var a)] (some (Impl (Var a) (Var b))) →
    Derivable minimal_F [Var a, Neg (Var a)] (some (Var b)) := by
  intro h
  -- Freeze the three specific instances so that they survive the
  -- `induction` tactic and remain available for case analysis.
  generalize hf : (minimal_F : FragmentF)                 = f at h
  generalize hG : ([Neg (Var a)] : List Formula)          = G at h
  generalize hC : (some (Impl (Var a) (Var b)) :
                    Option Formula)                       = C at h
  induction h with
  | @Ax f G A hin =>
      -- A ∈ [Neg (Var a)] forces A = Neg (Var a); hC forces
      -- some A = some (Impl (Var a) (Var b)). Two distinct constructors.
      subst hG
      cases hin with
      | head        => cases hC
      | tail _ hin' => cases hin'
  | L_neg _ _ =>
      -- Succedent is `none`, but `hC` demands `some ...`.
      cases hC
  | @R_arrow f G A B _ _ =>
      -- Succedent `some (Impl A B)` matches `hC`; injecting gives
      -- A = Var a, B = Var b; `hG` gives premiss-context
      -- = [Var a, Neg (Var a)] after consing.
      injection hC with hAB
      injection hAB with hA hB
      subst hA; subst hB; subst hG; subst hf
      assumption
  | L_arrow _ _ _ _ =>
      -- Context starts with `Impl ...`, but `hG` demands it starts
      -- with `Neg (Var a)`. Two distinct constructors.
      cases hG
  | @Exchange f x y C' _ _ =>
      -- Context `[y, x]` has length 2; `hG` demands length 1.
      cases hG
  | R_arrow_core _ _ =>
      -- This case demands `f = core_logic`; `hf` demands
      -- `f = minimal_F`.
      cases hf

/- ── Local note ──
   The three `generalize` invocations freeze the three specific
   instances (`minimal_F`, the singleton context, the implication
   succedent) so that they survive the `induction` tactic. Of the
   six branches, only `R_arrow` yields the inverted derivation
   directly; the other five are closed as impossible by case
   analysis on the frozen equations. -/

theorem DNS1_inv_instantiated (a b : Nat) :
    Derivable minimal_F
      [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
      (some (Var b)) →
    Derivable minimal_F [Var a, Neg (Var a)] (some (Var b)) := by
  intro h
  -- The auxiliary lemma is generalised over both orderings of the
  -- doubleton context, so that the `Exchange` case can fire on the
  -- permuted context. The disjunction in `hG` is the formal
  -- counterpart of the symmetry imposed by `Exchange`.
  suffices hgen :
      ∀ {f : FragmentF} {G : List Formula} {C : Option Formula},
        Derivable f G C →
        f = minimal_F →
        (G = [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)] ∨
         G = [Neg (Var a), Impl (Impl (Var a) (Var b)) (Var b)]) →
        C = some (Var b) →
        Derivable minimal_F [Var a, Neg (Var a)] (some (Var b)) by
    exact hgen h rfl (Or.inl rfl) rfl
  intro f G C hD
  induction hD with
  | @Ax f G A hin =>
      -- After subst, A = Var b. Then hin : Var b ∈ G, and G is one of
      -- two two-element lists in which neither member equals Var b.
      -- The Mem type is therefore uninhabited: `nomatch` closes both
      -- sub-goals by no-confusion on the constructors of Formula.
      intro _ hG hC
      injection hC with hC'
      subst hC'
      rcases hG with hG | hG
      · subst hG; nomatch hin
      · subst hG; nomatch hin
  | L_neg _ _ =>
      intro _ _ hC; cases hC
  | @R_arrow f G A B _ ih =>
      -- Succedent some (Impl A B); hC forces some (Impl A B)
      -- = some (Var b). Var b is not an Impl. Contradiction.
      intro _ _ hC
      cases hC
  | @L_arrow f G A B C' hPrem1 hPrem2 ih1 ih2 =>
      -- Context starts with `Impl A B`. Two cases on `hG`.
      intro hf hG hC
      rcases hG with hG | hG
      · -- G = [Impl ((Var a → Var b) → Var b), Neg (Var a)]
        -- After consing on the head, we read off:
        --   A = Var a → Var b,  B = Var b,  rest = [Neg (Var a)]
        injection hG with hAB hRest
        injection hAB with hA hB
        subst hA; subst hB; subst hRest; subst hC
        -- Premisses:
        --   hPrem1 : [Neg (Var a)] ⊢ some (Var a → Var b)
        --   hPrem2 : [Var b, Neg (Var a)] ⊢ some (Var b)
        -- Apply R_arrow_inv_NegA_min to hPrem1 (after using hf to know
        -- we are at f = minimal_F).
        subst hf
        exact R_arrow_inv_NegA_min a b hPrem1
      · -- G = [Neg (Var a), Impl ((Var a → Var b) → Var b)]
        -- But the L_arrow conclusion has Impl at the head.
        injection hG with hHead _
        cases hHead
  | @Exchange f x y C' _ ih =>
      -- Conclusion-context is `[y, x]`. The two cases on `hG`
      -- correspond to swapping which element is which; in each, the
      -- IH applies to the other ordering.
      intro hf hG hC
      rcases hG with hG | hG
      · -- [y, x] = [Impl ..., Neg (Var a)]  ⇒  y = Impl..., x = Neg...
        -- The premiss has context [x, y] = [Neg..., Impl...], which
        -- is the second disjunct. IH applies.
        injection hG with hy hx_tail
        injection hx_tail with hx _
        subst hy; subst hx
        exact ih hf (Or.inr rfl) hC
      · -- [y, x] = [Neg (Var a), Impl ...]  ⇒  y = Neg..., x = Impl...
        -- Premiss context [x, y] = [Impl..., Neg...] is the first
        -- disjunct.
        injection hG with hy hx_tail
        injection hx_tail with hx _
        subst hy; subst hx
        exact ih hf (Or.inl rfl) hC
  | R_arrow_core _ _ =>
      intro hf _ _; cases hf

/- ── Local note ──
   The auxiliary lemma `hgen` is generalised over both orderings of
   the doubleton context. This generalisation is needed because the
   `Exchange` case yields a derivation on the permuted context: only
   a disjunction in `hG` allows the IH to apply to either ordering. -/

/- The invertibility of DNS.1 means that conclusion-derivability
   entails premiss-derivability. Contraposing: premiss-non-
   derivability entails conclusion-non-derivability. This is exactly
   the antisequent form of DNS.1:

               A, ∆ ⊬ B
      ──────────────────── DNS.1-anti
      (A → B) → B, ∆ ⊬ B

   Note that, pace Tennant, antisequents are encoded as sequents
   implying False, to avoid coding "unprovable" as a primitive. -/

theorem DNS1_anti_instantiated {a b : Nat} :
    (Derivable minimal_F [Var a, Neg (Var a)] (some (Var b)) → False) →
    (Derivable minimal_F
       [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
       (some (Var b)) → False) := by
  intro h1 h2
  exact h1 (DNS1_inv_instantiated a b h2)

/- The derivation of contradiction needs two axioms that the file
   makes explicit and traceable. The first encodes Tennant's Claim 1
   (Core Logic, p. 156): the antisequent ¬A, A ⊬ B is posited as
   holding in ℂ. The second encodes the structural property of ℱ as
   a fragment shared by 𝐌 and ℂ: any antisequent rule established by
   induction on the rules of ℱ shared by 𝐌 and ℂ belongs to both
   readings. To deny this axiom would amount to claiming that the
   shared rules of ℱ produce consequences in 𝐌 that they do not
   produce in ℂ — which would contradict the very notion of a shared
   fragment. -/

axiom Claim1_Tennant :
  ∀ (a b : Nat),
    Derivable core_logic [Var a, Neg (Var a)] (some (Var b)) → False

axiom min_antisequent_rule_to_core :
  ∀ (G G' : List Formula) (C C' : Option Formula),
    ((Derivable minimal_F G C → False) →
     (Derivable minimal_F G' C' → False)) →
    ((Derivable core_logic G C → False) →
     (Derivable core_logic G' C' → False))

/-  (1) DNS.1-anti, established in `minimal_F` (`DNS1_anti_instantiated`),
        is lifted to `core_logic` by the rule-transfer axiom
        (`min_antisequent_rule_to_core`). This yields
        a Core-level antisequent rule
                  ¬A, A ⊬ B  ⇒  ¬A, (A → B) → B ⊬ B.
    (2) The lifted rule is applied to Tennant's Claim 1, yielding
        the fatal antisequent ¬A, (A → B) → B ⊬ B in ℂ.
    (3) DNS.2 (`DNS2_instantiated`), derivable in ℂ from the absurdity
        ¬A, A ⊢ via R→ℂ, yields ¬A, (A → B) → B ⊢ B in ℂ.
    (4) (2) and (3) directly contradict each other, producing
        False.
    Therefore Claim 1 cannot be maintained in ℂ without
    contradiction: if ℂ is consistent, it cannot be paraconsistent. ∎ -/

set_option linter.unusedVariables false in
theorem claim1_false : ∀ (a b : Nat), False := by
  intro a b
  -- Lift DNS.1-anti from minimal_F to core_logic.
  have Hanti_core :
      (Derivable core_logic [Var a, Neg (Var a)] (some (Var b)) → False) →
      (Derivable core_logic
         [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
         (some (Var b)) → False) :=
    min_antisequent_rule_to_core _ _ _ _ DNS1_anti_instantiated
  -- Apply the lifted rule to Tennant's Claim 1 to obtain the fatal
  -- antisequent, then collide with DNS.2 applied to the Core absurdity.
  exact Hanti_core (Claim1_Tennant a b)
                   (DNS2_instantiated a b (absurdity_core a))

/- ── Local note ──
   `have` introduces the intermediate proposition `Hanti_core`, the
   Core-lifted DNS.1-anti rule, proved by applying the rule-transfer
   axiom to `DNS1_anti_instantiated`. The final term executes steps
   (2)–(4) of the schema above.

   To verify the axiom budget, run `#print axioms claim1_false` after
   this theorem: the output lists exactly `Claim1_Tennant` and
   `min_antisequent_rule_to_core`, and nothing else (plus Lean's
   built-in `propext`, `Classical.choice`, `Quot.sound` only if any
   of the proofs above secretly used them — they do not). -/

#print axioms claim1_false

/- COROLLARY: Claim 2 — the antisequent ¬A, A ⊬ ¬B — entails exactly
   the same contradiction, by substituting ¬B for B throughout the
   statements and proofs of `DNS1_instantiated`, `DNS2_instantiated`,
   `R_arrow_inv_NegA_min`, `DNS1_inv_instantiated`,
   `DNS1_anti_instantiated`, and `Claim1_Tennant`. The substitution
   is purely textual; the proof scripts are identical modulo this
   renaming. The explicit re-instantiation is omitted. -/

/- ════════════════════════════════════════════════════════════════
   GLOSSARY — Lean 4 documentation pointers
   ════════════════════════════════════════════════════════════════

   Commands
     • `inductive`   — declaration of inductive types and their
                       constructors.
                       https://leanprover.github.io/theorem_proving_in_lean4/
                       inductive_types.html
     • `theorem`, `axiom`
                     — assertion commands.
                       https://leanprover.github.io/theorem_proving_in_lean4/
                       propositions_and_proofs.html
     • `#print axioms`
                     — list the axioms a theorem ultimately depends
                       on.
                       https://leanprover-community.github.io/mathlib4_docs/

   Tactics on inductive types and equality
     • `induction`, `cases`, `injection`, `rcases`, `subst`
                     — structural induction, case analysis,
                       extraction of subterm equality.
                       https://leanprover.github.io/theorem_proving_in_lean4/
                       tactics.html

   Generalisation
     • `generalize`  — counterpart of Coq's `remember`; freezes a
                       term as a fresh variable plus an equation.

   Reference (entry point)
     • https://leanprover.github.io/theorem_proving_in_lean4/
   ════════════════════════════════════════════════════════════════ -/
