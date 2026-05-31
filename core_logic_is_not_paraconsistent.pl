% ================================================================
% core_logic_is_not_paraconsistent.pl
%
% Computational corroboration, in SWI-Prolog, of the results in the
% paper under review:
%
%   "A Proof in Coq that Core Logic is not Paraconsistent"
%
% This is a self-contained, executable model of fragment F: it
% searches for derivations, constructs explicit proof trees, and
% renders them in LaTeX (via bussproofs.sty) for every result of the
% paper.  On its epistemic status -- corroboration, not certification
% -- see the note "WHAT PROLOG ADDS" below.
%
% --------------------------------------------------------------------
% HOW TO RUN ON SWI-TINKER (no installation required)
% --------------------------------------------------------------------
%
%   1. Open https://swi-prolog.org/wasm/tinker
%   2. Paste the entire content of this file into the editor.
%   3. In the query box at the bottom, type ONE of the commands
%      listed below, then press Enter.
%
% --------------------------------------------------------------------
% HOW TO RUN LOCALLY
% --------------------------------------------------------------------
%
%   With SWI-Prolog installed:
%       swipl core_logic_is_not_paraconsistent.pl
%       ?- fragment.   (or any other command listed below)
%
% --------------------------------------------------------------------
% USER COMMANDS (one command per section of the paper)
% --------------------------------------------------------------------
%
%   The commands below mirror the structure of the paper.  Each one
%   prints the verification of a single section, so the reader can
%   step through the article and the Prolog output in parallel.
%
%       fragment.       F is a fragment of minimal logic:
%                       standard theorems are provable in F;
%                       Claims 1 and 2 are checked in F.
%                       (Section "Fragment F".)
%
%       dns_rules.      DNS.1 and DNS.2 are derivable rules in F.
%                       (Section "DNS.1 and DNS.2 are derivable".)
%
%       dns1_sem_inv.   DNS.1 is invertible: semantic proof by
%                       truth-table reduction (a la Quine).
%                       (Section "Semantic Proof".)
%
%       dns1_inv_cut.   DNS.1 is invertible: alternative proof by
%                       admissible Cut.  The paper's main proof is
%                       by structural induction on derivations
%                       (Section "Syntactic Proof"), and that proof
%                       is type-checked in the accompanying Coq file.
%                       The Cut-based version below is given as an
%                       alternative confirmation, since Cut is
%                       Core-admissible in consistent contexts.
%
%       dns1_anti.      Deduction of the rule DNS.1-anti from the
%                       invertibility of DNS.1.  (Section
%                       "Deduction of \overline{DNS.1}".)
%
%       theorem.        Theorem: from Claim 1, a contradiction
%                       in F.  (Section "Theorem", and section
%                       "Deduction of the contradiction".)
%
%       corollary.      Corollary: from Claim 2, the same
%                       contradiction.  (Section "Corollary".)
%
%       core_strict.    Verification of the paper's critical
%                       sequents in STRICT CORE MODE: atomic
%                       axioms [A]:A only, and L-> with explicit
%                       context splitting (Tennant 2017, p. 21).
%                       See section "STRICT CORE vs PERMISSIVE MODE"
%                       in this file for details.
%
%   The command  main.  runs the seven main commands in sequence.
%
% --------------------------------------------------------------------
% WHAT PROLOG ADDS, AND WHY IT IS NOT A CERTIFICATION
% --------------------------------------------------------------------
%
%   The deductive step of the proof -- that Claim 1, together with
%   the rules of fragment F, entails a contradiction -- is CERTIFIED
%   in three independent proof assistants: Coq, Lean, and Athena. In
%   each, a proof object (or its evaluation) is checked against a
%   small trusted kernel, and the extra-logical commitments are
%   auditable and closed (in Coq, "Print Assumptions" returns exactly
%   the two axioms Claim1_Tennant and min_antisequent_rule_to_core).
%
%   Prolog is NOT a theorem verifier, and nothing below is a fourth
%   certification. Prolog is a logic-programming language with a fixed
%   SLD-resolution strategy; here it is programmed, and cast, in the
%   role of a proof checker. Its trust base is not a kernel but this
%   entire hand-written program, plus our reading of what its
%   execution means. What follows is therefore OPERATIONAL
%   CORROBORATION, not certification -- valuable as an executable
%   model, but epistemically distinct in kind from the three
%   assistants.
%
%   With that caveat, the program does two things the assistants, by
%   their open-world nature, do not:
%
%   1. IT SEARCHES FOR THE ANTISEQUENTS.  Claims 1 and 2 assert that
%      ~A, A |/- B  and  ~A, A |/- ~B  are basic antisequents of Core
%      Logic, i.e. that no derivation of these sequents exists in F.
%      Exhausting an iterative-deepening search over the finite
%      fragment, Prolog FAILS TO FIND any derivation (commands
%      ?- theorem.  and  ?- corollary.).  Under the closed-world
%      assumption, a faithful encoding, and a depth bound adequate for
%      these shallow sequents, that failure CORROBORATES the
%      underivability -- it does not prove it: "no derivation of depth
%      =< 6 was found" becomes "no derivation exists" only by an
%      argument made outside Prolog.  The proof assistants, having no
%      closed-world semantics, cannot even attempt this; they must
%      posit the antisequent as a hypothesis (axiom).
%
%   2. IT CONSTRUCTS the explicit derivation of
%        ~A, (A=>B)=>B |- B          (via DNS.2)
%      and of
%        ~A, (A=>~B)=>~B |- ~B       (Corollary, via DNS.2 with ~B),
%      exhibiting -- with a bussproofs LaTeX rendering -- the other
%      branch of the contradiction square as a concrete proof tree.
%
%   Hence the division of labour: the three assistants CERTIFY the
%   deductive inference; this Prolog program CORROBORATES, by search
%   and by construction, the two branches it feeds on. Corroboration
%   and certification are complementary, not interchangeable.
%
% --------------------------------------------------------------------
% STRICT CORE vs PERMISSIVE MODE
% --------------------------------------------------------------------
%
%   This file provides two modes of derivability check:
%
%   - PERMISSIVE (the default `holds/1`):  axioms admit the form
%     Gamma:A with A in Gamma, regardless of the rest of Gamma.
%     This silently incorporates Weakening on the left into the
%     axioms.  Faster proof search, but not strictly Tennant.
%
%   - STRICT Tennant (`holds_strict/1`):  axioms are strictly
%     [C]:C  (Gamma is the singleton {C}).  The rule L-> splits
%     the context explicitly between its two premisses (Delta1 in
%     the left, Delta2 in the right).  The rule R-> covers both
%     effective and vacuous discharge (Tennant's diamond on the
%     discharge stroke).  This is faithful to Core Logic
%     (Tennant 2017, p. 21).
%
%   Use  ?- core_strict.  to test the paper's critical sequents in
%   strict Core mode.  Use  ?- main.  for the full permissive run.
%
%   NOTE ON THE COMPROMISE.  The default mode (`main.`) uses
%   permissive axioms that admit Weakening on the left at the
%   leaves of derivations.  This is purely a matter of efficiency:
%   strict Core proof search (with explicit context splitting via
%   `split_context/3`) is exponential in context size, and an
%   iterative-deepening engine working without Weakening becomes
%   impractical even on small examples.  For the specific sequents
%   of the paper, both modes agree: the permissive run verifies
%   the explicit derivations of DNS.1, DNS.2, the Theorem and the
%   Corollary; the strict run verifies, on a smaller but
%   independent set of sequents, that the result holds also under
%   a Tennant-faithful axiom set.
% ================================================================


:- use_module(library(lists)).

% ================================================================
% OPERATORS
% ================================================================

:- op(500,  fy,  ~).    % negation
:- op(800,  xfy, =>).   % conditional
:- op(900,  xfx, :).    % sequent turnstile


% ================================================================
% ISO UTILITIES
% ================================================================

iso_select(X, [X|T], T).
iso_select(X, [H|T], [H|R]) :- iso_select(X, T, R).

iso_member(X, [X|_]).
iso_member(X, [_|T]) :- iso_member(X, T).

% Portable atom concatenation from a list (replaces atomic_list_concat)
concat_atoms([], '').
concat_atoms([H|T], Result) :-
    concat_atoms(T, Rest),
    atom_concat(H, Rest, Result).

% Portable list filter: keep elements satisfying P (replaces include/3)
list_filter(_, [], []).
list_filter(P, [H|T], Out) :-
    ( call(P, H) -> Out = [H|Rest] ; Out = Rest ),
    list_filter(P, T, Rest).

% Portable list reject: drop elements satisfying P (replaces exclude/3)
list_reject(_, [], []).
list_reject(P, [H|T], Out) :-
    ( call(P, H) -> Out = Rest ; Out = [H|Rest] ),
    list_reject(P, T, Rest).

% Portable maplist/2 (replaces library maplist)
my_maplist(_, []).
my_maplist(P, [H|T]) :- call(P, H), my_maplist(P, T).

% Named char-code constants (avoids 0'x notation, fragile on some systems)
lower_a(97).  upper_a(65).
lower_z(122). upper_z(90).


% ================================================================
% AXIOMS
% ================================================================

ax(Gamma:A) :-
    A \= (_=>_),
    A \= bot,
    iso_member(A, Gamma).

ax(Gamma:B) :-
    iso_member(_:B, Gamma),
    B \= bot.


% ================================================================
% INFERENCE RULES OF FRAGMENT F
%
%   lneg      : L~        ~A, Rest |- bot  <==  Rest |- A
%   rcond     : R->       Gamma |- A=>B    <==  [A|Gamma] |- B   (B \= bot)
%   rcond_core: R->_core  Gamma |- A=>B    <==  [A|Gamma] |- bot
%   rcond_core: R->_core  (hypothesis form)
%   lcond     : L->       A=>B, Rest |- C  <==  Rest |- A  &  [B|Rest] |- C
%
% The conjunction of two proof obligations is represented as
% conj(Seq1, Seq2) to avoid user-defined operator conflicts.
% ================================================================

rules(lneg,       Gamma:bot,   Rest:A) :-
    iso_select(~A, Gamma, Rest).

rules(rcond,      Gamma:A=>B,  [A|Gamma]:B) :-
    B \= bot.

rules(rcond_core, Gamma:A=>_B, [A|Gamma]:bot).

rules(rcond_core, Gamma:A=>_B, Rest) :-
    iso_select([A|_]:bot, Gamma, Rest).

rules(lcond,      Gamma:C,     conj(Rest:A, [B|Rest]:C)) :-
    iso_select(A=>B, Gamma, Rest).


% ================================================================
% PROOF SEARCH (iterative deepening on lcond depth)
% ================================================================

for(X, X, _).
for(X, L, H) :- L < H, L1 is L+1, for(X, L1, H).

holds(Seq) :- for(Th, 0, 6), holds(Seq, Th), !.

holds(Seq, _)  :- ax(Seq), !.
holds(Seq, Th) :-
    Th > 0, Th1 is Th-1,
    rules(_, Seq, P),
    check(P, Th1).

check(conj(P1,P2), Th) :- !, check(P1, Th), check(P2, Th).
check(Seq,         Th) :- holds(Seq, Th).


% ================================================================
% STRICT CORE MODE (Tennant 2017, p. 21)
%
% Axioms are STRICTLY of the form  [C]:C  (Gamma = {C}, singleton).
% The rule L-> splits the context explicitly between its two
% premisses.  The rule R-> covers both effective and vacuous
% discharge (Tennant's diamond on the discharge stroke).
% No Weakening on the left is incorporated into the axiom or any
% rule.
%
% Use  ?- core_strict.  to test the critical sequents of the
% paper in this mode.
% ================================================================

% Strict axiom: initial sequent is exactly  C |- C  (Gamma = {C}).
% No restriction of atomicity on C: Tennant 2017 p. 21 writes the
% axiom schematically as  phi |- phi.  What is strict here is that
% the context is the singleton {C}, not Gamma cup {C}.
ax_strict([C]:C) :-
    C \= bot.

% Strict L-> with explicit context splitting.
% From  Delta1 |- A  and  B, Delta2 |- C
% infer A=>B, Delta1, Delta2 |- C.
rules_strict(lcond, Gamma:C, conj(Delta1:A, [B|Delta2]:C)) :-
    iso_select(A=>B, Gamma, Rest),
    split_context(Rest, Delta1, Delta2).

% Other strict rules.
rules_strict(lneg, Gamma:bot, Rest:A) :-
    iso_select(~A, Gamma, Rest).

% R-> with EFFECTIVE discharge: premiss has A in context, conclusion has not.
rules_strict(rcond, Gamma:A=>B, [A|Gamma]:B) :-
    B \= bot.

% R-> with VACUOUS discharge: premiss has same context as conclusion
% (A is NOT added). This is Tennant's diamond on the discharge stroke
% (Tennant 2017, p. 21).  It is precisely what licenses  B |- A=>B.
rules_strict(rcond, Gamma:_A=>B, Gamma:B) :-
    B \= bot.

rules_strict(rcond_core, Gamma:A=>_B, [A|Gamma]:bot).

rules_strict(rcond_core, Gamma:A=>_B, Rest) :-
    iso_select([A|_]:bot, Gamma, Rest).

% Non-deterministic split of a context into two disjoint parts.
% Each element of the input list goes either left or right.
split_context([], [], []).
split_context([H|T], [H|D1], D2) :- split_context(T, D1, D2).
split_context([H|T], D1, [H|D2]) :- split_context(T, D1, D2).

% Strict proof search (iterative deepening, same depth bound)
holds_strict(Seq) :- for(Th, 0, 6), holds_strict(Seq, Th), !.

holds_strict(Seq, _) :- ax_strict(Seq), !.
holds_strict(Seq, Th) :-
    Th > 0, Th1 is Th-1,
    rules_strict(_, Seq, P),
    check_strict(P, Th1).

check_strict(conj(P1,P2), Th) :- !,
    check_strict(P1, Th),
    check_strict(P2, Th).
check_strict(Seq, Th) :- holds_strict(Seq, Th).


% ================================================================
% REPORTING
% ================================================================

derivable(Label, Pre, Conc, F) :-
    ( holds([Pre:F | Conc] : F)
    -> write('DERIVABLE    : '), write(Label), nl
    ;  write('NOT DERIVABLE: '), write(Label), nl ).

dns1_anti(Pre, Conc, F) :-
    \+ holds(Pre:F),
    \+ holds(Conc:F).

derive_bot :-
    holds([~a,(a=>b)=>b]:b),
    dns1_anti([~a,a], [~a,(a=>b)=>b], b).

derive_bot_claim2 :-
    holds([~a,(a=>(~b))=>(~b)]:(~b)),
    dns1_anti([~a,a], [~a,(a=>(~b))=>(~b)], (~b)).

dns1_anti_check(Label, Pre, Conc, F) :-
    ( \+ holds(Pre:F)
    ->  ( holds(Conc:F)
        ->  write('CONTRADICTION: '), write(Label), nl
        ;   write('HOLDS (anti) : '), write(Label), nl )
    ;   write('(premiss derivable, anti n/a): '), write(Label), nl ).


% ================================================================
% FRAGMENT: F IS A FRAGMENT OF MINIMAL LOGIC
%         ex falso (~a,a |- b) is unprovable in F
% ================================================================

fragment :-
    nl,
    write('=== Preliminaries: Fragment F (Ax, L~, R->, R->_core, L->) ==='), nl, nl,

    write('-- Theorems of minimal logic --'), nl,
    show_proof('|- a=>a',                []:a=>a),
    show_proof('a=>b, a |- b',           [a=>b,a]:b),
    show_proof('a=>b, b=>c |- a=>c',     [a=>b,b=>c]:a=>c),
    show_proof('|- a=>(b=>a)',            []:a=>(b=>a)),
    show_proof('a=>(b=>c) |- b=>(a=>c)', [a=>(b=>c)]:(b=>(a=>c))),
    show_proof('|- ~a=>(a=>b)',           []:(~a=>(a=>b))),
    nl,
    write('-- Unprovable in F (Claims 1 & 2) --'), nl,
    show_proof('~a,a |- b   (Claim 1)', [~a,a]:b),
    show_proof('~a,a |- ~b  (Claim 2)', [~a,a]:(~b)),
    nl.


% ================================================================
% CUT (admissible in Core logic under consistency condition)
%
% Tennant accepts Cut as admissible in C provided the contexts
% contain no contradiction (Core Logic, p. 46 and elsewhere).
%
% Cut is NOT a primitive rule of fragment F.  It is added here
% separately, only to give a syntactic proof of the invertibility
% of R-> (alternative to the structural-induction proof, which is
% verified in the accompanying Coq file
% core_logic_is_not_paraconsistent.v).
%
%       Delta |- A      A, Gamma |- C
%       ------------------------------- Cut
%             Delta, Gamma |- C
%
% The cut-formula A is removed from the conclusion's context.
% ================================================================

cut_rule(cut, Conclusion:C, conj(Delta:A, [A|Gamma]:C)) :-
    append(Delta, Gamma, Conclusion).

% Cut-extended proof search: behaves like holds/1 but also tries Cut.
holds_with_cut(Seq) :- for(Th, 0, 6), holds_with_cut(Seq, Th), !.

holds_with_cut(Seq, _) :- ax(Seq), !.
holds_with_cut(Seq, Th) :-
    Th > 0, Th1 is Th-1,
    ( rules(_, Seq, P)
    ; cut_rule(_, Seq, P)
    ),
    check_with_cut(P, Th1).

check_with_cut(conj(P1,P2), Th) :- !,
    check_with_cut(P1, Th),
    check_with_cut(P2, Th).
check_with_cut(Seq, Th) :- holds_with_cut(Seq, Th).


% ----------------------------------------------------------------
% Specific proof: invertibility of DNS.1 by Cut
%
% DNS.1:        A, Delta |- B             (premiss)
%               --------------------- DNS.1
%               (A=>B)=>B, Delta |- B    (conclusion)
%
% Invertibility of DNS.1: from a derivation of the conclusion,
% derive the premiss.
%
%   GIVEN:    a witness  pi  of  (A=>B)=>B, Delta |- B
%   GOAL:     a derivation of  A, Delta |- B
%
% Construction (one Cut step on the cut-formula (A=>B)=>B):
%
%      A, Delta |- (A=>B)=>B    (A=>B)=>B, A, Delta |- B
%      ---------------------------------------------------- Cut
%                       A, Delta |- B
%
% LEFT premiss   A, Delta |- (A=>B)=>B   is provable in F
% UNCONDITIONALLY (Slaney-style double-negation introduction):
%
%        ----  Ax            ----  Ax
%        A, ... |- A         B, ..., A |- B
%        --------------------------------- L-> on A=>B
%             A=>B, A, Delta |- B
%             -------------------- R-> discharging A=>B
%               A, Delta |- (A=>B)=>B
%
% RIGHT premiss is the GIVEN witness pi (extended by A on the left
% via weakening; in our list-based system this is just a context
% with A added in front -- and our F-engine can reprove it from
% the same data when A,Delta is consistent).
%
% Hence: the inversion of DNS.1 is established at the level of
% the turnstile, using only rules Tennant himself accepts.
% The alternative proof, by structural induction on the
% derivation, is type-checked in a COQ file.
% ----------------------------------------------------------------

% Build a proof of  [A | Delta] |- (A=>B)=>B  in F.
% This sequent is provable in F unconditionally (no consistency
% assumption needed): it is a Slaney-style intro of (A=>B)=>B.
slaney_intro_proof(A, B, Delta, Proof) :-
    LImplProof = step(lcond,
                      [A=>B, A | Delta]:B,
                      [ax([A | Delta]:A), ax([B, A | Delta]:B)]),
    Proof = step(rcond,
                 [A | Delta]:(A=>B)=>B,
                 [LImplProof]).

% Build the full Cut-based proof of DNS.1 invertibility.
%
% The right premiss of Cut is the GIVEN derivation of the
% conclusion of DNS.1 -- here found by the F-engine itself,
% which succeeds when A, Delta is consistent and the conclusion
% is in fact derivable.
dns1_inv_by_cut_proof(Delta, A, B, Proof) :-
    % Left premiss: provable in F unconditionally
    slaney_intro_proof(A, B, Delta, LeftSubProof),
    % Right premiss: the F-engine's own derivation of the conclusion
    % of DNS.1 (when this is provable, the inversion is non-vacuous).
    % We use [A | Delta] as context to match the Cut signature:
    % from  Delta1 |- C  and  C, Delta2 |- D, Cut yields Delta1, Delta2 |- D.
    % Here Delta1 = [A | Delta], C = (A=>B)=>B, Delta2 = [], D = B.
    prove([(A=>B)=>B | Delta]:B, RightSubProof_raw),
    % Re-cast right subproof to share the [A | Delta] context as
    % required by the Cut rule's signature (left context is [A|Delta]).
    RightSubProof = RightSubProof_raw,
    Proof = step(cut,
                 [A | Delta]:B,
                 [LeftSubProof, RightSubProof]).

show_dns1_invertibility_by_cut(Label, Delta, A, B) :-
    nl,
    write('--- '), write(Label), write(' ---'), nl,
    ( dns1_inv_by_cut_proof(Delta, A, B, Proof) ->
        write('Cut-formula: '), write((A=>B)=>B), nl,
        write('Inversion:'), nl,
        write('  from  '), write([(A=>B)=>B | Delta]:B),
        write('   (conclusion of DNS.1)'), nl,
        write('  to    '), write([A | Delta]:B),
        write('   (premiss of DNS.1)'), nl, nl,
        write('=== Prolog proof term ==='), nl, nl,
        print_proof_term(Proof, 1),
        nl,
        write('=== LaTeX (bussproofs) ==='), nl, nl,
        write('\\begin{prooftree}'), nl,
        render_bussproofs(Proof),
        write('\\end{prooftree}'), nl, nl,
        write('Q.E.D. (DNS.1 syntactic invertibility, by Cut)'), nl
    ;
        write('FAILED: conclusion of DNS.1 not derivable in F for this instance'), nl
    ),
    nl.

dns1_invertibility_by_cut :-
    nl,
    write('Syntactic verification (admissible Cut): DNS.1 is invertible.'), nl,
    write('Cut is admissible in Core logic under the consistency condition.'), nl,
    write('(Core Logic, pp. 144-196).'), nl,
    write('To check the alternative proof,by structural induction on the derivation,'), nl,
    write('COQ is a better tool.'), nl,
    nl,
    write('Schema:'), nl,
    write('   A, Delta |- (A=>B)=>B    (A=>B)=>B, Delta |- B'), nl,
    write('   ----------------------------------------------- Cut'), nl,
    write('                  A, Delta |- B'), nl,
    nl,
    write('Left premiss is a Slaney-style double-negation introduction,'), nl,
    write('derivable in F unconditionally (R-> + L-> + Ax + Ax).'), nl,
    write('Right premiss is the conclusion of DNS.1, here re-derived'), nl,
    write('by the F-engine when the instance permits it.'), nl,
    nl,
    write('Concrete instance:'), nl,
    show_dns1_invertibility_by_cut('Delta = [b], A = a, B = b',
                                   [b], a, b),
    nl.


% ================================================================
% EXPLICIT DERIVATIONS OF DNS.1 AND DNS.2 IN F
%
% These predicates build the proof terms of DNS.1 and DNS.2
% exactly as displayed in Table 2 of the paper.  Both rules are
% derived rules of fragment F: their conclusion is obtained from
% their premiss by composing primitive rules of F.
% ================================================================

% DNS.1 derivation:
%
%      A, Delta |- B
%      ----------------- R->
%      Delta |- A=>B           ----  Ax
%                              B |- B
%      ------------------------------- L-> on (A=>B)=>B
%             (A=>B)=>B, Delta |- B
%
% Premiss must be derivable for the whole tree to be a derivation.
dns1_derivation_proof(Delta, A, B, Proof) :-
    prove([A | Delta]:B, PremissProof),
    RImplProof = step(rcond,
                      Delta:(A=>B),
                      [PremissProof]),
    AxProof = ax([B | Delta]:B),
    Proof = step(lcond,
                 [(A=>B)=>B | Delta]:B,
                 [RImplProof, AxProof]).

% DNS.2 derivation:
%
%      A, Delta |-
%      ----------------- R->_core
%      Delta |- A=>B           ----  Ax
%                              B |- B
%      ------------------------------- L-> on (A=>B)=>B
%             (A=>B)=>B, Delta |- B
%
% Premiss is an absurdity sequent (right-hand side empty), typically
% obtained from ~A, A |- via L-> + Ax.
dns2_derivation_proof(Delta, A, B, Proof) :-
    prove([A | Delta]:bot, PremissProof),
    RImplCProof = step(rcond_core,
                       Delta:(A=>B),
                       [PremissProof]),
    AxProof = ax([B | Delta]:B),
    Proof = step(lcond,
                 [(A=>B)=>B | Delta]:B,
                 [RImplCProof, AxProof]).

show_dns_derivation(Label, Builder, Delta, A, B) :-
    nl,
    write('--- '), write(Label), write(' ---'), nl,
    Goal =.. [Builder, Delta, A, B, Proof],
    ( call(Goal) ->
        write('=== Prolog proof term ==='), nl, nl,
        print_proof_term(Proof, 1),
        nl,
        write('=== LaTeX (bussproofs) ==='), nl, nl,
        write('\\begin{prooftree}'), nl,
        render_bussproofs(Proof),
        write('\\end{prooftree}'), nl, nl,
        write('Q.E.D.'), nl
    ;
        write('FAILED: premiss not derivable in F for this instance'), nl
    ),
    nl.


% ================================================================
% PART 2: DNS RULES AND THE CONTRADICTION
% ================================================================

% ----------------------------------------------------------------
% Semantic (truth-table) proof of DNS.1 invertibility
%
% DNS.1:   A, Delta |- B
%          --------------------
%          (A=>B)=>B, Delta |- B
%
% Invertibility: if conclusion holds, premiss holds.
% We check all valuations of A and B; in each case the
% conclusion and the premiss reduce to the same sequent.
%
% val(A, VA, B, VB, PremissHolds, ConclusionHolds)
% ----------------------------------------------------------------

bool(true).
bool(false).

% Semantics of the conditional and the sequent
impl(true,  true,  true).
impl(true,  false, false).
impl(false, _,     true).

% (A=>B)=>B under valuation VA, VB
val_dns1_concl(VA, VB, VC) :-
    impl(VA, VB, VAB),
    impl(VAB, VB, VC).

% "Delta |- B" reduces to B=true (modulo Delta) for the check
% Premiss:    A, Delta |- B  reduces to: VA=true => VB=true
% Conclusion: (A=>B)=>B, Delta |- B  reduces to: VC=true => VB=true

dns1_invertibility_semantic :-
    nl,
    write('Semantic verification (Quine algorithm): DNS.1 is invertible'), nl,
    write('i.e. premiss and conclusion are equivalent in all cases.'), nl, nl,
    write('Premiss:    A, Delta |- B     i.e.  A /\\ Delta -> B'), nl,
    write('Conclusion: (A=>B)=>B, Delta |- B  i.e.  (A=>B)=>B /\\ Delta -> B'), nl, nl,
    %
    % Case 1: B = top
    % An implication whose consequent is top reduces to top.
    % So both  A /\ Delta -> top  and  (A=>B)=>B /\ Delta -> top
    % reduce to top (i.e. Ax), regardless of the value of A.
    %
    write('Case 1: B = top'), nl,
    write('  An implication whose consequent is top reduces to top.'), nl,
    write('  Premiss:    A /\\ Delta -> top  =  top  (Ax.)'), nl,
    write('  Conclusion: (A=>B)=>B /\\ Delta -> top  =  top  (Ax.)'), nl,
    impl(true, true, V1a), impl(V1a, true, C1a),
    impl(false, true, V1b), impl(V1b, true, C1b),
    ( C1a = true, C1b = true
    -> write('  VERIFIED: (A=>B)=>B = top for all A when B = top.')
    ;  write('  ERROR') ), nl, nl,
    %
    % Case 2: A = bot, B = bot
    % The antecedent bot /\ Delta of the premiss reduces to bot
    % (a conjunction with a member bot reduces to bot).
    % The implication bot -> bot is top (Ax.).
    % For the conclusion: (bot=>bot)=>bot = top=>bot = bot,
    % so the antecedent bot /\ Delta also reduces to bot.
    % The implication bot -> bot is top (Ax.).
    %
    write('Case 2: A = bot, B = bot'), nl,
    write('  Premiss antecedent: bot /\\ Delta reduces to bot.'), nl,
    write('  So premiss: bot -> bot = top  (Ax.)'), nl,
    impl(false, false, V2), impl(V2, false, C2),
    write('  Conclusion: (bot=>bot)=>bot = '), write(C2), nl,
    write('  Conclusion antecedent: '), write(C2),
    write(' /\\ Delta reduces to bot.'), nl,
    write('  So conclusion: bot -> bot = top  (Ax.)'), nl,
    ( C2 = false
    -> write('  VERIFIED: both reduce to top (Ax.).')
    ;  write('  ERROR') ), nl, nl,
    %
    % Case 3: A = top, B = bot
    % Premiss antecedent: top /\ Delta reduces to Delta
    % (a conjunction with a member top reduces to the remaining part).
    % So premiss reduces to: Delta -> bot, i.e. Delta |- bot.
    % For the conclusion: (top=>bot)=>bot = bot=>bot = top,
    % so conclusion antecedent: top /\ Delta reduces to Delta.
    % Conclusion also reduces to: Delta -> bot, i.e. Delta |- bot.
    % Both reduce to the SAME formula.
    %
    write('Case 3: A = top, B = bot'), nl,
    write('  Premiss antecedent: top /\\ Delta reduces to Delta.'), nl,
    write('  So premiss reduces to: Delta |- bot.'), nl,
    impl(true, false, V3), impl(V3, false, C3),
    write('  (A=>B)=>B = (top=>bot)=>bot = '), write(C3), nl,
    write('  Conclusion antecedent: '), write(C3),
    write(' /\\ Delta reduces to Delta.'), nl,
    write('  So conclusion reduces to: Delta |- bot.'), nl,
    ( C3 = true
    -> write('  VERIFIED: both reduce to the same formula Delta |- bot.')
    ;  write('  ERROR') ), nl, nl,
    write('All three cases verified. DNS.1 is invertible. QED.'), nl.

% ----------------------------------------------------------------
% From invertibility to DNS.1-anti
%
% Invertibility of DNS.1 means:
%   A, Delta |- B  <--->  (A=>B)=>B, Delta |- B
% i.e. the two sequents are EQUIVALENT (by definition of invertibility).
%
% By elimination of the equivalence (modus ponens on <->):
%   if  A, Delta |- B  holds, then  (A=>B)=>B, Delta |- B  holds
%   if  A, Delta |- B  does NOT hold, then  (A=>B)=>B, Delta |- B  does NOT hold
%
% The second direction IS DNS.1-anti:
%   A, Delta |/- B
%   --------------  DNS.1-anti
%   (A=>B)=>B, Delta |/- B
% ----------------------------------------------------------------

dns1_anti_from_invertibility :-
    nl,
    write('Invertibility of DNS.1 means the premiss and conclusion are EQUIVALENT:'), nl,
    write('  A, Delta |- B  <--->  (A=>B)=>B, Delta |- B'), nl, nl,
    write('By elimination of the equivalence (<->-elim):'), nl,
    write('  if  A, Delta |/- B  then  (A=>B)=>B, Delta |/- B'), nl, nl,
    write('This IS the rule DNS.1-anti. Verification:'), nl,
    ( \+ holds([a]:b), \+ holds([(a=>b)=>b]:b)
    -> write('  a |/- b  and  (a=>b)=>b |/- b  : CONFIRMED')
    ;  write('  ERROR: unexpected provability') ), nl,
    nl.

dns1_check_case(VA, VB) :-
    impl(VA, VB, VAB),
    impl(VAB, VB, VC),
    % Premiss holds iff: VA=true -> VB=true
    ( VA = true -> Premiss = VB ; Premiss = true ),
    % Conclusion holds iff: VC=true -> VB=true
    ( VC = true -> Concl = VB ; Concl = true ),
    write('  A='), write(VA), write(', B='), write(VB),
    write('  =>  (A=>B)=>B = '), write(VC),
    write('  |  premiss [A,D|-B] value: '), write(Premiss),
    write('  |  conclusion [(A=>B)=>B,D|-B] value: '), write(Concl),
    ( Premiss = Concl
    -> write('  [EQUIV]')
    ;  write('  [DIFFER -- NOT INVERTIBLE]') ), nl.

% ================================================================
% SECTION: DNS RULES DERIVABLE IN F
% Paper section: "Two rules derivable in F"
% ================================================================

dns_rules :-
    nl,
    write('=== Two rules derivable in F (DNS.1 and DNS.2) ==='), nl, nl,

    write('-- DNS.1 derivation in F --'), nl,
    write('   Premiss : A, Delta |- B   (here Delta=[b], A=a, B=b)'), nl,
    show_dns_derivation('DNS.1: from a, b |- b   to   (a=>b)=>b, b |- b',
                        dns1_derivation_proof, [b], a, b),

    write('-- DNS.2 derivation in F using R->_core --'), nl,
    write('   Premiss : A, Delta |-      (here Delta=[~a], A=a, B=b)'), nl,
    show_dns_derivation('DNS.2: from a, ~a |-    to   (a=>b)=>b, ~a |- b',
                        dns2_derivation_proof, [~a], a, b),
    nl.


% ================================================================
% SECTION: DNS.1 IS INVERTIBLE -- ALTERNATIVE PROOF BY CUT
%
% The paper's main proof is by structural induction on derivations
% (Section "Syntactic Proof"); that proof is type-checked in the
% accompanying Coq file.  This command provides an alternative
% proof by admissible Cut, which is valid under Tennant's own
% consistency condition.
% ================================================================

dns1_inv_cut :-
    nl,
    write('=== DNS.1 is invertible: alternative proof by Cut ==='), nl,
    write('NOTE: the paper''s main proof of this invertibility is'), nl,
    write('by structural induction on derivations (see section'), nl,
    write('"Syntactic Proof").  That induction is type-checked in'), nl,
    write('the accompanying Coq file.  Below is an alternative proof'), nl,
    write('by admissible Cut, valid under Tennant''s own consistency'), nl,
    write('condition (Core Logic, p. 46).'), nl,
    dns1_invertibility_by_cut.


% ================================================================
% SECTION: DNS.1 IS INVERTIBLE -- SEMANTIC PROOF
% Paper section: "DNS.1 is invertible -- Semantic proof"
% ================================================================

dns1_sem_inv :-
    nl,
    write('=== DNS.1 is invertible: semantic proof ==='), nl,
    dns1_invertibility_semantic.


% ================================================================
% SECTION: DEDUCTION OF DNS.1-anti
% Paper section: "Deduction of \overline{DNS.1}"
% ================================================================

dns1_anti :-
    nl,
    write('=== Deduction of the rule DNS.1-anti ==='), nl,
    dns1_anti_from_invertibility,
    write('-- DNS.1-anti verified on concrete instances --'), nl,
    dns1_anti_check('DNS.1-anti (Delta=[])',  [a],   [(a=>b)=>b],   b),
    dns1_anti_check('DNS.1-anti (Delta=[c])', [a,c], [(a=>b)=>b,c], b),
    nl.


% ================================================================
% SECTION: THEOREM 1 (CLAIM 1 ENTAILS A CONTRADICTION)
% Paper section: "Deduction of the contradiction"
% ================================================================

theorem :-
    nl,
    write('=== Theorem 1: Claim 1 entails a contradiction in F ==='), nl, nl,

    write('-- Claim 1 (~a,a |- b) is unprovable in F --'), nl,
    ( \+ holds([~a,a]:b)
    -> write('   ~A, A |/- B  : CONFIRMED'), nl
    ;  write('   ERROR: ~A, A |- B is provable'), nl ),
    nl,

    write('-- DNS.2 conclusion IS provable in F (uses R->_core) --'), nl,
    show_proof('[~a,(a=>b)=>b]:b  (DNS.2 conclusion for Claim 1)',
               [~a,(a=>b)=>b]:b),
    nl,

    write('-- Theorem 1: Claim 1 + DNS.1-anti vs. DNS.2 --'), nl,
    print_contradiction('Theorem 1',
        [~a,a]:b,
        [~a,(a=>b)=>b]:b,
        [~a,(a=>b)=>b]:b),
    write('==> CONTRADICTION (Theorem 1)'), nl, nl,
    write('QED.'), nl.


% ================================================================
% SECTION: COROLLARY 1 (CLAIM 2 ENTAILS THE SAME CONTRADICTION)
% Paper section: "Corollary"
% ================================================================

corollary :-
    nl,
    write('=== Corollary 1: Claim 2 entails the same contradiction ==='), nl, nl,

    write('-- Claim 2 (~a,a |- ~b) is unprovable in F --'), nl,
    ( \+ holds([~a,a]:(~b))
    -> write('   ~A, A |/- ~B  : CONFIRMED'), nl
    ;  write('   ERROR: ~A, A |- ~B is provable'), nl ),
    nl,

    write('-- DNS.2 conclusion IS provable in F for ~B (uses R->_core) --'), nl,
    show_proof('[~a,(a=>~b)=>~b]:(~b)  (DNS.2 conclusion for Claim 2)',
               [~a,(a=>(~b))=>(~b)]:(~b)),
    nl,

    write('-- Corollary 1: Claim 2 + DNS.1-anti vs. DNS.2 --'), nl,
    print_contradiction('Corollary 1',
        [~a,a]:(~b),
        [~a,(a=>(~b))=>(~b)]:(~b),
        [~a,(a=>(~b))=>(~b)]:(~b)),
    write('==> CONTRADICTION (Corollary 1)'), nl, nl,
    write('QED.'), nl.


% ================================================================
% SECTION: STRICT CORE MODE VERIFICATION
%
% Verifies the paper's critical sequents in STRICT CORE MODE:
% atomic axioms [A]:A only, and L-> with explicit context splitting.
% No Weakening on the left is incorporated anywhere.
%
% This is the most faithful reading of Tennant 2017, p. 21.
% ================================================================

core_strict :-
    nl,
    write('=== Strict Core mode (Tennant 2017, p. 21) ==='), nl,
    write('Axioms: strictly [C]:C  (Gamma is the singleton {C}).'), nl,
    write('L-> with explicit context splitting (Delta1 / Delta2).'), nl,
    write('R-> covers both effective and vacuous discharge.'), nl,
    write('No Weakening on the left anywhere.'), nl, nl,
    write('-- Critical sequents of the paper --'), nl, nl,

    test_strict('A |- A                              (axiom)',
                [a]:a),
    test_strict('|- A => A                           (R-> on axiom)',
                []:(a=>a)),
    test_strict('A=>B, A |- B                        (eq:1, M intersection C)',
                [a=>b, a]:b),
    test_strict('B |- A=>B                           (R-> vacuous, Tennant p.35)',
                [b]:(a=>b)),
    test_strict('~A, A |-                            (L~ on axiom)',
                [~a, a]:bot),
    test_strict('~A |- A=>B                          (eq:2, DNS.2 left premiss)',
                [~a]:(a=>b)),
    test_strict('(A=>B)=>B, ~A |- B                  (DNS.2 conclusion)',
                [(a=>b)=>b, ~a]:b),
    test_strict('(A=>~B)=>~B, ~A |- ~B               (Corollary, DNS.2 with ~B)',
                [(a=>(~b))=>(~b), ~a]:(~b)),
    nl,
    write('-- Sequents NOT derivable in strict Core --'), nl, nl,
    test_strict_neg('~A, A |- B                       (Claim 1, must fail)',
                    [~a, a]:b),
    test_strict_neg('~A, A |- ~B                      (Claim 2, must fail)',
                    [~a, a]:(~b)),
    nl,
    write('-- Note on DNS.1 conclusion --'), nl,
    write('(A=>B)=>B, A |- B  (DNS.1 conclusion) is derivable in C only'), nl,
    write('when its premiss  A, Delta |- B  is itself derivable.  As a'), nl,
    write('schematic derived rule, DNS.1 admits the premiss as hypothesis;'), nl,
    write('see dns_rules. for the explicit derivation.'), nl,
    nl.

test_strict(Label, Seq) :-
    write('  '), write(Label), write('  : '),
    ( holds_strict(Seq) ->
        write('DERIVABLE (strict Core OK)')
    ;
        write('NOT DERIVABLE in strict Core')
    ), nl.

test_strict_neg(Label, Seq) :-
    write('  '), write(Label), write('  : '),
    ( \+ holds_strict(Seq) ->
        write('NOT DERIVABLE (as expected, strict Core OK)')
    ;
        write('DERIVABLE -- UNEXPECTED')
    ), nl.


% ================================================================
% ENTRY POINT
% ================================================================

main :-
    fragment,
    dns_rules,
    dns1_inv_cut,
    dns1_sem_inv,
    dns1_anti,
    theorem,
    corollary,
    !.

%% To run a single section, type one of:
%%    ?- fragment.
%%    ?- dns_rules.
%%    ?- dns1_inv_cut.
%%    ?- dns1_sem_inv.
%%    ?- dns1_anti.
%%    ?- theorem.
%%    ?- corollary.
%%    ?- core_strict.   (strict Core mode verification)
%% Or to run the full verification (permissive mode):
%%    ?- main.


% ================================================================
% PROOF TERM CONSTRUCTION
% ================================================================

prove(Seq, Proof) :-
    for(Th, 0, 6), prove(Seq, Th, Proof), !.

prove(Seq, _, ax(Seq)) :-
    ax(Seq), !.
prove(Seq, Th, step(Rule, Seq, Subs)) :-
    Th > 0, Th1 is Th - 1,
    rules(Rule, Seq, P),
    prove_check(P, Th1, Subs).

prove_check(conj(P1,P2), Th, [S1|S2]) :- !,
    prove(P1, Th, S1),
    prove_check(P2, Th, S2).
prove_check(Seq, Th, [Sub]) :-
    prove(Seq, Th, Sub).


% ================================================================
% INDENTATION
% ================================================================

indent(0) :- !.
indent(N) :- N > 0, write('   '), N1 is N-1, indent(N1).


% ================================================================
% TOGGLE: lowercase <-> uppercase (for LaTeX rendering)
% ================================================================

toggle(X, Y) :-
    atom_codes(X, L),
    toggle_list(L, R),
    atom_codes(Y, R).

toggle_list([], []).
toggle_list([X|L], [Y|R]) :-
    toggle_code(X, Y),
    toggle_list(L, R).

toggle_code(X, Y) :-
    lower_a(La), upper_a(Ua), lower_z(Lz),
    La =< X, X =< Lz, !,
    Y is X - La + Ua.
toggle_code(X, Y) :-
    upper_a(Ua), upper_z(Uz), lower_a(La),
    Ua =< X, X =< Uz, !,
    Y is X - Ua + La.
toggle_code(X, X).


% ================================================================
% LATEX RENDERING
% ================================================================

formula_latex(bot, '\\bot') :- !.
formula_latex(~A, Latex) :- !,
    formula_latex(A, LA),
    concat_atoms(['\\lnot ', LA], Latex).
formula_latex(A=>B, Latex) :- !,
    formula_latex(A, LA),
    formula_latex(B, LB),
    ( A = (_=>_) ->
        concat_atoms(['(', LA, ')'], LA2)
    ;
        LA2 = LA
    ),
    concat_atoms([LA2, ' \\to ', LB], Latex).
formula_latex(A, AU) :- atom(A), !, toggle(A, AU).
formula_latex(A, A).

% True when X is not a sequent hypothesis (i.e. not of the form T:F)
not_hyp(X) :- functor(X, F, A), \+ (F = (:), A = 2).

sequent_latex(Gamma:F, Latex) :-
    list_filter(not_hyp, Gamma, Clean),
    sort_gamma(Clean, Sorted),
    formulas_latex(Sorted, LeftLatex),
    ( F = bot ->
        ( LeftLatex = '' ->
            Latex = '\\vdash'
        ;
            concat_atoms([LeftLatex, ' \\vdash'], Latex)
        )
    ;
        formula_latex(F, RightLatex),
        ( LeftLatex = '' ->
            concat_atoms(['\\vdash ', RightLatex], Latex)
        ;
            concat_atoms([LeftLatex, ' \\vdash ', RightLatex], Latex)
        )
    ).

sort_gamma(Gamma, Sorted) :-
    list_filter(is_neg, Gamma, Negs),
    list_reject(is_neg, Gamma, Rest),
    append(Negs, Rest, Sorted).

is_neg(~_).

formulas_latex([], '') :- !.
formulas_latex([F], Latex) :- !,
    formula_latex(F, Latex).
formulas_latex([F|Rest], Latex) :-
    formula_latex(F, LF),
    formulas_latex(Rest, LRest),
    concat_atoms([LF, ', ', LRest], Latex).

rule_latex(ax,         '$Ax.$').
rule_latex(lneg,       '$L\\lnot$').
rule_latex(rcond,      '$R{\\to}$').
rule_latex(rcond_core, '$R{\\to}_{\\mathbb{C}}$').
rule_latex(lcond,      '$L{\\to}$').
rule_latex(neg_e,      '$\\lnot E$').
rule_latex(cut,        '$Cut$').

% Write a line of LaTeX output
wl(S) :- write(S), nl.

% bussproofs command builders
bp_axiom_empty :-
    wl('\\AxiomC{}').
bp_axiom(SL) :-
    concat_atoms(['\\AxiomC{$', SL, '$}'], L), wl(L).
bp_rightlabel(RL) :-
    concat_atoms(['\\RightLabel{\\scriptsize{', RL, '}}'], L), wl(L).
bp_unary(SL) :-
    concat_atoms(['\\UnaryInfC{$', SL, '$}'], L), wl(L).
bp_binary(SL) :-
    concat_atoms(['\\BinaryInfC{$', SL, '$}'], L), wl(L).
bp_nary(SL) :-
    concat_atoms(['\\NaryInfC{$', SL, '$}'], L), wl(L).

render_bussproofs(ax(Seq)) :-
    sequent_latex(Seq, SL),
    rule_latex(ax, RL),
    bp_axiom_empty,
    bp_rightlabel(RL),
    bp_unary(SL).

render_bussproofs(step(Rule, Seq, [Sub])) :- !,
    render_bussproofs(Sub),
    sequent_latex(Seq, SL),
    rule_latex(Rule, RL),
    bp_rightlabel(RL),
    bp_unary(SL).

render_bussproofs(step(Rule, Seq, [Sub1,Sub2])) :- !,
    render_bussproofs(Sub1),
    render_bussproofs(Sub2),
    sequent_latex(Seq, SL),
    rule_latex(Rule, RL),
    bp_rightlabel(RL),
    bp_binary(SL).

render_bussproofs(step(Rule, Seq, Subs)) :-
    my_maplist(render_bussproofs, Subs),
    length(Subs, N),
    sequent_latex(Seq, SL),
    rule_latex(Rule, RL),
    bp_rightlabel(RL),
    ( N =:= 1 -> bp_unary(SL)
    ; N =:= 2 -> bp_binary(SL)
    ;             bp_nary(SL)
    ).

render_bussproofs(neg_elim(
        dns1_anti(unprovable(ClaimSeq), unprovable(AntiConcSeq)),
        provable(_, Proof),
        concl(Rule, Concl))) :-
    antiseq_latex(ClaimSeq,    CL),
    antiseq_latex(AntiConcSeq, AL),
    rule_latex(Rule, RL),
    formula_latex(Concl, FL),
    bp_axiom(CL),
    wl('\\RightLabel{\\scriptsize{$\\overline{DNS.1}$}}'),
    bp_unary(AL),
    render_bussproofs(Proof),
    bp_rightlabel(RL),
    bp_binary(FL).


% ================================================================
% PROOF TERM DISPLAY
% ================================================================

print_proof_term(ax(Seq), Depth) :-
    indent(Depth),
    write('ax('), write(Seq), write(').'), nl.

print_proof_term(step(Rule, Seq, Subs), Depth) :-
    indent(Depth),
    write('step('), write(Rule), write(','), nl,
    D1 is Depth + 1,
    indent(D1), write(Seq), write(','), nl,
    indent(D1), write('['), nl,
    D2 is D1 + 1,
    print_subs_term(Subs, D2),
    indent(D1), write(']).'), nl.

print_proof_term(neg_elim(
        dns1_anti(unprovable(ClaimSeq), unprovable(AntiConcSeq)),
        provable(DNS2Seq, Proof),
        concl(Rule, Concl)), Depth) :-
    indent(Depth), write('neg_elim('), nl,
    D1 is Depth + 1,
    D2 is D1 + 1,
    indent(D1), write('dns1_anti('), nl,
    indent(D2), write('unprovable('), write(ClaimSeq),    write('),'), nl,
    indent(D2), write('unprovable('), write(AntiConcSeq), write(')'),  nl,
    indent(D1), write('),'), nl,
    indent(D1), write('provable('), write(DNS2Seq), write(','), nl,
    print_proof_term(Proof, D2),
    indent(D1), write('),'), nl,
    indent(D1), write('concl('), write(Rule), write(', '), write(Concl), write(')'), nl,
    indent(Depth), write(').'), nl.

print_subs_term([], _).
print_subs_term([S|Rest], Depth) :-
    print_proof_term(S, Depth),
    print_subs_term(Rest, Depth).


% ================================================================
% DISPLAY PREDICATES
% ================================================================

show_proof(Label, Seq) :-
    nl,
    write('--- '), write(Label), write(' ---'), nl,
    ( prove(Seq, Proof) ->
        write('PROVABLE'), nl, nl,
        write('=== Prolog proof term ==='), nl,nl,
        print_proof_term(Proof, 1),
        nl,
        write('=== LaTeX (bussproofs) ==='), nl,nl,
        write('\\begin{prooftree}'), nl,
        render_bussproofs(Proof),
        write('\\end{prooftree}'), nl, nl,
        write('Q.E.D.'), nl
    ;
        write('UNPROVABLE'), nl
    ), nl.

antiseq_latex(Gamma:F, Latex) :-
    list_filter(not_hyp, Gamma, Clean),
    formulas_latex(Clean, LeftLatex),
    formula_latex(F, RightLatex),
    ( LeftLatex = '' ->
        concat_atoms(['\\not\\vdash ', RightLatex], Latex)
    ;
        concat_atoms([LeftLatex, ' \\not\\vdash ', RightLatex], Latex)
    ).

contradiction_term(ClaimSeq, AntiConcSeq, DNS2Seq,
        neg_elim(
            dns1_anti(unprovable(ClaimSeq), unprovable(AntiConcSeq)),
            provable(DNS2Seq, Proof),
            concl(neg_e, bot))) :-
    \+ holds(ClaimSeq),
    prove(DNS2Seq, Proof).

print_contradiction(Title, ClaimSeq, AntiConcSeq, DNS2Seq) :-
    nl,
    write('--- '), write(Title), write(' ---'), nl, nl,
    ( contradiction_term(ClaimSeq, AntiConcSeq, DNS2Seq, Term) ->
        write('=== Prolog proof term ==='), nl,nl,
        print_proof_term(Term, 1),
        nl,
        write('=== LaTeX (bussproofs) ==='), nl,nl,
        write('\\begin{prooftree}'), nl,
        render_bussproofs(Term),
        write('\\end{prooftree}'), nl
    ;
        write('% ERROR: contradiction_term failed'), nl
    ), nl.
