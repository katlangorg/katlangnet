# KatLang closed-issue decision ledger

> **Demand-driven evaluation: short-circuit `and`/`or` (#202), lazy `reduce` accumulators (#203), lazy collections and pipelines (#204) — 2026-11-26 (current-rule pointers from the issue texts, their commits and the maintained language rules; the issue classifications below are unchanged; owner decisions recorded from the record, none made here; uncommitted over `main` @ `c9116ed6`):** the index still ends at #170, so these three issues, closed after it, are mapped here to their decisions and current rules, as the pointer for post-snapshot closed issues does (closing dates are GitHub's, UTC; this round read the three issue texts). **#202** "Short-circuit evaluation for and and or" (closed 2026-11-23, `65b1b136`): `and` and `or` evaluate the left operand once and require a Boolean, return `false` for `false and …` and `true` for `true or …` without evaluating the right operand, and otherwise evaluate the right operand once and require a Boolean; `xor` stays eager (`constitution.md` BOOL-04; BOOL-02, OP-03, RUN-08; `open-questions.md` Q-57, narrowed to the `xor` tier). *(2026-11-28: Q-57 has since been RESOLVED BY DECISION — on 2026-11-27 the owner confirmed the order `or` < `xor` < `and` and adopted its rationale; `constitution.md` OP-01.)* **#203** "Evaluate reduce accumulators on demand" (closed 2026-11-23, `66ebae56`): the collection is evaluated first, then only the last step is demanded, each accumulator deferred and evaluated at most once, so that the fold's accumulator VALUE demands follow `Step(b, Step(a, start))`, and an empty fold evaluates and returns `start` (HO-02, HO-03; CALL-03, RUN-08); the later C#-only fold execution work (`5a672ad0`, `e4398204`, `7cf1e7eb`) changes no meaning (RUN-03). **#204** "Evaluate collections and pipelines on demand" (closed 2026-11-23, `108268c7`): a list is a collection of positions read on demand, `map`, `filter` and `take` are stages, and spreads, structural patterns, equality and the run's result consume lazy collections as the issue asked them to be defined (SEQ-02, COLL-04; SUP-02, NEED-04, CMP-03, RUN-05, RUN-07 (g), RUN-08), with the passive-observation and stage-release qualifications of 2026-11-24 and 2026-11-25 (`998870d8`, `76df3dc4`, `b2cd4f2b`, `81cb3f13`; RUN-01, RUN-03). Three passages below that state "no short circuit" as surviving semantics or rationale carry dated pointers. The lineages are the three sections of 2026-11-26 at the end of `decision-lineages.md`.

> **Inner-property lifetime (INNER-PROPERTY LIFETIME) — 2026-11-21 (current-rule pointer; the issue classifications below are unchanged; the owner decision is recorded from the follow-up brief, none is made here; uncommitted over `main` @ `5ae82403`):** every entry below that says a self-contained (exported) property is evaluated once per run across all calls of its owner, or that exposure decides cache scope, describes the rule until November 2026. Storage now follows the declaring binding and its owning invocation: each actual call of an owner evaluates the owner's inner properties afresh, reads in one call share them, and a property no call owns is one value per run. The current rule is `constitution.md` PROP-04 and PROP-08.

> **Exposure enforcement, follow-up (EXPORTED-DETACHED) — 2026-11-21 (qualification of the pointer below; the issue classifications are unchanged; no owner decision is made here; uncommitted over `main` @ `5ae82403`):** the refusal the pointer below describes holds on the paths the evaluators check — every executed operation on a captured parameter (value read, call, transport), a local-only member access, a local-only property read — and is not unconditional: the binding cell a local runtime-target alias retains is not checked (formal ledger row R-1, open). The current rule is `constitution.md` PROP-08 and RES-08. *(2026-11-24: the retained cell is now checked at every reuse — formal ledger row R-1, closed; PROP-08.)* *(2026-11-24, later: the row is QUALIFIED, not closed — the reuse is judged before the cell's channel runs, the demand decides the reads that follow, and the admitted access of an `open`-provided local-only member is not recorded; PROP-08.)* *(2026-11-26: that access is recorded now, where the selection is consumed; the row stays QUALIFIED for the path step of an `open` target; PROP-08.)*

> **Exposure enforcement (EXPORTED-DETACHED) — 2026-11-21 (current-rule pointer; the issue classifications below are unchanged; no owner decision is made here; uncommitted over `main` @ `6e99edc9`):** the entry "Local-only properties: accessibility -> also cache scope" says the evaluator trusts the static exposure classification. Both evaluators now ENFORCE the classification: an exported property is evaluated detached from the activations that exist when its evaluation starts, a captured parameter is read only through its lexical owner's activation, and a local-only member or property that needs a detached activation is refused. A classification that under-approximates a dependence is therefore a deterministic refusal (`UnknownName`, `LocalOnlyProperty`), observable only for misclassified and host-built trees; no value, key or charge of a correctly classified program changes. The entry carries a dated pointer; the current rule is `constitution.md` PROP-08 and RES-08.

> **Constitution catch-up — 2026-11-15 (current-rule pointers from commit and document evidence; the issue classifications below are unchanged; no owner decision is made here; over `main` @ `9ec6bf3b`):** two entries describe rules that later owner decisions replaced. **#118** (`DisplayDecimals`): the owner decision of 2026-11-12 extends Q-10 D-F to two independent settings, `MinDecimalPlaces` and `MaxDecimalPlaces`, and removes `DisplayDecimals` and `--display-decimals` outright (`1d3e1354`, whose message says "Replaces #118"); the current rule is `constitution.md` RUN-06, with `open-questions.md` Q-10 and `decision-lineages.md` § Q-10 owner extension. **#180** (Q-80 / STR-02, double-quoted escapes and interpolation): the owner's STR-03 decision of 2026-11-11 removes both (`65885c4f`); the current rules are SYN-15, SYN-02 and VAL-02, VAL-12 is retired, and the lineage is `decision-lineages.md` § STR-03. So the pointer "Current-rule pointer, Q-80 (2026-10-11)" below is itself history: strings are single-quoted only again, a double-quoted string is an error again (now the targeted `UnsupportedDoubleQuotedString`, no longer #142's `UnexpectedCharacter`), and the string operations of #36 stay open. Both commits name #197 in their subjects ("fixes #197"); this ledger has no entry for #197, and none is added, because this round read no issue text. Declaration-level output spreading (`6c736e3f`, `899789d8`, `4562d74c`; SUP-08) and the E-18 exposure decisions (`73d6256e`; RES-08) correspond to no closed issue recorded here.

> **Constitution restructuring — 2026-11-06:** `constitution-draft.md` was restructured and reconciled with decisions accepted after 2026-10-25. Rule identifiers are unchanged. References in this record to Evidence sections, topic tails, Appendix A rows, annex headings or the rules-only edition mean the pre-restructuring edition, kept at `../constitution-cleanup-20261106/backup/`. This record's dated entries were not rewritten.

> **Constitution audit — 2026-10-23 (`main` @ `e62e3ac6`; audit record `../constitution-audit-20261023T141727Z/`):** the issue classifications are unchanged; 17 corrections add current-rule pointers — one paragraph mapping every issue closed after the 2026-09-27 snapshot (#64, #171, #172, #174–#181, #183–#187, #189) to its decision and current rules, and dated pointers where loop areas, #64 and #170 still read as current.

> **R3′ pattern helper totalization — 2026-10-21 (FORMAL-07 roadmap item R3′, not the 2026-10-14 repeated-spread work that reused the label; formal-evidence strengthening and a behaviour-preserving Lean restructuring; no rule text change; no observable behaviour change; no C# change; no issue-status change; uncommitted over `main` @ `24c554fa`):** the pure helpers the total Model-C binder and clause dispatcher reach are now structural recursion in `lean/KatLang.lean` — value-pattern matching `matchPatternInto`/`matchStructureInto` (walker `matchItemsInto`), the kind-mismatch rendering `ParameterPattern.displayName` (`displayNames`) and `resultDiagnosticString` (`resultDiagnosticStrings`), duplicate-clause comparison `Pattern.matchEquivalentWithRenaming` (`matchEquivalentPairsWithRenaming`; `matchEquivalentItemsWithRenaming` is now a non-recursive wrapper), and the adjacent `ParameterPattern.captures` (`capturesOfList`), `Pattern.parameterPattern?` (`parameterPatternsOf?`) and `plainClauseParameterPatterns?`; `KatLang.lean`'s `partial def` count is 38 → 29 (nine removed). New `lean/KatLangArityLaws/PatternHelpers.lean` (130 theorems, 10 definitions; standard axioms only) proves the former recurrences, literal matching iff the same constructor and payload, the prefix/fresh-append environment contract, the conversion boundary (eligible iff literal-free; the converted head IS the clause's binder head), the STRUCTURAL CHARACTERIZATION of duplicate clauses (`isMatchEquivalent_iff`: equality up to an injective binder renaming covering every binder; reflexive, symmetric; the check is the pairwise test over clause patterns only), and production specializations: the binder's literal arm per literal constructor, its ordinary kind-mismatch error as an explicit string, and the dispatcher's rejection of a renamed duplicate head before any effect; `PatternHelperGuards.lean` adds executable witnesses. Preservation is these kernel equations plus a bounded executable comparison against verbatim frozen pre-R3′ copies (local `artifacts/validation/r3prime-pattern-helpers/preservation/`) — "equal to the old opaque constant" is NOT claimed. Not established: recursive VALUE demand, whole-run refinement (R7 stays OPEN), Q-66 (OPEN), C#'s mutable matching accumulator, or a Lean-`Int`/C#-Decimal128 text theorem; the remaining 29 `partial` definitions (alias counts, static chains, AST validation, `ScopeCtx.declaration` behind S5's `reprStr` fallback, lookups, cache shapes, identification, `exprDiagnosticName`, post-elaboration invariants and others) are unchanged. Report: `experimental/features/r3prime-pattern-helper-totalization.md`.

> **S6c CF-4 production connection — 2026-10-20 (formal-evidence strengthening and a behaviour-preserving Lean extraction; no rule text change; no observable behaviour change; no C# change; no issue-status change; uncommitted over `main` @ `7d6a58be`):** the shared body setup of the two row readers is the ONE total activated-body boundary `ActivatedBody.readRows` (checks: duplicate property, conditional read as a value, missing output; ONE `enterAlgorithmBody`; the builtin body's atomic route); `evalAlgOutputSlots` / `whileVerdictSlots` are that boundary with their distinct readers, kernel-checked equal to the former inline bodies. `KatLangArityLaws/WhileRoundProduction.lean` (62 theorems, standard axioms only) proves: one body entry and ONE context for every row of a round (`readRows_entered`, `readRows_uses_one_context`); body entry allocates no cell and keeps the binder's parameter cells, binding context and caches, recording at most one lexical activation (`enter_run`, `entered_*`); the production `formOutputRow` IS the production `evalCounted` plus `OutputRows.items` (exact); a finite-use converse of R7's `production_unfolds` (`production_eq_of_finite`) so the production `whileVerdictSlots` / `evalAlgOutputSlots` EQUAL their activated-body runs wherever those complete; the CF-1/2/5 and no-flag laws restated about the production `whileVerdictSlots` (`production_cf*`), check failures reaching no row, the builtin body's atomic row; the round's dispatch for COMPLETED runs (`runNeedWhileRound_user/_family/_builtin/_alias`: one binding or one family dispatch, then ONE `whileVerdictSlots`); shared cells (`round_parameter_cell`, `completed_cell_reused_after`); and, SEPARATELY, cache reuse: the production access returns a published entry without evaluating (`property_cache_hit_production`), published entries survive the transitions (Q-37), so an EXPORTED binding published during discovery is reused by every later read (`exported_publication_reused`); the local-only counterpart keeps an explicit key-stability premise (`local_publication_reused`). CF-4 status: the shared-activation / one-context / production-row-formation subclaims are DISCHARGED at the production `whileVerdictSlots`; the cache-reuse subclaim is discharged for exported keys and remains OPEN for local-only keys across rows (a whole-run lexical-activation invariant; `propertyOwnerBindingContext` is `partial`) and for evaluator-internal routing of property reads; the dispatch equations keep a completion premise (binder channels not `Finite`). Whole-run heap/cache refinement, reachable-state / active-cell discipline, termination, R7, Q-66, S6a and S6b are unchanged. Report: `experimental/features/s6c-cf4-production-shared-activation.md`; backups/evidence: `artifacts/validation/s6c-cf4/`.

> **Independent S6d R7 review correction — 2026-10-20 (R7 remains OPEN; no rule or issue-status change):** the implementation is an unaccepted checkpoint. The total recursive control core still calls opaque pure partial leaves and public identification/admission; operation-level completion is not an admitted-public-run refinement theorem. `ProductionDiscipline` now preserves existing suspensions, completed VALUEs and prepared supplies in its stated general form; it does not cover completed CALLABLE stability, canonical links, address validity or activation/D4 ownership. Cache-entry preservation and completed owner-list restoration do not discharge all Q-37 publication/key laws. Reachability, callback/direct-call body and consumer refinement, active-cell plan conservativity, dot-funnel and qualified Q-25 obligations remain unresolved acceptance findings. The `Error.fuelExhausted` representation still needs an owner decision: compiled completed runs retry incompletion, but the kernel-level unbounded noncompletion default uses that error and the entry state. The original 3,030 migration summaries omit cache/activation contents and successful callable identities and do not establish full-state equality. Reviewer repairs, actual validation and limits: `artifacts/validation/r7-review/`; final verdict/totals are in the coordination result. The earlier implementation ready status and blanket TOTAL/public-nonerror claims are superseded. Q-66, S6a, S6b, CF-4 and R3-prime are not closed.


> **S6d R7 whole-run evaluator — 2026-10-20 (formal-evidence strengthening and a behaviour-preserving Lean restructuring; no rule text change; no observable behaviour change; one OWNER DECISION REQUESTED (incomplete-outcome representation); no Q, PV or X status change; uncommitted over `main` @ `74eed733`):** the Lean evaluator is TOTAL: the former `partial` block is a fuel-indexed core (`EvalCall`/`EvalBody`/`evalStep`/`evalFuel`) and every production operation is that core under a `partial_fixpoint` fuel search (`evalUnbounded`/`searchFuel`); running out is the Lean-only incomplete outcome `Error.fuelExhausted`, never captured, memoized, published or returned by a public run. Kernel theorems (standard axioms): monotonicity; fuel laws (completion stable with identical final state, determinism, failure stability, finite-height derivations ↔ fuel); the production bridge (`production_completes_iff`, `production_unfolds`); whole-run heap discipline making **`ProductionDiscipline` a theorem** (`productionDiscipline_holds`, general form); Q-37 whole-run cache monotonicity and owner-set restoration on completed runs; FORMAL-05 plain = counted value as production equations. Old/new evaluators agree byte-for-byte (outcomes + per-cell state summaries) on all 3,030 corpus cases. OPEN: remaining reachable-state invariants, callback ≡ direct call, dot funnel, Q-25, plan conservativity, converse unfolding; Q-66 is NOT discharged. Evidence: `experimental/features/s6d-r7-whole-run-evaluator-refinement.md`.

> **Q-68 independent review — 2026-10-20 (final current inventory):** The incoming 14 pending-file hashes matched `main` @ `2908ddaa`. Review corrected the initial discovery/flat-shape evidence: current scalar outputs do not establish nested preservation, equal outcomes do not establish failure, and an error-to-empty-heap fallback cannot establish inert successful execution. Ten guard commands were strengthened (one overlapping the initial strengthening): exact nested collector value, actual empty/spread/root counts with whole-program validation retained, explicit DivByZero completion, actual successful capture/view construction, and two missing-callee payloads. Final inventory: **2,745 handwritten guards in 77 files; 618 candidate rows = 29 strengthened + 411 already strong + 178 deliberately broad**, plus a separate overlapping census of 983 failure-related guards and ten shared observers. The initial 613-row classification below is superseded for final assertion-strength/readiness. All 25 original negative controls are rebuilt from final source, with 12 new controls; independent serial V1 commands, actual exits, assertion locations and .NET counts are in `artifacts/validation/q68-current-guard-audit/reviewer/validation.json`. Q-68 remains **CLOSED against the replacement current inventory**; the unavailable historical FORM-05 list was not reconstructed. This is executable guard/evidence closeout, not universal evaluator refinement. No rule, production or other issue-status change. Q totals remain **54 resolved + 1 superseded + 2 partial + 24 fully open = 81** (26 with an open part); Q-66, R3′, R4, R6, CF-4 and R7 are unchanged. Maintained audit: `docs/design/q68-current-guard-audit.md` § 9. Backups/reversal: `artifacts/validation/q68-current-guard-audit/reviewer/constitution-review.json`.

> **Q-68 CLOSED — 2026-10-20 (current guard audit; owner direction to replace the unavailable historical FORM-05 inventory; Lean test/evidence closeout — no rule text, semantics or production change; uncommitted over `main` @ `2908ddaa`):** Q-68 is closed against the newly completed current guard inventory, following the owner's direction to replace the unavailable historical FORM-05 inventory. The audit censused 2,740 handwritten `#guard` commands in 77 Lean files (the `CoreTests` and `KatLangArityLaws` targets; the generated corpora are listed separately and unchanged), reviewed 613 candidate rows (pattern discovery, supplementary searches, and the instrumented structured result of every `runFlat` observation), strengthened 20 rows / 29 assertion sites to exact constructors, counts, Boolean-required roles or `Result` shapes, added a builtin arity-payload sweep and a checked `failsAs` observer, and justified every remaining broad assertion by its intended scope (S4's three exceptions retained). Current findings are resolved or justified by their intended assertion scope; the historical list was not reconstructed, and no runtime defect was found. This is executable guard/evidence closeout, not universal evaluator refinement: Q-66, R3′, R4, R6, CF-4 and R7 keep their statuses. Current Q81 totals: **54 resolved + 1 superseded + 2 partially resolved (Q-35, Q-44) + 24 fully open = 81** (26 with an open part; zero before release). PV50 and X49 are unchanged; earlier dated totals are historical snapshots. Audit: `docs/design/q68-current-guard-audit.md`; evidence: `artifacts/validation/q68-current-guard-audit/`.

> **S6a independent review, 2026-10-20 (evidence scope and regression repairs; no rule/status/semantics change):** `production_head_walk_no_cross` composes nested traversal and production stability with the initial observed identity domain `ModelNoCross`. `model_present_before_growth` proves that Ready children, collector allocation and META adapters add no observed callable identities; `head_callable_trans_on_of_no_cross` therefore discharges transitivity for final contributions from that initial condition. Equal initial parent profiles suffice (`model_no_cross_of_profiles`); the condition is not proved for every source-reachable callable. Full mixed-profile transitivity and printer separation remain open. Review replaced singleton sequence-pattern guards with valid list/two-item sequence patterns, checked Error constructors, and strengthened child-count, collector/META address-prefix and refusal-order regressions. A printer-opacity boundary is not an impossibility proof. S6a has the stated completed/Ready and restricted-identity scope; R4 and Q-66 stay OPEN. Final reviewer V3 and axiom evidence: `artifacts/validation/s6a-review/`; before-edit six-record backups are hash-verified in `constitution-backup.json` there.

> **S6a R4 / Q-66 repeated-name laws for nested and mixed heads — 2026-10-20 (formal-evidence strengthening; no owner decision; no rule text change; no observable behaviour change; Lean proofs and one behaviour-preserving Lean wiring change, a C# doc comment only; no Q, PV or X status change; totals unchanged):** the evaluator's binder call sites pass the total `NeedChannels.shell` over `demandNeedRecursive` / `projectNeedWrittenAt` (`bindingChannels`; one unfolding of the two drivers). R4 advances and stays PARTIAL as a whole: `lean/KatLangArityLaws/NestedRepeatedNames.lean` proves Q-28's representative and permutation laws for every validated nested or mixed head (sequence, list and unpack patterns at any depth, literals, collectors, META) through an observation walk whose erasure is the production binder run, with fresh-child provenance (identityless, holding the allocation's counted value), first-conflict stopping and permutation of completed contributions up to addresses, and proves the production binder channels stable on completed and Ready cells (`shell_model_caps`). `lean/KatLangArityLaws/CallableIdentityDomain.lean` proves callable-identity transitivity whenever no compared level is decided by an identified/anonymous printed-declaration fallback, and full transitivity under one residual about the opaque printer (`ReprSeparatesPresence`, executable evidence only); an intransitive triple would make satisfiability order dependent. Open: arbitrary suspended, failing or collector-materializing contributions (the recursive drivers stay opaque), the printer residual, R6 and R7. Failure categories stay order dependent. Q-66 stays OPEN. Report `experimental/features/s6a-r4-repeated-name-laws.md` (local).

> **S5 remaining Q-66 formal laws — 2026-10-18 (formal-evidence strengthening; no owner decision; no rule text change; no observable behaviour change; Lean helper totalization and proofs, a C# doc comment only; no Q, PV or X status change; totals unchanged):** `BEq Result` is now the structural total `Result.beq` and `sameDeclaringScope` / `compatibleActivations` are total (kernel equations with the former bodies; exhaustive executable comparisons against the old definitions, zero mismatches). R4 is PARTIAL: `lean/KatLangArityLaws/RepeatedNameLaws.lean` proves Q-28's permutation and representative laws (success ⇔ pairwise compatibility, permutation-invariant satisfiability, an original contribution retained, callable availability iff any, first among the richest, permutation-preserved value/count/identity) over stable completed contributions, with `==` = `=` and callable-identity transitivity on a stated domain, connected to the production traversal of FLAT levels; nested and mixed heads, the `partial` channels' stability and mixed-profile transitivity remain open, and failure categories stay order-dependent. R6 is PARTIAL: `lean/KatLangArityLaws/SupplyCorrespondence.lean` proves a heap-renaming simulation of the binder over corresponding supplies and its production instance, so the callback route's Ready supplies of the same counted values bind correspondingly at any two heaps; a suspended written argument and its Ready value are not equivalent (CALLABLE, META). Q-66 item (4): the post-S2 checked opening is documented, `stacked_star_is_grouped_recapture` is added, and RESOURCE equivalence of `E**` and `(E*)*` is withdrawn as false for C# (`SequenceConstructSpreadReviewTests.StackedAndGroupedSpreadAgreeInValueButCanDifferUnderAResourceLimit`). Q-66 stays OPEN. Report `experimental/features/q66-formal-laws-s5-report.md`; evidence `artifacts/validation/q66-formal-laws-s5/`.

> **Independent R3 adversarial review addendum, 2026-10-15:** the earlier R3 counts describe the implementation snapshot. The reviewed sources now have 69 BinderTrace theorems (one added local allocator-freshness law), 25 FamilyDispatch theorems, 63 BinderCorrespondence theorems, 55 BinderGuards guards and 7 correspondence instance guards. Together with the 26 BinderCore and 12 adapted FORMAL-07 laws, the R3 axiom-audit inventory is 195 theorems. `allocateNeed_fresh_for_valid_supply` proves that one allocation avoids all addresses valid in its incoming heap and preserves their validity; it does not prove whole-binder freshness. The static plain-cell noninterference corollary still assumes no allocation reuses the excluded cells: initial supplied-address validity and nonshrinking channels would discharge that assumption, but the whole-run bridge and the partial production channels' heap-monotonicity proof remain outstanding. Trace erasure quantifies over arbitrary original EvalM capabilities lifted through the protected interface, not arbitrary trace-aware capabilities. Mode correspondence is one-directional: differing outcomes imply a family non-match and ordinary binder incompatibility; a channel raising an incompatibility-shaped error still raises in both modes. New guards pin this distinction, state retention after failed VALUE/allocation, emitted-count inequality, nested repeated names, equal callable identities and allocator reuse. The stale C# repeated-name test comment is corrected; executable C# is unchanged. FORMAL-06, Q-66 (OPEN), R4-R7, opaque-helper limitations and all prior decisions/statuses remain unchanged. This note records proof scope and guard coverage; validation and the final review verdict are recorded separately in `artifacts/validation/r3-independent-review/`.


> **Q-67 COMPLETED — 2026-10-15 (approved implementation, final frozen V3 passed):** FORMAL-06's neutral success/raw-value/root-count/innermost-category contract is UNCHANGED. Separate reviewed shared-payload guards, public failure-phase checks, route payload checks, exact demand/terminality witnesses and executable generator claims settle Q-67. Current Q81 totals: **53 resolved + 1 superseded + 2 partially resolved (Q-35, Q-44) + 25 fully open = 81** (27 with an open part; zero before release). PV50 and X49 classifications/totals are unchanged. Q-66 remains OPEN; X-43 remains SUPERSEDED by Model C. Earlier dated Q-67-open statements and totals are historical snapshots. Full mapping and evidence: `docs/design/differential-observations.md`, `artifacts/validation/q67-differential-observations/`.


> **Status:** analysis artifact — a DRAFT for human review, not authoritative. Produced 2026-09-27 against `main` @ `a2700f4` by a read-only archaeology of all closed issues in `katlangorg/katlangnet`. No production code, Lean, tests, or documentation were changed.

> **Snapshot boundary, clarified 2026-09-30:** issue classifications and observations below describe the dated archaeology above. Post-audit structural-pattern and forwarding decisions are recorded in `decision-lineages.md` parameter-inference Chain G steps 16-18, and current rules in `constitution.md` PAT-06/PAT-08 and FWD-02. The final hostile review adds no issue reclassification or semantic decision.
>
> **Current-rule pointers, post-lifting re-baseline 2026-10-01 (pushed `d6b88a9`):** the issue CLASSIFICATIONS below are unchanged (no new evidence shows one factually wrong). Where a "Surviving semantics" or "surviving rule" statement below describes a rule a later decision replaced, a dated pointer now names the current rule: the unified formula-lifting law of 2026-09-30 (`constitution.md` PAR-07; `decision-lineages.md` parameter-inference Chain G step 19, Chain H step 7, calls-arguments § J step 7) for lifting positions and callable categories, and Q-01 (CALL-06, 2026-09-28) for the re-derivation of failed arguments. All other post-audit decisions are in the lineages.
>
> **Current-rule pointer, X-49 (2026-10-08):** the issue classifications below are unchanged. The Grace entries (#21, #22, #38, #147, #161, #168 and the "Grace on dot edges" and "Closed branch inputs, Grace, and branch scoping" lineages) describe syntax, eligibility and dot composition, which X-49 does not change; the multi-marker ORDER of several weighted names is now PAR-06's movement law (`constitution.md` PAR-06 Movement, Order of movement and Residual weights; `decision-lineages.md` Chain C step 14 and § X-49).
>
> **Historical current-rule pointer, Q-33 (2026-10-09; conflicting line-final subrule superseded 2026-10-14 by Q-65/SYN-11):** the issue classifications below are unchanged. Q-33 (P0, owner decision) confirms #161's layout-independent star as law for a line-final star in every context, definition bodies included, with no warning or error (`constitution.md` SYN-11; `decision-lineages.md` star-layout § G step 8). #140's newline rule stays superseded. *(Issue #183, 2026-10-14: for line-final stars it is current law again, by owner decision — see the #183 pointer above)*
>
> **Current-rule pointer, Q-25 (2026-10-10):** the issue classifications below are unchanged. Q-25 (Option B, owner decision) supersedes the single-value callback-result contract that #37 decided and #132 and #135 kept: a `map` transform or `reduce` step now returns the ordinary result of calling its callback (several rows one sequence value, `()` and `[]` ordinary values, nothing spread), because after ordinary calls became value boundaries, retaining the raw-output callback restriction broke compositionality, identity mapping and wrapper equivalence. Where a "Surviving part" or "Surviving semantics" statement below names that contract, a dated pointer now says so (`constitution.md` HO-03; `decision-lineages.md` § Q-25).
>
> **Current-rule pointer, Q-45 (2026-10-10):** the issue classifications below are unchanged. Q-45 (owner decision) keeps the current Model-C order of `.string(args)` as the law: a written argument list is formed like any call's supply (explicit spreads executed, every other slot suspended), a supply of one or more items is rejected by cardinality before the receiver or any argument is demanded, and only a supply of zero items demands the receiver. The ".string intrinsic" lineage's statement that `R.string(args)` evaluates the arguments and rejects them without evaluating the receiver describes the pre-Model-C order; a dated pointer now says so (`constitution.md` DOT-08, RUN-08; `decision-lineages.md` § Q-45).
>
> **Current-rule pointer, X-18 (2026-10-10):** the issue classifications below are unchanged. X-18 is RESOLVED — the owner confirmed the existing Model-C argument semantics as intended: every callee forms its supply alike (explicit spreads executed at formation, every other slot suspended, collector slices transferred unforced), cardinality is checked before any ordinary VALUE demand, and each callee demands what it uses in its own order (a builtin through its argument roles). The "Callee identity and the builtin argument adapter" lineage's statements that user callables share one eager left-to-right assembly and that builtins use their own adapter describe the pre-Model-C regimes; a dated pointer now says so (`constitution.md` CALL-02, CALL-03, BOOL-05; `decision-lineages.md` builtin-adapter Chain H step 8 and § X-18).
>
> **Current-rule pointer, Q-80 (2026-10-11):** the issue classifications below are unchanged. Q-80 (owner decision, task STR-02) gives KatLang double-quoted strings — six escapes and one-expression interpolation holes rendered as their values' structural text (SYN-15, VAL-12) — and resolves Q-64. Where entries below say that strings are single-quoted only, that a double-quoted string is an `UnexpectedCharacter` error (#142), or that the string operations of #36 are wholly open, those statements describe their dates; ordering and the other #36 operations remain open.

> **Current-rule pointer, Q-37 (2026-10-11):** the issue classifications below are unchanged. Q-37 (owner decision) supersedes the first-successful-entry rule that F3 (31f7c76) introduced: the OUTERMOST successful property-style evaluation of a key owns its entry, and a re-entrant read evaluates but never publishes. Where the "Cache key / binding identity" and "Failures, re-entrancy, re-derivation" lineages state that "the first successful entry wins" or that a self-recursive property can return two different values for two reads, a dated pointer now says so (`constitution.md` PROP-04, PROP-09; `decision-lineages.md` property-caching Chain 9 step 6 and § Q-37).

> **Current-rule pointer, Q-81 (2026-10-12):** the issue classifications below are unchanged. Q-81 (owner decision) replaces `:` indexing with variadic postfix selection `A[s1, …, sn]` and retires the colon with a migration diagnostic (SEQ-04, SEQ-05). Where entries below write selection as `A:i`, say that there is no bracket indexing or that `A[0]` / `A[1]` is rejected (#137, #160), treat `A*:0` as `MisplacedSpread` (#140), or describe the selector as a primary, those statements describe their dates; the selection semantics they establish — zero-based positions, the stored element, the value boundary, `BadIndex` and `TypeMismatch` — survive under the bracket spelling. Dated notes now say so at #137, #140, #160 and in the selection and layout lineages.

> **Current-rule pointer, Q-65 refinement / #183 (2026-10-14):** the issue classifications below are unchanged. katlangorg/katlangnet#183 (owner decision) refines Q-65's line-final star subrule: an attached line-final `expr*` (EOF included) is a spread that completes the expression; a detached `expr *` is multiplication. This reinstates, for line-final stars, #140's attached/detached newline rule that #161 reversed; #161's same-line classification and marker attachment law remain current. Where entries below say every physical line-final star multiplies, EOF is not a spread boundary, `7*` at EOF is a missing operand, or `A*` newline `B` multiplies, those statements describe their dates. Dated notes say so at #140, #161 and in the star-layout lineages.

> **Current-rule pointer, post-snapshot closed issues (Constitution audit, 2026-10-23):** the issue classifications below are unchanged, and the index still ends at #170 (snapshot 2026-09-27, `a2700f4`); issues closed later are mapped here to their decisions and current rules, not archaeologized (closing dates are GitHub's, UTC). #171 (closed 2026-09-28, `3e57a08d`), PV-02: module elaboration transforms only directives (MOD-07). #172 (2026-09-28, `33c99718`), Q-01 / PV-04: at-most-once argument value evaluation (CALL-06; under Model C NEED-01..03). #174 (2026-09-29, `abe13834`), Q-04 / PV-01: automatic forwarding reuses existing parameter bindings only (PAR-07; PAR-04, PAR-05, FWD-02). #175 (2026-09-28, `13196f8d`), Q-03 / PV-03: a callable that accepts zero supplied arguments is read, not lifted (PAR-07, FWD-02; PROP-04, PROP-05, CALL-05). #176 (2026-09-30, `4bea2e4c`): structural pattern kinds and `SingletonSequencePattern` (PAT-06, PAT-08), by-name bare forwarding and written calls as written (FWD-02, PAR-04), and exact aliases, whose wrapper was superseded on 2026-10-01 by binding indirection (FWD-02, `9a8cbd11`); it kept by-name formula lifting, whose Q-72 reversal is the issue-less `c719f43b` (2026-09-29; PAR-07). #177 (2026-09-30, `d6b88a95`): the unified formula-lifting law (PAR-07; Q-11/Q-12/Q-13 collapse into it for formulas). #178 (2026-10-10, `5041bffe`), Q-25 Option B: `map` and `reduce` callbacks return their ordinary call result (HO-03, VAL-06). #179 (2026-10-11, `516a381c`), Q-37: the outermost successful evaluation owns the entry (PROP-09, PROP-04). #180 (2026-10-11, `3e244f91`), Q-80 / STR-02: double-quoted escapes and interpolation (SYN-15, VAL-12, VAL-02). #181 (2026-10-12, `c22662ec`), Q-81: variadic postfix selection, colon retired (SEQ-04, SEQ-05). #183 (2026-10-15, `28bb5e84`, `5f0e498b`): Q-65 grammar-priority newlines and the line-final star refinement (SYN-08, SYN-11, SYN-12, OP-01; the pointer above). #184 (2026-10-17, `9cb38612`), CallReference S1/S2: `meta` parameters, `R.Invoke()`, `R.Arguments` (VAL-01, VAL-09, VAL-12, DOT-01, DOT-08 and the dated S1/S2 amendments). #185 (2026-10-18, `2febbb47`), LOOP-CF1: condition-first `while` (LOOP-06; LOOP-03, LOOP-08). #186 (2026-10-19, `b45871f7`): META-S3-1 `R.Algorithm` callable projection and, in the same commit, META-S3-2 runtime-target callable aliases (DOT-08, DOT-09, NEED-06, FWD-02 and the dated S3-1/S3-2 amendments). #64 (open at the snapshot; closed 2026-10-20, `9c8623f2`), META-S3-3: `while(meta step)` / `repeat(meta step, count)` (LOOP-01, LOOP-05, LOOP-08). #187 (2026-10-20, `7d6a58be`), META-S3-4: every written invocation is capturable (DOT-01, DOT-09, LOOP-01; `call-by-need.md` CR-2, CR-13). #189 (2026-10-22, `586f32f3`), CACHE-PUB-1: a qualifying zero-supply `A()` that finds the entry empty establishes it (PROP-06, PROP-09, PROP-04). #173 and #182 are pull requests, not issues: #173 (merged 2026-09-28, `a4ae04a2`) carries the Q-02 / PV-06 terminal resource-limit rule (RUN-03); #182 (merged 2026-10-12, `6bf2f624`) fixes release publication and decides nothing about the language. Still open: #157 (static deconstruction mismatch) and #169 (scope-visibility balance, non-semantic), listed with #33, #47 and #85 in `open-questions.md` Q-70's post-release backlog (#36 there as Q-64's duplicate), and #188 (`do` execution rows, a future idea opened 2026-10-20), added to that row by this audit. Some entries below spell loops `while(step, init…)`, `repeat(step, n, init…)`, `Step.while(a…)` or `Step.repeat(n, a…)`, or cite Lean `builtinAcceptsArity` `n >= 2` / `n >= 3` and `evalInitialLoopStateSlots`. Those forms are retired with no compatibility form: they are now exact-arity `ArityMismatch`, and Lean arity is exact 1 / 2. Their state, binding and flag semantics survive under `Step(a…).while` / `Step(a…).repeat(n)`, as amended by Q-09b (a configured limit no longer disables planning or fusion), Q-23 (any callable is a step), Q-24 (no patterned packing), Q-26 (a loop result is one value) and LOOP-CF1. Where entries say `A()` never populates an entry, CACHE-PUB-1 supersedes that clause.

> **Current-rule pointer, post-snapshot closed issue #197 (2026-11-18):** the issue classifications below are unchanged, and the index still ends at #170. #197 (opened 2026-11-11, closed as completed 2026-11-12, `1d3e1354`), "Replace DisplayDecimals with MinDecimalPlaces and MaxDecimalPlaces": two independent, display-only settings, `MinDecimalPlaces` and `MaxDecimalPlaces`, each an integer from 0 to 99, set as a top-level program property or by the host (`RunOptions`, `--min-decimal-places`, `--max-decimal-places`). When the program and the host set the same property, the smaller value applies, and a minimum above the maximum is an error. `DisplayDecimals`, `--display-decimals`, `RunOptions.DefaultDisplayDecimals`, `RunOptions.MaxDisplayDecimals` and `RunResult.WithHostDisplayDecimals` are removed with no compatibility path, and `DisplayDecimals` is an ordinary name. The issue says it replaces #118 (the 2026-11-15 catch-up pointer above). The current rule is `constitution.md` RUN-06, with `open-questions.md` Q-10 and `decision-lineages.md` § Q-10 owner extension. A second commit, `65885c4f` ("Remove string interpolation and double-quoted literals (fixes #197)"), also cites #197, but the issue's text does not mention that change: it is the owner's STR-03 decision of 2026-11-11, which the catch-up pointer above maps under #180.

## Scope and method

- **Closed issues inspected:** 155 (every closed issue, #1–#170; numbers not listed are open issues or pull requests). Bodies and **all comments** were read, together with timeline cross-references and every commit whose subject names the issue (513 commits in `git log --all`).
- **Language/design-relevant:** 138 of 155 (semantic, syntactic, evaluation, resolution, value-model, runtime-contract, or public-language significance). The rest are implementation/performance, host API/packaging, web-UI accessibility, or documentation work.
- **Method:** 15 chronological batches, each classified against the CURRENT repository (language-rule docs, `lean/KatLang.lean`, tests, tutorial, EBNF) and, where behaviour was in doubt, re-executed with a differential probe runner (5 execution paths: public sync engine, public async engine, generic evaluator, optimized evaluator, forced async twin). A second pass reconstructed **decision lineages** per semantic area (15 areas, 145 chains) from issues, commits, and dated maintainer session notes, and audited the batch classifications: 67 corrections/addenda were reported, 18 of which changed a classification label (marked *revised in lineage review* on the entry).
- **Rule:** a closed issue is not automatically current law. Where a later issue superseded, narrowed, reversed, or removed a decision, the entry says so and names the successor. Bug reports are recorded for the semantics they reveal, not for the broken behaviour they describe.
- Full lineage write-ups (per area, with superseded-decision lists and unresolved questions) are in the companion artifact `decision-lineages.md`.

## Classification legend

| Classification | Meaning | All issues | Language-relevant |
|---|---|---|---|
| CURRENT | the decision is current law as decided | 51 | 51 |
| PARTIALLY CURRENT | part survives; the entry states exactly which part | 42 | 42 |
| SUPERSEDED | replaced by a later decision (named) | 21 | 20 |
| REMOVED | the feature/syntax no longer exists | 6 | 6 |
| BUG FIX / REAFFIRMED EXISTING RULE | restored or enforced an already intended rule | 18 | 16 |
| IMPLEMENTATION ONLY | performance/internal work without language meaning | 6 | 1 |
| DOCUMENTATION ONLY | documentation/examples only | 2 | 0 |
| HOST/API ONLY | host API, packaging, tooling, UI | 9 | 2 |
| UNCERTAIN | evidence insufficient (none remain) | 0 | 0 |
| **Total** | | **155** | **138** |

## Issue index

| # | Title | Lang. | Classification | Topics | Superseded by / surviving rule |
|---|---|---|---|---|---|
| [#1](https://github.com/katlangorg/katlangnet/issues/1) | Inline parametrized algorithm call syntax broken in v0.7+ | yes | CURRENT | SYN ALG HO CALL | A same-line {...} after a call target is one AlgorithmExpr argument slot: Algo{e} is exactly Algo({e}). |
| [#2](https://github.com/katlangorg/katlangnet/issues/2) | Fix combining operator ';' | yes | REMOVED | SYN SUP SEQ | superseded by #75, #104, #125 (ad75720), #140 postfix * spread. ';' is not expression syntax (UnsupportedSemicolon); concatenation is written with spread inside a capture, e.g. (A*, B*). |
| [#3](https://github.com/katlangorg/katlangnet/issues/3) | Check conditional loop simplified example | yes | CURRENT | LOOP VAL SEQ BOOL | while(Step, init...) runs Step; its last output is a Boolean continuation flag (true continues with the new state, false returns the current state); call results are one value, never auto-trimmed. |
| [#4](https://github.com/katlangorg/katlangnet/issues/4) | Fix KatLang examples that worked in v06 and does not work in v07+ | no | DOCUMENTATION ONLY | COLL LOOP |  |
| [#5](https://github.com/katlangorg/katlangnet/issues/5) | Decide about adding explicit property Output (continue to support implicit output definition). | yes | SUPERSEDED | SYN PROP | superseded by #63 (8cf85f5). Every non-definition expression row contributes output, rows may interleave with definitions, and Output/output are ordinary identifiers. |
| [#6](https://github.com/katlangorg/katlangnet/issues/6) | Check 'open' builtin design | yes | CURRENT | MOD SYN | Each algorithm has at most one open declaration, placed before any property or output row, with a comma-separated target list; open 'url' is sugar for load elaboration. |
| [#7](https://github.com/katlangorg/katlangnet/issues/7) | Broken result grouping | yes | CURRENT | VAL SEQ RUN | Root/body output accumulation is not a value boundary: comma slots emit separate rows, while a named property/call result is one sequence value displayed in parentheses. |
| [#8](https://github.com/katlangorg/katlangnet/issues/8) | KatLang web page produces error on numbers exceeding decimal limit | yes | BUG FIX / REAFFIRMED EXISTING RULE | OP SYN | An unrepresentable number literal is the front-end diagnostic NumberLiteralTooLarge; literals with more than 34 significant digits are rounded. |
| [#9](https://github.com/katlangorg/katlangnet/issues/9) | Math.Tan abnormal results | yes | CURRENT | OP | Math functions return full-precision approximations of the rounded argument; tan(Pi/2) is a huge finite value, not an error. |
| [#10](https://github.com/katlangorg/katlangnet/issues/10) | Remove self | yes | REMOVED | RES SYN | There is no self construct; self is an ordinary identifier and recursion/lookup is by name. |
| [#11](https://github.com/katlangorg/katlangnet/issues/11) | Trigonometric functions lose precision due to Double conversion | yes | SUPERSEDED | OP FORMAL | superseded by #153 (7f0bab0). Math functions compute natively in Decimal128 and are never rounded to nice values (sin(pi) is a ~1e-34 residue); transcendental results are only quantum-canonicalized. |
| [#12](https://github.com/katlangorg/katlangnet/issues/12) | Algorithm (accepting one or more parameters) call without arguments should result in error | yes | CURRENT | CALL PAR PROP TOOL | A callable satisfies a zero-argument value demand iff an ordinary call with zero supplied arguments can bind it; otherwise the bare reference is an ArityMismatch at its span. |
| [#13](https://github.com/katlangorg/katlangnet/issues/13) | Large Number should be able to be handled, for instance, in scientific notation, whatever | yes | SUPERSEDED | OP SYN | superseded by #97 (cadb441), #153 (7f0bab0). Numbers are Decimal128 (34 digits, exponent about +-6144); arithmetic overflow yields signed Infinity as an ordinary value; scientific literals like 2e30 are supported. |
| [#14](https://github.com/katlangorg/katlangnet/issues/14) | Dot-call syntax is not working on constants | yes | CURRENT | DOT CALL | When the receiver has no structural member of that name, R.F(args) is exactly F(R, args) for any receiver expression, composing along chains. |
| [#15](https://github.com/katlangorg/katlangnet/issues/15) | Two argument form builtin if | yes | REMOVED | BOOL CALL VAL | superseded by #49 (93a036d), SYN-01 (a8bcae7). if has exactly one signature if(condition, whenTrue, whenFalse); any other count is an evaluation-time ArityMismatch, and () is not an operator identity. |
| [#16](https://github.com/katlangorg/katlangnet/issues/16) | Implement conditional algorithms feature. | yes | PARTIALLY CURRENT | PAT CALL PAR | Clauses Name(patterns) = body with one name form a conditional algorithm tried top to bottom; no match is an error; `when` syntax was replaced by clause heads (#26/#27). |
| [#17](https://github.com/katlangorg/katlangnet/issues/17) | Think how to simplify KatLang code execution from C# | no | HOST/API ONLY | API |  |
| [#18](https://github.com/katlangorg/katlangnet/issues/18) | Non-public algorithms cannot be opened | yes | CURRENT | MOD RES | open Name may target a lexically visible private head, but open-provided names and dotted open steps select only PUBLIC members. |
| [#19](https://github.com/katlangorg/katlangnet/issues/19) | Property is not seen when used inside conditional algorithm body | yes | BUG FIX / REAFFIRMED EXISTING RULE | PAT RES | Clause bodies are lexical children of the family's owner and see its sibling and ancestor properties. |
| [#20](https://github.com/katlangorg/katlangnet/issues/20) | Consider supporting string literals in conditional algorithm pattern matching and in algorithm calls | yes | CURRENT | VAL PAT CALL | Strings are first-class values with exact equality and no ordering or coercion, and string literals are clause patterns matching by exact value. |
| [#21](https://github.com/katlangorg/katlangnet/issues/21) | In conditional algorithm branch - all parameters should be declared in when (...) braces and Grace~ operator should be forbidden | yes | CURRENT | PAT PAR SYN | Clause patterns and every explicit parameter list are closed: unresolved free names are UndeclaredIdentifier and Grace in a clause/closed list is InvalidGraceMarker. |
| [#22](https://github.com/katlangorg/katlangnet/issues/22) | Wrong Grace~ error location | no | BUG FIX / REAFFIRMED EXISTING RULE | TOOL PAT |  |
| [#23](https://github.com/katlangorg/katlangnet/issues/23) | Pattern matching checks if all parameters are explicit only for branches which are used in calls | yes | CURRENT | PAT PAR | Undeclared identifiers in any clause body are front-end errors that block evaluation, whether or not that clause is ever called. |
| [#24](https://github.com/katlangorg/katlangnet/issues/24) | All branches of the same conditional algorithm must have the same top-level pattern arity | yes | CURRENT | PAT CALL | Clauses of one family must share top-level pattern arity (BranchArityMismatch) and top-level output arity; arity never distinguishes branches. |
| [#25](https://github.com/katlangorg/katlangnet/issues/25) | Restrict conditional algorithm all branches to have the same top level output shape | yes | CURRENT | PAT SEQ | All clauses of one conditional algorithm share one top-level output arity (written output slots); a pair must be written as one captured slot. |
| [#26](https://github.com/katlangorg/katlangnet/issues/26) | Add support for conditional algorithm syntax without keyword 'when' | yes | CURRENT | PAT SYN | Conditional algorithms are written as same-name clauses Name(pattern) = body (EBNF ClauseDefinition), elaborated as a whole family by elaborateClauseGroup. |
| [#27](https://github.com/katlangorg/katlangnet/issues/27) | Remove keyword 'when' from conditional algorithm definition syntax | yes | CURRENT | SYN PAT | 'when' is not a keyword (Lexer KeywordDefinitions: div mod and or xor not public open true false); clauses are Name(pattern) = body. |
| [#28](https://github.com/katlangorg/katlangnet/issues/28) | Error is not detected in the inner call | no | BUG FIX / REAFFIRMED EXISTING RULE | TOOL RUN | Evaluation errors keep an inner span when present; an outer span is attached only if missing. |
| [#29](https://github.com/katlangorg/katlangnet/issues/29) | Property redefinition is ignored, but should cause error | yes | CURRENT | PROP PAT RES | A second definition of a name in one algorithm is an error, and two match-equivalent branch patterns in one clause family are an error. |
| [#31](https://github.com/katlangorg/katlangnet/issues/31) | Improve type mismatch error messages | yes | PARTIALLY CURRENT | OP CMP TOOL | superseded by #127 (structural equality: different kinds compare false), #165 (total equality reaffirmed). String/Boolean misuse in arithmetic/ordering is typeMismatch, but == and != are total structural equality returning false across kinds. |
| [#32](https://github.com/katlangorg/katlangnet/issues/32) | Consider implementing builtin support for number to string conversions | yes | CURRENT | DOT VAL OP | The .string intrinsic (dispatched before structural members and lexical fallback) converts one numeric value to text, reads a named receiver through the property cache, and rejects arguments. |
| [#34](https://github.com/katlangorg/katlangnet/issues/34) | Add aggregation builtins over outputs: sum, min, max, avg, count | yes | CURRENT | COLL DOT VAL | Collection builtins are fixed-arity with one collection parameter read through a one-level post-binding view; sum(1, 2, 3) is an arity error and A.sum is sum(A). |
| [#35](https://github.com/katlangorg/katlangnet/issues/35) | Add built-in range for sequence generation | yes | PARTIALLY CURRENT | COLL SEQ | range(start, end) returns one exact list of the whole numbers from start to end inclusive (counting down when start > end). |
| [#37](https://github.com/katlangorg/katlangnet/issues/37) | Add collection transforms over multi-output values: map, filter, and reduce | yes | PARTIALLY CURRENT | HO COLL | map/filter call f(element), reduce calls f(element, accumulator), each element is ONE ordinary argument, results are exact lists, filter predicates must return Boolean. |
| [#38](https://github.com/katlangorg/katlangnet/issues/38) | bug: Grace~ operator is ignored when applied on parameter which is callable algorithm | yes | BUG FIX / REAFFIRMED EXISTING RULE | PAR HO | Postfix/prefix Grace on a bare-name callee occurrence is ordinary Grace (effective only on an unfixed implicit parameter, F10). |
| [#39](https://github.com/katlangorg/katlangnet/issues/39) | bug: Conditional algorithm does not work well -- i suppose it do not like parameter call in conditional algorithm branch | yes | CURRENT | PAT CALL HO PAR | A same-name clause group with exactly one clause whose head is a capture/sequence-value parameter pattern is an ordinary Algorithm.mk; otherwise the family is conditional. |
| [#40](https://github.com/katlangorg/katlangnet/issues/40) | Add foreach iteration over multi-output collections | yes | CURRENT | LOOP HO COLL | There is no foreach builtin; collection iteration is map, filter, reduce, repeat, while. |
| [#41](https://github.com/katlangorg/katlangnet/issues/41) | Predicate returning value should be single atomic value 0 or 1 | yes | PARTIALLY CURRENT | BOOL HO COLL | superseded by #165 (first-class Booleans; numeric truthiness removed). A predicate result must be one Boolean (Result.asBool?: a Boolean or redundant singleton around one); numbers and multi-item values are typeMismatch. |
| [#42](https://github.com/katlangorg/katlangnet/issues/42) | Optimize repeated property evaluation with per-run memoization | yes | PARTIALLY CURRENT | PROP RUN FORMAL | superseded by #170 (caching by semantic binding identity, observable semantics), #110 (A vs A() fresh evaluation). A zero-parameter property is evaluated once per run per resolved binding and reused by every consumer; A() is a fresh evaluation that neither reads nor writes the entry. |
| [#43](https://github.com/katlangorg/katlangnet/issues/43) | Need to improve pow operator ^ precision | yes | PARTIALLY CURRENT | OP | superseded by #153 (Decimal128 core numeric type, 7f0bab0), commit ec48b91, commit 869c1bc. ^ is computed in Decimal128 (DelegatedPower, integer-power accuracy, log1p band); zero to a negative exponent is an error; details are a C#-only numeric tier. |
| [#44](https://github.com/katlangorg/katlangnet/issues/44) | Improve error messages | yes | PARTIALLY CURRENT | TOOL |  |
| [#45](https://github.com/katlangorg/katlangnet/issues/45) | Add collection utility builtins for more intuitive everyday use | yes | PARTIALLY CURRENT | COLL SEQ | order/orderDesc/distinct/first/last/take/skip/contains are fixed-arity prelude builtins; producers return exact lists, first/last select one value, contains returns Boolean; range stays arity 2. |
| [#46](https://github.com/katlangorg/katlangnet/issues/46) | Improve KatLang generator | no | DOCUMENTATION ONLY | TOOL |  |
| [#48](https://github.com/katlangorg/katlangnet/issues/48) | Decide if some Math functions can be made available directly without prefix Math. | yes | SUPERSEDED | MOD RES OP | superseded by #154 (predefined lower-camel-case Math aliases, b3738b9). Every Math member has a shadowable lower-camel-case prelude alias (sqrt, round, pi, ...); canonical PascalCase names live only in Math; no implicit open Math. |
| [#49](https://github.com/katlangorg/katlangnet/issues/49) | Think about removing support of 2 argument 'if' builtin | yes | PARTIALLY CURRENT | BOOL CALL SYN | Builtin if is an ordinary prelude binding of arity 3 with a Boolean condition, lazy in the unselected branch; wrong arity is an evaluation-time ArityMismatch. |
| [#50](https://github.com/katlangorg/katlangnet/issues/50) | Implement reusable semantic-analysis infrastructure for editor tooling | no | HOST/API ONLY | TOOL API |  |
| [#51](https://github.com/katlangorg/katlangnet/issues/51) | Implement support for static string-literal aliases in 'open' targets | yes | CURRENT | MOD | open targets are resolve / argumentless dot path / block / string-literal load sugar; a string-valued property opened by name provides no names. |
| [#52](https://github.com/katlangorg/katlangnet/issues/52) | Cleanup Output semantics: forbid external Output usage and require parameters on algorithm level | yes | PARTIALLY CURRENT | SYN PROP CALL | superseded by #63, 8cf85f5. Output is an ordinary identifier (explicit Output removed by #63); an algorithm is called through its own parameter list. |
| [#53](https://github.com/katlangorg/katlangnet/issues/53) | filter operation fails when arguments for filter call are received as enclosed property parameters | yes | BUG FIX / REAFFIRMED EXISTING RULE | HO CALL PAR FWD | A parameter binds on value and/or algorithm channel; an invoking builtin slot reads a forwarded parameter's algorithm channel; a sequence argument is one value. |
| [#54](https://github.com/katlangorg/katlangnet/issues/54) | Preserve ancestor implicit-parameter capture in nested properties, but make captured and conditional nested properties local-only | yes | PARTIALLY CURRENT | RES PAR PROP PAT MOD | Members requiring ancestor-owned names are selected normally then usable only where an activation of every required owner is lexically available (K1-08); conditional-algorithm properties are never public. |
| [#56](https://github.com/katlangorg/katlangnet/issues/56) | length is inconsistent with count on computed collections | yes | PARTIALLY CURRENT | COLL SEQ | superseded by #59, 04fedfe. count(collection) counts the one bound collection's items one level; no arity/length builtin; arity survives only as maintainer terminology. |
| [#57](https://github.com/katlangorg/katlangnet/issues/57) | Decide what to do with builtins accepting list in input | yes | SUPERSEDED | COLL CALL SUP | superseded by #135, 0ca55e9. Collection builtins take ONE fixed collection argument; order(3, 4, 2) is an ArityMismatch; spread items must be re-grouped, e.g. order((A*, B*)). |
| [#58](https://github.com/katlangorg/katlangnet/issues/58) | Test how unwrapping works with builtins, especially count and arity | yes | SUPERSEDED | COLL SEQ DOT HO VAL | superseded by #135, #168, #167, 874625a, 702e7d7. count((1, 7)) is 2; redundant parens are syntax; selection returns the stored element as one value; callback element is one ordinary argument; dot-call = plain call. |
| [#59](https://github.com/katlangorg/katlangnet/issues/59) | Investigate if arity should be made full citizen of KatLang builtins | yes | CURRENT | COLL RES | There is no arity builtin; builtins are ordinary prelude bindings resolved by identity (SYN-05). |
| [#60](https://github.com/katlangorg/katlangnet/issues/60) | Regression related to group unwrapping | yes | BUG FIX / REAFFIRMED EXISTING RULE | SEQ COLL DOT | Selection returns the stored element as one value and count opens its bound collection one level, so (Data:0).count is 5. |
| [#61](https://github.com/katlangorg/katlangnet/issues/61) | Passing an expression as an argument should not implicitly spread its emitted values into the surrounding sequence | yes | PARTIALLY CURRENT | SUP CALL COLL SEQ | superseded by #125, #140, #135. Every non-spread argument slot is exactly one item; only postfix expr* opens a value (one level). |
| [#62](https://github.com/katlangorg/katlangnet/issues/62) | Think about improving combining operator performance by moving its processing to lexer when possible | no | IMPLEMENTATION ONLY | SYN RUN | superseded by #125.  |
| [#63](https://github.com/katlangorg/katlangnet/issues/63) | Research if explicit Output is still needed | yes | CURRENT | SYN PROP | Algorithm output is its expression rows; there is no output keyword; Output/output are ordinary identifiers. |
| [#65](https://github.com/katlangorg/katlangnet/issues/65) | Improve error reporting for reduce builtin call with less arguments than required | no | SUPERSEDED | TOOL COLL | superseded by #135. reduce(collection, reducer, initial) is fixed-arity; wrong counts are ordinary ArityMismatch naming the signature. |
| [#66](https://github.com/katlangorg/katlangnet/issues/66) | Introduce shared AST walker and small reusable helpers in C# front-end passes | no | IMPLEMENTATION ONLY | TOOL |  |
| [#67](https://github.com/katlangorg/katlangnet/issues/67) | Make the C# front-end/elaboration boundary explicit | no | HOST/API ONLY | API TOOL | Parser.Parse/KatLangEngine run the complete pipeline; elaboration stages are internal (Elaboration boundary). |
| [#68](https://github.com/katlangorg/katlangnet/issues/68) | Replace string-based evaluator error context with structured error context | no | HOST/API ONLY | TOOL API | ErrorContext is a public closed record hierarchy attached via EvalError.WithContext. |
| [#69](https://github.com/katlangorg/katlangnet/issues/69) | Bug sum(P) and sum(range(1, 100)) is failing | yes | BUG FIX / REAFFIRMED EXISTING RULE | COLL CALL DOT | A collection builtin binds one collection argument and reads it through the one-level post-binding view; sum(range(1, 100)) is 5050. |
| [#70](https://github.com/katlangorg/katlangnet/issues/70) | Grouping in conditional algorithm is broken | yes | CURRENT | PAT CALL | All clauses of a family share one top-level pattern arity; a nested group pattern counts as one slot. |
| [#71](https://github.com/katlangorg/katlangnet/issues/71) | Sequence builtins should preserve comma argument boundaries and flatten only via explicit combining operator usage ';' | yes | PARTIALLY CURRENT | SUP COLL SEQ SYN | superseded by #125, #140, #135, #167. No builtin silently unfolds an argument; collection builtins open their one bound collection one level; flatten via explicit expr*; selection returns stored element. |
| [#72](https://github.com/katlangorg/katlangnet/issues/72) | Remove support of variadic parameters | yes | SUPERSEDED | VAR COLL SUP DOT | superseded by 4367f57, #135. Collection builtins are fixed-arity with one collection (#135); symmetry via dot-call passing a value; user collecting parameters exist. |
| [#73](https://github.com/katlangorg/katlangnet/issues/73) | Research how to add variadic parameter as KatLang feature | yes | PARTIALLY CURRENT | VAR PAR CALL DOT FWD SYN | superseded by #138, #139, #140, #167, 702e7d7. One collecting *name per level collects exactly its allocated arguments as one exact list; a lone sequence argument/receiver is one item; aliases may infer a collecting parameter. |
| [#74](https://github.com/katlangorg/katlangnet/issues/74) | Fix Extension property call (dot-call) receiver boundary semantics | yes | PARTIALLY CURRENT | DOT CALL VAR | R.F(args) is exactly F(R, args); the receiver's item count never satisfies arity; only R*.F opens it, for every callee shape. |
| [#75](https://github.com/katlangorg/katlangnet/issues/75) | Redesign combining ';' operator to 'result join' operator | yes | SUPERSEDED | SYN SUP SEQ | superseded by #104, #125, #140, ad75720. ';' is not expression syntax (UnsupportedSemicolon); postfix spread expr* opens exactly one level; spread of an output-less operand is SpreadMissingOutput. |
| [#76](https://github.com/katlangorg/katlangnet/issues/76) | Bug: count fails on empty sequence | yes | BUG FIX / REAFFIRMED EXISTING RULE | COLL DOT VAL | An empty value is one visible argument, never an omitted one; filter with no survivors is [] and its count is 0. |
| [#77](https://github.com/katlangorg/katlangnet/issues/77) | Feature: Random Integer and Random Float | yes | PARTIALLY CURRENT | RAND OP | superseded by #109, 489b77f, 668ff3c. Math.Random/random(start, end) and Math.RandomInt/randomInt(start, end), half-open, whole-number integer bounds, one run-scoped host-seedable stream. |
| [#78](https://github.com/katlangorg/katlangnet/issues/78) | Bug implicit parameter c not detected as implicit argument in Discriminant property call | yes | PARTIALLY CURRENT | PAR DOT OP | Registry-strict Math argument positions lift referenced properties' implicit parameters; order is first semantic occurrence (b, a, c here). **Current rule since 2026-09-30:** every value role of the unified formula-lifting law lifts (PAR-07), Math arguments among them; the order is unchanged. |
| [#79](https://github.com/katlangorg/katlangnet/issues/79) | Stack overflow when Recursion with list | yes | BUG FIX / REAFFIRMED EXISTING RULE | DOT CALL PROP RUN | x.f is f(x) through one call funnel; local-only property cache is per activation; dot chains are nested calls with EvaluationStackExhausted backstop. |
| [#80](https://github.com/katlangorg/katlangnet/issues/80) | variadic parameters and reduce | yes | PARTIALLY CURRENT | COLL HO VAR CALL | reduce(collection, reducer, initial) is fixed-arity; the reducer is called as F(element, accumulator); AoC example yields 31. |
| [#81](https://github.com/katlangorg/katlangnet/issues/81) | Allow empty result definition directly in KatLang code | yes | SUPERSEDED | VAL SEQ SYN | superseded by #128 (73cdba2): removes `empty`, makes `()` the empty sequence value, #143: parentheses are a value-capture boundary, not an Algorithm, #168: `(())` is `()`. `()` is the empty sequence value, a real visible value; `{}` is a no-output algorithm, and forcing it as a value is a MissingOutput error whose message suggests `()`. |
| [#82](https://github.com/katlangorg/katlangnet/issues/82) | Line continuation using backslash | yes | CURRENT | SYN | A trailing binary/comparison operator, `,`, `:`, `.`, prefix `-`/`not`, or a definition `=` continues onto the next line (but never into a declaration head); postfix continuations are same-line only; `\` is an unexpected character. |
| [#83](https://github.com/katlangorg/katlangnet/issues/83) | Execution of KatLang code without output should return error | yes | CURRENT | RUN VAL API | A root with no output rows is Error.missingOutput (Lean evalProgramOutput / evalAlgOutputSlots); KatLangEngine projects it to RunResult.NoProgramOutput, while `()` is a successful visible empty row. |
| [#86](https://github.com/katlangorg/katlangnet/issues/86) | Optimize while / repeat loops with pre-bound loop execution frames | yes | IMPLEMENTATION ONLY | LOOP RUN PROP | Optimized loops must be observationally identical to generic Lean loop semantics: next-state outputs are computed from the old state and committed together; local-only temps are memoized per iteration. |
| [#87](https://github.com/katlangorg/katlangnet/issues/87) | Optimize sequence pipeline filter(...).count by fusing into count-where execution | no | IMPLEMENTATION ONLY | COLL HO RUN | Filter-count fusion is a C#-only optimization, needs no Lean change, and requires equivalence with the generic path (SEMANTIC-ALIGNMENT.md row 23). |
| [#88](https://github.com/katlangorg/katlangnet/issues/88) | The behaviour of `count` seems to be eccentric. | yes | SUPERSEDED | VAL CALL VAR COLL SUP | superseded by #132/#135: count reads the bound collection through a one-level view, #138/#140: `*list` collects an exact list, #167 + 702e7d7 (C-full, values stay values): collectors never open an argument. `count` opens its one bound collection one level (builtinCollectionItems), so an ordinary parameter's `list.count` counts elements; a collecting parameter `*list` collects exactly the supplied  |
| [#89](https://github.com/katlangorg/katlangnet/issues/89) | Inline grouped dot-call receiver does not bind correctly to user-defined variadic parameter | yes | SUPERSEDED | DOT VAR CALL SUP | superseded by #167 (68b3607) + 702e7d7: dot-call passes a value; the collector collects the receiver as one item, #168: `((…))` is no longer distinct from `(…)`. Dot-call passes the receiver as one ordinary leading argument whatever its spelling (`R.F(a)` ≡ `F(R, a)`); only the fluent spread `R*.F(a)` supplies its items. |
| [#90](https://github.com/katlangorg/katlangnet/issues/90) | Improve result display to make grouping structure visible | no | HOST/API ONLY | TOOL API VAL | Engine display renders a sequence row as `(…)`, a list as `[…]`, and multiple emitted values as separate rows. |
| [#91](https://github.com/katlangorg/katlangnet/issues/91) | Add ungroup builtin for one-level group removal | yes | SUPERSEDED | SEQ SUP COLL | superseded by #98: renamed to content, #129 (7458502): content removed in favour of postfix spread, #124/#140: spread is the postfix unary `*`. One-level opening is the postfix spread marker `v*` (spreadItems: one sequence or list boundary, never recursive); `atoms` is the separate recursive projection returning one list. |
| [#92](https://github.com/katlangorg/katlangnet/issues/92) | Recursive algorithms do not work with `map` | yes | BUG FIX / REAFFIRMED EXISTING RULE | HO CALL RES PAR | A bound parameter owns its name on every channel: each binding site shadows the callee's parameter names out of the value, counted, and algorithm tiers (EvalCtx.bindParameters / ShadowInheritedParameterEnvironments). |
| [#93](https://github.com/katlangorg/katlangnet/issues/93) | Why is built-in algorithms like `sum`, and `Math`, not visible inside "libraries" | yes | BUG FIX / REAFFIRMED EXISTING RULE | MOD RES | Opened members evaluate in their declaring lexical chain with the prelude as the global base and are isolated from the opener; `open` must precede properties and output rows. |
| [#94](https://github.com/katlangorg/katlangnet/issues/94) | `Math.Atan2` should be added? | yes | CURRENT | OP | `Math.Atan2(y, x)` and its alias `atan2` compute the two-argument arctangent; this is C#-only library surface (Lean does not model Math). |
| [#95](https://github.com/katlangorg/katlangnet/issues/95) | Implicit parameter and Collection Issue | yes | BUG FIX / REAFFIRMED EXISTING RULE | LOOP HO RES RUN | Generic and planned loop steps bind their state parameters through the one shadowing helper, so loop-state parameters shadow outer callback bindings; optimizations must be observationally identical. |
| [#96](https://github.com/katlangorg/katlangnet/issues/96) | Shouldn't it `Step.repeat(1, [PARAMETERS])` be equivalent to `Step([PARAMETERS])` ? | yes | PARTIALLY CURRENT | LOOP VAR SUP VAL | superseded by #125: the `;` join formulation removed, #139/#140: `history...` → `*history`. Each written initial loop argument is one state slot (a spread supplies its items); step outputs define the next slots; a collecting step parameter collects the current slots (`repeat(Step, 1, (1, 2))` with `Step(*xs) = xs.count` is 1). |
| [#97](https://github.com/katlangorg/katlangnet/issues/97) | Number Extension: support numbers in scientific notation | yes | CURRENT | SYN OP | Number = /[0-9](_*[0-9])*(\.[0-9](_*[0-9])*)?(e[+-]?[0-9](_*[0-9])*)?/ parsed into Decimal128; uppercase `E` and hex are not number literals. |
| [#98](https://github.com/katlangorg/katlangnet/issues/98) | Rename ungroup builtin to content | yes | REMOVED | SEQ SUP COLL SYN | superseded by #129 (7458502): content removed; postfix spread replaces it, #140: spread spelled `*`. No `content` builtin exists; one-level opening is the postfix spread marker `v*`. |
| [#99](https://github.com/katlangorg/katlangnet/issues/99) | Add variadic group destructuring in parameter patterns | yes | PARTIALLY CURRENT | PAT VAR LOOP SUP | superseded by #138/#140: syntax `(*xs)`, exact lists, parentheses-group-syntax / #168: the pattern opens the value, written-slot view deleted, S3 (Sep 2026): scalar one-item fallback at every group size, #125: `;` join in examples removed. A nested sequence-value pattern `F((*xs))` consumes one argument slot and opens that argument's VALUE one level (a sequence or list opens; a scalar is a one-ite |
| [#100](https://github.com/katlangorg/katlangnet/issues/100) | Unify callable signatures and binding layout metadata | no | IMPLEMENTATION ONLY | CALL VAR TOOL |  |
| [#101](https://github.com/katlangorg/katlangnet/issues/101) | Reconsider implicit final-argument unpacking in flat fixed calls | yes | CURRENT | CALL SUP VAL SEQ | A non-spread argument supplies exactly one item and a fixed parameter binds it whole; only the explicit spread Pair* opens it (Add(Pair) is ArityMismatch, Add(Pair*) is 30). |
| [#102](https://github.com/katlangorg/katlangnet/issues/102) | Support variadic accumulator-state binding in `reduce` callbacks | yes | SUPERSEDED | HO VAR COLL LOOP SUP | superseded by #167, commit 702e7d7 (C-full: deleted reducerAccumulatorSideHasTopLevelCollecting). reduce(xs, R, init) calls R(element, accumulator) as an ordinary two-argument call; Acc(x, *acc) collects [acc]; only an explicit pattern like Append(item, (*history)) opens the accumulator. |
| [#103](https://github.com/katlangorg/katlangnet/issues/103) | Add explicit result-stream spread operator for call argument supply | yes | SUPERSEDED | SUP SYN CALL DOT VAR | superseded by #104, #140. Postfix expr* is the only general opener; a comma is required after a spread (Sum(Values*, 7)); A*.F is F(A*) for any callee. |
| [#104](https://github.com/katlangorg/katlangnet/issues/104) | Consider replacing semicolon result join with ellipsis stream join | yes | PARTIALLY CURRENT | SUP SYN CALL VAR FWD SEQ | superseded by #122/#124 (infix join removed), #125 (semicolon removed again), #128 (empty removed), #138 (provenance forwarding removed, ab7d2f5), #140 (star spelling), #167 / commit 702e7d7 (variadic-slot opening removed). ; is not expression syntax (UnsupportedSemicolon); explicit postfix spread expr* is the only opener; a plain argument, property or block stays one boundary. |
| [#105](https://github.com/katlangorg/katlangnet/issues/105) | Regression in KatLang user-defined variadic dot-call receiver binding. | yes | SUPERSEDED | DOT VAR SUP CALL | superseded by #167, commit 68b3607, commit 702e7d7. R.F(args) is exactly F(R, args): (1, 2).Mean collects [(1, 2)]; only (1, 2)*.Mean opens the receiver. |
| [#106](https://github.com/katlangorg/katlangnet/issues/106) | Regression: variadic parameter forwarding now requires explicit sequence supply | yes | SUPERSEDED | FWD VAR CALL SUP | superseded by #138 (commit ab7d2f5), #140. A bare collected parameter passes one list; forwarding is explicit Target(items*). The front end inserts that spread only for implicit forwarding when both bindings collect. |
| [#108](https://github.com/katlangorg/katlangnet/issues/108) | Regression variadic parameter should work without sequence supply operator usage | yes | SUPERSEDED | FWD VAR PAT CALL SUP LOOP | superseded by #138 (commit ab7d2f5 removed VariadicStreamEnv), #140. No runtime stream provenance: forward a collected or pattern-collected list explicitly, e.g. FindNext(history*, pre1, pre2). |
| [#109](https://github.com/katlangorg/katlangnet/issues/109) | Remove `Math.RandInt` | yes | CURRENT | RAND OP | Math.RandomInt/randomInt(start, end) draws uniformly from [start, end) over whole-number bounds within ±1e34 with start < end, from the run's one seedable stream. |
| [#110](https://github.com/katlangorg/katlangnet/issues/110) | Concern random seed for `Math.Rand` | yes | CURRENT | PROP RAND CALL FORMAL RUN | A zero-parameter property is evaluated once per run for each resolved binding; `A()` bypasses only A's own entry, and nested reads keep their own cache rules whatever their purity. |
| [#111](https://github.com/katlangorg/katlangnet/issues/111) | Improve variadic calls with variadic-slot sequence supply | yes | SUPERSEDED | VAR SUP CALL DOT FWD | superseded by #125 (ad75720), #138 (ab7d2f5), #167 / 702e7d7 values stay values (sequences-lists-and-calls.md § Collecting parameters). Exact collector law: a non-spread argument supplies exactly one item whatever its value, and only the spread `v*` opens it, so `Qmean(Vector)` collects `[Vector]`. |
| [#112](https://github.com/katlangorg/katlangnet/issues/112) | Dot-call receiver expansion should follow flat variadic-slot allocation rules | yes | PARTIALLY CURRENT | DOT VAR CALL SUP | superseded by #167 / 68b3607 dot-call passes a value (reaffirms the equivalence), 702e7d7 exact collector law (replaces the variadic-slot supply half). `R.F(args)` is exactly `F(R, args)` and `R*.F` is exactly `F(R*)`; a collector binds the receiver as one item. |
| [#113](https://github.com/katlangorg/katlangnet/issues/113) | Dot-call trailing block parsing is accidentally whitespace-sensitive | yes | CURRENT | SYN DOT | A `(` or `{` after a callable on the same physical line is a call delimiter even across whitespace; a physical newline never continues a closed expression into a call. |
| [#114](https://github.com/katlangorg/katlangnet/issues/114) | Bare builtin callable aliases do not propagate implicit parameters | yes | CURRENT | PAR RES ALG CALL | A Math function referenced bare through the qualified `Math.X` or the prelude alias lifts its registry signature; a callable reached through `open` is never implicitly forwarded. **Current rule since 2026-09-30:** in a FORMULA every builtin, host operation, opened and dotted member lifts (the unified formula-lifting law, PAR-07); as a LONE row only a Math alias or bare `Math.X` is an exact alias, and whether other callables should be is open question Q-12. |
| [#116](https://github.com/katlangorg/katlangnet/issues/116) | Parser generates too many errors for from open statement | no | IMPLEMENTATION ONLY | MOD TOOL |  |
| [#117](https://github.com/katlangorg/katlangnet/issues/117) | Add reserved private metadata properties for KatLang libraries | yes | REMOVED | MOD RES SYN | superseded by c5c762e revert. Author, Version, Description and Name are ordinary property names with no special meaning. |
| [#118](https://github.com/katlangorg/katlangnet/issues/118) | Add display-only decimal formatting for final output | yes | CURRENT | RUN PROP API | One display-decimals setting per run: the root's declared property wins, even when invalid, else the host default, else canonical display; 0..99, midpoints away from zero, rendering only. |
| [#119](https://github.com/katlangorg/katlangnet/issues/119) | Parser: treat newline after postfix ... as continuation unless followed by explicit comma | yes | SUPERSEDED | SYN SUP | superseded by #122 (acbfa7d) removed the postfix newline continuation, #124 (4b32111) unary postfix supply, #140/#161 star syntax, SYN-07B. The spread marker `A*` is layout-independent: a following operand makes it multiplication, so a comma is required between a spread and a following item. |
| [#120](https://github.com/katlangorg/katlangnet/issues/120) | Output joining gives different results depending if is used property or inline expression | yes | PARTIALLY CURRENT | SYN VAL SEQ PROP | superseded by #122 (acbfa7d), #125 (ad75720) removed `;` and output joining. No output-join operator exists (`;` is UnsupportedSemicolon); a property reference is one value and behaves like its parenthesized body. |
| [#121](https://github.com/katlangorg/katlangnet/issues/121) | Support repeated bind names as equality constraints in patterns | yes | PARTIALLY CURRENT | PAT CALL CMP | A repeated name binds iff every pair of its contributions is compatible (equal values, same callable identity), decided order-independently after the range binds. |
| [#122](https://github.com/katlangorg/katlangnet/issues/122) | Design: split output joining and sequence supply semantics for `...` | yes | PARTIALLY CURRENT | SYN SEQ SUP VAL RUN | superseded by #125 (ad75720) removed `;` and flat output-stream joining, #140 (73648e9) replaced `...` with postfix `*`, #132 (9a4c70f) call results are one value. The spread marker (now postfix `*`) has one role and never joins or continues. Newline-separated rows are separate output slots, parenthesized groups stay whole values, top-level rows display on separate lines as presentation only, `;`  |
| [#123](https://github.com/katlangorg/katlangnet/issues/123) | Normalize implicit semicolon, call continuation, and sequence supply ... precedence | yes | PARTIALLY CURRENT | SYN MOD SUP SEQ CALL DOT | superseded by #125 (ad75720) removed `;` and output join, #160 (2b03c0b, SYN-07A) made same-line adjacency an error, #140 removed `...` chain absorption (spread applies only to its own operand), #63 (8cf85f5) removed `Output =`, #168 made `(F)(1)` a call. Postfix continuations (`(`/`{` call delimiters, `:`, `~`, binary operators) bind only on the same physical line; a newline never continues a clo |
| [#124](https://github.com/katlangorg/katlangnet/issues/124) | Make sequence supply postfix-only and unary internally | yes | PARTIALLY CURRENT | SUP SYN FORMAL SEQ | superseded by #140 (73648e9) `...` spelling replaced by postfix `*`, b568c66 renamed SequenceSupply to SequenceSpread, #125 (ad75720) removed output join, so `F(X...Y)` as one joined argument no longer applies (`X*Y` is multiplication). Spread is postfix-only with no right operand. It lowers to ONE unary node (C# Expr.SequenceSpread(Operand) / Lean sequenceSpread : Expr -> Expr) that evaluates its |
| [#125](https://github.com/katlangorg/katlangnet/issues/125) | Remove semicolon, unify comma/adjacency, and tighten variadic calls | yes | PARTIALLY CURRENT | SYN SEQ SUP VAR CALL DOT VAL COLL FORMAL | superseded by #126 (416e9c7) reversed strict variadic destructuring, d2837f4 builtin rest params made item-stream, #129 (7458502) removed .content, #135 (0ca55e9) re-established builtin strictness as a fixed collection parameter, #139/#140 (eab2468, 73648e9) replaced '...' with *name / expr*, #160 (2b03c0b, SYN-07A) removed same-line adjacency as a separator, #167 + 702e7d7 values-stay-values exac |
| [#126](https://github.com/katlangorg/katlangnet/issues/126) | Add movable-rest deconstruction and singleton-boundary item-stream binding | yes | PARTIALLY CURRENT | VAR PAT CALL SUP SEQ PAR VAL | superseded by e6c2bdc (2026-07-11) removed user-call singleton-boundary opening, #135 (0ca55e9) removed builtin singleton normalization, #138 rest collects exact lists, #139 lone rest assignment made valid; prefix ...name, #140 *name syntax, #167 / Sep 23 2026 values-stay-values (C-full). Deconstruction `x, *y, z = RHS` opens one lone sequence/list one level and allocates fixed front/back with one |
| [#127](https://github.com/katlangorg/katlangnet/issues/127) | Make equality structural for first-class sequence values | yes | CURRENT | CMP VAL SEQ OP FORMAL | ==/!= are total structural equality over all value kinds (sequences, lists, Booleans, strings), yielding true/false; ordering operators need numeric scalars; a spread cannot be a comparison operand. |
| [#128](https://github.com/katlangorg/katlangnet/issues/128) | Improve empty sequence representation | yes | PARTIALLY CURRENT | VAL SEQ SUP CMP COLL SYN | superseded by e6c2bdc (2026-07-11) canonicalized (()) to (), #168 parentheses group syntax, #134 exact nested empties via lists [[]], #135 collection builtins return lists, #138 empty rest is []. `()` is the empty sequence value displayed `()`, one visible slot, spread supplies zero items; `empty` is an ordinary identifier; `{}` has no output (MissingOutput); `(())` normalizes to `()`. |
| [#129](https://github.com/katlangorg/katlangnet/issues/129) | Remove `content` | yes | CURRENT | SUP COLL SYN | There is no `content` builtin; `content` is an ordinary non-reserved identifier and explicit postfix spread `v*` is the only value opener. |
| [#130](https://github.com/katlangorg/katlangnet/issues/130) | Unexpectedly lost sequence wrapping | yes | BUG FIX / REAFFIRMED EXISTING RULE | VAL BOOL SUP COLL FORMAL | `if` re-counts the selected branch via Result.valueCount, so a multi-output branch is one sequence value; only caller spread opens it. |
| [#131](https://github.com/katlangorg/katlangnet/issues/131) | `if` does not support spreading | yes | BUG FIX / REAFFIRMED EXISTING RULE | SUP CALL COLL SYN RES | superseded by #159 (0243678) removed the residual parse-time if arity gate (SYN-05). Every spread slot expands into ordinary argument slots before arity checking for any callable, builtin if included; no parser counts arguments by callee spelling (wrong-arity if is an evaluation-time ArityMismatch). |
| [#132](https://github.com/katlangorg/katlangnet/issues/132) | Make property/call boundaries return one sequence value | yes | PARTIALLY CURRENT | VAL SUP SEQ COLL VAR FWD FORMAL | superseded by #135 collection builtins return exact lists, #138 collecting bindings are exact lists; raw variadic supply env removed. Every property/call/builtin result boundary returns ONE value with count Result.valueCount; only explicit caller spread reopens; root/body output and while/repeat state keep multi-item counts; collection builtins and collecting bindings yield one exact list. |
| [#133](https://github.com/katlangorg/katlangnet/issues/133) | Fix non-canonical singleton sequence values produced by builtins | yes | PARTIALLY CURRENT | VAL SEQ COLL CMP FORMAL | superseded by #135 (0ca55e9) makeCollectionListResult exact lists, #135 single fixed collection parameter (distinct((), ()) is an arity error). Collection builtins materialize one exact list (a single survivor is [item], never erased), so every result is literal-writable and all observations agree; sibling boundaries are preserved. |
| [#134](https://github.com/katlangorg/katlangnet/issues/134) | Add exact immutable list values with [] syntax | yes | PARTIALLY CURRENT | VAL SEQ SUP CALL VAR SYN COLL FORMAL | superseded by #138 / ab7d2f5: rest/collecting bindings collect exact lists, reversing §9 'rest captures a canonical sequence', #139 / eab2468: lone collecting assignment `...items = RHS` made valid, reversing §10 'lone-rest assignment forbidden'; now `*items = [1, 2, 3]`, spec case list-lone-collecting-assignment, #140 / 73648e9: `value...` spread becomes `value*` and rest `items...`/`...items` be |
| [#135](https://github.com/katlangorg/katlangnet/issues/135) | Make collection builtins accept one fixed collection object and return exact lists | yes | PARTIALLY CURRENT | COLL CALL SEQ SUP VAL DOT HO VAR FORMAL | superseded by #138 (ab7d2f5): rest/variadic capture produces exact lists, reversing #135's sequence-centered scope guard, fa381ae: core arity algebra moved to exact-list rest, C-full 'values stay values' exact collector law (Sep 2026, AGENTS.md): replaces the Inspect(items...) examples, #165: Boolean contains result; no list or numeric truthiness, #139/#140: star syntax replaces ... spread and res |
| [#136](https://github.com/katlangorg/katlangnet/issues/136) | Define list semantics for the atoms builtin | yes | CURRENT | COLL SEQ VAL BOOL FORMAL | atoms(value) = makeCollectionListResult(languageAtoms value): numbers give [n]; sequences and lists are traversed recursively; strings and Booleans contribute nothing (atoms(7) is [7], atoms('text') is []). |
| [#137](https://github.com/katlangorg/katlangnet/issues/137) | Add `:` indexing support for exact immutable lists | yes | CURRENT | SEQ VAL SYN COLL FORMAL | A:i selects position i of the target's projectionItems (sequence or list elements; a scalar is its own position 0) and returns the stored element as one value (Result.select?, re-counted by valueCount); only spread opens it. |
| [#138](https://github.com/katlangorg/katlangnet/issues/138) | Make all rest bindings collect exact immutable lists | yes | PARTIALLY CURRENT | VAR SUP SEQ VAL CALL DOT FWD HO FORMAL | superseded by eab2468 (#139 commit) reversed 'lone-rest assignment forbidden': *items = RHS is now valid, #139 -> 09382b3 -> #140/73648e9 replaced items.../A... syntax with *items/A*, 5377b9c and #140 renamed rest binding/variadic parameter to collecting binding/parameter, #165 Booleans replace 1/0 equality results. Every collecting binding (parameter, mixed list, deconstruction) collects exactly  |
| [#139](https://github.com/katlangorg/katlangnet/issues/139) | Distinguish rest bindings from spread expressions with prefix and postfix ellipsis | yes | PARTIALLY CURRENT | SYN VAR SUP | superseded by 41c0bb6 (postfix rest rejected, deprecation period dropped), 09382b3 (#140 first commit: back to postfix name... plus spread(x)), #140 / 73648e9 star syntax (*name collect, x* spread, ellipsis token removed), #161 layout-independent star and attached-marker law. Prefix *name (directly attached, binding positions only) collects, postfix expr* spreads, at most one collecting binding pe |
| [#140](https://github.com/katlangorg/katlangnet/issues/140) | Adopt prefix collect and postfix spread star syntax | yes | PARTIALLY CURRENT | SYN SUP VAR FWD DOT SEQ | superseded by #161 (cb6cfda, SYN-07B layout-independent star + marker attachment law) for the same-line/newline disambiguation rules. *name is the only collecting-binding syntax and expr* the only spread spelling. Q-65 (2026-10-14) supersedes the old line-final fallback: physical line-final star always means multiplication, including EOF/later declarations/closers; explicit same-line closure selects spread. *(#183, 2026-10-14: refined — an attached line-final star is a spread again, a detached one multiplies.)* Declaration heads are never operands. A spread marker must be attached to its operand. value** ≡ (value*)*, never r |
| [#141](https://github.com/katlangorg/katlangnet/issues/141) | Equality crashes with an uncatchable StackOverflowException on deeply nested values | yes | BUG FIX / REAFFIRMED EXISTING RULE | RUN CMP VAL | Structural equality and every whole-value traversal are total and stack-safe. Auxiliary storage is O(depth) and DAG-memoized. A legal program yields its value or a structured error and never crashes the host. |
| [#142](https://github.com/katlangorg/katlangnet/issues/142) | Replace `//` line comments with `#` | yes | CURRENT | SYN | A '#' outside a string literal starts a comment that runs to the next physical line break. Comments are semantically invisible, and '//' is never a comment. |
| [#143](https://github.com/katlangorg/katlangnet/issues/143) | Simplify Algorithm abstraction: make parentheses a value-capture boundary, not an Algorithm | yes | PARTIALLY CURRENT | ALG SEQ VAL CALL MOD DOT RES SYN FORMAL | superseded by #168 (50c74c1, parentheses group syntax): (Name), (M), (Obj), ((1,2)) are no longer captures, so Apply((Increment)) forwards identity, open (M) opens M, (Obj).V navigates. Braces are AlgorithmExpr and always carry identity. A surviving group (several slots, or a lone spread) is a Capture with no identity, no structural members and no open target. Any one-slot non-spread group is eras |
| [#144](https://github.com/katlangorg/katlangnet/issues/144) | Fix collecting-parameter binding for lexical dot-call receivers | yes | SUPERSEDED | DOT VAR CALL SUP FWD | superseded by #167: 68b3607 (dot-call passes a value, receiver segments deleted), dada1b6 (interim collector supply-boundary law, briefly restored averaging), 702e7d7 (C-full values stay values; spec probe (1, 2, 2.718).Mean -> err arity). Dot-call passes a value: R.F(args) ≡ F(R, args) and R*.F(args) ≡ F(R*, args). A collector collects the receiver as one item, so (1, 2, 3).Mean errors and (1, 2, |
| [#145](https://github.com/katlangorg/katlangnet/issues/145) | Accessibility: Monaco IntelliSense moves NVDA focus away from the editor while typing | no | HOST/API ONLY | TOOL |  |
| [#146](https://github.com/katlangorg/katlangnet/issues/146) | Pieejamība: uzlabot virsrakstu struktūru KatLang darbnīcā | no | HOST/API ONLY | TOOL |  |
| [#147](https://github.com/katlangorg/katlangnet/issues/147) | Dot-call lexical fallback should reuse ordinary callable resolution | yes | PARTIALLY CURRENT | DOT RES CALL PAR HO SYN FORMAL | superseded by d21b163 (removed 6c63486 extension-dot mode; a~.t infers (t, a), not the comment's (a, t)), 68b3607 DOT-CALL PASSES A VALUE (strengthens fallback law), G-24 missing-member fallback, F10 Grace effectiveness. Dot-call is structural-member-first at every chain level, otherwise the extension fallback F(R, args) through the one call funnel with canonical callee resolution; a~.t / a.~t are |
| [#148](https://github.com/katlangorg/katlangnet/issues/148) | Uncharged AlgEnv re-entry causes exponential evaluation | yes | BUG FIX / REAFFIRMED EXISTING RULE | RUN PROP CALL | Dynamic depth counts every simultaneously active evaluator entry that can re-enter an algorithm body; resource-limit failures are structured errors (twin path may report EvaluationStackExhausted earlier by documented backstop). |
| [#150](https://github.com/katlangorg/katlangnet/issues/150) | Add cooperative CancellationToken support to KatLang evaluation | yes | HOST/API ONLY | RUN API | Host cancellation lives on the run-scoped budget, is observed before any counter mutation, and always escapes as OperationCanceledException, never as an in-language error. |
| [#151](https://github.com/katlangorg/katlangnet/issues/151) | Add asynchronous execution support to the KatLang evaluator | yes | HOST/API ONLY | RUN API | The sync evaluator is the semantic oracle; async twins (// MIRROR OF) must match it in outcome and counters, with only the documented twin-only stack backstop allowed to fail earlier. |
| [#152](https://github.com/katlangorg/katlangnet/issues/152) | Allow a~t as shorthand for a~.t / a.~t | yes | REMOVED | SYN DOT PAR | superseded by b28567f revert, #160 SYN-07A makes a~t an UnseparatedSameLineItem. Only a~.t and a.~t exist; a~t is a same-line UnseparatedSameLineItem parse error. |
| [#153](https://github.com/katlangorg/katlangnet/issues/153) | Use Decimal128 as KatLang's core numeric type | yes | CURRENT | OP VAL FORMAL RUN | C# numbers are IEEE Decimal128 (Lean core stays Int); specials are ordinary values but division/modulo by an evaluated zero is divByZero and 0^negative is a domain error. |
| [#154](https://github.com/katlangorg/katlangnet/issues/154) | Add predefined lower-camel-case aliases for all Math members | yes | PARTIALLY CURRENT | RES MOD OP HO DOT TOOL | superseded by #155 (e/Math.E row replaced by exp/Math.Exp), G-24 (Math.cos(1) falls back to cos(Math, 1), not unknown property), audit #8 (alias and canonical member are distinct bindings). Math aliases are distinct prelude property bindings sharing the member's algorithm; shadowable, beat opens, usable in dot fallback and higher-order positions. |
| [#155](https://github.com/katlangorg/katlangnet/issues/155) | Replace Math.E with Math.Exp and the exp prelude alias | yes | CURRENT | OP RES | Math.Exp(x) and the prelude alias exp compute Decimal128.Exp; Math.E and e do not exist (free e is an implicit parameter). |
| [#156](https://github.com/katlangorg/katlangnet/issues/156) | Fix native callback argument lookup using ambient values | yes | BUG FIX / REAFFIRMED EXISTING RULE | RES HO CALL RUN | A bound parameter owns its name on every channel; native wrappers read arguments via LookupNativeArgument (the Expr.Param value read). |
| [#158](https://github.com/katlangorg/katlangnet/issues/158) | Preserve nearer explicit-parameter ownership in nested bodies | yes | CURRENT | RES PAR PROP FORMAL | The owner walk selects the nearest owning scope's parameter-then-property binding; properties may not share a name with a parameter of their own or an enclosing algorithm (root checked against its own declarations only). |
| [#159](https://github.com/katlangorg/katlangnet/issues/159) | Resolve if by callable identity, not spelling or arity | yes | CURRENT | RES CALL BOOL HO DOT SUP FORMAL | superseded by #165 Booleans (numeric if conditions in examples now TypeMismatch). resolve -> one identity -> ordinary supply -> bind that signature -> invoke; a nearer if/count/sum shadows completely; no layer branches on callee spelling (load excepted). |
| [#160](https://github.com/katlangorg/katlangnet/issues/160) | Require commas between same-line slots | yes | CURRENT | SYN SEQ | Whitespace never creates a slot; a same-line unseparated item is UnseparatedSameLineItem; newlines still separate output rows. |
| [#161](https://github.com/katlangorg/katlangnet/issues/161) | Make `*` disambiguation layout-independent and require attached marker syntax | yes | CURRENT (conflicting line-final subrule superseded 2026-10-14) | SYN SUP VAR | Physical line-final star announces multiplication, including EOF or a later declaration/closer. *(#183, 2026-10-14: refined — only a detached line-final star; an attached one is a completed spread.)* Explicit same-line closure permits spread, after which attachment is required. Prefix collect, Grace and spread VALUE semantics are retained; Q-65 grammar priority governs leading binary roles. |
| [#162](https://github.com/katlangorg/katlangnet/issues/162) | Dot access should prefer structural property over extension fallback | yes | CURRENT | DOT RES MOD | An argumentless dot receiver is navigated through declared members (private included) before the outer edge resolves; a declared-but-inaccessible or branch-only member is LocalOnlyProperty, never a fallback; otherwise lexical fallback `F(receiver)`. |
| [#165](https://github.com/katlangorg/katlangnet/issues/165) | Add first-class Boolean values and remove numeric truthiness | yes | CURRENT | BOOL CMP OP SYN PAT HO LOOP FORMAL | Only Boolean values have a truth value (Result.asBool?); every predicate position and logical operand rejects non-Booleans with TypeMismatch, and `true == 1` is false. |
| [#166](https://github.com/katlangorg/katlangnet/issues/166) | Add first-class comparison chaining with unified comparison precedence | yes | CURRENT | CMP BOOL SYN OP FORMAL | `a < b <= c` is an Expr.Comparison chain true iff every adjacent link holds; operands are evaluated exactly once, left to right, not short-circuited by false; parentheses break chains; `not` binds below comparisons. |
| [#167](https://github.com/katlangorg/katlangnet/issues/167) | Define collector supply boundaries for sequences, selection, and dot-call | yes | CURRENT | VAL SEQ SUP CALL VAR DOT HO FWD LOOP PAT FORMAL | A non-spread argument supplies one item whatever its value; `v*` opens one level; a collector collects exactly its allocated items; `R.F(a)` ≡ `F(R, a)`; `A:i`/first/last choose one value; a callback element is one argument. |
| [#168](https://github.com/katlangorg/katlangnet/issues/168) | Make redundant expression parentheses semantically transparent | yes | CURRENT | SYN VAL SEQ PAT CALL DOT PROP | Parser.IsRedundantGrouping erases every one-slot non-spread group; only multi-slot groups and lone-spread `(A*)` survive as Expr.Capture; patterns open the argument's value, never a written-slot view. |
| [#170](https://github.com/katlangorg/katlangnet/issues/170) | Define zero-parameter property caching by semantic binding identity | yes | CURRENT | PROP RES VAL HO COLL LOOP RAND RUN FORMAL | Cache identity is the resolved semantic binding (not spelling or path); how a value is consumed never affects caching; explicit `A()` neither reads, populates nor replaces the entry. *(Constitution audit, 2026-10-23, current-rule pointer: the populate clause is superseded by CACHE-PUB-1 (owner decision 2026-10-22, #189, `586f32f3`): a qualifying zero-supply `A()` that finds the entry empty establishes it; it still never reads or replaces it; PROP-06.)* |

## Part 1 — Decision lineages (compact)

Each chain lists the decision steps in order (A proposes → B refines → C regresses → D changes the rule) and the semantics that SURVIVE today. Only surviving semantics may appear in the constitution; everything else in a chain is history.

### Area: calls-arguments

#### A. What one written argument supplies (argument boundary)

**Steps:** #57 2f27fba 2026-04-17 PROPOSES variadic builtins (order(3,4,2) and order((…)) both accepted) -> #58 c9a43fa 04-18 REFINES: one-level 'content projection' for receivers/:/callbacks -> #61 17e34bd 04-19 ESTABLISHES 'an argument expression does not implicitly spread its emitted values' (opener then = ';') -> #69 d3ee6d7 04-23 regression fix makes builtins open argument content -> #71 c876d28 04-23 REAFFIRMS: comma = slot, flatten only via ';' ('content-based consumers') -> #74 b3af83b 04-25 EXTENDS to dot receiver -> #101 5555cd1 05-12 EXTENDS to flat fixed user calls -> #103 40f7745 (reverted a025cbe) / #104 0e9b41f 05-13 REPLACE opener with '...' -> #111 4c9877d 05-14 COUNTER-STEP: variadic-slot sequence supply re-opens lone sequences at flat variadic slots -> #125 ad75720 06-17 REMOVES ';', replaces #111 model -> d2837f4 06-19 COUNTER-STEP: builtin rest params w/ pre-binding lone-group opening -> #135 0ca55e9 07-17 CHANGES builtins to one fixed collection param + post-binding one-level view -> #138 ab7d2f5 07-18 collectors collect exactly supplied args -> 245b10c 07-20 (F03) UNIFIES one argument pipeline, spread before clause/pattern binding -> #140 73648e9 07-29 opener = postfix * -> #144 f12af0f 08-11 COUNTER-STEP receiver segments -> #167 874625a/68b3607/dada1b6 09-21 selection value boundary, dot-call passes a value, collector supply-boundary law (SupplyOrigin fusion) -> 5d6d60b + 702e7d7 09-23 FINAL 'values stay values' (C-full): SupplyOrigin/collectorSupply/row convention deleted

**Surviving semantics:** Shared user-call assembly (C# BuildCallArgumentInputs Evaluator.ParameterBinding.cs:1549; Lean collectVariadicCallItems KatLang.lean:6020): each non-spread written slot is evaluated in the caller's context through the one EvalCounted and supplies exactly ONE item (its value, never opened, whatever its kind or origin); a spread slot e* supplies the items of one boundary; the supply is complete before arity checking, clause selection, or pattern binding; items carry no provenance. Collection builtins bind one fixed collection argument and open it one level only after binding. Pinned by spec fixed-call-preserves-boundaries, spread-fills-remaining-slots, values-stay-values, call-spread-dispatches-before-clause-selection; CallArgumentAssemblyTests, ExplicitValueOpeningTests, CoreTests ExplicitValueOpening.

#### B. Implicit final-argument unpacking in flat fixed calls

**Steps:** legacy tutorial 6cb9334 2026-04-02 'Algorithm as Argument': KatLang unpacks a multi-output final argument (UnpackArgs in EvalUserCall; Sum3(Input)=6) -> #74 b3af83b 04-25 CARVES OUT dot receiver (preserveArgBoundaries) while normal calls still unpack -> #96 6469363 05-07 parallel: loop initial args keep written boundaries (replacing c647330's parse-time packaging) -> #101 5555cd1/c518b69 05-12 REMOVES final-argument unpacking for flat fixed user calls (Add(Pair) arity error; ';'/.content as explicit forms) -> #125 ad75720 06-17 / #129 7458502 06-26 remove ';' and .content, #140 makes Pair* the remedy -> callback residue (#58 S:i callback projection, flat-callback row convention) -> 702e7d7 2026-09-23 GENERALIZES: callback element is one ordinary argument; complete-supply arity payload (flat_binding_arity_reports_complete_supply, Lean bindParams length check)

**Surviving semantics:** A fixed parameter binds its allocated item unchanged; one argument never fills several fixed parameters in any spelling: Add(Pair), (10, 20).Add and map([(1, 2)], Add) all fail with ArityMismatch payload (expected 2, actual 1). Remedies are explicit: Add(Pair*), Add(Pair:0, Pair:1), or a pattern parameter AddPair((x, y)). Loop initial arguments supply one state slot per written argument (a spread supplies its items). Law collector_fixed_parameter_binds_value_unchanged (KatLangArityLaws.lean:899); spec fixed-call-preserves-boundaries; tutorial 'KatLang never takes a value apart on its own'.

#### C. Property/call result boundaries

**Steps:** #7 comment 2026-03-10 ESTABLISHES flat root output (root accumulation is not a boundary) -> 83eccae 04-08 introduces Result.valueCount (reduce/map) -> lexical property access already one grouped value before June (origin UNCERTAIN) -> #130 daf8a4c 06-26 BUG->RULE: if re-counts the selected branch -> #132 9a4c70f 06-27 GENERALIZES: every property/call/builtin/structural-dot result is one value, reCountValueBoundary; keeps 'rest capture raw internal counts' clause -> #134/#135 d202b74/0ca55e9 07-16/17 REFINES builtin results to one exact list (makeCollectionListResult) -> #138 ab7d2f5 07-18 REMOVES raw-internal-count clause (variadicSupplyEnv deleted) -> 245b10c 07-20 (F09) reduce initial accumulator reified -> (counter-state: #58 c9a43fa S:i projected content, Aug-7 selection re-emits projected count, lone-root projection display rule) -> 874625a 2026-09-21 (#167) EXTENDS: selection (A:i, first, last, callback item) is a value boundary; projection rule removed

**Surviving semantics:** Every property read, user/clause call, builtin result, if, structural dot access, and selection returns ONE value with emitted count Result.valueCount (0 for (), else 1); only a caller-site spread reopens it. Collection producers return exact lists; collecting bindings store one list. NOT boundaries: root/body row accumulation, while/repeat multi-slot state, and the map/reduce callback output contract (single emitted value required). Lean reCountValueBoundary KatLang.lean:2910, select_is_stored_element KatLangArityLaws.lean:1118; C# ReCountValueBoundary Evaluator.Builtins.cs:144; spec call-value-boundary, property-value-boundary, property-call-boundary, dot-access-value-boundary, if-value-boundary, index-selects-one-value, reduce-empty-initial-is-one-value.

#### D. Written-slot reification

**Steps:** pre-July 2026 list elements/written pattern items SPLICE multi-emitting expressions ([S:0, 5] -> [1, 2, 5]); reduce initial leaks emitted count -> 34b8e0e 2026-05-28 ADDS second written-slot VIEW for grouped parameter patterns (explicitItems?) -> 245b10c 07-20 (F02/F09) ESTABLISHES one persistent value per non-spread written slot ([S:0, 5] -> [(1, 2), 5]) and reified reduce initial -> b78f4f9 08-07 REPAIRS double evaluation with one PreparedAlgorithmOutput pass -> 874625a 09-21 selection itself one value -> 50c74c1 09-22 (#168) DELETES the written-slot pattern view (patterns open the VALUE via structureItems?) -> c723e20 09-22 REFINES spans of unfolded written slots

**Surviving semantics:** Every grammar position that defines one value per written slot — list-literal elements (Lean evalListLiteralCounted -> evalExplicitSequenceValueExprSlots KatLang.lean:6103), capture rows, call arguments, loop initial arguments, and reduce's initial accumulator — takes ONE value from a non-spread slot even when the expression emits several items; only a spread slot splices. Root/body rows and loop step outputs keep multi-item emission (plus the documented sequence-value-patterned loop-step packing exception). Patterned callees see only the argument's value. Probes [S:0,5]->[(1,2),5], [Step.repeat(1,0,0),5]->[(1,1),5], F((Step.repeat(1,0,0),5)) with F((x,y))=x -> (1,1).

#### E. Parentheses: grouping vs capture vs algorithm

**Steps:** pre-2026-03-22 special ((…)) argument-grouping syntax -> c647330 03-22 (A) REMOVES it: '((expr)) is equivalent to (expr) in all positions' -> d08cc58 04-02 docs: ( ) is a non-parametrized Algorithm wrapper layer (IsParametrized model) -> #58 c9a43fa 04-18 (B) REVERSES: extra paren layers preserved on receivers (count((1,7)) = 1) -> 5555cd1 05-12 tutorial ((1, 2)); 3 preserves nested group; 34b8e0e 05-28 call-site parens affect grouped-pattern binding -> #128 73cdba2 06-22 (()) != () -> e6c2bdc 07-11 REVERSES: (()) == () -> b78f4f9-era 08-07 kind-dependent unwrap ((S:0) erased, (A) kept) -> 57e9ed0 08-08 RESTRICTS: no declarations inside parentheses, braces only scope -> #143 7075071 08-09 (C) AST SPLIT AlgorithmExpr vs Capture(OutputBundle), IsParametrized deleted, braces always identity (Call0({42})=42); Track D makes open (M) rejection and (Obj).V suppression 'PERMANENT', (Name)/((1,2)) captures -> #168 50c74c1 09-22 (D) CHANGES RULE: IsRedundantGrouping erases every one-slot non-spread group regardless of kind; written-slot view deleted -> ebf623e 09-27 (#170) grouped consumers read the property cache (equivalence now via cache, not direct demand)

**Surviving semantics:** Parentheses group syntax: a declaration-free group of exactly one non-spread slot IS its inner node (Parser.IsRedundantGrouping Parser.cs:4743), so E ≡ (E) ≡ ((E)) for value, count, normalization, every binder, selection, dot receiver, spread, caching, evaluation count/order, error kind and every strategy (Apply((Increment)) = Apply(Increment), (Obj).V = Obj.V, open (M) = open M, ((1,2)) is the pair, (()) is ()). Only multi-slot groups and lone-spread groups (A*) are Expr.Capture (capture: Supply -> Value), which have no algorithm identity (Apply((Inc, Dec)) arity error), no structural members, and are not open targets (open (M, N) BadOpenForm). Every brace block is an AlgorithmExpr with identity. Parentheses never own declarations. Grammar caveat: (a.b)(1) calls the dot result, unlike a.b(1).

#### F. Output-less arguments, absences, and argument blame

**Steps:** #12 ebb4dab 2026-03-23 bare-reference arity error gets a span -> #28 66dc3cd 04-05 inner call span survives outer frame (precursor of attach-if-missing) -> #65 4e19be6 04-25 variadic-reduce diagnostics (superseded by #135 fixed arity) -> #76 315dd54 04-26 empty receiver is not zero arguments -> #81 b950d86 / #83 1ca8b3f 04-29 explicit empty ('empty', later () via #128 73cdba2) vs no-program-output error -> F9 9f6cdfb 09-13 builtin value slots via one zero-arg demand law -> F2 a1bae94 / F3 f9615af 09-22 null spans, transparent synthetic deconstruction frames -> F5 989fcea 09-22 ESTABLISHES: output-less WRITTEN argument blamed at the argument (ArgumentEvaluationContext, BlameWrittenArgumentForMissingOutput), provenance carried not re-derived, names not blamed -> c723e20 09-22 list-element spans -> 5d6d60b 09-23 argument wrapper keeps inner span

**Surviving semantics:** Four absences stay distinct by slot provenance, never by the final item count: an omitted argument is the binder's arity error before evaluation (F(), count()); a written argument whose expression produced no output is that argument's MissingOutput, rendered 'The argument `{...}` has no defined output' at the argument under the callee's frame (Coll({}) is never Coll()); an empty value (), [] is one ordinary value (Coll(()) = [()], Coll([]) = [[]]); an explicit zero-item spread is a legal supply (Coll(Empty*) = []), while spreading a no-output operand is SpreadMissingOutput. A fixed parameter keeps its parameter-worded report; a callee with no output keeps callee blame; a program with no output rows is NoProgramOutput/MissingOutput, distinct from an explicit (). Error kinds unchanged (C#-only diagnostics). Spec output-less-argument-is-not-an-omitted-argument, missing-output-not-a-value; OutputLessArgumentBlameTests.

#### G. Zero-argument value demand (bare reference as value)

**Steps:** #12 ebb4dab 2026-03-23 (A) bare reference to a parameterized algorithm is an ArityMismatch at the reference (criterion: declares parameters) -> #159 0243678 09-10 builtins are ordinary prelude bindings (identity decides) -> F9 9f6cdfb 09-13 (B) EXTENDS the one demand law to builtin value slots and .string receiver (if(1, Inc, 0) no longer enters Inc's body) -> 2d47a93 09-22 (C) CHANGES eligibility: iff an ordinary zero-argument call can bind it (minimumSuppliedSlots == 0; Only(*xs) bare -> []), rejection reports true minimum; F4 29c94b8 aligns arity facts -> 5d6d60b 09-23 forwarded callable keeps algorithm channel at invoking slots -> ebf623e 09-27 (D) builtin value slots read the property cache

**Surviving semantics:** A callable satisfies a zero-argument value demand iff an ordinary call supplying zero arguments can bind it (Evaluator.AcceptsZeroSuppliedArguments Evaluator.cs:1219; Lean Algorithm.acceptsZeroSuppliedArguments KatLang.lean:2714 over minimumSuppliedSlots :181: one slot per top-level pattern, none for a top-level collector; a family accepts iff a branch has top-level arity zero); otherwise the demand is an ArityMismatch at the reference reporting the true minimum. Builtins keep their own rejection. Accepted demands run through one funnel; callback/invoking slots receive the algorithm, value slots the (cached) value. Laws zero_argument_value_demand_accepts_exactly_zero_supply_callables, minimum_supplied_slots_*; spec zero-argument-demand-follows-actual-call-arity.

#### H. Callee identity and the builtin argument adapter

**Steps:** c647330 2026-03-22 parser packs extra while/repeat init args by argument count (removal commit UNCERTAIN, per-argument slots by #96 6469363) -> #49 93a036d 04-13 if standardized to arity 3 -> #131 7e1085e 06-26 spread if-argument expands before arity (only skips Parser.ValidateIfArity for spreads) -> 57e9ed0 08-08 pre-evaluation validation aligned with if-arity diagnostics; b638c24 08-08 fixes spread-argument slot order (Lean had gone rightmost-first) -> #159 0243678 09-10 (D) CHANGES RULE: resolve -> ONE identity -> ordinary supply -> bind that signature -> invoke; ValidateIfArity deleted, shadowing complete, if laziness belongs to resolved builtin (load remains spelling-recognized) -> F9 9f6cdfb 09-13 lazy builtin value slots use the zero-arg demand law

**Surviving semantics:** Call resolution selects one callee identity without considering the argument count or spelling; no layer counts arguments by callee name; a wrong-arity builtin call is an evaluation-time ArityMismatch. User callables share one eager left-to-right assembly. Builtins use their own adapter (ExpandSequenceSpreadBuiltinArguments / Lean expandSequenceSpreadBuiltinArguments KatLang.lean:5948): spread slots are forced first in written order before the builtin runs, non-spread slots stay algorithm-lazy and are demanded by the builtin (unselected if branch never demanded), and control builtins (if/while/repeat/range/atoms) check arity before demanding non-spread slots (range(trace(1), trace(3)*) traces 3 then 1). Pinned by SpreadArgumentEvaluationOrderTests, BuiltinCallableIdentityTests, spec spread-arguments-keep-written-order, spread-arguments-fail-left-to-right, builtin-callable-is-an-ordinary-prelude-binding.

*(X-18, 2026-10-10: "User callables share one eager left-to-right assembly. Builtins use their own adapter" is SUPERSEDED — since Model C (2026-10-02) every callee forms its supply alike, explicit spreads executing at formation and every other slot suspended, checks cardinality before any ordinary VALUE demand and then demands in its own order; Q-07 was resolved by that law on 2026-10-03, and the owner confirmed it as intended when closing X-18; `constitution.md` CALL-02, CALL-03.)*

#### I. Argument channels and retained argument failures

**Steps:** #53 b627c21 2026-04-15 (A) abstracting a call behind implicit parameters must not change it: sequence arg = one value, block keeps callable identity when forwarded -> #92 3997ad6 05-06 / #95 37c6898 05-07 newer call-frame parameter shadows inherited callback binding -> 245b10c 07-20 shared pipeline defers algorithm-resolvable argument value errors for every shape (deferral origin UNCERTAIN) -> #156 04b5fc8 08-29 native wrappers read their own bound parameter (LookupNativeArgument) -> 8d2fc53 09-04 / f321843 09-08 (D) a bound parameter owns its name on every channel (ShadowInheritedParameterEnvironments / EvalCtx.bindParameters) -> 989fcea 09-22 CHARACTERIZES (not changed) fixed-parameter re-derivation of a retained failure -> 5d6d60b 09-23 invoking builtin slots read a forwarded parameter's algorithm channel

**Surviving semantics:** A user call binds each parameter on the value channel, the algorithm channel, or both; argument slots evaluate in the caller's context and the callee's bindings shadow its parameter names on all three inherited tiers (value, counted, algorithm); natives read their own bound argument. A non-spread argument that fails but has an algorithm channel (name, block, dot member) is retained, not raised, so an undemanded failing argument is no error (Ignore(Bad) = 0, F(x, y) = x with F(1, {}) = 1); a slot without an algorithm channel fails the call at assembly. Collecting, patterned and clause-family binders surface the retained error; a FIXED parameter re-derives the argument on value demand (effects run twice; C# resource-limit failures sticky) — current behavior, characterized by OutputLessArgumentBlameTests.FixedParameterDemand_ReDerivesTheArgument_AsBefore but not ratified as law (open question). **Superseded 2026-09-28 for the re-derivation (Q-01, CALL-06):** a written argument slot is evaluated at most once for its value, a failure included, and a parameter read never replays it (`decision-lineages.md` calls-arguments § I step 8).

#### J. Argument positions and implicit lifting

**Steps:** #78 8fbc972 2026-04-27 references inside Math member arguments lift implicit parameters -> #114 c1e19b1 05-16 bare builtin aliases lift registry signatures -> Track D3 in 7075071 08-09 PRINCIPLE: lifting is a consumer property (ProcessValueDemandingArgumentBundle); registry-strict Math args lift, ordinary call-argument slots neutral; sum(Double) documented gap -> 8d2fc53 09-04 closed-list strict-value diagnostic (ReportBlockedStrictValueForwarding) -> ad6d6bf 09-23 audit #8 Math strict-value contract by identity

**Surviving semantics:** Value-context lifting of a referenced callable's implicit parameters is decided by the consuming position: output rows, list elements, arithmetic operands in value positions and registry-strict Math arguments lift; ordinary call-argument slots and capture rows are neutral as whole bundles (even operator operands nested inside them), preserving higher-order references: with A = x + 1, F = A + 1, 2 and F = [A + 1, 2] lift but F = (A + 1, 2) and F = G(A + 1) do not (F(5) is an arity error). A closed explicit parameter list that blocks a strict-value lift is a front-end UndeclaredIdentifier diagnostic. **Superseded 2026-09-30 (the unified formula-lifting law, PAR-07; re-verified 2026-10-01):** a formula lifts a reference whose IMMEDIATE consumer uses it as a value — capture elements, builtin value slots and operands nested inside any argument included (`F = (A + 1, 2)` and `F = G(A + 1)` now lift); only a user callable's whole argument, callbacks, loop steps and runtime callees' arguments keep the reference. The closed-list diagnostic still covers registry-strict Math positions only (Q-15).

### Area: supply-spread

#### A. Semicolon: combining operator -> result join -> removed -> output join -> removed for good

**Steps:** Before March 2026 (v0.6): `;` combines algorithms. `combineAlg` merges params, properties and opens, and `open A; B` uses it (seen at 9f3a0f9^). -> #2 (2026-03-10, 9f3a0f9) PROPOSES + IMPLEMENTS a value-level `.combine` eval arm plus Result.toItems: concatenate top-level items, then normalize. Here `;` binds tighter than comma. -> #61 (17e34bd) and #71 (c876d28) USE `;` as the only explicit spreading mechanism. -> #62 (d53eec8) IMPLEMENTATION: stack-safe combine. -> #75 (2026-04-26, 23d9a0c) REDESIGNS `;` as the result join (Expr.ResultJoin). It no longer merges properties (combineAlg is deleted) and does not flatten recursively. A side with no output is an error (resultJoinMissingOutput). -> #104 (2026-05-13, 0e9b41f) REMOVES the `;` join in favour of `x...y`. -> #120 (2026-06-10) DISCOVERS A REGRESSION: the property and inline forms of the `...` join disagree. -> #122 (7b5fe7a, 65301ce, acbfa7d; 2026-06-10/11) REVERSES #104's removal: `;` returns as the output join (Expr.OutputJoin), comma now binds tighter than `;`, `;` never flattens explicit groups, and newline means an implicit `;`. This also fixes #120. -> #123 (007917a) REFINES: adjacency is also an implicit `;`, and `open` gets its own comma grammar. -> #125 (2026-06-17, ad75720) REMOVES `;` from expression syntax (UnsupportedSemicolon). OutputJoin is renamed to the internal, never-parser-produced SequenceConstruct. Adjacency becomes an implicit comma. -> #160 (2026-09-12, 2b03c0b, SYN-07A) REVERSES the same-line adjacency rule: adjacency is now an error.

**Surviving semantics:** `;` is not expression syntax. It is the targeted parse error UnsupportedSemicolon (Parser.cs:1638/3738; DiagnosticCode.cs:54; spec semicolon-not-expression-syntax). There is no join operator. Concatenation is written as spreads inside a capture or list: (A*, B*) or [A*, B*]. Comma is the only same-line slot separator, and a newline separates slots where the context is open. Result.toItems (from 9f3a0f9) survives as the non-spread item view. Join semantics (dropping () leaves) survive only in the internal SequenceConstruct node, which is reachable only from host-built ASTs. Probe: `A = ((1, 2)*, 3) / A / 4` and `((1, 2)*, 3) / 4` both give S[S[1,2,3],4], which is exactly #122's resolution of #120.

#### B. Explicit opener: ungroup/content -> postfix `...` sequence supply -> unary postfix supply -> 'spread' -> spread(x) -> star marker

**Steps:** #91 (5d1b52c) ADDS the builtin `ungroup`, a one-level projection. -> #98 (7ad022c) RENAMES it to `content`. -> #101 (5555cd1) REMOVES implicit final-argument unpacking (`Add(Pair)` is an arity error), which creates the need for an explicit opener. -> #103 (40f7745, 2026-05-12) PROPOSES postfix `expr...` as explicit stream expansion. It bans a comma after a spread, and the dot-receiver spread applies only to variadic callees. REVERTED next day (a025cbe). -> #104 (0e9b41f, 2026-05-13) REPLACES it with the sequence-supply operator: infix `x...y`, and `x...` means `x...empty`. A comma after a supply is allowed. The node is binary SequenceSupply, renamed from ResultJoin. Stream-provenance forwarding is added. -> #122/#123 NARROW it: `...` means supply only, and postfix `...` absorbs the accumulated chain. -> #124 (4b32111, 2026-06-13) makes supply postfix-only with a unary node, no empty tail, and a sideless missing-output error. -> #125 (ad75720) KEEPS the unary supply and drops chain absorption. -> b568c66 (2026-06-18) RENAMES supply to spread (SequenceSpread, spreadMissingOutput). -> #128 (73cdba2) REMOVES `empty`: `()*` supplies zero items. -> #129 (7458502) REMOVES `content`: spread is the only opener. -> e6c2bdc formalizes the opener as `open : Value -> Supply` in the algebra. -> #139 (eab2468) keeps postfix `expr...` for spread. -> 09382b3 (2026-07-28) REPLACES it with the reserved intrinsic `spread(x)` / `x.spread`. -> #140 (73648e9, 2026-07-29) REPLACES THE SYNTAX with postfix `expr*`. The Ellipsis token is deleted, `spread` is un-reserved, and the fluent form `x.C*.T(args)` lowers to `T(x.C*, args)`.

**Surviving semantics:** There is one spelling, the attached postfix `expr*`. It lowers to one unary node (C# Expr.SequenceSpread, Ast.cs:724; Lean sequenceSpread, KatLang.lean:888), never a Call or DotCall. So there is no value boundary, one evaluator path, and the operand is evaluated exactly once. `...` is not a token. `spread`, `content`, `ungroup` and `empty` are ordinary identifiers. Only the explicit spread turns one value into several argument slots: `Add(Pair)` is ArityMismatch and `Add(Pair*)` gives 30. Historical only: infix `...`, `x...empty`, the #103 comma ban, chain absorption, 'F(X...Y) is one joined argument', and `spread(x)` / `x.spread`.

#### C. What spread opens: one boundary, total item view, empties, missing output, repeated spread, never reopened

**Steps:** #2 toItems opens one level. -> #75: no recursive flattening, and an operand without output is an error. -> #91/#98: one-level content, distinct from recursive atoms. -> #128 (73cdba2): `()*` supplies zero items, while an unspread `()` is visible. -> 7a05b99/ecd1b74 (2026-07-13) PROVE empty-spread neutrality, plus the since-deleted `variadic_capture_unchanged_by_spread`. -> #134/#135 (d202b74, 0ca55e9): spread opens list boundaries too. -> 245b10c / July sequence-boundary audit DISCOVERS that Lean's plain evalAlgOutputCore did not splice spread slots (`(A.spread, 99)` gave ((1,2),99)). FIXED by making it a projection of the counted core. -> #140 (73648e9) states that spread-produced items are not reopened. -> the #140 comment (7c1da97, 2026-07-30) CORRECTS `value**` to mean (value*)*, i.e. spread∘capture∘spread, not recursive flattening. c087356 adds the guards. -> #167 874625a: selection is a value boundary, so `A:0*` spreads the stored element and a selected () spreads to nothing. -> F5 (989fcea): a zero-item spread is legal, and a spread of an output-less operand stays SpreadMissingOutput. -> #167 C-full (702e7d7, 2026-09-23) FIXES `v*` as the only value->supply conversion and states that items are never reopened by binders.

**Surviving semantics:** spreadItems (KatLang.lean:1273): a sequence gives its items, a list its elements, and any other value (number, string, Boolean) gives itself. Spread creates no value; the receiver decides. Capture makes a canonical sequence, a collector an exact list, fixed params take one item each, root/body output emits rows, a list literal takes elements, and deconstruction captures then unpacks. `()*` and `[]*` are neutral. An operand without output raises SpreadMissingOutput (EvalError.cs:283; Lean evalSequenceSpreadOperandItems). E** ≡ (E*)*: a multi-item supply is a fixed point, and only a lone structured item opens one further level. Laws: explicit_spread_opens_one_level, collector_collects_spread_items_exactly, capture_*_spread_neutral, repeated_spread_cardinality/_fixed_point_of_multi, and ArityDifferential SPREAD_ITEMS_ARE_NEVER_REOPENED. Scope caveat: 'never reopened' applies to binders and collectors. Assignment deconstruction captures a spread RHS and can open one more level (deconstruct_spread_capture_can_open_further; `x, y = [(1,2)]*` succeeds where the bare RHS fails).

#### D. Spread vs capture: parenthesized spread, grouped-spread receiver, selection forms

**Steps:** #103 PROPOSES `(Values...).Sum`, allowed only for a variadic receiver parameter. -> #104 (0e9b41f) IMPLEMENTS a parenthesized-supply receiver helper, later parenthesizedSequenceSpreadReceiver?. -> #105 (b8a1bca) and #112 (4685ba0, hasLeadingFlatVariadicParameter) WIDEN receiver expansion to flat variadic callees. -> #140 (73648e9) STATES that parentheses around a supply perform capture: A*.F ≡ F(A*), and (A*).F is an arity error for a fixed F. It keeps the exception GROUPED_SPREAD_RECEIVER_FEEDS_LEADING_COLLECTING. The #140 comment / 7c1da97 ADDS A*:0 invalid (SpreadSelectionDiagnostic), (A*):0 as capture-then-select, and A:0* ≡ (A:0)* as select-then-spread. -> #144 (f12af0f, 2026-08-11) REPLACES the exception with the general receiver-segment rule and deletes parenthesizedSequenceSpreadReceiver?. -> #167 68b3607 (2026-09-21) REVERSES that: dot-call passes a value, and (R*).F ≡ F((R*)) for every callee (GROUPED_SPREAD_RECEIVER_CAPTURES). -> #168 (50c74c1, 2026-09-22): a single non-spread-slot group is erased, so (A)* is literally A*, while a lone-spread group (A*) survives as Expr.Capture.

**Surviving semantics:** (E*) is a capture: one sequence value, not redundant grouping. (E)* ≡ E*. A*.F ≡ F(A*), including implicit-parameter inference. (A*).F ≡ F((A*)) for every callee, collectors included. A*:0 is MisplacedSpread; (A*):0 captures then selects; A:0* ≡ (A:0)* selects then spreads. Probe with A=(1,2,3), Coll(*xs)=xs: A*.Coll=L[1,2,3], (A*).Coll=L[S[1,2,3]], (A)*.Coll=L[1,2,3]. With A=[[1,2],[3,4]]: (A*).count=2. Historical only: the variadic-only dot-receiver spread, the leading-collector grouped-spread exception, and receiver segments.

#### E. Layout: newlines and whitespace around the marker

**Steps:** #104: binary `x...y`, and a leading `...A` continued the previous line. -> #119 (ac15218, 2026-06-04) PROPOSES + IMPLEMENTS that a line ending in `...` continues onto the next line (`A...` + newline + `A` = SequenceSupply(A, A)); `A...,` ends it. -> #122 (2026-06-11) REVERSES #119: postfix `...` does not force continuation. -> #123 (007917a) REFINES with one ContinuationPolicy: `...` is same-line only, postfix `...` absorbs the chain including newline-joined rows, and supply in open targets is rejected at parse time. -> #124 (4b32111): no right operand, so `A...` + newline + `B` = (A...) ; B. -> #125: newline and adjacency become implicit commas, giving two slots. -> #140 (73648e9, 2026-07-29) NEW STAR LAW: any same-line operand after a star means multiplication, so a comma is required after a spread. Newline rule: an attached line-final star is a spread, a detached one multiplies. -> #161 (cb6cfda, 2026-09-11, SYN-07B) REVERSES the newline rule: the next significant token on any line decides, and a declaration head is never an operand. It ADDS the marker attachment law (InvalidSpreadMarker), and open-target spread moves to open-form validation. -> #160 (2b03c0b) makes same-line adjacency an error. f7ee8ea adds LineFinalStarContinuationDiagnostic. -> e4d19cc (2026-09-20): a star before `not` is a spread marker. -> 2a140c9 introduces one StartsDeclarationAt relation.

**Surviving semantics (Q-65 revision, 2026-10-14):** A physical line-final `*` has multiplication priority, attached or spaced (current SYN-11): *(Issue #183, 2026-10-14: superseded — current SYN-11 classifies a line-final star by attachment: attached spreads and completes, detached multiplies; the probes below that rely on an attached line-final star multiplying are history)* a newline, EOF, a declaration on a later line, or a later comma or closer never retroactively turns it into a spread marker, and comments or blank lines cannot close it. The postfix spread marker needs explicit same-line closure or separation — a same-line comma, closing delimiter, fluent dot or a further closed spread layer (`F(A*)`, `A*, B`, `[A*]`, `Data[A*]`, `A*.F`, `(A**)`) — and is then checked for direct attachment (IsPostfixSpreadMarkerStar, ParseSpreadMarkerContinuation, IsDirectlyAttached; a detached `F(A *)` is InvalidSpreadMarker). A same-line operand after the star still means multiplication. Consequences: a comma is required between a spread and the next item (A*, B / A*, + newline + B); a definition body or deconstruction RHS that ends in a spread closes it on the same line, as (A*) or { A* }. A `*`-led line continues multiplication unless it begins a collecting declaration (`*r = 4, 5`). Prefix collecting syntax and spread VALUE semantics are unchanged. Probes: A*+newline+B gives 6; 7*+newline+8 gives 56; 7* at EOF is an incomplete multiplication (parse error); A*+newline+B = 5 reports the dangling multiplication and preserves B; A*,+newline+B gives S[2,3]; F(A *) gives InvalidSpreadMarker; A*+newline+not x is a misplaced `not` operand (parse error); `x, y = V*`+newline+`x + y` parses as `x, y = (V * x) + y`. Lean is untouched (surface syntax only).

#### F. Spread in call assembly: no implicit opening, expansion before binding, and the collector detour

**Steps:** #57 (variadic builtins inline). -> #61 (17e34bd) and #71 (c876d28) DECIDE that an argument never spreads implicitly. #72 removal attempt reverted. -> #101 (5555cd1): fixed calls bind written slots. -> #103/#104: an explicit `...` supplies items, and a normal segment is one item. -> implicit opening RE-ENTERS for collectors and receivers: #104/#106/#108 stream provenance, #111 (4c9877d) variadic-slot supply, #105/#112 receiver expansion. af92bad (#99) keeps a patterned-step `;`-join row as one packed state slot. -> #125 (ad75720) introduces strict one-sequence variadic destructuring. -> #126 (416e9c7, d2837f4) REVERSES it with singleton-boundary normalization, so G(A) ≡ G(A...). -> #131 (7e1085e) REAFFIRMS that spread expands before `if` arity; #159 (0243678) removes the parser gate. -> #135 (0ca55e9) makes builtins take a fixed collection. -> #138 (ab7d2f5) REVERSES #126: exact lists, F(A) ≠ F(A*), and VariadicStreamEnv is deleted. -> 245b10c (July audit F03) DISCOVERS + FIXES that spread did not expand for patterned and clause callees; one shared assembly stage now expands before binding. -> b638c24 (2026-08-08) DISCOVERS + FIXES Lean expanding builtin spreads rightmost-first; it pins spread-first, left-to-right expansion with non-spread slots lazy. -> #144 (f12af0f) receiver segments. -> dada1b6 collector supply-boundary law. -> 702e7d7 (C-full, #167) REVERSES both: a non-spread argument is one item, and only v* opens.

**Surviving semantics:** Every spread slot expands into ordinary argument slots before arity checking, clause selection and pattern binding, for every callee shape including builtins. There is no parser arity by spelling. Every non-spread slot is one item (BuildCallArgumentInputs / collectVariadicCallItems; expandSequenceSpreadBuiltinArguments). Probe: F(0,0)=100, F(a,b)=2, P=0,0 gives F(P*)=100. Intentional exception: if/while/repeat/range/atoms force spread slots first, in written order, and keep non-spread slots lazy (range(trace(1), trace(3)*) logs [trace(3), trace(1)]). Receiver-specific survivor from the join era: a sequence-value-patterned loop step keeps a top-level spread output row as one packed next-state slot (evalAlgOutputSlots preserveSequenceSpreadExpressionBoundaries, KatLang.lean:5170-5210, C# Evaluator.Loops.cs:81/107). Probe: Step((a,b)) = (b, a+b)* gives S[2,3] n=1, while the flat step gives n=2. No dedicated pinning test was found.

#### G. Marker orientation: collecting binding vs spread expression

**Steps:** #73 (3bc2a29): postfix `name...` collects. #103/#104: postfix `expr...` also spreads, so one spelling serves two opposite operations. -> #139 (eab2468, 2026-07-24) SPLITS BY ORIENTATION: prefix `...name` collects, postfix `expr...` spreads. It adds a single-target `...items = RHS` and plans a deprecation period. -> 41c0bb6 drops the deprecation, making postfix rest a hard error. 5377b9c adopts 'collecting binding' / 'spread expression'. -> 09382b3 (2026-07-28) REVERSES: collecting goes back to postfix `name...`, and spread becomes the reserved `spread(x)` / `x.spread`. -> #140 (73648e9, 2026-07-29) REPLACES THE SYNTAX and restores #139's orientation with a new glyph: prefix `*name` collects, postfix `x*` spreads, infix `*` multiplies. It states spread(collect(xs)) = xs. -> #161: the attachment law also covers `*name` (InvalidCollectMarker).

**Surviving semantics:** Prefix `*name` (binding positions only, attached) is collect : Supply -> ListValue. Postfix `expr*` is spread : Value -> Supply. Infix `*` is multiplication. At most one collecting binding is allowed per pattern level. Forwarding is ordinary list spread: Forward(*items) = Target(items*) ≡ items*.Target (forwarding_resupplies_the_collected_items). Historical only: name..., ...name, the deprecation plan, and the reserved spread intrinsic.

### Area: variadic-forwarding

#### Builtin variadics: added, removed, reverted, retired

**Steps:** #57 2f27fba (04-17) PROPOSES+IMPLEMENTS sequence builtins taking several top-level values -> #61 17e34bd (04-19) REFINES argument boundaries -> #72 f2898cb (04-23) REMOVES builtin variadics -> #72 4367f57 (04-24) REVERTS removal (sum(1,2,3,4) must work; first-class sequence / [ ] rejected) -> #80 5172e62 (04-28) REFINES with 'single-source expansion, comma-boundary preservation' law -> c147585 (05-04) shared variadic binding -> #125 ad75720 (06-17) CHANGES to strict one-slot destructuring -> d2837f4 (06-19, no issue) CHANGES to item-stream normalization -> #134 d202b74 (07-16) REVERSES the [ ] rejection (lists) -> #135 0ca55e9 (07-17) CHANGES FUNDAMENTAL RULE: one fixed collection parameter + post-binding one-level view, normalization helper deleted -> #138 REAFFIRMS no variadic collection builtins -> 68b3607 (09-21) REAFFIRMS no sequence-builtin dot path

**Surviving semantics:** Collection builtins are fixed-arity with ONE collection parameter read one level after binding (sum(1,2,3,4) is ArityMismatch; (1,2,3,4).sum == sum((1,2,3,4)) = 10). Only repeat/while keep a variable initial-state tail (BuiltinRegistry.AcceptsArity: repeat >= 3, while >= 2).

#### User collecting parameter shape, allocation, arity

**Steps:** #73 3bc2a29 (05-04) PROPOSES+IMPLEMENTS name... (one per list, front/back fixed first, middle collected, no ~, explicit only, rejected in clause families) -> 21467f3 (05-08, no issue) NARROWS 'explicit only' (lifted variadic shapes, shape forwarding; aliases infer collectors) -> #99 af92bad (05-08) EXTENDS to nested (xs...) patterns; Stage 2 for clause families never landed -> #126 416e9c7 (06-19) EXTENDS matcher to deconstruction, arity metadata -> 2d47a93 (09-22) REFINES zero-argument demand (collecting-only callable is a value: Only = []) -> 29c94b8 F4 (09-22) arity facts per level -> 5d6d60b D1 (09-23) REFINES failure order around the collector

**Surviving semantics:** At most one collecting capture per pattern level (Parser.cs:3006/2252), no Grace on it (3270), none in clause families (1558). Fixed captures bind front and back first; the collector takes the possibly empty middle. Minimum supplied slots = top-level patterns minus 1 if a top-level collector exists (minimumSuppliedSlots, KatLang.lean:181); a collecting-only callable satisfies a zero-argument value demand.

#### What a collector receives from one structured argument (oscillating rule)

**Steps:** #73 3bc2a29 + #89 5cf09fc (05-04) PROPOSE lone source (receiver or plain arg) feeds its items (Qmean(Arg)=2, Arg.Group.count=3) -> #104 0e9b41f (05-13) REMOVES plain-call half (test rewritten to Qmean(Arg...)) -> #105 b8a1bca (05-13) keeps receiver expansion -> #111 4c9877d (05-14) RESTORES as variadic-slot sequence supply after allocation -> #112 4685ba0 (05-15) REFINES receiver = ordinary leading segment -> #125 ad75720 (06-17) CHANGES to strict one-sequence destructuring -> #126 416e9c7 (06-19) REVERSES via singleton-boundary normalization (recursive) -> e6c2bdc (07-11) REMOVES user-call normalization (canonical capture keeps visible coincidence) -> #138 ab7d2f5 (07-18) CHANGES FUNDAMENTAL RULE: exact, F(A) != F(A*) -> #144 f12af0f (08-11) NARROWS: receiver segments feed raw rows -> #167 68b3607 (09-21) REVERSES #144 -> #167 dada1b6 (09-21) CHANGES: lone written sequence opens one level (SupplyOrigin/collectorSupply) -> investigation (09-23) DISCOVERS seq/list asymmetry, recommends B-full -> #167 702e7d7 (09-23) C-full CHANGES FUNDAMENTAL RULE (maintainer chose C-full), deletes SupplyOrigin/collectorSupply/Origin algebra

**Surviving semantics:** Exact collector law: a non-spread argument supplies exactly ONE item whatever its value or origin (Coll((1,2)) = [(1,2)], Coll(()) = [()], Coll([1,2]) = [[1,2]]); only postfix v* opens one sequence-or-list boundary and spread items are never reopened; the collector collects exactly its allocated items. F(A) and F(A*) coincide only for non-structured values.

#### Collected result kind: canonical sequence -> exact list

**Steps:** #73 (05-04) PROPOSES canonical sequence capture -> #126 (06-19) REAFFIRMS 'one grouped sequence value' -> #135 (07-17) REAFFIRMS scope guard (Inspect(7) -> 7) -> #138 ab7d2f5 (07-18) CHANGES FUNDAMENTAL RULE: capture/collect/open triple, every collecting binding is ONE exact list -> fa381ae (07-19) IMPLEMENTS in paper algebra -> 245b10c (07-20) EXTENDS empty loop collectors to [] -> 5377b9c (07-27) RENAMES collectRest -> collectSegment

**Surviving semantics:** Every collecting binding (parameter, mixed list, nested pattern, deconstruction, loop step) materializes one exact immutable list with emitted count 1: [] / [x] / [a, b, ...], never singleton-erased (collectSegment = Result.listValue, KatLang.lean:2889; CollectSegment Evaluator.ParameterBinding.cs:561).

#### Forwarding collected arguments

**Steps:** 21467f3 (05-08, no issue) PROPOSES front-end implicit forwarding preserving variadic shapes + name-mismatched shape forwarding -> #104 0e9b41f/97867d0 (05-13) PROPOSES runtime stream-provenance exception -> #106 75f0d2b (05-13) IMPLEMENTS for top-level variadics -> #108 fd1a975 (05-14) GENERALIZES (VariadicStreamEnv / variadicSupplyEnv) -> #111 REAFFIRMS coexistence -> #138 ab7d2f5 (07-18) REMOVES provenance; forwarding = ordinary spread; resolver ForwardAsSpread iff SOURCE binding collecting -> #139/#140 RESPELL Forward(*items) = Target(items*) -> aa1d260 (09-14) REAFFIRMS as prohibition -> dada1b6 (09-21) interim: Use(items) = Target opened a sequence value -> 702e7d7 (09-23) REAFFIRMS no forwarding/alias mechanism silently spreads -> 5d6d60b (09-23) sibling: forwarded callable keeps algorithm channel in invoking slots

**Surviving semantics:** spread(collect(S)) = S: Forward(*items) = Target(items*) re-supplies exactly the collected items; the unspread list is ONE argument; no runtime supply provenance. Front-end implicit forwarding (C#-only elaboration) matches by name, or by shape for a lone-collector caller to a one-collecting-stream callee, and inserts name* iff the caller's source binding is collecting (ImplicitArgumentResolver.cs:1878-1893). An alias of a collecting callable elaborates to Alias(*xs) = Cnt(xs*).

#### Dot-call receiver into a collector

**Steps:** #74 b3af83b (04-25) PROPOSES receiver = one leading argument, carve-out 'reserved for variadic parameters for sequence builtins' -> #89 5cf09fc (05-04) IMPLEMENTS carve-out for user variadics (inline == named, items feed collector) -> #105 b8a1bca (05-13) REFINES (1,2).Mean == Mean(1,2) -> #112 4685ba0 (05-15) REFINES receiver = leading segment with callee-dependent boundary flag (hasLeadingFlatVariadicParameter; (A*).F leading-collector exception) -> #125 (06-17) REAFFIRMS P(receiver, args) never P(receiver..., args) -> #138 (07-18) REAFFIRMS A.Inspect = [[1,2]] -> #144 f12af0f (08-11) DISCOVERS regression and CHANGES to receiver segments -> #167 68b3607 (09-21) CHANGES FUNDAMENTAL RULE: [receiver] ++ args, callee-independent -> dada1b6 (09-21) briefly re-obtains averaging -> 702e7d7 (09-23) removes it -> #168 50c74c1 (09-22) REMOVES ((...)) vs (...) difference -> #170 ebf623e (09-27) REAFFIRMS receiver as ordinary cache consumer

**Surviving semantics:** Dot-call passes a value: R.F(a) == F(R, a), R*.F(a) == F(R*, a), (A*).F == F((A*)); a collector collects a receiver as ONE item ((1,2,3).Mean is an error; (1,2,3)*.Mean = 2); receiver origin and spelling never matter.

#### Reducer accumulator and callback element binding

**Steps:** <= c9a43fa (04-18) flat-callback row convention (last arg unpacked across remaining params; map([(1,2)], Add) = [3]) -> #80 5172e62 (04-28) reduce collection alignment -> #102 33b318a (05-11) PROPOSES+IMPLEMENTS accumulator-side variadic receives accumulator's top-level items -> #135 (07-17) REFINES reduce(collection, reducer, initial) fixed -> #138 ab7d2f5 (07-18) EXTENDS row convention to collecting callbacks (bindCountedCallbackParameterPatternList) -> 245b10c (07-20) REFINES initial accumulator reified as one value -> 73648e9 (07-29) RENAMES helper -> dada1b6 (09-21) REAFFIRMS in provenance form (accumulator/row slots finalItem) -> 5d6d60b S3 (09-23) REFINES nested callback patterns, records conventions unchanged -> 702e7d7 (09-23) CHANGES FUNDAMENTAL RULE: THE CALLBACK LAW, deletes row convention and accumulator-slot opening

**Surviving semantics:** map/filter bind F(element); reduce binds the ordinary two-argument call F(element, accumulator), each ONE argument (evalSequenceReduceStepCounted, KatLang.lean:5509). Acc(x, *acc) collects [acc]; Append(item, *history) nests; only an explicit pattern such as Append(item, (*history)) opens the accumulator; map([(1,2)], Add) is the ordinary ArityMismatch.

#### Loop-step collecting state

**Steps:** #96 6469363 (05-07) PROPOSES+IMPLEMENTS collecting step parameters over multi-slot state, one slot per written initial argument -> #99 af92bad (05-08) EXTENDS with (history...) group state -> #86 lineage NARROWS execution (collecting steps decline planning) -> #125 (06-17) REMOVES ; join formulation -> #138 / 245b10c (07-18/20) REFINES exact lists, empty [] -> dada1b6 (09-21) REAFFIRMS loop slots final -> 702e7d7 (09-23) REAFFIRMS loop state slots unchanged

**Surviving semantics:** Each written initial loop argument is one state slot (a spread supplies its items); step output rows define the next slots, a captured output is one slot; a collecting step parameter collects the current slots exactly (repeat(Step, 1, (1, 2)) with Step(*xs) = xs.count is 1; repeat(Step, 1, 1, 2) is 2).

#### Deconstruction with one movable collecting binding

**Steps:** #126 416e9c7 (06-19) PROPOSES+IMPLEMENTS x, y..., z = RHS with shared matcher, recursive lone-sequence opening, lone rest forbidden -> #138 ab7d2f5 (07-18) CHANGES rest to exact list, REAFFIRMS lone-rest ban -> #139 eab2468 (07-24) REVERSES ban (decon-lone-rest, not requested by the issue) -> opening becomes one level (structureItems?) -> d14f4a7 (09-13) CLARIFIES spread RHS / singleton-list opening -> f9615af F3 (09-22) diagnostics transparent -> open #157 pending

**Surviving semantics:** x, *y, z = RHS captures the RHS into one shared value, opens ONE lone sequence or list level, binds fixed front/back and collects the middle exactly into a list; *all = RHS alone is valid; sequence-valued items among the middle are never reopened; this unpacking never changes calls.

#### Collect/spread syntax and terminology

**Steps:** 3bc2a29 (05-04) name... collect -> #103 40f7745 (05-12) postfix spread, REVERTED a025cbe (05-13) -> #104 (05-13) ... as supply+join -> #119/#122/#123/#124 4b32111 (06-13) spread postfix-only unary -> b568c66 (06-18) 'supply' -> 'spread' -> #139 eab2468 (07-24) prefix ...name / postfix value..., deprecation -> 41c0bb6 (07-25) postfix rest hard error -> 5377b9c (07-27) RENAMES rest -> collecting binding -> 09382b3 (07-28) REVERSES orientation (postfix name..., spread(x)) -> #140 73648e9 (07-29) CHANGES to *name / x* / infix *, ellipsis token removed, 'collecting parameter' canonical -> 7c1da97 (07-30) value** = (value*)* -> #161 cb6cfda (09-11) NARROWS: layout-independent star, attached markers

**Surviving semantics:** Prefix *name is the only collecting-binding syntax, valid only in binding positions and directly attached; postfix expr* is the only spread, one unary node, with explicit same-line closure and direct attachment (current SYN-11/Q-65, 2026-10-14); every physical line-final star is multiplication, including EOF/later declaration/closer errors; *(Issue #183, 2026-10-14: refined — only a detached line-final star; an attached one is a completed spread)* infix * multiplies. name..., ...name, spread(x), x.spread are not KatLang syntax; 'collecting parameter' is the construct name.

### Area: dot-call

#### Receiver generality (extension calls on any value)

**Steps:** e0b23ef 2026-03-13 merges property access and extension call into one dotCall node -> #14 d901280 2026-03-30 implements 5.Square == Square(5) in C# (Lean already allowed any receiver) -> #79 9ce4a29 reaffirms that a recursive dot-call binds like the plain call -> #162 6ef913c refines it: values, argument-bearing edges and .string edges take the fallback, so 3.A.B == B(A(3)) -> 68b3607 makes a dot chain a nested call for the host-stack contract

**Surviving semantics:** Any expression may be a receiver. A non-algorithm value receiver takes the extension fallback. Fallback composes along the chain (3.A.B == B(A(3))). Probe p06: 3.A.B -> 50.

#### Fixed-parameter receiver boundary

**Steps:** #74 b3af83b 2026-04-25 proposes that the receiver is one argument ((3,7).F fails), using a receiver-only preserveArgBoundaries flag, plus an AGENTS carve-out letting sequence/variadic builtin dot paths expand the receiver -> #101 5555cd1 generalizes: plain fixed calls stop final-argument unpacking, so R.F == F(R) holds literally -> #112 4685ba0 reaffirms Values.Sum == Sum(Values), not Sum(Values...) -> #125 ad75720 reaffirms that dot never hides supply -> #135 0ca55e9 makes collection builtins fixed-arity, removing the carve-out's target -> f12af0f replaces the flag with InjectedDotReceiverLeading -> 68b3607 (#167) makes the receiver the ordinary first slot, deletes the machinery and the AGENTS carve-out bullet

**Surviving semantics:** The receiver's item count never satisfies arity, and a fixed parameter binds the receiver whole. (1,2).Add is ArityMismatch; (1,2)*.Add is Add(1,2). Laws: dot_receiver_fixed_binds_value and dot_receiver_count_never_satisfies_arity.

#### Collecting (variadic) receivers and receiver segments

**Steps:** #89 5cf09fc 2026-05-04 implements receiver expansion into the variadic ((10,20,30).TotalWithFee(5)=65) -> #104 0e9b41f regresses it and adds the (A...) supply receiver -> #105 b8a1bca re-fixes via callee inspection (CanBindReceiverAsLeadingFlatVariadic) -> #111 4c9877d extends variadic-slot supply to plain calls -> #112 4685ba0 refines: receiver = segment (EvalDotReceiverCallSegmentCounted), supply applied after allocation -> #125/#126 ad75720/416e9c7 move the effect to the collector (variadic destructures one sequence) -> e6c2bdc removes singleton opening -> #138 ab7d2f5 reverses: receiver = one captured slot, exact lists -> #140 73648e9 respells (*name, expr*) -> #144 f12af0f revives segment supply (CollectingSegmentEmittedCount; (1,2,2.718).Mean = 1.906) -> #167 68b3607 2026-09-21 reverses it and deletes segments -> dada1b6 re-introduces the effect through the collector supply-boundary law (SupplyOrigin) -> 702e7d7 2026-09-23 (C-full) makes it final: exact collector law, SupplyOrigin deleted -> #170 ebf623e reaffirms cache transparency

**Surviving semantics:** R.F(args) == F(R, args) and R*.F(args) == F(R*, args). A collector collects the receiver as ONE item. (1,2).Coll = [(1,2)]; (1,2,3).Mean is an arity error; (1,2,3)*.Mean = 2. There is no receiver segment, supply, carrier or dot-only binder. Laws: dot_receiver_is_one_collected_item and dot_receiver_with_suffix_is_one_collected_item. Spec case: dot-receiver-passes-a-value.

#### Spread and grouped-spread receivers

**Steps:** #103 40f7745 (reverted a025cbe) proposes receiver spread only for a callee with a leading variadic -> #104 0e9b41f adds the (Values...).Sum parenthesized supply receiver, gated by callee inspection in #105/#112 (HasLeadingFlatVariadicParameter) -> b568c66 renames it to spread -> #140 73648e9 2026-07-29 introduces fluent A*.F == F(A*) and makes (A*).F a capture receiver, but a leading-collector special case remains -> #144 f12af0f deletes the special case -> 68b3607 makes (A*).F == F((A*)), one value -> #168 50c74c1 keeps (A*) as a Capture; (A)*.F stays the fluent form

**Surviving semantics:** A*.F lowers to the lexical call F(A*): the items become argument slots and structural lookup is never used. (A*).F is F((A*)), one captured value. Probe p04: A*.F = 3, (A*).Coll = [(1,2)], A*.Coll = [1,2]. Probe p05: (A*).F -> ArityMismatch. Law: spread_dot_receiver_is_ordinary_spread_argument.

#### Empty receiver ()

**Steps:** #76 315dd54 2026-04-26 decides that an empty value is one receiver (filter(...).count = 0) -> #144 f12af0f narrows it for collectors: ().Collect supplies zero items and a named V=() gives [] -> 68b3607 restores it: valueCount 0 is never an implicit zero-argument supply, and only ()* supplies nothing

**Surviving semantics:** ().Coll = [()], V.Coll with V=() is [()], ()*.Coll = [], and ().One with One(a)=1 gives 1. Only the spread ()* supplies no items.

#### Builtin callees through dot (sequence-builtin dot path, property cache)

**Steps:** #34 cccffea proposes collection.sum == sum(collection) -> 48a03c8/e4630d0/22788b9(#60)/c9a43fa(#58)/17e34bd(#61) April 2026 implement a separate sequence-builtin dot path (trySequenceBuiltinDotCall) -> #74 carve-out allows receiver expansion on that path -> #135 0ca55e9 redefines the builtins (fixed collection parameter, 'A.count exactly count(A)') but the path is retained -> caf1a46/ee2b726 optimize it (lazy reification) -> an 2026-08-08 audit discovers A.sum read the cache while sum(A) did not -> 68b3607 deletes the path and routes the receiver through the one funnel (both spellings now bypass the cache) -> #170 ebf623e 2026-09-27: both spellings read the cache

**Surviving semantics:** A builtin binds the receiver as its ordinary collection/value argument through the ONE call funnel. A bare named receiver is judged by the zero-argument value-demand law and read through the property cache like count(A). How a value is consumed does not affect caching.

#### Fallback callee resolution and implicit inference

**Steps:** Before Aug 14 the fallback saw lexical declarations only and member names were never implicit parameters -> #147 2026-08-14 problem: K(a,t)=a.t failed; an uncommitted runtime gate (DotCallMemberUsesParameterChannel) was superseded -> 6c63486 implements Expr.DotCall.LexicalFallback elaborated by ShouldRewriteAsParam (member still never an implicit parameter) -> d21b163 2026-08-16 reverses that: MAY-selection inference, order receiver, fallback, args (K=a.t -> (a,t)); an uncommitted fallback-call order (t,a) was rejected; closed lists use MUST -> 600fedd codifies -> #154 b3738b9 extends fallback to prelude aliases (Math.cos(1) -> cos(Math,1) ArityMismatch) -> G-24 ef0f1cf refines diagnostics only: a missing member on a known receiver is an ordinary fallback -> 68b3607 routes the fallback through callLexicalWithReceiverCounted -> evalResolvedCallCounted -> audit #8 ad6d6bf codifies rule 4

**Surviving semantics:** After a structural miss, R.F(args) is F(R, args) with F chosen by the ordinary owner walk, then opens, then promotion (algorithm-valued parameters and prelude aliases included). A fallback that MAY be selected participates in implicit-signature inference in the order receiver, fallback, arguments (K=a.t(b) -> (a,t,b)). A closed list asks MUST. Receiver knowledge is diagnostic-only (G-24). Spec cases: dot-member-higher-order-parameter, dot-member-fallback-implicit-signature, dot-member-fallback-in-closed-parameter-list, dot-fallback-on-known-receiver-stays-valid.

#### Grace on dot edges

**Steps:** 6c63486 2026-08-14 proposes an ExtensionOnly ~./.~ mode that skips structural lookup and .string (Obj~.V=99) -> the #147 reopening comment asks for a~.t == t(a) with order (a,t) -> 7496f5b (dangling, amended away) implements a parser lowering to Call -> d21b163 2026-08-16 reverses it: ~ is ordering-only on the same structural-first DotCall; base (a,t), graced (t,a); Obj~.V=42 -> 600fedd codifies -> #152 e82c301 adds a~t, b28567f removes it the same day -> #160 2b03c0b makes a~t UnseparatedSameLineItem -> F10 aaae65c narrows: Grace must be effective, so Grace on a bound name or under a closed list is InvalidGraceMarker -> #168 50c74c1 extends: (~a).V == ~a.V

**Surviving semantics:** a~.t and a.~t are the ordinary structural-first dot edge plus inferred-parameter ordering, and both infer (t,a). Grace never changes selection. K(a,t)=a~.t and Obj~.V are InvalidGraceMarker. a~t is a parse error. Spec cases: grace-dot-higher-order-implicit, grace-dot-keeps-structural-precedence.

#### Structural-first navigation and grouped receivers

**Steps:** e0b23ef merges access and extension into one node -> #58 c9a43fa preserves extra parenthesized receiver layers -> #143 7075071 2026-08-10 decides that (Obj).V is a capture with no structural members (falls back) -> until 09-12 every dot edge lifts to a memberless wrapper (Lib.Sub.Q reaches an extension Q) -> #162 6ef913c 2026-09-12 reverses that: structural first at every level via resolveDotReceiver/ResolveDotReceiver; a local-only or branch intermediate is LocalOnlyProperty (c621e81 spans) -> G-24 ef0f1cf -> K1-08 7300596 refines: select by declaration (private included), then check accessibility -> #168 50c74c1 partially reverses #143/#58: (Obj).V == Obj.V and (Lib.Sub).Q == Lib.Sub.Q; only multi-slot or lone-spread groups are capture receivers

**Surviving semantics:** An argumentless non-string receiver edge is navigated through its declared members at every chain level, identity-only. A declared-but-inaccessible or branch-only member is an error, never a fallback. Private members are reachable structurally. Redundant parentheses around a receiver are erased. Probe p06: Lib.Sub.Q=1, (Lib.Sub).Q=1, (Obj).V=5.

#### .string intrinsic

**Steps:** #32 6869338 2026-04-06 implements x.string as a dot-only numeric intrinsic -> 6c63486 has extension edges bypass it (5~.string = string(5)) -> d21b163 restores the intrinsic for graced edges -> #148 72414cc depth-charges the receiver path -> SYN-05/F9 make the receiver a zero-argument value demand and have arguments assembled then rejected -> #170 ebf623e reads a named receiver through the property cache

**Surviving semantics:** Both engines dispatch the intrinsic by member spelling BEFORE structural lookup and before the lexical fallback (Lean KatLang.lean:6472; C# Evaluator.DotCalls.cs:493). Obj={string=5; 7}; Obj.string -> '7'. This precedence is undocumented. R.string(args) evaluates and rejects the args without evaluating the receiver.

*(Q-45, 2026-10-10: "R.string(args) evaluates and rejects the args without evaluating the receiver" is SUPERSEDED — since Model C (2026-10-02) a non-empty supply is rejected by cardinality before any argument or the receiver is demanded, explicit spreads executing during its formation; the owner adopted this order as the law; `constitution.md` DOT-08.)*

#### Dot edge on the higher-order channel (adjacent)

**Steps:** resolveAlg lifts an argumentless dot to a zero-parameter wrapper (kept by #162) -> #156 04b5fc8 adds the qualified canonical Math.X native exception -> audit #8 gates it on registry metadata plus the NativeCall body

**Surviving semantics:** As implemented: Apply(Lib.F, 5) is ArityMismatch (wrapper identity), map(xs, Math.Abs) works, and an argument-bearing dot result is callable (Twice(10.Sub(1)) = 18). So R.F(args) == F(R, args) holds on the value channel only (open question).

#### Dot-call layout

**Steps:** #113 e75ec7d 2026-05-15: a same-line { or ( after a dot member is the call delimiter, whitespace allowed -> #123 007917a: a newline never continues a closed expression -> F7 makes declaration heads line-local; the spec case dot-chain-continuation (leading-dot continuation) was added in e6c2bdc

**Surviving semantics:** A same-line ( or { after a callable, including a dot member, is a call delimiter; a newline is not. A leading . continues a chain across lines.

### Area: conditional-patterns

#### A. From `when` branches to clause families (surface form and elaboration)

**Steps:** #16 d7b0f6c 2026-04-02 proposes/implements `F when (p) = body` (bind/litInt/group, ordered first match, singleton (b) adaptation) -> #26 d194100 04-05 adds shorthand `F(1) = 100` -> #27 dc5b9ad 04-05 removes `when` (only clause form; `when` is an identifier) -> #39 419100a 04-09 discovers regression (single-clause `Filter(x, predicate)` was conditional, could not call predicate) and changes rule: clauseGroupDefinitionKind/elaborateClauseGroup, one flat clause = ordinary algorithm, decided per whole group -> #73 3bc2a29 05-04 refines: collecting bindings rejected in families -> #99 af92bad 05-08 generalizes to recursive capture/sequence-value heads; Stage 2 (collecting in families) never lands -> ef26d7e 05-27 uniform clause visibility -> d8ac461 07-21 C# Conditional.Opens=[] (Lean docstring left stale) -> B2b 6168822/8910bb6 09-06 branch bodies elaborated like any body (nested families, branch-owned opens, closed resolver gate) -> 45bc855 09-18 variant-owned payload -> a2700f4 09-27 tutorial chapter

**Surviving semantics:** All same-name clauses of one body (even non-contiguous) form ONE group; the group is an ordinary Algorithm.User with a closed explicit parameter list iff it has exactly one clause whose head is only binders and nested sequence-value patterns, otherwise Algorithm.Conditional. A conditional tries branches in written order, first match wins, no match = NoMatchingBranch; only structural duplicates are diagnosed (no reachability check); `F()` heads are a parse error; single-branch flat-binder conditionals are evaluated as the equivalent user algorithm only as a host-AST fallback. *(2026-11-28, current-rule pointer: since the owner decision recorded that day (Q-49, RESOLVED BY DECISION) each later, nonduplicate clause of the same arity after an unconditional catch-all gets the non-blocking `UnreachableClauseAfterCatchAll` warning; dispatch is unchanged; `constitution.md` PAT-02, `open-questions.md` Q-49.)*

#### B. One outer call interface: top-level arity, explicit slots, spread first, output arity

**Steps:** #24 b034c4b 2026-04-05 proposes uniform top-level pattern arity (BranchArityMismatch) -> #25 a68c51f 04-05 extends to uniform top-level output arity in written rows (BranchOutputArityMismatch) -> #70 fe1e3fb 04-23 discovers #24 misapplied (`M((a,b,c))` flattened to arity 3) and changes mechanism: pattern parens structural at every level, matchCallPattern/matchCallBranches over EXPLICIT argument slots replace #16's normalized whole-argument-shape matching (surplus args no longer absorbed) -> #132 9a4c70f 06-27 conditional result becomes value boundary (reCountValueBoundary), weakening #25 rationale -> 245b10c 07-20 (F03) spread expands before clause selection (catch-all no longer absorbs a spread) -> bb43c8a 08-09 pins `conditional-clause-head-rejects-extra-arguments`, `conditional-singleton-head-binds-its-argument-whole`

**Surviving semantics:** The front end reports an error when clauses disagree on top-level pattern arity or on the number of written output rows. A non-group top-level head consumes exactly one explicit argument slot, a top-level group head one slot per element; surplus arguments are never dropped (NoMatchingBranch). Spread expands before selection. Nested pattern parentheses are structural at every level (unlike redundant expression parentheses). The selected branch result re-counts at the value boundary. *(2026-11-28, current-rule pointer: the uniform written-row output arity is kept by the owner decision of that day (Q-48, RESOLVED BY DECISION), because the declared outer layout is part of the algorithm's structure. The step "weakening #25 rationale" above concerns ordinary calls only: a loop step consumes the selected clause's row supply. `constitution.md` PAT-03, `open-questions.md` Q-48.)*

#### C. Closed branch inputs, Grace, and branch scoping

**Steps:** #19 fa8500f 2026-04-04 bug fix: branch body wired to callee scope (sees sibling/ancestor properties) -> #21 6dbcc0c 04-05 proposes/implements full-input-specification rule (no implicit params in branches, Grace forbidden) -> #22 01ffdd4 04-05 Grace span fix -> #23 f647dac 04-05 refines to static front-end check over EVERY branch (UndeclaredIdentifier) -> #54 6d7617e 04-16 conditional nested properties local-only (K1-08 7300596 09-14 refines to post-selection accessibility) -> 6c64e66 05-08 generalizes: every explicit parameter list is closed -> B2b 6168822 09-06 closed resolver gate for branch bodies -> F10 aaae65c 09-13 generalizes Grace half: ineffective Grace = InvalidGraceMarker

**Surviving semantics:** A branch body sees only its pattern binders plus ordinary lexical/property/open/builtin names; a free name is a front-end UndeclaredIdentifier in any branch, called or not. Grace is rejected in heads and branch output rows. Branch-local properties/opens are branch-owned and inaccessible outside the family (LocalOnlyProperty); a family cannot be an open provider (IllegalInOpen).

#### D. Literal patterns: integer -> string -> Boolean (+ C# decimal tier) and duplicate heads

**Steps:** #16 d7b0f6c 2026-04-02 litInt -> #20 9408e73 04-06 adds first-class strings and litString (exact, case-sensitive) -> #29 fe613f6/59b0250 04-06 adds DuplicateBranchPattern (front end + Lean runtime) -> #121 e054a6f 06-10 refines match-equivalence to respect repeated-name positions (Same(x,x) vs Same(x,y) not duplicates) -> #153 Decimal128 migration: C# LitInt(Decimal128) so decimal literal patterns legal C#-only (Lean litInt : Int) -> #165 e4d19cc 09-20 adds litBool (true/false keywords)

**Surviving semantics:** A literal pattern matches only a value of its own kind equal to it (numbers by structural Decimal128 equality in C#, strings exactly, Booleans by equality); a binder matches anything; structurally match-equivalent heads (binders alpha-renamed, literals by value, repeated positions significant) are rejected.

#### E. Family patterns vs ordinary patterns (lists, first-order binders)

**Steps:** #16 d7b0f6c 2026-04-02 establishes value-evaluated family arguments and singleton adaptation (patternSequenceValueMembers?) -> #39 419100a 04-09 discovers value-only family args break higher-order use and sidesteps (single clauses become ordinary; families stay value-only) -> #134 d202b74 07-16 ordinary patterns open lists (structureItems?), family matching stays sequence-only -> #135 0ca55e9 07-17 declares 'list patterns are deferred' and flips #70's guard test151oa (M(range(1,3)) 1 -> 0) -> 245b10c 07-20 documents singleton exception; family function-valued-argument error left as 'follow-up' -> f321843 09-08 Lean guard: family binder value-only -> SYN-12 7876d01 09-13 pins asymmetry as deliberate (spec + TutorialSemanticContractTests) -> a2700f4 09-27 user chooses DOC fix (tutorial 'matches sequences, not lists'), not a semantic change

**Surviving semantics:** In a family (any multi-clause group or any literal-bearing head), `(p1..pn)` with n>=2 matches only a SEQUENCE value of n elements (lists fall through / NoMatchingBranch); a singleton `(x)` matches any one non-sequence value WHOLE, lists included. Family binders are value-channel only and every argument is value-demanded before matching (a callable argument fails with its zero-argument demand error); a bare family in value position is NoMatchingBranch; family callbacks take each element as one argument; a family is rejected as a repeat/while step (misleading message).

#### F. Ordinary nested (sequence-value) parameter patterns and S3

**Steps:** #99 af92bad 2026-05-08 proposes/implements `(history...)`: one slot, one level, written-slot view explicitGroupItems?, scalar fallback singleton-only -> 34b8e0e 05-28 refines written-slot view -> #126 416e9c7 06-19 changes ordinary binder: scalar is one-item supply at EVERY group size; callback binder left strict ('Callback deconstruction is intentionally deferred') -> e6c2bdc 07-11 removes user-call singleton-boundary opening -> #134 d202b74 07-16 lists open -> #138/#139/#140 ab7d2f5/eab2468/73648e9 07-18..29 respell to `(*history)`, exact lists -> b78f4f9 08-07 patterned args evaluated exactly once -> #168 50c74c1 09-22 DELETES written-slot view (patterns open VALUES only; IdSeq((x)) rejects a pair in every spelling) -> F4 29c94b8 09-22 per-level MinimumSuppliedSlots -> S3 session 09-22 (committed 5d6d60b 09-23) discovers callback binder singleton-only in Lean+C#, fixes via ONE sequenceValuePatternItems -> C-full 702e7d7 09-23 callback element = one ordinary argument (row convention deleted)

**Surviving semantics:** A sequence-value parameter pattern consumes ONE supplied slot and opens that slot's VALUE exactly one level (a sequence or list opens; any other value is a one-item supply at every level and group size), then the ordinary prefix/collector/suffix binder applies; how the argument was written never matters; a nested collector collects the opened items as an exact list; direct calls, callbacks, loop state, and deconstruction share the one rule (Result.sequenceValuePatternItems / Evaluator.SequenceValuePatternItems).

#### G. Repeated names as equality constraints

**Steps:** #121 e054a6f 2026-06-10 proposes/implements: repeated name = equality constraint, first binding kept, families fall through; mechanism pairwise fold merge (mergeEqualValEnv/mergePatternAlgEnv), distinct callables with equal values accepted, algorithm-only rejected, repeated collecting names rejected -> fa381ae 07-19 introduces stale algebra-doc claim that surface rejects duplicate parameter names -> D1 session 09-22 (committed 5d6d60b 09-23) discovers fold-order dependence for 3+ mixed occurrences (P(A,5,Inc) vs P(Inc,5,A)) and changes rule by user decision: decided once per level when last contribution joins, pairwise compatibility (repeatedNameFailure/settlePatternRange; permutation-invariance laws) -> 5d6d60b 09-23 tightens: distinct callable identities reject even for two occurrences with equal values ('deliberately tightens the former two-occurrence rule')

**Surviving semantics:** In ordinary binders (calls, callbacks, loop state) a repeated name binds iff every pair of contributions is compatible: equal values and counted pairs; algorithm-channel repeats only when each carries a value and all share one callable identity (declaration + captured activations; dot results are fresh identities). Unequal value = ArityMismatch ('Bad arity'), algorithm-only = TypeMismatch, distinct identity = TypeMismatch; verdict order-independent. In families, matching uses plain value equality with the first binding and a mismatch falls through to the next clause. Repeated names are not constraints in deconstruction heads (DuplicateProperty) and may not include collecting names.

#### H. Binding failure order (D1)

**Steps:** #99 af92bad 2026-05-08 Lean bindPairs binds all patterns of a range first, then concatenates -> #121 e054a6f 06-10 merges become equality-checked; Lean still binds-then-merges, C# merged each pattern as bound (repeated-name conflict could hide later nested-arity/retained error) -> D1 session 09-22 (committed 5d6d60b 09-23) aligns C# to Lean failure ORDER (no Lean change for part 1)

**Surviving semantics:** Arity check first; without a collector every pattern binds left to right before any repeated name is decided; with a collector the prefix binds+settles, then the suffix, then the collector collects, then cross-collector names are decided; between names the innermost merge wins, within one merge a value conflict precedes an algorithm conflict. A later binding failure outranks a repeated-name conflict of the same range (P(x,x,(a,b)) with P(1,2,Bad) is the division by zero).

#### I. Assignment deconstruction (pattern destructuring by assignment)

**Steps:** #126 416e9c7 2026-06-19 proposes/implements `x, y..., z = RHS` via one shared matcher with singleton-boundary normalization (also for calls), lone rest banned -> e6c2bdc 07-11 removes call-side normalization -> #134 d202b74 07-16 lone list opens too -> #138 ab7d2f5 07-18 rest = exact list -> #139 eab2468 07-24 reverses lone-rest ban, respells `...name` -> #140 73648e9 07-29 respells `*name` -> d14f4a7 09-13 doc clarification -> F3 f9615af 09-22 synthetic $deconstruct frames diagnostically transparent -> C-full 702e7d7 09-23 reaffirms calls never open -> open #157 pending (static arity)

**Surviving semantics:** The RHS is evaluated once as a row of the enclosing body, captured, and a lone sequence or list opens exactly ONE level; then the ordinary prefix/collector/suffix binder applies with at most one collecting target (collects an exact list); a scalar RHS is one item; heads are flat (no nested patterns/literals); a call with the same supply never opens it.

### Area: booleans-conditions

#### Truth values: numeric 0/nonzero truthiness -> first-class Booleans

**Steps:** 47f47a8 (2026-03-13) ESTABLISHES numeric truth (comparisons/logic return 1/0; if = first numeric atom of flattened condition, no atom = badArity; while stops on cont = 0) -> b2eb2b5 (2026-04-08) FACTORS Result.truthValue? for if+filter -> #41/ee8180c (2026-04-08) SPLITS: filter strict singleAtomicTruthValue? (one atom), if keeps lenient first-atom -> #45/aa4ce72 (2026-04-19) EXTENDS producers (contains returns 1/0) -> #127/bc383c3 (2026-06-21) makes ==/!= total structural equality (still 1/0) -> #135/0ca55e9 + #136/c133952 (2026-07-17/18) REFINE: lists have no truth value (truth view Result.atoms sequence-only, languageAtoms split) -> H2 (2026-08-29, implementation-only) DAG-bounded first-atom search -> SYN-01/a8bcae7 (2026-09-10) REMOVES () as operator identity incl. logical ops -> #165/e4d19cc (2026-09-20, subject mis-cites #156) REPLACES: true/false value kind, reserved literals, litBool patterns, ONE view asBool?, truthValue?/singleAtomicTruthValue?/Result.atoms deleted, rejections badArity -> typeMismatch via booleanRequiredMessage, Booleans unordered, no numeric projection, true == 1 is false -> #166/a085f35 (2026-09-20) REFINES producers (comparison chains yield one Boolean)

**Surviving semantics:** Only Boolean values have a truth value; every condition, predicate and logical operand is read through the one view Result.asBool?/AsBool (a Boolean or a redundant singleton around one) and anything else is a typeMismatch naming the role and value kind. No 0/nonzero convention, no first-atom flattening, no Boolean<->number conversion (expectInt, arithmetic, range, Math natives, .string reject Booleans; atoms omits them). Booleans are unordered; ==/!= stay total and kind-exact (true == 1 is false). true/false are reserved literals and literal patterns (F(true) distinct from F(1)). Comparison chains, and/or/xor/not and contains produce Booleans; display lowercase.

#### Two-argument if and its side mechanisms

**Steps:** #15/5a6c550 (2026-03-30) INTRODUCES if(c, v) (false -> empty group), empty-operand identity in binary ops (+ unary propagation), and the C# parse-time spelling gate Parser.ValidateIfArity (2 or 3) -> #49/93a036d (2026-04-13) REMOVES/REVERSES the 2-arg form (builtinAcceptsArity .ifBuiltin 3; ValidateIfArity exactly 3 as a parse error) but KEEPS empty transparency -> b950d86 (2026-04-29) REFINES identity (() == () is 1) -> #131/7e1085e (2026-06-26) NARROWS parse gate (skipped for spread slots) -> 57e9ed0/f42195d (2026-08-08) REFINE if arity diagnostics (Lean payload expected=3 for if only) -> SYN-01/a8bcae7 (2026-09-10) REMOVES empty-operand identity (10 + () TypeMismatch) -> #159/0243678 (2026-09-10, SYN-05) DELETES ValidateIfArity: wrong-arity if is an evaluation-time ArityMismatch, inert when unevaluated

**Surviving semantics:** Builtin if has exactly one signature if(condition, whenTrue, whenFalse); arity is checked after spread expansion, at evaluation time, before any non-spread slot is evaluated (payload expected 3); no builtin overloading by arity; () is an ordinary value, never an operator identity (if(false, 1, ()) is legal, using it as an operand is a TypeMismatch).

#### if resolved by identity; spreading into if

**Steps:** Lean preludeAlg already declared if as an ordinary publicProp (0243678^:lean/KatLang.lean:6160) while C# ValidateIfArity (since 5a6c550) intercepted the spelling -> #131/7e1085e (2026-06-26) REAFFIRMS call assembly: spread expands into ordinary slots before the arity check (Lean unchanged; C# only exempted spread calls from the gate) -> #159/0243678 (2026-09-10, SYN-05) GENERALIZES: resolve -> ONE identity -> bind -> invoke; property/parameter named if shadows completely with no arity fallback; dot, spread, higher-order agree; reserved-if design ABANDONED; laziness belongs to resolved builtin; spread not made lazy -> #165 (2026-09-20) REFINES examples (numeric conditions now TypeMismatch)

**Surviving semantics:** if is not reserved; it is an ordinary shadowable prelude binding reachable as if(c,t,e), c.if(t,e), if(args*), and higher-order (Apply3(if, true, 10, 20)). A user-defined if is an ordinary eager callable with its own arity. Spread slots follow expression -> value -> supply and are evaluated before builtin if can choose a branch (even in a branch position).

#### if laziness, value boundary, lazy-slot demand and the property cache

**Steps:** 47f47a8 (2026-03-13) ESTABLISHES laziness (Lean evaluates only the selected branch) -> 6fe4f51 (2026-04-22) zero-arg cache introduced but builtin direct-call slots (if(1, A, 0)) bypass it (GAP, Lean identical) -> #130/daf8a4c (2026-06-26) FIXES: if re-counts the selected branch via valueCount (multi-output branch = one sequence value; mirrored in Lean) -> #129 (2026-06-26) REMOVES content, if(C,T,F)* opens -> #132 (2026-06-27) GENERALIZES the value boundary to all results -> F9/9f6cdfb (2026-09-13) REFINES: condition/selected-branch slots demand through the ONE zero-argument value-demand law (if(true, Inc, 0) is an arity rejection; previously entered Inc's body -> Unknown name) -> #168/50c74c1 (2026-09-22) REAFFIRMS if(true, (A), 0) == if(true, A, 0) -> 2d47a93 (2026-09-22) REFINES demand to follow actual call arity (if(true, Only, 0) is []) -> #170/ebf623e (2026-09-27) SUPERSEDES the slot cache bypass (if(c, A, B) reads A's one cached value)

**Surviving semantics:** When resolution selects builtin if: spread slots are expanded (evaluated) first, arity 3 is checked, the condition is demanded and must be Boolean, then exactly the selected branch is demanded under the zero-argument demand law (the unselected branch is never demanded), and the result is re-counted to one value (valueCount); a named zero-parameter property in a slot reads the run cache like any consumer. Shadowing if removes the laziness; a wrong-arity builtin if evaluates none of its non-spread arguments. Bare names in unselected slots are still resolved eagerly (open question).

#### Predicate results: filter predicate and while continuation flag

**Steps:** #3 (2026-03-08..04-06) ESTABLISHES while step shape: last output is the continuation flag (numeric nonzero then), no shape-transforming feature -> b2eb2b5 (2026-04-08) INTRODUCES filter with first-atom truthValue? -> #41/ee8180c (2026-04-08) REFINES: predicate must be exactly ONE atomic number, groups/multi/empty/strings rejected with badArity, never flattened -> #135 (2026-07-17) REFINES: lists are not truth values -> d59274e (2026-08-18) / 14bb037 (2026-09-07) IMPLEMENTATION ONLY fused-predicate parity -> #165/e4d19cc (2026-09-20) REPLACES: filter predicate result and while flag must be ONE Boolean (asBool?), typeMismatch roles 'filter predicate result' / 'while continuation flag (the step's last output)', splitContSlots returns Bool, a single-output step's slot is both state and flag -> #166 (2026-09-20) REAFFIRMS (chains usable as flags)

**Surviving semantics:** filter keeps an element iff its predicate result is true; the result must be exactly one Boolean (no flattening, numbers, lists, or ()-bearing sequences). while continues on true and stops on false, returning the current state without committing the proposed next state; the flag is the step's last output. Clause-family literal patterns true/false match only Booleans. Fused and planned paths reproduce the same rejections.

#### Prefix not and the logical operators

**Steps:** 47f47a8 (2026-03-13) ESTABLISHES numeric not at the prefix '-' tier (tighter than comparisons), numeric and/or/xor, both operands always evaluated -> #15/5a6c550 (2026-03-30) empty-operand transparency reaches logical ops (() and 7 = 7) -> 065152c (2026-08-29) REFINES: ^ binds tighter than prefix -/not on the left -> SYN-01/a8bcae7 (2026-09-10) REMOVES empty transparency -> #165/e4d19cc (2026-09-20) REPLACES: not/and/or/xor Boolean-only (requireBooleanOperand), still eager; MOVES not below comparisons and above and/xor/or (Parser.NotPrecedence = 4); misplaced not is an UnexpectedToken diagnostic -> #166/a085f35 (2026-09-20) REAFFIRMS placement over one chaining comparison tier (not a < b < c negates the chain)

**Surviving semantics:** Precedence runs or < xor < and < prefix not < the ONE comparison tier; not x > 3 is not (x > 3) and not a and b is (not a) and b; a not in a tighter operand position is a parse diagnostic. The logical operators require Boolean operands on every side and evaluate both operands left to right before applying (no short circuit). *(2026-11-26, current-rule pointer: `and` and `or` short-circuit since #202 (`65b1b136`), and only `xor` keeps both operands eager; `constitution.md` BOOL-04.)*

### Area: operators-comparisons

#### Power vs prefix minus (top of the ladder)

**Steps:** 25a8558 (2026-03-07, v0.7.3) ESTABLISHES PowerExpr = UnaryExpr [^ PowerExpr]: -2^2 = (-2)^2 = 4, right-assoc; generator documents '-3 ^ 2 is 9' -> 065152c (2026-08-29, no issue; memory power-unary-precedence, v0.8.181 'intentional BREAKING') REVERSES: PowerExpr = PostfixExpr [^ UnaryExpr], so -2^2 = -4, (-2)^2 = 4, 2^-2 = 0.25; Lean evaluation unchanged, only diagnostic tiers -> e4d19cc (2026-09-20) NARROWS the rule to prefix '-' as 'not' leaves the unary tier

**Surviving semantics:** ^ is the tightest binary operator and right-associative. Its base is postfix-level, so -a ^ b = -(a ^ b) and a negative base needs parentheses. The exponent may be unary (2 ^ -1). Evidence: Parser.ParsePower (Parser.cs:4256); spec power-unary-precedence (LanguageSpecCorpus.cs:160, Lean-derived S[-4, 4, 512]); ParserTests.Parse_PowerWithUnaryMinusBase_NegatesTheWholePower. Probe: -2^2, (-2)^2, 2^3^2, 2^-2 gives S[-4, 4, 512, 0.25] on all 5 paths.

#### Prefix not placement

**Steps:** 25a8558 ESTABLISHES not in the prefix-unary tier with '-', tighter than ^, numeric truthiness (not x > 0 = (not x) > 0) -> a6aaa80 (2026-06-15) WORKS AROUND it in the generator only: 'never not x > 0' -> 065152c (2026-08-29) REFINES: not goes below ^ (not 0^0 = not (0^0)) but stays above * and the comparisons -> e4d19cc (2026-09-20; commit says 'fixes #156', actually #165; the #165 body never asks for this) CHANGES THE RULE: NotExpr sits below the comparisons and above and/xor/or, and not becomes Boolean-only -> a085f35 (#166) REAFFIRMS it and adds the targeted MisplacedNotDiagnostic (UnexpectedToken for 1 + not x, a == not b, 2 ^ not x, -not x)

**Surviving semantics:** not binds below every comparison, arithmetic and power operator and above and/xor/or. So not x > 3 = not (x > 3), not a < b < c negates the whole chain, and not a and b = (not a) and b. A not where a tighter operand is required is a parse error at the keyword. A star followed by not is the spread marker. Evidence: Parser.NotPrecedence=4 (Parser.cs:3956); spec not-binds-below-comparisons and not-cannot-be-a-tighter-operand; SEMANTIC-ALIGNMENT.md:561. The generator's 'never not x > 0' (agent.md:315, katlang-generator.txt:1048) is a style residue, not law.

#### Comparison tiers and chaining

**Steps:** 25a8558 ESTABLISHES two C-style tiers (== != looser than < > <= >=); comparisons are left-assoc BinaryOp nodes returning 1/0, and the generator documents 'comparison and equality levels are left-associative' (3<2<1 silently gave 1) -> e4d19cc (#165, 2026-09-20) Booleans EXPOSE the defect: 1<2<3 becomes a TypeMismatch, 1==1==1 false, 1!=1!=1 true -> a085f35 (#166, 2026-09-20) CHANGES THE RULE: one comparison tier; Expr.Comparison(First, Links) with ComparisonOp disjoint from BinaryOp; adjacent pairs; every operand once, left to right; eager past false; the first error stops the chain; parentheses end a chain; never lowered to and -> 0eb66db (2026-09-26) AUDITS the claim 'a < b == c is false' (ComparisonChainAuditTests) -> 3a649c5 renderer fix (implementation) -> 762cb03 (2026-09-27) REAFFIRMS: differential oracle plus 22 mutants killed, no defect

**Surviving semantics:** All six comparison operators share one tier. Consecutive unparenthesized comparisons form ONE chain that is true iff every adjacent link holds (!= compares adjacent pairs only). Each operand is evaluated exactly once, left to right, incrementally. A false link does not stop evaluation; an error does, and later operands are not evaluated. Each link keeps its operator's operand rules and reports its error with its own two operands' context and span. A parenthesized comparison is an ordinary operand. Leading comparisons now continue a preceding complete expression under SYN-08 grammar priority (Q-65 revision, 2026-10-14); independent declarations retain priority. Evidence: Lean ComparisonOp (KatLang.lean:431), Expr.comparison (:850), applyComparison (:3510), evalComparisonCounted (:6776); C# Ast.cs:674, Parser.ExtendComparisonChain (:4049), Evaluator.ApplyComparison (Evaluator.Loops.cs:507), LoopExprPlan.EvalLoopComparisonPlan (:675); CoreTests ComparisonChains.lean; spec comparison-chains-compare-adjacent-pairs, comparison-chain-is-eager-after-false, comparison-chain-boolean-and-arithmetic-operands.

#### Equality: numeric-only to total structural equality

**Steps:** 25a8558 ESTABLISHES numeric-only == (a non-number operand is badArity) -> 5a6c550 (2026-03-30) makes () transparent for == too (() == 5 gives 5) -> 9408e73 (#20, 2026-04-06) EXTENDS: string==string is exact; a string mixed with any other kind is an error for any operator -> 1d1526c (#31) REFINES the mixed-kind error to typeMismatch -> b950d86 (#81, 2026-04-29) SPECIAL-CASES empty equality -> bc383c3 (#127, 2026-06-21) CHANGES THE RULE: resultValueEq is the derived structural BEq; different kinds are unequal, never an error (REVERSES the == part of #20/#31); no vectorization (A... == A... is a parse error) -> 73cdba2 (#128) (()) != () -> e6c2bdc (2026-07-11) REVERSES #128: (()) canonicalizes to () -> d202b74 (#134) EXTENDS to lists as an exact kind ([] != (), [7] != 7) -> cf6a650/da96a0f (#141), fb31a54: implementation only -> 7f0bab0 (#153) Decimal128 leaves -> e4d19cc (#165) REFINES: Boolean results, true == 1 is false -> a085f35 (#166) makes ==/!= chain links -> 50c74c1 (#168) REAFFIRMS at the parser: (()) and (7) are the very nodes () and 7

**Surviving semantics:** ==/!= are total, kind-sensitive structural equality over numbers, strings, Booleans, sequences and lists, recursive at every depth with the kind checked at each level. They return a Boolean and never fail. != is the negation of ==. Equality compares canonical values: singletons normalize, lists are exact. {} is not a value (MissingOutput). A spread is never an operand (MisplacedSpread). The same comparer serves contains, distinct and repeated-name binding. Evidence: Lean resultValueEq (KatLang.lean:2438); C# Result.ValueComparer (Result.cs:88); spec boolean-values-and-equality, empty-eq-family, string-equality-exact, distinct-structural-pairs. Probe: [(1,2)] == [[1,2]] is false, (1,(2,[3,(4,5)])) == the same value is true, [] == () is false, (()) == () is true.

#### Empty sequence () as an operator operand

**Steps:** 5a6c550 (2026-03-30, 2-arg if) ESTABLISHES () transparency for every binary and unary operator -> b950d86 (#81) CARVES OUT ==/!= (explicit empty equality) -> bc383c3 (#127) CARVES OUT ==/!= again (structural) and deliberately RETAINS transparency for the other operators (() > 10 gives 10) -> a8bcae7 (SYN-01, 2026-09-10) CHANGES THE RULE: the transparency arms are deleted in Lean and C#

**Surviving semantics:** () is not an identity for any operator. Binary arithmetic, ordering comparisons and logical operators reject it with TypeMismatch; not () gives TypeMismatch; -() gives ArityMismatch 'Bad arity'. () == () is true and equality stays total. Empty neutrality belongs only to capture/collect/spread. Evidence: spec empty-sequence-is-not-an-operator-identity (LanguageSpecCorpus.cs:3525); EmptySequenceOperandTests; Lean evalBinaryCounted SYN-01 comment.

#### Numeric leaf equality vs IEEE ordering (C# Decimal128 tier)

**Steps:** System.Decimal era: quantum-insensitive, no NaN -> 7f0bab0 (#153, 2026-08-20) DECIDES atom equality = Decimal128.Equals (NaN equals NaN, quantum ignored, consistent with GetHashCode) and IEEE ordering -> e90826f (2026-08-31) PINS spec nan-equality-vs-ordering (with a LeanExclusionReason) -> 38b5918 (2026-09-27) freezes the separate min/max signed-zero rule while == still treats -0 and 0 as one value

**Surviving semantics:** C#-only tier (Lean Int has no NaN, -0 or quantum). NaN == NaN is true, 0 == -0 is true and 1.0 == 1.00 is true, but ordering is IEEE, so N <= N is false. Merging by equality keeps the first representative: distinct((1.00, 1.0)) is [1.00] but distinct((1.0, 1.00)) is [1.0]; with P(x, x) = x, P(-0, 0) is -0 but P(0, -0) is 0. All probed on 5 paths.

#### Deep/shared value equality robustness

**Steps:** #141 (2026-07-31) finds a REGRESSION: == on ~10k-deep values crashes the host with a StackOverflow -> cf6a650 + da96a0f (2026-08-01) FIX: iterative, breadth-safe whole-value traversals -> fb31a54 (2026-08-17) FIX: exponential cost of equality/hashing on shared value DAGs, via reference-identity memoization

**Surviving semantics:** The same total structural equality, now process-safe at any legal depth and polynomial on shared DAGs. Host-safety policy, no Lean counterpart (SEMANTIC-ALIGNMENT.md:342-346). Tests: DeepValueRobustnessTests, WideValueRobustnessTests, SharedValueGraphComplexityTests.

#### Power evaluation precision and domain (#43)

**Steps:** 25a8558: Lean x^negative = 0 (silent truncation); C# double Math.Pow -> a90fdd4 (#43, 2026-04-10) IMPLEMENTS exact decimal squaring for integer exponents, Math.Pow fallback for fractional ones, and the NEW error 'zero cannot be raised to a negative integer exponent' -> b7e6ba1 (2026-06-10) REPLACES the Lean truncation with negativeIntPow (explicit errors) -> 7f0bab0 (#153) REPLACES the mechanism with Decimal128 -> ec48b91/B4 REFINES: certified integer powers -> 869c1bc (2026-09-13) GENERALIZES the a90fdd4 zero-base rule to every negative exponent -> numeric audit #6 REFINES: log1p band, DelegatedPower sign symmetry

**Surviving semantics:** ^ is computed in Decimal128 with certified integral exponents and no double Math.Pow anywhere in src/KatLang. 0 ^ x for any x < 0 is IllegalInEval (Evaluator.EvalPow, Evaluator.cs:3268-3273; Lean negativeIntPow, KatLang.lean:3167; spec pow-zero-base-negative-exponent). Other numeric details are C#-tier.

#### Logical operator operand kinds

**Steps:** 25a8558 ESTABLISHES and/or/xor/not with numeric truthiness and 1/0 results, both operands always evaluated -> e4d19cc (#165, 2026-09-20) CHANGES THE RULE: Boolean-only operands via requireBooleanOperand, Boolean results, still no short circuit

**Surviving semantics:** and/or/xor evaluate both operands left to right, then validate left, then right, and require Booleans (TypeMismatch otherwise). *(2026-11-26, current-rule pointer: since #202 (`65b1b136`) only `xor` keeps this order; `and` and `or` judge their left operand first and evaluate the right one only when the left does not decide; `constitution.md` BOOL-04.)* The tier order or < xor < and is unchanged since v0.7.3, with no recorded rationale. *(2026-11-28, current-rule pointer: the order stands, and since the owner decision of 2026-11-27 it has a recorded rationale — each side of an exclusive choice can express a conjunction, and the whole choice can serve as one alternative in a larger disjunction; `constitution.md` OP-01, `open-questions.md` Q-57.)* Probe: trace(false) and trace(true), trace(true) or trace(false) gives S[false, true] with all four traces. Evidence: Lean evalBinaryCounted (KatLang.lean:6704-6722).

### Area: property-caching

#### Status of caching: invisible optimization -> Lean-modeled semantics

**Steps:** #42 (2026-04-10) PROPOSES per-run memoization as an optimization -> 5a37525 IMPLEMENTS it, fenced off as non-semantic (CLAUDE.md 'Memoization Boundary'; Lean comments 'optimization only') -> 6fea03c REFINES the key for closed lexical properties -> 4a77f87 (04-21) REMOVES it, #42 reopened -> 6fe4f51 (04-22) REIMPLEMENTS it as the Stage-1 run cache with cached/uncached parity tests -> #110 (05-14) DISCOVERS it is observable (Math.Rand twins) -> d7629b6 excludes builtins, REVERTED by 1cac168 -> 489b77f (05-17) REDESIGNS random as Math.Random(start,end) and still records the cache as C#-only policy -> d843523 (05-18) CHANGES the rule: the cache is modeled in Lean as core semantics -> #170/ebf623e (09-27) REAFFIRMS and GENERALIZES it as semantic law

**Surviving semantics:** The zero-parameter property cache is observable, normative semantics modeled in Lean (EvalState.zeroArgPropertyCache). Purity is irrelevant: random- and host-backed properties follow the same rule. Zero-parameter host operations are prelude properties and are cached property-style.

#### Explicit A() freshness: accidental -> recursive -> local

**Steps:** 6fe4f51 makes A() uncached as a side effect -> #110 c7 PROPOSES 'A cached, A() fresh' -> #110 c9 PROPOSES recursive freshness -> 489b77f IMPLEMENTS it (FreshZeroArgCallContext installs an uncached cache for the whole call subtree) -> #110 c10 REJECTS it (library locality) -> e0599ba (05-18) REVERTS to local freshness -> d843523 MODELS local freshness in Lean -> 31f7c76 states it as 'neither reads nor replaces' -> ebf623e/#170 adds 'nor populates'

**Surviving semantics:** A() is a fresh evaluation of A's own body and neither reads, replaces, nor populates A's entry. *(Constitution audit, 2026-10-23: superseded in part by CACHE-PUB-1 (owner decision, 2026-10-22, #189, `586f32f3`): a qualifying zero-supply `A()` — including `f()` on a forwarded callable whose cell names a property binding — that finds the entry empty owns and establishes it; it still never reads or replaces an entry, and invoking builtin slots (callbacks, loop steps) name no binding and never establish one; PROP-06.)* Nested property-style reads inside it keep their caching. Invoking slots (callbacks, loop steps, f() on a forwarded callable) are explicit calls and therefore fresh. A planned-loop temp call bypasses only its own memo.

#### Cache key / binding identity: environment-sensitive -> declaration-keyed with exposure scope

**Steps:** #42 c1 finds 0 hits (key too context-sensitive) -> 6fea03c relaxes the key -> 6fe4f51 keys on environment REFERENCE identity -> d843523 Lean key: accessKind split + reprStr of the environments, last-store-wins insert -> dfd97c6 (08-10) FIXES a regression where a process-wide structural owner sentinel aliased entries of different owners (adds RunIdentity) -> f7554e9 key-completeness audit -> 31f7c76 F3 (09-12) DISCOVERS the C# per-call re-evaluation and the C#/Lean divergence and CHANGES the rule: exported = no environment component, local-only = declaring-owner activation, lexical/structural/opened spellings share an entry, first successful entry wins (TryAdd / insert keeps the existing key) -> 5eb8cb2 makes the declaration token a field -> #170 RESTATES it as 'semantic binding identity, not spelling or path'

**Surviving semantics:** The key is the declaring scope (identified structurally, with its declaration token) + the property binding + the run. Local-only bindings add the declaring owner's activation. All spellings of one binding share an entry, and a shadowing property has its own. The first successful entry wins and failures are never stored.

*(Q-37, 2026-10-11: "The first successful entry wins" is SUPERSEDED — the outermost successful property-style evaluation of a key owns its entry, and a re-entrant read never publishes; the key itself is unchanged.)*

#### Local-only properties: accessibility -> also cache scope

**Steps:** #54/6d7617e (04-16) makes ancestor-capturing and conditional-body properties local-only (inaccessible) -> c58ce3a and bc099fa REFINE exposure -> 31f7c76 F3 makes exposure DECIDE cache scope (exported = per run, local-only = per declaring-owner activation) and closes the exposure hole where a MAY-selected dot fallback was misclassified -> 7300596 K1-08 makes accessibility a post-selection activation check -> ad73df8 FE-4a changes representation only -> ebf623e shares a local-only entry across consumers within one activation

**Surviving semantics:** Static exposure classification decides whether a property value is per run or per declaring-owner activation, and the evaluator trusts it. A parameter-free helper inside a function is evaluated once per run across all calls, while a helper that reads a parameter is evaluated once per activation.

*(EXPORTED-DETACHED, November 2026: "the evaluator trusts it" is SUPERSEDED — both evaluators enforce the classification. An exported property is evaluated detached from its enclosing calls — the activations of the levels enclosing it that exist when its evaluation starts (2026-11-27: until then every activation that existed; see `decision-lineages.md`, "returned callables across detached reads") — and a captured parameter is read only through its lexical owner's activation, so a misclassified or host-built tree is refused (`UnknownName`, `LocalOnlyProperty`) instead of sharing a value across calls; correctly classified programs are unchanged. Current rule: `constitution.md` PROP-08 and RES-08.)* *(Follow-up, 2026-11-21: the refusal holds on the checked paths and is not unconditional — a retained local runtime-alias cell is not checked, formal ledger row R-1.)* *(2026-11-24: retained runtime-alias cells are judged at every reuse too — formal ledger row R-1, closed; PROP-08.)* *(2026-11-24, later: row R-1 is QUALIFIED, not closed, after the independent review `050804fe` — the reuse is judged before the channel runs, the demand decides the reads that follow, and an `open`-provided local-only member's admitted access is not recorded; PROP-08.)*

#### Loops and planned temporaries

**Steps:** #86/4ea6bcc (05-01) requires that the local property cache not leak across iterations -> f7554e9 audit: the per-iteration CacheIdentity token -> 761c3ef (09-06): mixed planned/fallback rows share the generic memo -> 31f7c76 routes exported temps through the run cache and keeps a per-iteration memo for local-only temps -> ebf623e EvalLoopIfArgument (a planned if reads the temp through the planned access)

**Surviving semantics:** A local-only step property is evaluated once per iteration. An exported one is evaluated once per run, across iterations and loop invocations. Generic and planned strategies are identical.

#### Builtin-slot bypass (B1): accidental -> recorded law -> spread by refactors -> reversed

**Steps:** 6fe4f51 wires the cache only into zero-argument access, so builtin arguments resolve to the bare algorithm (Lean identical) -> Aug-8 audit DISCOVERS that sum(A) and A.sum differ observably for random properties and leaves an open question -> 31f7c76 F3 RECORDS 'if(true, A, 0) evaluates A's body directly' -> 9f6cdfb F9 keeps it -> 68b3607 #167 (dot-call passes a value) SPREADS it to A.sum/A.count (the receiver-only cache reuse is removed as 'accidental') -> 50c74c1 #168 SPREADS it to (A).count, and syntax.md records 'never a cached value-position read' -> 2d47a93 extends it to Only.count -> #170/ebf623e (09-27) CHANGES the rule: a property argument's VALUE channel is the ordinary property read, the named algorithm is kept only as invoked/InvokedAlgorithm, .string reads the property access or a parameter's bound value; the change supersedes the F3, F9, dot-call, zero-arg and parentheses entries

**Surviving semantics:** How a property value is consumed never affects caching. Every builtin value slot in every spelling and grouping, if branches, loop initial state, reduce's initial value, .string (including a parameter's v.string), selection, forwarding, and callback bodies read the one cached value. Stale remnants remain in syntax.md:7 and Evaluator.DotCalls.cs:153.

#### Cache eligibility

**Steps:** #110 c4-6 (rand(x...) hack; zero-parameter properties 'look like variables') -> d843523: cacheable iff the declared params list is empty -> 9f6cdfb F9: one zero-argument value-demand law -> 2d47a93 (09-22) CHANGES the criterion to acceptsZeroSuppliedArguments (collecting-only Only(*xs) is cacheable; Only() stays fresh)

**Surviving semantics:** A property is cacheable exactly when an ordinary call supplying zero arguments can bind it. A builtin never qualifies.

#### Property redefinition / bound-once (the premise of caching)

**Steps:** #29 (04-05) finds silent first-definition-wins -> 59b0250/fe613f6 (04-06) add DuplicateProperty and DuplicateBranchPattern (front end and runtime) -> #42 relies on immutability as the premise -> #121/e054a6f makes a repeated name in ONE pattern an equality constraint (a distinct mechanism) -> #158/3f57517 EXTENDS the rule with ParameterPropertyCollision -> f7ee8ea adds the root exception -> #170: nested shadowing is a different binding with its own cache entry

**Surviving semantics:** One definition per name per algorithm (mixed property/clause forms included), no match-equivalent duplicate branches, and no property/parameter collision in the same or an enclosing owner. Nested shadowing by a property is legal and creates a new binding with its own cache entry. There is no LanguageSpec case and no language-rules section.

#### Failures, re-entrancy, re-derivation (edges of the law)

**Steps:** since 6fe4f51/d843523 failures are never stored -> #148/72414cc (08-17) CHARGES depth on AlgEnv thunk re-entry (re-derivation itself is kept) -> 31f7c76 first-successful-entry wins, re-entrant completions never replace it -> 989fcea F5 PINS the characterization FixedParameterDemand_ReDerivesTheArgument_AsBefore -> ebf623e removes successful-path re-derivation for v.string, and the docs now claim 'no consumer can re-run the body'

**Surviving semantics:** Failures are not cached, and the first completed success is the entry. As implemented, a fixed parameter whose argument failed at binding re-derives it on every read (probe p3: 3 ticks). A self-recursive property can return two different values for two reads (probe p4: (2, 0)). Both contradict the documented wording and are unresolved.

*(Q-37, 2026-10-11: the re-entrancy edge is RESOLVED BY DECISION — the outermost successful property-style evaluation owns the entry, so probe p4 gives (2, 2) and "the first completed success is the entry" is SUPERSEDED. The re-derivation edge was resolved earlier by Q-01, 2026-09-28.)*

### Area: open-ownership-modules

#### A. open as a declaration: form, target list, placement

**Steps:** pre-2026-03 `open = Lib` property syntax (historical; ca7cb5b 2021 load/join builtin props) -> 27f6d78 (2026-03-07) REDESIGNS as keyword `open t1, t2`, at most ONE per algorithm, `public open` rejected, forms resolve/dotted/load/`;`-combine/paren inline block, `open 'url'` sugar -> #6/599fe16 (03-08) AFFIRMS one construct + REQUIRES placement before properties/output -> 23d9a0c (04-26) REMOVES `;` combine open form -> 57e9ed0 (08-08) REMOVES paren declaration scopes (braces only) -> 7075071 #143 (08-09) makes `open (M)` BadOpenForm (capture) -> 50c74c1 #168 (09-22) SUPERSEDES for single slots: `open (M)` == `open M`; only multi-slot/spread capture rejected -> SYN-07A/#9 line rules (first target on open line, comma/leading-dot continuation only, missing-comma diagnostics). Gap discovered: open after a clause definition accepted (Parser.cs:1440; probe o1).

**Surviving semantics:** open is a declaration, not an output row; exactly one comma-separated open list per algorithm, written before properties and output rows; targets are resolve, argumentless dot path, brace block, string (sugar for load), or a direct load call; redundant parentheses are erased; `open (M, N)`, spread and operator forms are BadOpenForm; `public open` rejected.

#### B. Open-target visibility: private heads, public members (#18)

**Steps:** 25a8558/27f6d78 (03-07) ESTABLISH opens provide PUBLIC members only, structural access sees private, head lookup public-only -> #18/a362ba3 (04-02) CHANGES C#: private lexically visible head may be opened -> d80208b (04-15) ALIGNS Lean (13-day divergence), dotted steps still public -> ef26d7e (05-27) REFINES clause-family `public` must be uniform -> 7300596 K1-08 (09-14) private dotted step = NotPublicProperty before accessibility -> ad6d6bf audit #8 (09-23) MAKES STATIC: private/missing/branch-only step = UnresolvedOpenTarget.

**Surviving semantics:** `open Name` may target a lexically visible private head; open-provided names and dotted open steps select PUBLIC members only; structural dot selects DECLARED members including private ones; `public` affects nothing else.

#### C. Local-only members and accessibility (#54 -> K1-08)

**Steps:** 58c227b (04-15) INTRODUCES ancestor implicit-param capture -> #54/6d7617e (04-16) ADDS exposure: captured/conditional nested members local-only, implemented as SELECTION FILTER (lookupPropDefPublic? required isExported; structural access refused non-exported even inside owner) -> c58ce3a (06-04) REFINES discharge at user-algorithm boundaries ('open imports only public exported') -> bc099fa/98147b3 (08-08) impl refinements -> 31f7c76 F3 (09-12) COUPLES exposure to zero-arg cache scope, closes may-select fallback hole -> K1-08 intermediate ExposureRounds/CircularOpenExposure PROPOSED then ABANDONED (never committed) -> 7300596 K1-08 (09-14) CHANGES rule: selection never reads exposure, ONE post-selection accessibility law (memberAccessible?/IsAccessibleFrom), local-only = context-dependent, open provider must need no call (IllegalInOpen) -> e4c7973 (09-15) REPAIRS settlement (opened name read by sibling; head declared between opener and settling level) -> ad6d6bf audit #8 D6 (09-23) FIXES order-dependent open-provider charging -> ad73df8 FE-4a impl only.

**Surviving semantics:** Selection is by visibility only; the unique selected member is then checked by one accessibility law: accessible exactly where its declaration and an activation of every required owner lie on the site's lexical chain (inside the owner works, outside is LocalOnlyProperty); local-only public members participate in open precedence/ambiguity; clause families expose no branch members; an open provider must need no call and must not be a family or builtin; exposure classification is C#-only and trusted by the evaluator.

#### D. Evaluation context of opened members: isolation and prelude (#93)

**Steps:** 27f6d78 (03-07) ESTABLISHES strict isolation (no transitive opens), unwired open resolution, ambiguousOpen, owned-before-open -> #93/4131b6d (05-06) FIXES opened members not seeing sum/Math/if: named open wired to declaration site; 'open member call == owner-qualified call' with caller-site isolation -> 2db605a (05-26) FIXES front-end elaboration of opened loaded modules -> 55d5672 (05-27) EXTENDS: inline/load block opens wired to global prelude (wireOpenBlockToGlobalScope) -> d8ac461 (07-21) impl only -> ad6d6bf audit #8 (09-23) AFFIRMS host ops as prelude members everywhere; spelling dedup of named targets -> fa1ec12 (09-26) impl only.

**Surviving semantics:** A named open's members evaluate in their declaring lexical chain (ending at the prelude) and never see the opener; inline/string/load block opens see only the prelude; transitive opens are not imported; opens are consulted only after everything owned including the prelude; open-member == owner-qualified equivalence holds for direct calls only (in algorithm position `Box.G` is a 0-ary dot wrapper); `open 'u'` differs from `M = load('u')` + `open M` for free names. *(Superseded: Model C (2026-10-02) and Q-18 C-B3 (2026-10-05) make the equivalence hold in every position (DOT-09, MOD-06), and Q-31 H-P (2026-10-06) roots every loaded module at the prelude, so `open 'u'` ≡ `M = load('u')` + `open M` (MOD-08); Constitution audit, 2026-10-23.)*

#### E. Lookup order and the owner walk (#19, #54, #158/SYN-03, audit #8)

**Steps:** 25a8558/27f6d78 (03-07) ESTABLISH ownership-first (owned before opens) -> #19/fa8500f (04-04) FIXES branch bodies as lexical children of family owner -> 58c227b (04-15) INTRODUCES defective rule: captured ancestor param used only if no visible property of that name -> 3bc2a29 #73 (05-04) NARROWS (builtins exempt) -> b3738b9 #154 (08-24) NARROWS (whole prelude exempt; farther root property/opened name still won) -> #158/3f57517 SYN-03 (09-09) CHANGES: owner walk (SelectOwnedDeclaration + ParameterOwnership), parameter before property per level, opens after whole walk (inner open no longer beats enclosing param), NEW ParameterPropertyCollision, CompleteOwnership -> f7ee8ea (09-12) REFINES root phantom exemption -> ad6d6bf audit #8 (09-23) CODIFIES six ordered rules, host ops in every layer -> FE-1..FE-4b impl only.

**Surviving semantics:** Owner walk outward by owning scope, parameters (any kind) before properties per level, first owner decides, prelude outermost; opens only after the whole walk, level by level, one provider selects, two or more are ambiguousOpen; promotion only after both; a property may not share a name with a parameter of its own or an enclosing owner (root's phantom signature exempt); farther property vs nearer parameter and nested vs enclosing parameter are legal (nearer parameter wins).

#### F. Static open: head ownership, target validity, provider eligibility (F2, K1-08, audit #8)

**Steps:** 27f6d78/599fe16 (03-07/08) ESTABLISH head via direct lexical lookup (never through opens), builtin target illegalInOpen, call targets BadOpenForm, lazy failure -> pre-release audit (09-12) DISCOVERS `open X` inside `F(X)` opens farther property -> e6390ed F2 (09-12) CHANGES: head classified by owner walk, parameter head -> Expr.Param + OpenTargetIsParameter, never searches farther, root phantom excluded (CallableBindings), Lean elaborateOpenHead -> 7300596 K1-08 (09-14) ADDS provider rule (requiresArguments / clause family / builtin -> IllegalInOpen, OpenProviderValidator) -> ad6d6bf audit #8 D3 (09-23) CHANGES lazy failure into static validity: every written target must resolve (UnresolvedOpenTarget), head never through another open, builtin head of dotted target refused eagerly. Gaps: non-name dotted heads (`open 5.N`) unvalidated; provider rule stricter than zero-argument demand law. *(Constitution audit, 2026-10-23: the first gap was fixed 2026-09-29 (PV-11: `BadOpenForm` at the head, MOD-02); the second stays open as X-27/Q-58.)*

**Surviving semantics:** open is static and never opens a runtime value; its head is an ordinary owner-walk occurrence (a parameter-owned head is OpenTargetIsParameter); every written target must resolve (head through the direct declaration chain and prelude, dotted steps through public declared members) or it is UnresolvedOpenTarget; the final provider must need no call and must not be a clause family or builtin (IllegalInOpen). *(Constitution audit, 2026-10-23: since FWD-02 (2026-10-01) a static callable alias is refused too, while a runtime-target alias (META-S3-2, 2026-10-19) is a namespace of its own declarations and is accepted; MOD-04.)*

#### G. String-literal open sugar, load, and modules (#6, #51, #116, audit #13)

**Steps:** ca7cb5b (2021) load/join builtin props gated by downloader -> 25a8558 (03-07) Lean Expr.load + load elaboration judgment; 27f6d78 ADDS `open 'url'` sugar -> d609af2 (03-13) REMOVES Expr.load from Lean core (surface directive) -> #51 (04-14) REJECTS string-valued property as open alias (NOT_PLANNED, Lean cost) -> a5b13bd (04-15) rejects unresolved load on no-elaboration paths -> 2db605a (05-26) elaborates opened modules -> #116/f032be3 (05-28) one HTML load-site diagnostic + follow-on evaluation error (latter REMOVED by 2a140c9, 09-23: every front-end error blocks evaluation) -> 3331581 (08-07) cancellation -> 2fa449b (08-19) CHANGES to async-only DownloadCode -> b403b9d (08-30) REMOVES ambient HttpClient default -> 8910bb6 (09-06) ADDS branch-lazy deferred regions -> ee6f22a/19e4eaf (09-08) spans/limits -> 0243678 SYN-05 (09-10) EXEMPTS load (spelling-recognized) -> 7f8aa7e audit #13 (09-25) HARDENS: ModuleLoadTarget canonical URL identity, downloads charge MaxModuleCount -> 0eb66db (09-26) CHANGES failure model: missing module = analysis state, no Num(0) stand-in, never evaluated.

**Surviving semantics:** `load('literal')` is a static front-end directive allowed only in definition/open context and recognized by spelling; `open 'url'` == `open load('url')`; the module is spliced as an ordinary block at the load site (names resolve against the splice scope; open-held blocks see only the prelude) *(superseded 2026-10-06 by Q-31 H-P and Q-32 I-U: one prelude-rooted declaration per canonical URL per compiled program, whatever holds it — MOD-07..MOD-09; Constitution audit, 2026-10-23)*; ordinary visibility applies (structural sees all declared members, open sees public); a string-valued property is not an open alias (opening it provides nothing); an unavailable or refused module leaves the result unevaluable; a load-bearing clause branch is materialized only when selected.

#### H. Builtins as ordinary prelude bindings; builtin visibility in libraries (#15 -> #159/SYN-05)

**Steps:** #15/5a6c550 (03-30) INTRODUCES 2-arg if + parse-time spelling gate Parser.ValidateIfArity -> #49/93a036d (04-13) REVERSES to arity 3 (gate kept) -> #59/04fedfe (04-18) removes arity builtin -> 3bc2a29/#93 4131b6d/55d5672 (05) builtins visible inside opened libraries (prelude is base of every chain) -> #131/7e1085e (06-26) NARROWS gate for spread args -> 57e9ed0/f42195d (08-08) gate diagnostics aligned -> #154/b3738b9 (08-24) Math aliases as shadowable prelude bindings (reverses #48) -> reserved-if design (09-09) PROPOSED then ABANDONED (stash) -> #159/0243678 SYN-05 (09-10) CHANGES: ValidateIfArity deleted, builtins ordinary prelude bindings, identity not spelling or arity, nearer binding shadows completely, if laziness belongs to resolved identity -> e4d19cc #165 (09-20) Boolean conditions -> 09-22/23 zero-argument demand law, audit #8 host ops as prelude + Math contract by identity.

**Surviving semantics:** resolve -> select ONE identity (no arity overloading) -> ordinary supply -> bind that signature -> invoke; builtins, Math, Math aliases and host operations are shadowable prelude members visible from every lexical chain including opened libraries; a wrong-arity builtin call is an evaluation-time ArityMismatch; no layer branches on callee spelling except the deliberate `load` directive (the `.string` dot intrinsic is an undocumented second spelling exception).

#### I. Reserved names and library metadata (#10, #117, SYN-05)

**Steps:** #10/890fcd4 (03-13) REMOVES `self` -> #117/7feb4b1 (05-28) ADDS reserved private metadata Author/Version/Description -> c5c762e (05-29) REVERTS: no reserved metadata names, no dunder names, no License field -> #118/233a2ae (05-30) ADDS ordinary root DisplayDecimals property with host display meaning (tension) -> SYN-05 (09-09/10) GENERALIZES: no reserved-name mechanism of any kind, reserved-if abandoned -> e4d19cc #165 (09-20) true/false become lexer keywords.

**Surviving semantics:** The only reserved words are the lexer keywords div, mod, and, or, xor, not, public, open, true, false; Author/Version/Description/Name/self/if/count/Math are ordinary declarable names; `load` is declarable but not callable with call syntax; a declared root DisplayDecimals configures host display.

### Area: sequences-lists-values

#### A. Root output rows vs grouping (display is presentation)

**Steps:** v0.6 per-row 'magic grouping' -> #7 (2026-03-10, comment 1) DECIDES root comma slots are flat top-level rows -> #90 fd3cabe (05-14) REFINES display: (…) for a sequence row, separate rows, 'without changing evaluation semantics' -> #122 7b5fe7a/acbfa7d (06-10/11) REAFFIRMS rows are presentation only -> #125 ad75720 (06-17) REFINES: comma/newline slots; lexical zero-arg property access re-counts to one value (Lean .resolve arm Result.valueCount) -> #132 9a4c70f (06-27) REAFFIRMS root/body accumulation is NOT a value boundary -> 245b10c F02 (07-20) ADDS lone-root S:0 projection display exception -> #160 2b03c0b (09-12, SYN-07A) REFINES: same-line items need commas -> 874625a (09-21) REMOVES the lone-root projection exception (selection is one value)

**Surviving semantics:** Root/body output accumulation is an item supply, not a value boundary: each non-spread row slot contributes exactly one visible top-level output (including `()`), a spread row contributes its items; a named multi-output property/call is one sequence value (one row). Display renders sequences `(…)`, lists `[…]`, one row per emitted value; display is presentation only. Evidence: spec supply-three-rows (LanguageSpecCorpus.cs:522), empty-visible-at-root (:899); probe p01 S[S[3, 5], 7, S[1, 2, 3], 1, 2, 3].

#### B. First-class sequence values and result value boundaries

**Steps:** 47f47a8 (03-13) BASELINE Result.group + normalize -> #72 (04-23) REJECTS first-class sequences ('[ ] would basically be syntax sugar for (( ))'; f2898cb reverted by 4367f57) -> #88 (05-04) DECIDES one argument = one group, list.count = 1 'not a bug' -> #125 ad75720 (06-17) DECIDES parentheses make ONE sequence value; property with comma outputs is one value; fixed calls never open -> 504c981/a0b396d (06-18) RENAMES group->sequence value -> #127 (06-19..21) EXTENDS structural equality -> #130 daf8a4c (06-26) FIXES if to return one value -> #132 9a4c70f (06-27) GENERALIZES: every property/call/builtin/structural-dot result is one value (reCountValueBoundary), raw-count clause for rest -> e6c2bdc (07-11) PINS model (audit doc + semantic explorer) -> #135 0ca55e9/#138 ab7d2f5 (07-17/18) REFINE: producers/collectors return one exact list; REMOVE raw internal counts -> 245b10c (07-20) EXTENDS written-slot reification (F02) and reduce-initial (F09) -> 874625a (09-21) EXTENDS selection value boundary -> 68b3607 (09-21) EXTENDS dot-call passes a value -> dada1b6 (09-21) ADDS collector supply-boundary law (G((1..5)) with x.sum: err arity -> 15) -> 702e7d7 (09-23, C-full) REVERSES dada1b6 (values stay values) -> #168 50c74c1 (09-22) parentheses no boundary

**Surviving semantics:** Sequences are first-class values (store, pass, compare, select, nest, display). Every property/call/builtin/if/selection result is ONE value with emitted count Result.valueCount (0 for `()`, else 1; Lean valueCount :1316, reCountValueBoundary :2910; C# Result.ValueCount Result.cs:701, ReCountValueBoundary Evaluator.Builtins.cs:144). A non-spread argument supplies exactly one item whatever its value; only an explicit spread reopens. Documented non-boundaries: root/body output accumulation, while/repeat multi-slot state, strict single-value map/reduce callback-result contract.

#### C. Singleton normalization and canonical sequences

**Steps:** 47f47a8 (03-13) BASELINE normalize group [r] => r -> c647330 (03-22) REMOVES special ((...)) syntax: ((expr)) ≡ (expr) in all positions -> #58 c9a43fa (04-18) REVERSES locally: ShouldUnwrapParenthesizedPrimary keeps paren-in-paren layer ((1,7)).arity = 1 -> #125 ad75720 (06-17) DECIDES single-group unwrapping 'Not recursive' -> #126 416e9c7 + d2837f4 (06-19) ADDS looping singleton-boundary item-stream normalization for user calls and builtins (G(A) ≡ G(A...)) -> #128 73cdba2 (06-22) ADDS exception (()) ≠ () via emptySequence depth -> #133 7a7c202 (07-07, not on main; landed in e6c2bdc) FIXES builtin orphan singletons via shallow singleton-erasing combineCollectionResult -> July memo sequence-design-decision REJECTS 'always preserve grouping' proposal -> 8eec709 (07-09) FIXES pattern explicit-items orphans -> e6c2bdc (07-11) REVERSES #128 depth ((()) = ()) and confines singleton-boundary normalization to builtin binding -> #134 d202b74 (07-16) REAFFIRMS normalization, ADDS lists as exact escape valve ('deterministic, but not injective') -> #135 0ca55e9 (07-17) REMOVES pre-binding normalization and combineCollectionResult -> #143 7075071 (08-09) keeps kind-dependent layers as Capture -> #168 50c74c1 (09-22) REVERSES #58 layers: IsRedundantGrouping erases every one-slot non-spread group; explicitItems? deleted

**Surviving semantics:** No sequence value has exactly one element: ordinary construction/capture normalizes redundant unary sequence structure recursively (Lean Result.normalize :1162; laws normalize_sequenceValue_singleton, capture_singleton, normalize_nested_empty_sequence), `((1, 2))` IS `(1, 2)` and `(())` IS `()`; output-slot combine is shallow (combineOutputSlots :2827); list boundaries never normalize (list elements do). Grouping never suspends normalization. Probe p03: (7)==7, ((1,2))==(1,2), [7]==7 false, ([1,2])==[1,2] true.

#### D. The empty sequence value ()

**Steps:** #76 315dd54 (04-26) DECIDES empty receiver is still one argument (count 0) -> #81 e8f8b10 allows () (04-28) -> b8a24db REVERTS same day ('() and {} define an algorithm') -> b950d86 (04-29) ADDS reserved builtin `empty` -> #83 1ca8b3f (04-29) DECIDES no program output ≠ explicit empty output -> #104 (05-13) x... ≡ x...empty -> #125 ad75720 (06-17) state: count(()) is an error -> #128 73cdba2 (06-22) REVERSES #81: () is the visible empty sequence value, empty removed, {} not comparable, (()) ≠ () -> e6c2bdc (07-11) REVERSES (()) ≠ () -> #134/#135 (07-16/17) REFINE: [] ≠ (), exact nested empties via lists, empty filter = [] -> #138 (07-18) empty collecting = [] -> #143 (08-09) () is the empty-sequence node -> SYN-01 a8bcae7 (09-10) REVERSES operator transparency (() + 1 TypeMismatch) -> #165 e4d19cc (09-20) no truth value -> 874625a (09-21) selected () re-counts to 0; #167 v-original A:0.Coll = [] -> 702e7d7 (09-23) REVERSES: unspread selected () is one argument ([()]) -> F5 989fcea (09-22) REFINES: omitted arg / output-less arg / empty value / zero-item spread distinct -> #168 50c74c1 (09-22) (()) elaborates to the () node

**Surviving semantics:** `()` is a real empty sequence value: displayed `()`, comparable (`() == (())` true, `() == []` false), count(()) = 0, valueCount 0 so spreading it (or a result equal to it) supplies nothing, but as a non-spread slot/argument it is exactly one visible item (`Coll(())` = `[()]`, `(E, 5)` = `((), 5)`, `(E*, 5)` = 5). It is not an operator identity and has no truth value. `{}` is an output-less algorithm; forcing it is MissingOutput (message suggests `()`). `empty` is an ordinary identifier. Evidence: Lean emptySequence :869 (depth ignored), buildEmptySequenceValue :2916; spec empty-literal/empty-wrapped/empty-sequence-is-not-an-operator-identity/missing-output-not-a-value; probes p02, p09.

#### E. One-level opening: ungroup -> content -> removed (spread is the only opener)

**Steps:** #88 (05-04, comment 1) PROPOSES one-level opening, rejects atoms as unwrapping tool -> #91 5d1b52c (05-05) ADDS ungroup(value) one level -> #98 7ad022c (05-08) RENAMES to content -> #101 5555cd1 (05-11..13) USES .content as fixed-call workaround -> #103/#104/#111 (05-12..14) ADD postfix ... supply -> #124 4b32111 (06-13) spread postfix-only unary -> #129 7458502 (06-26) REMOVES content (spread covers it; if(...)... replaces T.content) -> #140 09382b3 then 73648e9 (07-28/29) RESPELLS spread(v) then v* -> SYN-05 #159 0243678 (09-10) REAFFIRMS no reserved builtin names

**Surviving semantics:** The postfix spread `v*` is the only general value->supply opener: it opens exactly ONE sequence or list boundary (Lean spreadItems :1273; C# SpreadItems Result.cs:803), never recursively, and spread-produced items are never reopened. atoms is the separate recursive projection. `ungroup`, `content`, `arity` are ordinary unresolved names (probe p08; EvaluatorValueBoundaryTests.Eval_Content_NoLongerResolvesAsBuiltin).

#### F. atoms: recursive flattening to one exact list

**Steps:** 47f47a8 (03-13) BASELINE atomsBuiltin (arity 1), Result.atoms recursive over group -> ee8180c (04-08) truth view reads atoms -> #88/#91 (05-04/05) REAFFIRM atoms as recursive, distinct from one-level opening -> #132 (06-27) REFINES: atoms returns one canonical sequence -> #134/#135 (07-16/17) lists opaque to atoms (atoms([1,2]) = ()), atoms deferred -> #136 c133952 (07-18) REVERSES list opacity: traverses sequences AND lists, always one exact list (atoms(7) = [7]); languageAtoms separate from truth view and hostAtoms -> #165 e4d19cc (09-20) truth view removed, Booleans contribute nothing

**Surviving semantics:** atoms(value) = makeCollectionListResult(languageAtoms value): numbers give [n], sequences and lists traversed recursively depth-first left-to-right, strings and Booleans contribute nothing; result kind never depends on input; fixed one-argument builtin (atoms(1, 2) ArityMismatch). Evidence: Lean languageAtoms :1185, laws atoms_* (KatLangArityLaws.lean:2093-2142), spec atoms-recursive-flatten (:2791), atoms-exact-list-result (:2802); probe p04 atoms(((1,2),[3,[4]])) = [1,2,3,4].

#### G. arity vs count

**Steps:** #34 9b3f1ff (04-09) ADDS count over one collection -> #56 732549d (04-17) RENAMES length intrinsic to arity; count = top-level values -> #58 c9a43fa (04-18) DECIDES count((1,7)) = 1, ((1,7)).arity = 1 -> #59 04fedfe (04-18) REMOVES arity entirely -> #60 22788b9 (04-18) FIXES (Data:0).count = 5 -> #88 (05-04) DECIDES parameter-bound group list.count = 1 -> #125 ad75720 (06-17) REVERSES: count((1,2,3)) = count(Values) = 3 -> #135 0ca55e9 (07-17) DECIDES mechanism: fixed count(collection) + post-binding builtinCollectionItems -> 68b3607 (09-21) REAFFIRMS A.count ≡ count(A)

**Surviving semantics:** count(X) is the length of the one-level collection view of the ONE bound value (sequence/list -> elements, other value -> 1; count(()) = count([]) = 0; never recursive). No arity/length builtin exists; 'arity' survives only as maintainer terminology. Probe p04: count((1, 7)) 2, ((1, 7)).count 2, count(7) 1, count((1, [2], 3)) 3, (Data:0).count 5.

#### H. Collection builtins take ONE collection

**Steps:** #34 cccffea/9b3f1ff (04-09) DECIDES one collection argument -> #57 2f27fba (04-17) EXTENDS to variadic order(3, 4, 2, …) -> #61 17e34bd (04-19) REFINES: argument expressions do not implicitly spread -> #69 d3ee6d7 (04-23) FIXES sum(P) -> #71 c876d28 (04-23) DECIDES comma boundaries kept, flatten only via ';', consumers 'content-based' -> #72 f2898cb (04-23) PROPOSES removing variadics -> 4367f57 (04-24) REVERTS to keep sum(1, 2, 3, 4) -> #111 4c9877d (05-14) ADDS variadic-slot supply -> #125 ad75720 (06-17) REVERSES: strict one-slot, count(Values...) arity error -> d2837f4 (06-19) REVERSES again: item-stream binding, sum(3,4,2,1,3,3) = 16, sum() = 0 -> #132 (06-27) results one sequence -> #133 7a7c202/e6c2bdc (07-07/11) shallow singleton erasure -> #134 d202b74 (07-16) defers lists (count([1,2,3]) type error) -> #135 0ca55e9 (07-17) REVERSES variadics and deferral: ONE fixed collection + controls, no pre-binding opening, post-binding one-level view, exact-list results -> #137/#136 (07-17/18) COMPLEMENT -> 68b3607 (09-21) REAFFIRMS: dot receiver fills collection, dot-only path deleted -> #170 ebf623e (09-27) REFINES cache reads

**Surviving semantics:** count/sum/first/last/min/max/avg/order/orderDesc/distinct(collection), take/skip(collection, count), contains(collection, item), map/filter(collection, cb), reduce(collection, reducer, initial), range(start, stop) are fixed-arity; an unspread sequence or list is ONE argument, nothing opens before binding (count(1,2,3), sum(), order(3,1,2), count([1,2,3]*) are ArityMismatch; re-group sum((A*, B*))); the bound value is read one level (builtinCollectionItems :2665 / C# Evaluator.ParameterBinding.cs:1663); producers return ONE exact list ([], [x], [x,…]; makeCollectionListResult :2842), take(((1,2),(3,4)),1) = [(1,2)]; result kind never depends on input kind; A.f ≡ f(A).

#### I. Exact lists []

**Steps:** #72 (04-23) REJECTS [ ] as 'syntax sugar for (( ))' -> #125 (06-17) table rows need explicit parens, no exact one-row form -> #128 (06-22) ATTEMPTS exact nested empties via depth (reversed 07-11) -> July memo IDENTIFIES dimension erasure at n=1 -> #134 d202b74 (07-16) ADDS exact immutable list kind (never normalized, kind-distinct, spread opens one boundary, calls never open, lone-list deconstruction opens one level; §9 rest = canonical sequence, §10 lone-rest forbidden; builtins/indexing deferred) -> #135 0ca55e9 (07-17) REVERSES builtin deferral -> #137 2c0af18 (07-17) ADDS list indexing via projectionItems -> #136 c133952 (07-18) EXTENDS atoms through lists -> #138 ab7d2f5 (07-18) REVERSES §9 (collecting = exact list) -> #139 eab2468 (07-24) REVERSES §10 -> #140 (07-28/29) RESPELLS * -> d14f4a7 (09-13) NARROWS singleton-list deconstruction claim -> #165 (09-20) no list truth -> #168 (09-22) ([1,2]) is the list -> 702e7d7 (09-23) GENERALIZES sequence/list symmetry (Coll([1,2]) = [[1,2]])

**Surviving semantics:** A list `[…]` is an exact, observably immutable, kind-distinct collection value: never singleton-normalized ([7] != 7, [[]] != [], [] != ()), structural equality; opened only by explicit openers (spread spreadItems, deconstruction/structural pattern structureItems?, `:` target positions projectionItems, builtin post-binding view, atoms, host flattening); toItems keeps it opaque elsewhere; calls never open it; `[` never begins indexing (A[1] is UnseparatedSameLineItem). Documented deferral: multi-clause family sequence-value patterns match sequences only.

#### J. Indexing and the selection value boundary

**Steps:** pre-04-18 BASELINE ':' preserves grouped structure verbatim -> #58 c9a43fa (04-18) CHANGES: ':' projects selected content one level (projectSelectedContent introduced), callback items use S:i projection -> #60 22788b9 (04-18) FIXES (Data:0).count -> #71 c876d28 (04-23) STATES 'index access is content-based' -> #137 2c0af18 (07-17) EXTENDS to list targets via projectionItems; selected list element opaque, selected sequence element still projected -> 245b10c F02 (07-20) NARROWS: projections in written slots reify to one value ([S:0, 5] = [(1,2),5]) -> #140 (07-28/29) A*:0 MisplacedSpread -> #167 v-original (09-20) PROPOSES selection value boundary incl. A:0.Coll = [] for selected () -> 874625a (09-21) REVERSES #58: select? returns stored element re-counted by valueCount, projectSelectedContent deleted, first(A) ≡ A:0, last(A) ≡ A:(count-1), callback items value boundaries -> 702e7d7 (09-23) REVERSES v-original detail: B:0.Coll = [()]

**Surviving semantics:** A:i selects position i of the target's position view (Lean projectionItems :1327: sequence/list elements; a scalar is its own position 0) and returns the stored element as ONE value (select? :1344, law select_is_stored_element), re-counted by valueCount (selected () emits 0, else 1); origin forgotten; only spread opens a selected value ((A:0)*.Coll = [1, 2]); first(A) ≡ A:0 and last(A) ≡ A:(A.count-1) wherever the selection is valid; one path for sequence and list targets; no bracket indexing. Probe p05: A=((1,2),3): A:0 one row (1,2), Coll(A:0, 3) = [(1,2),3], B=((),1): B:0.Coll = [()], (B:0)*.Coll = [].

*(Q-81, 2026-10-12: selection is now written `A[i]` and is variadic — `A[i1, …, in]`, one chosen element per supplied index, the result grouping normalized — with the receiver demanded once and the selectors demanded left to right up to the first failure; `first(v) ≡ v[0]` and `last(v) ≡ v[count(v) - 1]` hold over every value in hand, errors included (Q-27), and bracket selection now exists. The rest of this surviving semantics holds under the bracket spelling.)*

#### K. Parentheses: from algorithm-like groups to pure grouping syntax

**Steps:** pre-03-22 ((...)) special argument grouping -> c647330 (03-22) DECIDES ((expr)) ≡ (expr) in all positions -> d08cc58 (04-02) state: ( ) may add an algorithm layer (non-parametrized Algorithm) -> #58 c9a43fa (04-18) REVERSES in part: kind-dependent ShouldUnwrapParenthesizedPrimary keeps paren-in-paren -> #128 73cdba2 (06-22) EXTENDS: (Name) keeps its layer, (()) keeps EmptySequence layer -> 57e9ed0 (08-08) DECIDES delimiter model: no declarations in parens (DeclarationInParentheses) -> #143 7075071 (08-09) DECIDES AST split Algorithm vs Expr.Capture(OutputBundle), IsParametrized deleted, but keeps Capture around names/nested captures/() (Apply((Inc)) suppressed, open (M) rejected, (Obj).V capture receiver) -> #162 (09-12) (Obj).V still capture receiver -> #168 50c74c1 (09-22) REVERSES layers, RESTORES 03-22 principle: IsRedundantGrouping (no declarations, one slot, not a spread) erases groups whatever the kind; explicitItems? deleted -> #170 ebf623e (09-27) SUPERSEDES #168's stated cache consequence ('never a cached read') while preserving (A).count ≡ A.count; syntax.md not updated

**Surviving semantics:** A parenthesized group with exactly one non-spread slot IS that expression (Parser.IsRedundantGrouping, Parser.cs:4743, kind-independent): E ≡ (E) ≡ ((E)) for value, count, normalization, every binding, storage, caching (both read the cache), selection, dot receivers, open targets, (F)(1) = F(1), evaluation count/order and every execution strategy. Only multi-slot groups (a sequence value) and a lone spread (A*) survive as Expr.Capture: no algorithm identity, no structural members, not an open target. Braces are the only scoped algorithm form; every AlgorithmExpr has identity. Pattern parentheses are call-shape syntax opening the argument's VALUE via structureItems?. Documented carve-out: (a.b)(1) calls the dot result, a.b(1) is the member edge with arguments (probe p07).

### Area: random-numerics

#### Core numeric representation: System.Decimal+double -> Decimal128, two-tier model

**Steps:** #11 (2026-03-17) asks whether to keep Decimal and whether to normalize residues -> 10fbd40 (04-06) IMPLEMENTS NormalizeDoubleResult (15 digits, |x|<1e-15 -> 0) -> #153/7f0bab0 (08-20) REPLACES the substrate with IEEE Decimal128 end to end: no decimal or double stage, NormalizeDoubleResult and NumericOverflow deleted, transcendentals quantum-canonicalized, equality via Decimal128.Equals, IEEE ordering -> e90826f/M12 (08-31) FORMALIZES the two-tier routing (Lean Int on the exact-integer subdomain; Decimal128-only behavior is a reviewed C#-only divergence with its own spec family) -> dbeb93b (09-10) REPAIRS the RC1 scientific ToString: KatLang owns positional number text

**Surviving semantics:** C# numbers are IEEE Decimal128 (34 digits, exponent about ±6144). Decimal fractions are exact (0.1+0.2==0.3), and non-terminating quotients round. The result quantum is visible except for transcendental results, which are canonicalized. == is value equality (NaN one value, quantum ignored, -0==0), and ordering is IEEE. Lean models only the exact-integer subdomain; Decimal128-only rules are reviewed C#-only divergences (evaluator-and-hosting.md § Numerics; SEMANTIC-ALIGNMENT.md:27,:319; lean/KatLang.lean:8-43).

#### Number literals: range, too-large diagnostic, scientific notation, separators, rounding

**Steps:** #8 (03-08) a crash on a literal beyond System.Decimal -> 8a34693 (03-13) FIXES it with a positioned 'Number literal is too large.' diagnostic -> #97/cadb441 (05-26) EXTENDS the syntax (lowercase e exponent, _ separators, digits on both sides of the point; still parsed as System.Decimal, so 2e30 stayed too large) -> #153/7f0bab0 (08-20) CHANGES the rule: parse into Decimal128, more than 34 digits ROUNDS half-even, only an out-of-range magnitude is too large, underflow is a quiet zero -> 49edb94 (08-30) adds the code NumberLiteralTooLarge -> 5fa9db5 (09-13) REFINES with a distinct InvalidNumberLiteral for non-ASCII digits -> ee1fdc7 (09-16) span-based parsing (implementation only)

**Surviving semantics:** Number = /[0-9](_*[0-9])*(\.[0-9](_*[0-9])*)?(e[+-]?[0-9](_*[0-9])*)?/; only lowercase e (1.5E3 is UnseparatedSameLineItem). Literals are unsigned (-0 is prefix minus; +0 is a parse error). Excess digits round to 34. A magnitude beyond the range is NumberLiteralTooLarge; unparseable digits are InvalidNumberLiteral. A written nonzero literal rounding to zero is InvalidNumberLiteral (Q-56).

#### Arithmetic overflow and IEEE special values

**Steps:** #13/12e278a (03-26) PROPOSES 'beyond the decimal range is unsupported' as EvalError.NumericOverflow -> #153/7f0bab0 (08-20) REVERSES it: overflow gives signed Infinity, a domain violation gives NaN, ln(0) gives -Infinity, -0 is representable, specials are ordinary values; divByZero on an evaluated zero and 0^negative-integer stay errors (Lean-modeled); NaN was kept truthy -> e90826f (08-31) PINS overflow-produces-infinity, nan-equality-vs-ordering and negative-zero-display -> 869c1bc/G-6 (09-13) REFINES: a zero base with ANY exponent < 0 (incl. 0^-0.5, previously Infinity) is an error; G-11 keeps non-finite spellings under DisplayDecimals -> #165/e4d19cc (09-20) REMOVES numeric/NaN truthiness

**Surviving semantics:** Overflow is ±Infinity. NaN, ±Infinity and -0 are ordinary values; NaN==NaN is true while NaN<x is false. Division or mod by any zero-valued divisor (incl. -0 and an underflowed zero) is DivisionByZero. 0^x for x<0 is IllegalInEval, and 0^0 is 1. Numbers have no truth value (if(sqrt(-1),1,2) is TypeMismatch).

#### Transcendental precision: from nice values to honest 34-digit approximations

**Steps:** #9 (03-09) tan(pi/2) gives 618986325617924 -> 9dff45e (03-17) side fix: high-precision decimal Pi/E literals; #9 closed NOT_PLANNED with the policy 'finite approximation near a singularity, no special error' -> #11/10fbd40 (04-06) IMPLEMENTS normalization of double residues (sin(pi)->0) -> #153/7f0bab0 (08-20) REPLACES it with native Decimal128 functions, Decimal128.Pi constants and quantum canonicalization; normalization deleted (sin(pi) is about -1.158e-34) -> f9e4825 (09-08) REFINES asin/acos near ±1 -> e4c7973 (09-15) REFINES ln/lg/log near 1 with log1p -> 7c66530 audit #6 (09-24) AUDITS accuracy (<=0.5 ulp for core functions) and fixes the doc overclaim about Log(9,3)

**Surviving semantics:** Math functions are 34-digit approximations of the rounded argument. They are never snapped to nice values and carry no correct-rounding guarantee ('roughly the last digit or two', tutorial.md:1979). A singularity gives a large finite value, not an error (EvaluatorMathTests.Eval_MathTan_NearSingularity_ReturnsLargeMagnitude). Transcendental results are quantum-canonicalized (lg(1000) is 3); Abs/Ceil/Floor/Round/Sign keep their argument quantum.

#### Power operator ^ / pow

**Steps:** ^ via System.Math.Pow (double) -> #43/a90fdd4 (04-10) IMPLEMENTS an exact decimal power for integer exponents with a double fallback for fractional ones -> #153/7f0bab0 (08-20) RE-IMPLEMENTS it as exact by-squaring for |n|<=long.MaxValue, Decimal128.Pow otherwise, with Math.Pow sharing EvalPow -> 065152c (08-29, no issue) CHANGES precedence: ^ binds tighter than prefix -/not, so -2^2=-4 (was 9) -> ec48b91/B4 (09-07) REFINES integral powers to CORRECTLY ROUNDED with certification (IllegalInEval on exhaustion) -> 869c1bc/G-6 (09-13) REFINES: any negative exponent of zero is an error -> e4c7973 (09-15) near-one fixed-point power -> 7c66530 audit #6 (09-24) FIXES a regression: DelegatedPower selects the band by |base| with parity sign for negative bases

**Surviving semantics:** ^ ≡ pow ≡ Math.Pow is one implementation. Integral exponents are exact when representable, otherwise correctly rounded or a loud failure. Fractional, non-finite and beyond-long exponents are Decimal128 approximations (near-one reformulation; IEEE special bases keep sign and parity). 0^(x<0) is an error. ^ is right-associative and binds above prefix -/not. Lean models only the integer instance (intPow/negativeIntPow).

#### div/mod and numeric avg/min/max/order

**Steps:** bebee03 (04-09) avg = decimal total/count in C# (Lean Int quotient) -> 1fe689e (04-17) CHANGES the C# avg to Math.Floor to match Lean -> a6aaa80 (06-15) REVERSES that to the decimal mean and declares Lean truncation a model limitation -> 7f0bab0 (08-20) re-implements: min/max via Decimal128.Min/Max (NaN propagates), order via CompareTo, div=Truncate(x/y) -> bbca492/G-3 (09-13) FIXES a regression: div truncates the EXACT quotient (IntegerDivide) -> e4c7973 (09-15) order becomes STABLE -> 7c66530 audit #6 (09-24) REFINES avg to the correctly rounded exact mean (avg((1,1e34,-1e34)) was 0) -> 38b5918 (09-27) PINS signed-zero extrema (min((0,-0)) is -0, max((-0,0)) is 0; the quantum tie stays unspecified)

**Surviving semantics:** div/mod truncate toward zero (-7 div 2 = -3, -7 mod 2 = -1; shared with Lean tdiv/tmod), and div is exact whenever representable. sum is the left-to-right Decimal128 sum; avg is the exact mean rounded once (bit-identical to total/count while every addition was exact). min/max are IEEE minimum/maximum (NaN propagates, signed-zero rule). order is stable and orderDesc reverses it. Lean keeps Int truncation for / and avg, a documented tier limitation.

#### Math surface: prefix-only -> prelude aliases; Math.E -> Math.Exp; Atan2; Round

**Steps:** #48/9c4e063 (04-12) DECIDES Math only as Math.X or via open Math -> #94/20fc773 (05-14) ADDS Atan2(y,x) -> f273d69 (05-15, no issue) CHANGES Round(x) (unary, banker's rounding) to Round(x, digits) with digits 0..28, AwayFromZero -> #114/c1e19b1 (05-16) bare builtin alias forwards its signature -> 17d480b (08-08) FIXES Atan2 metadata from (x,y) to (y,x) -> #153/7f0bab0 (08-20) widens Round digits to >=0 (clamped at 6176) and moves constants to Decimal128 -> #154/b3738b9 (08-24) REVERSES #48: one explicit lower-camel prelude alias per member (incl. e), shadowable, prelude before opens -> #155/667155e (08-25) REMOVES Math.E and e, ADDS Math.Exp/exp (no Exp(1)==E contract) -> #156/04b5fc8 (08-29) + 09-04 fix: a native reads its own parameter -> audit #8/ad6d6bf (09-23) REFINES: alias and canonical are distinct bindings sharing ONE algorithm (own cache entries; P(pi, Pi) rejects); G-24 makes Math.cos(1) a lexical fallback

**Surviving semantics:** 21 canonical PascalCase members exist only inside Math (Pi, Exp, Abs, Ceil, Floor, Round(value,digits), Sign, Sqrt, Ln, Lg, Sin/Cos/Tan(radians), Asin, Acos, Atan, Atan2(y,x), Pow, Log(value,base), Random(start,end), RandomInt(start,end); BuiltinRegistry.cs:353-373). Each has one explicit, shadowable prelude alias. There is no Math.E, no e, and no nullary function (MathMemberKind = Constant/Unary/Binary). round rounds midpoints away from zero and needs integral digits >= 0. Lean does not model Math.

#### Random API: Rand/RandInt -> Random/RandomInt

**Steps:** #77 (04-27) PROPOSES Perl-like Rand in [0,1), inclusive Python-like RandInt and RandFloat -> 238ff20 (05-14, PR #107) IMPLEMENTS Math.Rand (new NullaryFunction kind, Random.Shared.NextDouble) and RandInt (inclusive, int-limited) -> #109 (05-14) REGRESSION: fractional bounds, int crash, overflow; proposes half-open and whole-number checks -> #110 comment 9 (05-16) PROPOSES one symmetric parameterized Random(start,end) and no zero-arg random member -> 489b77f (05-17) CHANGES the API: Rand, RandInt and NullaryFunction removed; Random(start,end) half-open; RandomInt whole-number bounds, start<end, floor of the scaled draw -> #153/7f0bab0 (08-20) RE-IMPLEMENTS: exact 10^-34 lattice draws; RandomInt by unbiased Int128 rejection sampling with |bound|<=1e34; Random requires finite bounds and range -> #154 (08-24) adds aliases random/randomInt

**Surviving semantics:** random(start,end)/Math.Random is a uniform lattice draw in [start,end) with finite bounds and start<end. randomInt(start,end)/Math.RandomInt is a uniform whole number in [start,end) with whole-number bounds, |bound|<=1e34, start<end. Validation precedes every draw (an invalid call consumes nothing). No zero-argument random member exists; Math.Rand and Math.RandInt fail as unknown members.

#### Random values x zero-argument property cache

**Steps:** #42/5a37525+6fe4f51 (04-10/04-22) IMPLEMENTS the zero-arg cache as an optimization -> #110 (05-14) REGRESSION: 'unexpected twins' (Pair = (Math.Rand, Math.Rand)) -> d7629b6 (05-14) excludes builtins from the cache -> 1cac168 (05-17) REVERTS that (no impurity tracking) -> 489b77f (05-17) IMPLEMENTS recursive B() freshness (FreshZeroArgCallContext) -> e0599ba (05-18) REVERSES it to local freshness -> d843523 (05-18) CHANGES the status: the cache is Lean-modeled semantics -> 31f7c76 (09-12), 2d47a93 (09-22), #170/ebf623e (09-27) REFINE: identity = semantic binding, and consumers never affect caching

**Surviving semantics:** R = random(0,1) draws once per run per resolved binding. R,R are twins; R() redraws only R, and nested reads keep their own cache rules. Purity is irrelevant and no consumer can re-run the body (probe --seed 42: R,R,R(),R -> 0.7945..,0.7945..,0.3928..,0.7945.. on all 5 paths; tutorial Roll == Roll is true).

#### Seeds and reproducibility

**Steps:** #110 comment 1 (05-14) DECIDES 'Random.Shared … cannot affect seeding — and it is correct' (ambient, unseedable) -> 7f0bab0 (08-20) still Random.Shared behind a test-only injectable draw -> 668ff3c (09-14, no issue) CHANGES the fundamental rule: one run-scoped SplitMix64 stream on EvaluationBudget, eager per run, seeded by RunOptions.RandomSeed / Evaluator.Run* randomSeed / CLI --seed, or 8 entropy bytes; no static/options state; sync, async and optimizer must preserve draw count and order; not stable across versions; no source seed -> 96092a6 (09-24) shared CLI value parsing -> 5753e84 (09-24) RENAMES --seed to --random-seed (no alias) and declares that a source RandomSeed property is ordinary

**Surviving semantics:** Seeding is host configuration with no language presence. A seed reproduces a stream (it never memoizes); ordinary evaluation rules decide which calls draw; Parser.Parse* ignore the seed; Lean does not model it (SEMANTIC-ALIGNMENT row 50; seeded-randomness-2026-09.md §§1-8). Probe --seed 42: randomInt(1,1000) -> 522 with or without a RandomSeed=1 property. Known open violation: absorbed stack exhaustion makes the stream path-dependent (3 outcomes at HEAD).

#### Display decimals and number text

**Steps:** #118/233a2ae (05-30) IMPLEMENTS the root DisplayDecimals property: display-only, recursive over numeric leaves, readable, invalid value is an error, max 99, scale-0 integers plain, rendered with decimal ToString(F) (per-value annotations and significant/scientific properties never implemented) -> 6206522 (08-05) formatters honor it; 7f0bab0 (08-20) moves it to Decimal128 -> dbeb93b (09-10) REPAIRS RC1 scientific ToString: KatLang owns positional reparseable text -> 869c1bc/G-11 (09-13) non-finite values keep canonical spelling -> e4c7973 (09-15) KatLang OWNS the rounding (midpoints away from zero) because the runtime tie rule changed -> 96092a6 audit #12 (09-24) REFINES: one effective setting per run via ResolveDisplayOptions (the declared root property wins even when invalid, else RunOptions.DefaultDisplayDecimals/--display-decimals, else canonical); public MaxDisplayDecimals=99 is a validity bound, never a clamp

**Surviving semantics:** One effective display setting per ENGINE run. It changes only rendered text (midpoints away from zero; integral-quantum whole numbers plain; NaN/Infinity keep their spelling), never values, counts, errors, draws or cache. Canonical number text is positional, quantum-faithful and a reparseable literal. Only the root's own DisplayDecimals counts. It is an engine-level rule: the direct Evaluator path treats it as an ordinary property (probe: DisplayDecimals = 1.5 fails the engine run, generic ok).

#### Numeric truthiness (cross-reference)

**Steps:** #41/ee8180c (04-08) IMPLEMENTS a predicate result = one atomic number, 0 false, nonzero true -> 7f0bab0 (08-20) keeps NaN truthy (!= 0) -> #165/e4d19cc (09-20; subject mis-cites #156) REMOVES numeric truthiness

**Surviving semantics:** Numbers (NaN included) have no truth value; only Booleans are conditions (if(sqrt(-1),1,2) is TypeMismatch).

### Area: loops

#### A. while continuation flag and termination

**Steps:** 25a8558 (2026-03-07, v0.7.3) INTRODUCES while(step, init) with a numeric flag: 0 stops and returns the CURRENT state, and a single-output step's atom is both state and flag -> #3 (2026-04-06) REAFFIRMS: no shape-transforming 'drop output' feature; a while step is a specialized algorithm; reuse it manually via A(..):0 -> #15 two-argument if 'for shorter loop examples' REMOVED by #49 93a036d (2026-04-13) -> #132 9a4c70f (2026-06-27) REFINES: a call result is one value, so A(A(0)) passes the pair (TypeMismatch) -> e4d19cc (#165, 2026-09-20) CHANGES the rule: the flag must be a Boolean via Result.asBool?; numeric truthiness and the numeric single-output flag are deleted, and the planned-loop plans are updated in the same commit

**Surviving semantics:** The step's LAST output slot is the flag and must be Boolean (a Boolean or a redundant singleton around one). A single-output step's slot is both state and flag. Zero outputs is badArity. true commits the proposal and continues; false returns the CURRENT state without committing the proposal. The step runs at least once, and the terminating proposal is fully evaluated: its errors and effects occur (p46 DivisionByZero, p47 trace). *(Current-rule pointer, Constitution audit 2026-10-23: the termination clauses are superseded by LOOP-CF1 (owner decision 2026-10-17; `2febbb47`, katlangorg/katlangnet#185): a `while` round reads its flag first, from the last EFFECTIVE item found right to left, and `false` returns the state that entered the round without forming its earlier rows, so p46 (respelled `S(0).while` since META-S3-3) is `3` and p47 (`S(7).while`) is `7` with no host event; the Boolean flag contract is unchanged (LOOP-06).)* Evidence: Lean 5885-5898, splitContSlots 3865; C# SplitContSlots Evaluator.Loops.cs:627; EvaluatorLoopTests.Eval_While_TerminatingNextStateIsNotCommitted; spec boolean-loop-state-transition.

#### B. Loop initial state: one slot per written argument

**Steps:** 25a8558 (2026-03-07) INTRODUCES a fixed-arity single init Result; multi-value init needs double-parens Algo.while((x, 0)) -> c647330 (2026-03-22) REPLACES it: double-parens removed; the parser lowers while(Step, x, 0) to while(Step, block([x, 0])) by callee spelling, and the evaluator packages dot-call inits -> 6469363 (#96, 2026-05-07) CHANGES the rule: the parser lowering is removed; each WRITTEN init argument is one state slot (Pair is one slot); while/repeat become variadic (n>=2 / n>=3); aggressive unpacking of init contents is removed -> 9a4c70f (#132, 2026-06-27) REFINES: a call/property init is one slot (the benchmark stayed broken until f2a4e2a, 2026-09-17, which added Init(x)*) -> dada1b6/702e7d7 (#167 C-full, 2026-09-21..23) REAFFIRM: loop state slots are established items, never opened -> 50c74c1 (#168, 2026-09-22) REAFFIRMS: parentheses are syntax, and ExplicitSequenceValueItems is dropped from loop inputs -> 9f6cdfb/2d47a93 (2026-09-13/22) REFINE: init slots are zero-argument value demands

**Surviving semantics:** while(step, s1..sk) and repeat(step, n, s1..sk) require k>=1. *(Current-rule pointer, Constitution audit 2026-10-23: superseded by META-S3-3 (2026-10-20, `9c8623f2`, #64): the forms are `while(meta step)` / `repeat(meta step, count)`, the initial state is the captured step call's effective supply (each supplied cell one slot, zero cells the empty state), and the retired forms are exact-arity `ArityMismatch`; the one-slot and spread rules below survive for the step call's arguments, while a written callable argument keeps its CALLABLE identity for the first iteration (since Model C, LOOP-01), so "loop state carries values only" holds for the states the step's rows produce.)* Each non-spread init argument is ONE value slot (a sequence, a list, (), or a zero-declaration block alike). A spread init argument supplies its items. The repeat count must be an integer >= 0 (IllegalInEval otherwise; the integrality check is C#-only). n=0 returns the initial state without binding the step. Loop state carries values only (p41, p42). Evidence: Lean evalInitialLoopStateSlots 5216, builtinAcceptsArity 597-598; C# Evaluator.Loops.cs:57; ExplicitValueOpeningTests.LoopStateSlots_AreEstablishedItems; probe p10.

#### C. Step output rows become next-state slots

**Steps:** v0.7.3: the step output Result is the next state -> 6469363 (#96, 2026-05-07) INTRODUCES slot shaping by output: a bare A;B join gives several slots, (A;B) gives one -> 19488a9 (2026-05-07) REFINES with counted top-level emissions -> af92bad (#99, 2026-05-08) INTRODUCES the patterned-step exception: preserve join boundaries on output ('open on input, close on output'; flag preserveResultJoinExpressionBoundaries, renamed by 0e9b41f #104 and b568c66) -> ad75720 (#125, 2026-06-17) REMOVES the ; join -> 73cdba2 (#128) REFINES: a () row is one visible slot -> #132 REFINES: a call/property row is one slot -> 874625a (2026-09-21) CHANGES the rule: a selection row (A:i, first, last) is ONE slot, where previously it was a live multi-slot supply

**Surviving semantics:** All rows are evaluated under the OLD state (simultaneous update). A non-spread row with count 0 or 1 is one slot. A non-spread row emitting k>1 (a nested loop row) contributes k slots. A spread row contributes its items (0 items gives no slot). EXCEPTION: in a sequence-value-PATTERNED step, a top-level spread row is ONE packed slot (LOOP_PATTERNED_STEP_PACKS_TOPLEVEL_SPREAD; p22 vs p23). Evidence: Lean evalAlgOutputSlots 5170-5204; C# Evaluator.Loops.cs:77-117; LoopStepSpreadContributionTests; sequences-lists-and-calls.md:19.

#### D. Loop-step binding model

**Steps:** v0.7.3 positional bindParams -> 3997ad6 (#92, 2026-05-06) REFINES: loop-step parameters shadow inherited callback bindings -> 6469363 (#96) EXTENDS to variadic (collecting) steps through the callable signature -> af92bad (#99) EXTENDS to sequence-value patterns (bindStructuredLoopState) -> 7b2590a/4c4d5ff/9c7241f (2026-05-10/11): binding plans, implementation only -> e054a6f (#121) REFINES: repeated names are equality constraints -> ab7d2f5 (#138, 2026-07-18) CHANGES the rule: a collecting step collects an EXACT LIST, so the #96 example TestStep.repeat(2, List) now gives BadIndex (p08) and List* is needed -> eab2468/73648e9 (#139/#140) respell to *xs -> D1 (2026-09-22) aligns failure order with Lean -> 5d6d60b (2026-09-23) REFINES: a forwarded callable reaches the while/repeat step slot on its algorithm channel (p16)

**Surviving semantics:** Each iteration binds the state slots as a flat value supply to the step's OWN parameter list: fixed positional, one collecting parameter as an exact list (possibly []), or patterned via bindParameterPatternList. Step parameters shadow all inherited tiers through the one helper, which planned loops also use (LoopOptimizer.cs:398-401). The state may change size (down to zero slots, giving ()) and kind. UNRESOLVED: clause families and non-native builtins are rejected as steps ('step has no parameters', p13/p14), while native Math wrappers work (p38).

#### E. Loop result: multi-slot state, not a value boundary

**Steps:** 19488a9 (2026-05-07) INTRODUCES counted receiver itemization of while/repeat results, so .take acts on the slots -> #132 plus the 2026-07 sequence-boundary audit REAFFIRM: loop state is a NON-value-boundary -> 0ca55e9 (#135, 2026-07-17) REFINES: collection builtins read one bound collection one level, so take/count still see the slots -> 68b3607 (2026-09-21) CHANGES the rule: dot-call passes a value; receiver-segment machinery is deleted, so repeat(..).Coll is [(2, 3)] and only repeat(..)*.Coll opens it (p17)

**Surviving semantics:** loopStateResult is normalize(sequenceValue slots) with emitted count = slot count. A lone root loop row displays one row per slot, while beside other rows it displays one combined row (p18/p19; OutputRows, KatLangEngine.cs:144-177). As a written argument or receiver it is ONE value. Step.repeat(1, a, b) has the same value as Step(a, b) but emits k instead of 1 (p33).

#### F. Planned loops (pre-bound loop execution frames)

**Steps:** #86 4ea6bcc (2026-05-01) INTRODUCES a C#-only planned loop with generic fallback; it must keep simultaneous update, no cross-iteration leak of the local cache, and stable captured parent values -> 020b7ec EXTENDS it (temps, counted callback slots) -> #95 37c6898 (2026-05-07) REPAIRS a REGRESSION of #86: the planned step read the outer callback binding -> 6469363 RESTRICTS: collecting and patterned steps decline planning -> e8c7eed (2026-05-11) plan-aware eligibility -> b638c24/5631c07 (Aug) diagnostic parity -> 085b611 (M3, 2026-08-29) shared ApplyUnaryOperator -> ad9ea35 (M16, 2026-09-01) prepares binding once and keeps the fresh concat identity -> 761c3ef (B3, 2026-09-06) matches depth charges for planned if/TempSlot/TempCall -> 31f7c76 (F3, 2026-09-12): exported temps use the run cache, local-only temps a per-iteration memo -> e4d19cc: Boolean in plans -> ebf623e (#170 B1, 2026-09-27) CHANGES the if-argument temp from memo bypass to the ordinary cached read (p28) -> 02aa84e (2026-09-26), implementation only

**Surviving semantics:** The optimizer is observationally invisible: values, counts, error kinds, contexts and spans, host effects, random draws, cache entries, and depth/collection verdicts all match. Planning is disabled whenever a step limit is configured (Evaluator.cs:2571 loopOptimize = !HasStepLimit), so its lower step counts are unobservable. A mid-loop shape change hands the already-evaluated iteration to the generic loop once. SEMANTIC-ALIGNMENT row 22; LoopPlanned*ParityTests, CorpusExecutionEquivalenceTests.

#### G. Filter->count fusion

**Steps:** #87 020b7ec (2026-05-01) INTRODUCES count-where fusion plus direct range iteration (C#-only) -> c6e6e13 (2026-08-18) REPAIRS budget cross-talk: fusion elided depth levels, so always-active budgets are now equalized -> c5931ee (M15, 2026-09-01), implementation only -> 14bb037 (2026-09-07) REPAIRS fused predicate preparation and sync/async budget parity -> e4d19cc (2026-09-20) REFINES: the predicate must be Boolean (p31) -> 5d6d60b (2026-09-23) REPAIRS: a forwarded predicate keeps its algorithm channel in both spellings, and the complete resolved argument is copied (p30) -> ebf623e (#170, 2026-09-27) REFINES: the fused receiver is read through the property cache (the comment at Evaluator.DotCalls.cs:151-155 is stale)

**Surviving semantics:** Implementation only: the result equals generic count(filter(...)) in value, errors, predicate effect order, and depth. Fusion is disabled under a configured step, string, or materialization limit (Evaluator.cs:2571-2581). SEMANTIC-ALIGNMENT row 23; FilterCountFusionSpanParityTests, BudgetCrossTalkMatrixTests; probe p06 gives 61 on both strategies.

#### H. foreach proposal

**Steps:** #40 (2026-04-08) PROPOSES a general foreach(collection, step) -> the maintainer REJECTS it the same day ('worse abstraction'; harder Lean formalization) and closes it as a DUPLICATE -> #37 SUPERSEDES it with map/filter/reduce, whose callbacks were later governed by the 2026-09-23 CALLBACK LAW

**Surviving semantics:** There is no foreach builtin: the Lean preludeAlg (KatLang.lean:7375-7398) has none, and the generator guidance lists foreach as foreign syntax (agent.md:256). Iteration is map/filter/reduce for collections and repeat/while for evolving state (tutorial.md:1583).

#### I. Step.repeat(1, ARGS) vs Step(ARGS) (#96 title)

**Steps:** #96 (2026-05-07) ASKS -> 6469363 ANSWERS by aligning slot assembly and binding with the ordinary (variadic) call model -> #132 ADDS a boundary divergence (a call result is one value; a loop result is k slots) -> #138 / C-full REAFFIRM slot = argument for collectors (repeat(Step, 1, (1, 2)) with Step(*xs) = xs.count is 1, like Step((1, 2)))

**Surviving semantics:** Slot assembly and binding of Step.repeat(1, a1..ak) equal those of the direct call Step(a1..ak), and the results are equal as values. The loop result is not a value boundary, though: it emits k, not 1 (p33a/b/c). Exceptions: the patterned-step packed spread row; clause families and builtins, which are callable directly but rejected as steps; dot-call structural-first shadowing of .repeat. *(Current-rule pointer, Constitution audit 2026-10-23: since Q-23, Q-24 and Q-26 (2026-10-04) the first two exceptions are retired and a loop result is one value (emitted count 1); since META-S3-3 (2026-10-20) the spelling is `Step(a1..ak).repeat(1)`, whose initial state is the captured call's own supply (LOOP-01, LOOP-07).)*

#### J. Loop construction syntax (#64 OPEN at the snapshot; CLOSED 2026-10-20 by META-S3-3)

**Steps:** #64 (2026-04-19, OPEN, no comments) PROPOSES sugar like Algo(1, 2, 0).while -> 68b3607 (2026-09-21, dot-call passes a value) CONSTRAINS it: Algo(1, 2, 0).while is while(Algo(1, 2, 0)), which is ArityMismatch today (p12); the original example still runs (p11 gives 4613732) *(Current-rule pointer, Constitution audit 2026-10-23: both are superseded — #64 was CLOSED 2026-10-20 by `9c8623f2` (META-S3-3), so `Algo(1, 2, 0).while` captures `Algo(1, 2, 0)` as the `meta step` and is the loop; the original `Algo.while(1, 2, 0):2` no longer runs as written: `:2` is `RetiredColonSelection` since Q-81 and `Algo.while(1, 2, 0)` an exact-arity `ArityMismatch` (LOOP-01).)*

**Surviving semantics:** No new syntax. Any future loop sugar must be a new explicit construct and cannot reinterpret dot-call or call results (R.F == F(R); a call result is one value). *(Current-rule pointer, Constitution audit 2026-10-23: #64 was CLOSED 2026-10-20 as completed by `9c8623f2` (META-S3-3); the new explicit construct is the META step of `while(meta step)` / `repeat(meta step, count)`, so `Algo(1, 2, 0).while` — the ordinary `while(Algo(1, 2, 0))` — is now the loop without reinterpreting dot-call (LOOP-01). Classifications unchanged.)*

### Area: output-syntax-layout

#### A. Output definition: explicit Output added then removed

**Steps:** 25a8558 (2026-03-07, v0.7.3) baseline: implicit output rows; the grammar already allows rows interleaved with definitions -> #5/49640ea (03-13) PROPOSES+IMPLEMENTS optional `Output = expr` (at most once, no mixing, `public Output` rejected, reserved) -> #52/6f1f40d (04-15) REFINES (no `Algo.Output`, no `Output(x)=`, no conditional Output; algorithm params are the call interface) -> 9764de1 (04-15, no issue) IMPLEMENTS ExplicitParametersRequireOutput (Lean validateExplicitParamOutputInvariant) -> #123/007917a (06-13) REFINES (`Output =` body line-bounded, never mixed with rows) -> #63/8cf85f5 (07-31; the commit title wrongly says 'implicit') REVERSES #5 and SUPERSEDES #52 rules 1-3 plus the #123 mixing rule: one output model, `Output` an ordinary identifier, SpecialOutputAccess/ReservedName removed

**Surviving semantics:** An algorithm's output is the ordered list of its non-declaration rows, which may sit anywhere among declarations (declaration order is unobservable). There is no output keyword; Output/output are ordinary identifiers. An algorithm with an explicit parameter list must have at least one output row (ExplicitParametersRequireOutput; Lean KatLang.lean:2021-2034, C# Parser.cs:567). Pinned by spec output-rows-interleave-definitions, output-is-ordinary-property, output-dotted-access-ordinary; probes p06, t04, n01.

#### B. Explicit empty result vs no-output program

**Steps:** v0.7.3 baseline: () and {} are no-output algorithm forms, so no empty result can be written -> #81/e8f8b10 (04-28) PROPOSES+IMPLEMENTS `()` as empty output, then b8a24db REVERTS it the same day ('() and {} define an algorithm') -> #81/b950d86 (04-29) IMPLEMENTS the reserved builtin `empty` -> #83/1ca8b3f (04-29) IMPLEMENTS no-program-output as distinct from explicit empty output -> #104 (05-13) uses `empty` as the x... tail (removed by #124/4b32111) -> #128/73cdba2 (06-22) REVERSES #81: `()` is the empty sequence value, `empty` ordinary, {} not a value, (()) != () -> e6c2bdc (07-11) REVERSES nested-empty distinctness -> #143/7075071 (08-09) GENERALIZES: parentheses are never an Algorithm, braces always carry identity -> SYN-01/a8bcae7 (09-10) REFINES: () is not an operator identity -> #168/50c74c1 (09-22) REAFFIRMS (()) as the () node -> F5/989fcea (09-22) REFINES blame (count({}) is blamed at the argument) -> #11/3613d58 (09-24) REAFFIRMS RunResult.NoProgramOutput

**Surviving semantics:** () is a real visible value, the empty sequence (one slot; spreading it supplies zero items). {} is an algorithm without output: forcing it where a value is needed is MissingOutput, and the message suggests (). `empty` is an ordinary name. A program with no output rows (properties only, comments only, or empty source) has no program output: NoProgramOutput from the engine, MissingOutput from the raw evaluator, and distinct from a program that outputs (). Lean evalProgramOutput / missingOutput (KatLang.lean:5167, 5185).

#### C. Root rows are not a grouping mechanism

**Steps:** v0.6 displayed output grouped per written line -> #7 (03-10, NOT_PLANNED) DECIDES: from v0.75 root rows are flat top-level outputs ('no magic grouping') -> #90/fd3cabe (05-14) REFINES display (a sequence value in parentheses, several values as rows) -> #122/acbfa7d (06-11) REAFFIRMS: visual rows are presentation only -> #132/9a4c70f (06-27) REFINES: a property or call result is ONE value, so `A = 1+2, 2+3` / `A` displays (3, 5)

**Surviving semantics:** Root and body output accumulation is an item supply, not a value boundary: each written slot or row contributes its items (a root `A*` emits the items). Grouping comes only from values (parentheses, lists, call and property results), never from line layout. Spec supply-three-rows.

#### D. Newline continuation rules (incl. rejected backslash continuation)

**Steps:** v0.7.3 (03-07) layout-free parser (no line checks: `A` newline `-1` is A-1) -> df14e5a (04-02) INTRODUCES exact adjacency for call delimiters -> #44/d5cb0cd (04-11) silently INTRODUCES 'an operator-led line never continues', with a comment-sensitive exception -> #82 (04-29..05-04, NOT_PLANNED) REJECTS Python-style `\` and articulates 'a trailing operator continues, a complete line ends' -> #113/e75ec7d (05-15) RELAXES dot-call args to same-line -> #119/ac15218 (06-04) INTRODUCES line-final `...` continuation -> #122/7b5fe7a,acbfa7d (06-10/11) REVERSES #119, makes the newline an implicit join and definition bodies line-bounded; a cross-newline call continuation existed only uncommitted (memory) and was reverted -> #123/007917a (06-13) CONSOLIDATES into ONE ContinuationPolicy ((,{,:,~,binary ops same-line; leading . cross-line) and makes comments invisible (REVERSES the d5cb0cd exception) -> #125/ad75720 (06-17) CHANGES newline from join to slot separator -> ec48b91 (09-07) makes the postfix Grace run line-local -> #161/cb6cfda (09-11) makes a trailing star continue like any operator -> F7/aaae65c (09-13) RESTRICTS: declaration heads are line-local (REVERSES cross-line `Name` newline `= body`) -> e4d19cc (09-20) the not tier; trailing not/comparison continues -> audit #9/2a140c9 (09-23) REFINES: a declaration head is never an operand; reported characters are invisible

**Surviving semantics (Q-65 revision, 2026-10-14):** A physical newline separates complete expressions by default. Independent next-line expression/declaration grammar has priority; otherwise ordinary continuation crosses LF, including dot, expression-list comma and eligible binary roles. Attached unary minus is independent; detached minus can continue subtraction; leading star can continue multiplication unless it starts a binding declaration. Incomplete syntax and open delimiters continue. Calls/selection/Grace stay same-line. Declarations are never operands. LF breaks lines, CR is whitespace, comments do not reconstruct attachment, and backslash is an UnexpectedCharacter, never continuation. Surface-only (not a Lean parser).

#### E. Comments

**Steps:** v0.7.3 `//` comments; lexer breaks lines on LF only, so a lone CR was never a line break -> d5cb0cd (04-11) makes comments parse-relevant (a comment let an operator-led line continue) -> #123/007917a (06-13) REVERSES that: comments invisible to every continuation and declaration lookahead -> #142/f4c1b1b (08-03) REPLACES `//` with `#` (no alias; `//` is two divisions) -> F7/aaae65c (09-13) RESTRICTS: comments no longer let heads span lines -> 2a140c9 (09-23) / c5c4b9d (09-27, FZ-R2) EXTENDS invisibility to reported characters and a leading comment

**Surviving semantics:** '#' outside a single-quoted string starts a comment that runs to CR/LF/EOF, and needs no whitespace before it. Comments (and lexer-reported characters) are invisible to every grammar decision. The terminating newline keeps its row and continuation meaning. A physical line break is LF alone (a lone CR is whitespace). Lexer.cs:205, KatLang.ebnf:757-777, CommentSyntaxTests, spec comment-does-not-change-parse.

#### F. Slot separation: same-line comma requirement (and ;)

**Steps:** v0.7.3 (03-07): item boundary implicit wherever an expression cannot continue, same line or not (df14e5a example `Add = a + b 2.Add(6)`) -> #2/9f3a0f9 (03-10) `;` combining -> #75/23d9a0c (04-26) `;` result join -> #104/0e9b41f (05-13) `...` join replaces `;` -> #122 (06-10/11) `;` output join; newline an implicit join; PROPOSES adjacency diagnostic -> #123/007917a (06-13) REVERSES the proposal: same-line/newline adjacency is an implicit `;` (F(1 2) = F(1 ; 2)); comma never implicit; open comma-list grammar -> #125/ad75720 (06-17) REMOVES `;` (UnsupportedSemicolon); adjacency becomes an implicit expression-list separator; eadf87f (06-23) docs -> #152 a~t reused A~B two-slot adjacency, reverted b28567f (08-20) -> #160/2b03c0b (09-12, SYN-07A) REVERSES the same-line half of #125: UnseparatedSameLineItem, declarations begin a line; 89e5c86 extends it to parameter patterns -> 2a140c9 (09-23) recovery refinements

**Surviving semantics:** On one physical line a comma is the only slot separator; whitespace never creates a slot (1 2, 2(3), A[1], 2m, P = a b, x = 3 y = 4 are UnseparatedSameLineItem). A newline separates slots in multi-line contexts (root, brace bodies, open groups, argument lists, list literals) and ends simple definition bodies and open target lists. ';' is never expression syntax. Parsing never depends on arity, values, types or callee spelling.

*(Q-81, 2026-10-12: `A[1]` is no longer an unseparated item — a same-line `[` after a completed expression is postfix selection; `2(3)`, `1 2` and the other forms remain errors.)*

#### G. Star layout: spread vs multiplication

**Steps:** #104 (05-13) `...` binary supply/join -> #119/ac15218 (06-04) PROPOSES+IMPLEMENTS: a line-final `...` continues to the next line -> #122 (06-11) REVERSES #119 (`...` is supply only) -> #124/4b32111 (06-13) NARROWS: postfix-only unary, any following token starts a new expression -> #139/eab2468 (07-24) prefix/postfix ellipsis -> #140/09382b3 (07-28) spread(value) -> #140/73648e9 (07-29) REPLACES with star syntax; the decision uses attachment + same-line operand, with a NEWLINE RULE (attached line-final a* = spread, detached a * multiplies) -> #161/cb6cfda (09-11, SYN-07B) REVERSES the #140 newline rule: the next significant token on any line decides (declaration heads excluded); attachment checked afterwards (InvalidSpreadMarker); same law for *x, ~x, x~ -> f7ee8ea (09-12) F13a diagnostic -> e4d19cc (09-20) a star before `not` is a spread -> 2a140c9 (09-23) shared declaration-starter relation

**Surviving semantics (Q-65 revision, 2026-10-14):** Prefix collect is attached binding syntax; infix star multiplies; directly attached postfix star spreads only in an explicitly closed same-line slot. Physical line-final star always announces multiplication, including EOF or a later declaration/closer; missing operands are errors and declarations retain their scope. *(Issue #183, 2026-10-14: refined — only a detached line-final star; an attached one is a completed spread)* Attachment follows classification; multiplication spacing is ordinary. `A*,` before a later row, `F(A*)`, `(A*)` and `{ A* }` explicitly close spread. Spread VALUE semantics, chained composition and fluent lowering survive. since issue #183 the attached `X = A*` newline `B*` newline `X` is the spread definition `X = A*`, the spread row `B*` and the row `X`, while the fully detached `X = A *` newline `B *` newline `X` parses as `X = (A * B) * X` with no program output *(Constitution audit, 2026-10-23: formerly "`X = A*` newline `B*` newline `X` still parses as `X = (A*B)*X` with no program output"; corrected by issue #183.)*; the old broader EOF/declaration closure fallback is superseded.

#### H. Trailing-block and call-delimiter parsing

**Steps:** v0.7.3 (03-07) CallArgs = BraceArgs|ParenArgs, layout-free -> #1/61e191b (03-11) IMPLEMENTS higher-order inline blocks Algo{a + 1} -> df14e5a (04-02) RESTRICTS: ( or { must be exactly adjacent to the callee (direct and dot calls) -> #113/e75ec7d (05-15) RELAXES dot-call argument lists to a same-line ( or { after whitespace; direct calls stay exact-adjacent until acbfa7d -> #123/007917a (06-13) GENERALIZES IsCallArgumentStart to same-line for every callable target; a newline never continues into a call -> #143/7075071 (08-09) REPLACES the argument-wrapper lowering with one Expr.AlgorithmExpr slot (observable behavior unchanged) -> #160/2b03c0b (09-12) RESTRICTS: a non-callable LHS before ( or { is UnseparatedSameLineItem -> #168/50c74c1 (09-22) EXTENDS: a redundantly grouped callee is callable ((F){x}, (F)(1))

**Surviving semantics:** A same-line ( or { after a callable target (name, dot edge, Grace name, or a redundantly grouped one) is a call delimiter even across whitespace; a newline never continues a closed expression into a call. F{e} is F {e} is F({e}): ONE AlgorithmExpr argument slot whose free names are its implicit parameters. Non-callable left-hand sides (2 {3}, F(1) {x}) are UnseparatedSameLineItem. Lean KatLang.lean:7257-7300; Parser.IsCallArgumentStart.

### Area: parameter-inference-grace

#### A. Implicit-parameter promotion scope and the closed explicit list

**Steps:** v0.6 3e268b1 (2021-12-01) ORIGIN: ordered implicit params with GraceWeight -> v0.7.3 25a8558 (2026-03-07) IMPLEMENTS: any unknown identifier becomes a param, 'No casing restriction' (ParameterDetector.cs:12); tutorial 6cb9334 states the rule; camelCase by convention only -> #1 61e191b (03-11) IMPLEMENTS: brace blocks own their free names -> #21 6dbcc0c (04-05) RESTRICTS: branch pattern is the complete input spec, branch bodies infer nothing -> #23 f647dac REFINES: checked over every branch -> #39 419100a (04-09) IMPLEMENTS: single clause = ordinary algorithm whose list was OPEN (detector 'then infer additional implicit params') -> 6c64e66 (05-08, no issue) CHANGES THE RULE: every explicit list CLOSED, free names are UndeclaredIdentifier; Lean doc + tutorial updated -> d21b163 (08-15, #147) EXTENDS: MAY-selected dot fallback participates in inference (K = a.t is K(a,t)); closed checks MUST-only -> #154 b3738b9 (08-24) NARROWS: Math aliases are prelude names, not promotable -> #155 667155e (08-25) AMENDS: e promotable again -> a3a2932 (09-06, K1-05) REFINES: deconstruction RHS names belong to the enclosing body -> f7ee8ea (09-12) REFINES: root phantom never called -> ef0f1cf (09-13, G-24) REAFFIRMS: known-receiver missing member still infers (diagnostics only) -> ad6d6bf (09-23, audit #8) CONSOLIDATES: rule 3 'promotion only after owner walk and opens'

**Surviving semantics:** A bare name that no owner level declares (parameter or property, prelude included) and no open provides becomes an implicit parameter of the innermost enclosing algorithm without a written parameter list. Under a written list or in a branch body it is UndeclaredIdentifier. There is no casing rule. A brace block owns its unbound free names, but a name the enclosing level's own rows use belongs to that level. Closedness is per level, so nested bodies without a list still infer. A dot fallback that MAY be selected participates in inference, while closed checks use MUST. The root is never called, so an unresolved root name is an evaluation error.

#### B. Implicit-parameter order

**Steps:** 25a8558 (03-07) ORIGIN: own names by first appearance, lifted names appended ('existing first, then new ones from deps', ImplicitArgumentResolver.cs:312 at 25a8558) -> #78 (04-27) QUESTIONS the order ('another story'), not changed: implicit Quadratic is (b,a,c) -> uncommitted 0.8.160/0.8.161 (08-14/15) PROPOSES callee-first dot order a.t=(t,a) -> REPLACED by d21b163 (08-15): receiver, MAY-fallback, then args (a.t=(a,t), a.t(b)=(a,t,b), t(a)=(t,a)); AGENTS order bullet added -> a3a2932 (09-06) REFINES: deconstruction RHS rows merged by written position -> 3f57517 (09-09) REFINES: CompleteOwnership retains discovered order and Grace order, no replay

**Surviving semantics:** A signature lists the level's OWN free names in first-semantic-source-occurrence order: rows in written order; DotCall contributes receiver, then MAY-fallback, then args; Call contributes callee, then args. Grace reorders only this own list. Lifted names follow, appended in callee-reference order and deduplicated, and Grace cannot move a name across them (A = x - y; F = A - z~ gives (z,x,y)). The lifted-append part is pinned by the tutorial and TutorialSemanticContractTests.ForwardedParameters_FollowTheOwnNames_AndAreHandedOnByName, but AGENTS.md omits it.

#### C. Grace ~: weights, eligibility, effectiveness, attachment

**Steps:** v0.6 GraceWeight / v0.7.3 EBNF GraceIdentifier ORIGIN (prefix -1 earlier, postfix +1 later) -> #21 6dbcc0c (04-05) RESTRICTS: no Grace in branch patterns or bodies -> #22 01ffdd4 FIXES the span -> #38 022abc4 (04-07) BUG FIX/REAFFIRMS: Grace on a callee occurrence predicate~(x) -> 6c64e66 (05-08) NARROWS: no inference, so no Grace, under explicit lists -> Track3 F2 (08-08) IMPLEMENTATION: iterative ScanPendingForGraceSpan (walks block outputs, not properties) -> 08-15 intermediate weight distribution over compound operands PROPOSED then REMOVED the same day; d21b163 law: exactly ONE bare name occurrence -> ec48b91 (09-07, K5-R1) REFINES: marker run is physical-line-local; compound-operand runs rejected -> #161 cb6cfda (09-11) REFINES: attachment law (~ x, a ~ .t rejected) -> #160 2b03c0b (09-12) REMOVES the A~B two-slot adjacency -> F10 aaae65c (09-13) CHANGES THE RULE: Grace must be effective, InvalidGraceMarker on fixed bindings and under closed lists; reverses the August 'no-op on bound names' -> #168 50c74c1 (09-22) REFINES: (~a) is Grace on the name (no capture)

**Surviving semantics:** ~ decorates exactly one directly attached bare-name occurrence on its own physical line. Weights: prefix -1, postfix +1, summed per name; one swap per unit over the OWN inferred list, stopping at the boundary or at an equal or more extreme neighbour; excess movement is silently ignored (SEMANTIC-ALIGNMENT §1). It is legal only on a free name that promotion makes a parameter. Otherwise it is InvalidGraceMarker: explicit or captured parameter, property, builtin, opened name, structural member, .string, anything under a closed list at that level, clause-head pattern, collecting binding, open target, or branch body (parser rule). It is stripped before evaluation and never changes selection. A redundant group is transparent.

#### D. Grace composed with dot syntax (#147 -> #152)

**Steps:** 6c63486 (08-14, 0.8.159) A PROPOSES/IMPLEMENTS: extension-dot mode recv~.Name / recv.~Name that skips structural lookup -> #147 reopening comment (08-14) B PROPOSES: K = a~.t == K(a,t) = t(a), lowered to a call, order (a,t) -> uncommitted 0.8.160 B IMPLEMENTS: parser lowering to Call(t, Grace(a,-1)) with IsExtensionReceiver -> d21b163 (08-15, 0.8.162) D CHANGES THE RULE: ~ is ordering-only on the SAME structural-first DotCall; base (a,t), graced a~.t and a.~t give (t,a); extension mode and IsExtensionReceiver deleted (published API correction); Obj~.V, x~.string and S~.count agree with the ungraced forms -> 600fedd (08-16) DOCUMENTS the normative Grace+DotCall laws -> #152 e82c301 (08-20) A PROPOSES dotless a~t (review: the claimed equivalence a~t == t(a) is false under a structural collision) -> b28567f the same day REMOVES it -> #161/F10 (09-11/13) REFINE: a ~ .t rejected; K(a,t) = a~.t and Obj~.V are InvalidGraceMarker -> #160 2b03c0b (09-12) REMOVES: a~t is UnseparatedSameLineItem

**Surviving semantics:** a~.t(args) is postfix Grace on the bare receiver plus an ordinary .t. a.~t(args) is an ordinary dot with prefix Grace on the member/fallback occurrence. Both elaborate to the same ordinary structural-first DotCall as a.t: base order (receiver, MAY-fallback, args), graced (t,a). Postfix Grace on a compound receiver or on a second ~. in a chain is rejected. The runtime law R.F(args) == F(R,args) after a structural miss is untouched. Only free receivers or members may carry Grace.

#### E. Ancestor capture and local-only nested members (#54 -> K1-08)

**Steps:** 61e191b (03-11, #1) ORIGIN: inline blocks are algorithms -> 58c227b (04-15) IMPLEMENTS: nested scopes capture ancestor parameters (OccurrenceCount target), flat capturedParamNames -> #53 b627c21 (04-15) BUG FIX: grouped/higher-order argument binding preserved -> #54 6d7617e (04-16) IMPLEMENTS/RESTRICTS: nearest wins; a name used in the owner's output belongs to the owner; captured nested properties and family properties are local-only; no staged binding; mechanism = exported-only LOOKUP (Lean lookupPropDefExportedAny? filters exposure) -> c58ce3a (06-04) REFINES: captures discharged at user-algorithm boundaries, so public APIs over private helpers stay exported -> a3a2932 (09-06, K1-02) FIXES the summary through capture/call bundles -> 7300596 (09-14, K1-08) D CHANGES THE RULE: selection never depends on exposure; one post-selection accessibility law (IsAccessibleFrom / memberAccessible?); inside-owner access allowed; open provider needs no call -> ad6d6bf (09-23 audit #8 D6) REFINES: per-level open ambiguity in exposure -> ad73df8 (09-26 FE-4a) IMPLEMENTATION ONLY -> final hostile pass REFINES: open head between opener and settling level charges the capture

**Surviving semantics:** Nested bodies capture ancestor-owned parameters lexically, and the level whose own rows use a name owns it. A member whose transitive owner-bound requirement set (name plus owning scope) is non-empty is classified local-only, but the classification never affects selection. The uniquely selected member is accessible exactly inside an activation of every required owner (Outer(5) with Inner.X gives 5) and refused outside with LocalOnlyProperty. Clause families expose no branch members. There is no staged binding: Algo(6).Prop gives UnresolvedImplicitParams.

#### F. Explicit parameter ownership: property-beats-captured-parameter -> owner walk (#158, SYN-03)

**Steps:** 58c227b / 6753065 (04-15/22) A IMPLEMENTS: a captured ancestor parameter is used only if no visible property of that name exists (capturedParamNames.Contains && !HasVisiblePropertyName) -> 3bc2a29 (05-04) B NARROWS: builtins excluded (HasVisibleNonBuiltinPropertyName) -> b3738b9 (08-24) B NARROWS: prelude aliases excluded (HasVisibleNonPreludePropertyName; F(e) = {e+1} binds the parameter) -> #158 (09-09, CLI 0.8.179) C DISCOVERS: root v = 99 overrides the nested Outer(v) reference, giving 100 -> 3f57517 (09-09) D CHANGES THE RULE: owner walk ElaboratedScopeLookup.SelectOwnedDeclaration / Lean selectOwnedDeclaration, ParameterOwnership, ParameterPropertyCollision (Lean conflictingOwnedNames), CompleteOwnership; promotion (IsBoundName) unchanged -> f7ee8ea (09-12) REFINES: root phantom exemption -> e6390ed (09-12, F2) EXTENDS: open-target head through the owner walk, OpenTargetIsParameter (Lean elaborateOpenHead) -> ad6d6bf (09-23, audit #8) CONSOLIDATES the six-rule model, NameResolutionAuditTests

**Surviving semantics:** Search outward by owning scope; at each level a parameter binding (written, inferred, lifted, collecting, grouped, branch binder) comes before the level's properties; the first owner that declares the name decides. The prelude is the outermost property level, and opens are consulted only after the whole walk. A property may not share a name with a parameter of its own or an enclosing owner (ParameterPropertyCollision); the never-called root collides only with its own properties. A farther property versus a nearer parameter, and a parameter versus a parameter, are legal and the nearer one wins. Lifted parameters are ordinary owner parameters after completion. A parameter-owned open head is an error.

#### G. Lifting / forwarding of implicit parameters into callers

**Steps:** 25a8558 (03-07) ORIGIN: bare refs to parametrized siblings rewritten to calls, params appended; call args a 'separate scope' -> 999f14a (03-17): dot target in call position -> #78 8fbc972 (04-27) A INTRODUCES: Math member dot-call args are lifting positions, recognized by spelling (IsMathValueDotCall: target is Resolve 'Math', no shadow check) -> 6c64e66 + 21467f3 (05-08) B REFINES: pattern-aware lifting; closed lists forward BY NAME only; narrow single-collecting-stream shape forwarding -> #106 75f0d2b / #108 fd1a975 (05-13/14) A: runtime provenance forwarding -> #138 ab7d2f5 (07-18) REVERSES it: resolver ForwardAsSpread only collecting->collecting (C-full 702e7d7/5d6d60b 09-23 REAFFIRMS) -> b3738b9 (08-24) REFINES: Math shadow predicate + alias spelling -> 8aac3eb (09-04, B2a) C DISCOVERS a regression from the separate Math path: degenerate caller config, closed-list bypass (F(x) = Math.Abs(A) returned 21); FIX: one ImplicitRewriteContext -> 8d2fc53 (09-04) REFINES: closed-list strict-value (Math) diagnostic -> 3f57517 (09-09) REFINES: CompleteOwnership (lifted parameters re-select and collide; signatures retained, dead params possible) -> #168 50c74c1 (09-22) REFINES: Math.Abs((A)) now lifts -> ad6d6bf (09-23, audit #8) EXTENDS: Math contract by identity (opened Sin(A), must-selected A.sin) -> a974303 / 9078421 (09-26 FE-2/FE-3) IMPLEMENTATION ONLY

**Surviving semantics:** A bare reference to a parameterized declared property, a Math alias, or a qualified Math.X in a lifting position is rewritten into a call. It passes the caller's same-named bindings, and the missing captures are appended to the caller's signature with pattern shape and kind kept. Lifting positions: output rows, deconstruction RHS, operator operands, index parts, spread operands, list items, registry-strict Math args (any spelling that resolves to the member), and a must-selected Math fallback. Never lifted: ordinary call and builtin args, capture rows, callee positions, open-provided names, structural paths. A closed list forwards by name only. A blocked Math strict position is a front-end UndeclaredIdentifier; elsewhere it is a runtime zero-argument demand. Synthesized spread happens only collecting->collecting. Siblings are processed in topological order, cycles in declaration order. **Superseded 2026-09-30 (the unified formula-lifting law; re-verified 2026-10-01):** every callable category with a lifting signature — user, builtin, Math, host operation, opened or dotted member, nameable clause family — lifts in a formula; lone rows are FWD-02's exact aliases and bare forwarding.

#### H. Bare builtin callable aliases (#114)

**Steps:** 25a8558 ORIGIN: user aliases propagate (Test2 = Test1) -> #114 c1e19b1 (05-16) IMPLEMENTS, narrower than the title: TryGetBuiltinCallableSignature answers only ownerName == 'Math', i.e. the bare qualified Math.Round lifts the registry signature, with a sibling shadow check -> #154 b3738b9 (08-24) EXTENDS: the prelude alias round lifts too -> SYN-05 0243678 (09-10) CONSTRAINS: builtins are identity-resolved prelude bindings, but bare lifting was not extended to non-Math builtins -> ad6d6bf (09-23, audit #8) CLARIFIES/NARROWS: 'route-based' (alias and Math.X lift; an open Math spelling is never implicitly forwarded; stamping the opened name for lifting was rejected)

**Surviving semantics:** A bare Math FUNCTION member referenced through qualified Math.X or its prelude alias, in a lifting position, lifts its registry signature with the registry parameter names (RoundB = Math.Round and RoundC = round give 1.23). The open Math canonical spelling does not lift (RoundD = Round is ArityMismatch). Non-Math prelude builtins do not lift (S = sum is zero-parameter): undocumented and unpinned, and an open question. **Superseded for formulas 2026-09-30:** every prelude builtin, host operation and opened or dotted member lifts in a formula too; the lone-row alias eligibility of non-Math callables is open question Q-12.

#### I. A bound parameter owns its name (callbacks, loop steps, native wrappers) (#95)

**Steps:** #92 3997ad6 (05-06) A: every user-call, branch and loop-step scope shadows inherited same-named bindings (CountedParamEnv.shadow) -> #95 37c6898 (05-07) C DISCOVERS a regression of #86 planned loops: the optimized step read the outer filter callback's n; Lean and generic agreed; REAFFIRMS that loop-state parameters shadow -> #156 04b5fc8 (08-29) A: native wrapper reads its own argument (LookupNativeArgument) -> 8d2fc53 (09-04) + f321843 (09-08) D GENERALIZES: ONE helper ShadowInheritedParameterEnvironments / Lean EvalCtx.bindParameters for value, counted and algorithm tiers at every binding site, in both engines and the async twin

**Surviving semantics:** A bound parameter owns its name on every channel. Every binding site (user calls, clause binders, callbacks, generic and planned loop steps, native wrappers) shadows the callee's parameter names out of all inherited tiers, so lookup never falls through to a same-named caller binding. Optimizations must be invisible (#95 program gives [13, 17] on all paths).

### Area: builtin-surface

#### Builtin inventory (added / renamed / removed)

**Steps:** v0.7.3 25a8558 (<=03-07) baseline if/3, while/2, repeat/3, atoms/1 + dot-only .length + C#-only Math + load -> #15 5a6c550 (03-30) ADDS 2-arg if -> #32 6869338 (04-06) ADDS .string intrinsic -> #35 b3c39bc / #37 b2eb2b5,83eccae,a66564b (04-08) ADD range/filter/reduce/map; #40 REJECTS foreach -> #34 cccffea,9b3f1ff,03c035f,bebee03 (04-09) ADD sum/count/min/max/avg -> #49 93a036d (04-13) REMOVES 2-arg if -> #45 27d3f57,3b0dad3,c410c2f,902e530,aa4ce72 (04-16..19) ADD order/orderDesc/first/last/take/skip/distinct/contains -> #56 732549d RENAMES .length->.arity -> #59 04fedfe REMOVES .arity -> #81 b950d86 (04-29) ADDS empty -> #91 5d1b52c ADDS ungroup -> #98 7ad022c RENAMES content -> #94/#77/#109/#110/f273d69 (05-14..17) Math members Atan2, Random/RandomInt, Round(value,digits) -> #128 73cdba2 (06-22) REMOVES empty -> #129 7458502 (06-26) REMOVES content -> #154 b3738b9 (08-24) ADDS 21 Math prelude aliases -> #155 667155e (08-25) REPLACES Math.E/e with Math.Exp/exp

**Surviving semantics:** Exactly 21 Lean-modeled prelude builtins (if while repeat atoms range filter map order orderDesc count contains first last distinct take skip min max sum avg reduce; Lean preludeAlg KatLang.lean:7375-7398 = BuiltinRegistry.cs:314-336). C#-only surface: 21 Math members + 21 lower-camel aliases, dot-only .string intrinsic, load directive, host operations. length/arity/ungroup/content/empty/foreach/e are ordinary unresolved names.

#### Collection-argument shape (one collection <-> variadic items pendulum)

**Steps:** #34 9b3f1ff (04-09) DECIDES one collection arg, opened one level (count(((1,2),(3,4)))=2) -> #57 2f27fba (04-17) body PROPOSES 'support both' but IMPLEMENTS variadic items + lone grouped arg = ONE item (count((1,2,3))=1, order((1,2,3)) invalid): REVERSES #34 opening -> #58 c9a43fa/#61 17e34bd REFINE -> #69 d3ee6d7 FIXES sum(P)=P.sum; #71 c876d28 DECIDES comma boundaries, flatten only via ';' -> #72 f2898cb REMOVES variadics, 4367f57 REVERTS -> #73 3bc2a29/c147585 variadics as general feature -> #104 0e9b41f (05-13) REGRESSES: count(A)=1 while A.count=3 -> #125 ad75720 (06-17) CHANGES to strict one-slot values... (count((1,2,3))=3, sum(1,2,3) error) -> d2837f4 (06-19, no issue, after #126) CHANGES to item-stream + singleton normalization (count(1,2,3)=count((1,2,3))=3) -> #134 d202b74 lists deferred for builtins -> #135 0ca55e9 (07-17) CHANGES FUNDAMENTAL RULE: fixed arity, ONE collection param + fixed controls, nothing opened before binding, post-binding one-level view, no overloading -> #138 ab7d2f5 REAFFIRMS -> 68b3607 (09-21) REAFFIRMS no dot-specific path

**Surviving semantics:** Every collection builtin is an ordinary fixed-arity callable: count/sum/first/last/min/max/avg/order/orderDesc/distinct(collection), take/skip(collection,count), contains(collection,item), map(collection,mapper), filter(collection,predicate), reduce(collection,reducer,initial); range(start,stop), atoms(value), if(c,t,f) fixed. An unspread sequence/list is ONE argument; spread supplies ordinary slots obeying the same arity (re-group sum((A*,B*))). The bound value is read via builtinCollectionItems: lone sequence or list opens one level, any other value is one item, never recursive. Only loop init tails remain runtime-variadic (repeat(S,3,1,0) ok).

#### Plain vs dotted builtin calls

**Steps:** #14 d901280 (03-30) dot on any receiver; #34 body asks (1,2,3).sum vs sum((1,2,3)) -> 48a03c8, e4630d0, 22788b9 (#60), c9a43fa (#58), 17e34bd (#61) (04-15..19) REFINE builtin dot receivers -> #69 d3ee6d7 FIXES sum(P) vs P.sum; #76 315dd54 empty receiver is one argument; #80 5172e62 reduce(Right,..)=Right.reduce(..) -> #104 0e9b41f (05-13..06-17) REGRESSES: dot strips one receiver layer, count(A)=1 vs A.count=3 -> #125 ad75720 DECIDES dot is canonical P(receiver,args) -> #135 (f) REAFFIRMS no builtin-specific placement -> 68b3607 (09-21) DELETES sequence-builtin dot path and dotted reduce-initial hint -> #170 ebf623e REFINES receiver reads property cache

**Surviving semantics:** R.f(args) == f(R,args) for every builtin in value, arity, error kind, zero-argument demand and cache; a structural member beats builtin fallback (Obj.count member wins). Sole exception: the .string intrinsic, dispatched by spelling before structural lookup (Lean KatLang.lean:6472 vs :6495); string(5) is unresolved.

#### Collection builtin result kinds

**Steps:** #35/#37/#34/#45 (04-08..19) producers return multi-output sequences, contains 1/0 -> #130 (06-26) if value boundary -> #132 9a4c70f GENERALIZES one-value result boundary, producers one canonical sequence -> #133 e6c2bdc FIXES by shallow singleton erasure -> #135 0ca55e9 CHANGES FUNDAMENTAL RULE: producers return ONE exact list via makeCollectionListResult ([] / [item] / [..]), kind independent of input kind -> #137 2c0af18 COMPLEMENTS with list indexing; #136 c133952 EXTENDS to atoms -> #165 e4d19cc contains returns Boolean -> 874625a (09-21) first/last become selection value boundaries (first(A)==A:0)

**Surviving semantics:** range/filter/map/order/orderDesc/distinct/take/skip/atoms return one exact list (single survivor [item], never erased); count/sum/avg/min/max/contains return one scalar/Boolean; first/last choose a stored element re-counted by Result.valueCount; no builtin produces a literal-unwritable value.

#### Callback binding for map/filter/reduce

**Steps:** #37 a66564b/83eccae (04-08) DECIDES element passed whole (Swap((a,b))), reduce step(element, accumulator), single-value result; #41 ee8180c predicate one atomic truth -> #53 b627c21 FIXES forwarded predicate identity -> #58 c9a43fa (04-18) CHANGES: callback items projected one level = flat-callback row convention (Swap(a,b)) -> #92 3997ad6 FIXES callback binding shadowing (generalized f321843) -> #102 33b318a EXTENDS accumulator-side variadic opening -> #135/#138 ab7d2f5 REFINE (list results; row convention to collecting callees) -> #156 04b5fc8 (08-29) EXTENDS natives/qualified Math.X as direct callbacks -> #165 e4d19cc predicate Boolean -> 874625a/dada1b6 REFINE -> S3 5d6d60b + forwarded-callable (09-23) REFINE -> C-full 702e7d7 (09-23) CHANGES FUNDAMENTAL RULE back to #37: element = one ordinary argument, reduce = F(element, accumulator); deletes row convention and accumulator opening -> #170 ebf623e cache transparency -> Q-25 (10-10, owner decision, Option B) CHANGES the result rule: a callback returns its ordinary call result

**Surviving semantics:** THE CALLBACK LAW: each element is ONE ordinary argument bound by the ordinary counted binder; structural patterns open it explicitly; reduce calls F(element, accumulator) with the accumulator one argument; map/reduce callbacks must emit exactly one non-() value (not a value boundary); filter predicate must be a Boolean via Result.asBool?; invoking slots receive the callable, reduce initial is a value slot; Math members/host ops and qualified Math.X are direct callbacks. *(Q-25, 2026-10-10: "map/reduce callbacks must emit exactly one non-() value (not a value boundary)" is SUPERSEDED — a callback returns its ordinary call result, one value at the call boundary; HO-03.)*

#### Counting and structural size (length -> arity -> removed; what count counts)

**Steps:** v0.7.3 25a8558 .length intrinsic (output expression count) -> #34 9b3f1ff ADDS count(collection) -> #56 732549d RENAMES .length to .arity, keeps count -> #59 04fedfe REMOVES arity ('no specially treated builtins'; premise false because .string 6869338 predates it) -> #57 2f27fba count((1,2,3))=1 -> #88 declared list.count=1 'not a bug', fixed by user variadics -> #125 ad75720 count((1,2,3))=3 -> #135 0ca55e9 post-binding view reverses #88 diagnosis

**Surviving semantics:** count(v) = number of items in the one-level collection view of the one bound value (count('abc')=1, count(true)=1, count(())=0, count((1,[2],3))=3, count((1,7))=2). No arity/length builtin; 'arity' survives only as maintainer terminology distinct from count.

#### One-level opening builtins and atoms

**Steps:** v0.7.3 atoms recursive flatten -> #91 5d1b52c ADDS ungroup -> #98 7ad022c RENAMES content -> #103/#104/#111/#122-#124 postfix ... supply -> #129 7458502 REMOVES content (spread is the only opener) -> #139/#140 REPLACE SYNTAX ... -> * -> #136 c133952 DECIDES atoms traverses sequences and lists, returns one exact list, separate from hostAtoms -> #165 Booleans contribute nothing

**Surviving semantics:** atoms is the only recursive flattener: numbers give [n], sequences and lists traversed depth-first, strings/Booleans contribute nothing, result always one exact list (atoms(7)=[7]); v* opens exactly one sequence or list boundary; no ungroup/content builtin.

#### The empty builtin constant

**Steps:** #81 e8f8b10 allows () -> b8a24db REVERTS ('() defines an algorithm') -> b950d86 (04-29) ADDS reserved builtin empty -> #128 73cdba2 (06-22) REMOVES empty, () is the structural empty sequence value

**Surviving semantics:** The explicit empty result is the value (); empty is an ordinary identifier (unresolved when free).

#### if as a builtin

**Steps:** v0.7.3 if/3 -> #15 5a6c550 ADDS 2-arg form -> #49 93a036d REMOVES it (single signature, no overloading) -> #130 value boundary -> #131 7e1085e spread before arity, parse gate kept for non-spread -> 57e9ed0/f42195d arity diagnostics -> #159 0243678 (SYN-05) DELETES Parser.ValidateIfArity, if is ordinary shadowable prelude binding, laziness belongs to identity -> #165 Boolean condition

**Surviving semantics:** if(condition, whenTrue, whenFalse) is the only signature; wrong count is an evaluation-time ArityMismatch; a nearer user if/parameter shadows it completely; only the resolved builtin is lazy in its branches.

#### Utility-builtin design choices

**Steps:** #40 (04-08) REJECTS foreach -> #45 comment 2 (04-11) DECIDES SQL/C# names (order not sort), no range syntax 1..10, no laziness in language/Lean, no range(start,finish,transform) -> 27d3f57/3b0dad3/c410c2f/902e530/aa4ce72 IMPLEMENT (order = stable insertion sort, orderDesc = reverse) -> #127 structural equality for distinct/contains -> #165 contains Boolean -> e4c7973 (09-15) PINS order-is-stable -> 874625a first/last selection; #87 020b7ec fusions implementation-only (#135 h: never make an invalid form valid)

**Surviving semantics:** Named, non-lazy utility builtins; range stays 2-ary; distinct/contains use the one structural equality of ==; order stable ascending, orderDesc its reverse; take/skip counts whole numbers (<=0 gives [] / all, oversize saturates); first/last need non-empty collections.

#### Numeric aggregation semantics

**Steps:** bebee03 (04-09) avg decimal mean -> 1fe689e (04-17) CHANGES avg to integer quotient to match Lean -> a6aaa80 (06-15) REVERSES: runtime decimal mean, Lean Int.tdiv declared model limitation -> #153 7f0bab0 Decimal128 -> 7c66530 (09-24, audit #6) avg = correctly rounded exact mean -> 38b5918 (09-27) PINS min/max signed-zero IEEE minimum/maximum

**Surviving semantics:** sum of empty is 0; avg is the correctly rounded exact mean (avg((1,2))=1.5); min/max are IEEE minimum/maximum with NaN propagation and -0<0 tie rule; numeric collection builtins accept only single numeric atoms (sum([true]) error). Numeric details are C#-tier; Lean keeps Int truncation (stale Lean header comment avg(1, 2) = 1).

#### Math surface and prefix-free aliases (C#-only)

**Steps:** #48 9c4e063 (04-12) DECIDES prefix-only Math (Math not in Lean) -> #94 20fc773 Atan2 (17d480b metadata fix), #77 238ff20 Rand/RandInt -> #109/#110 489b77f Random/RandomInt(start,end), f273d69 (05-15) Round(value,digits) away-from-zero -> #114 c1e19b1 FIXES bare Math alias lifting -> #153 Decimal128 -> #154 b3738b9 (08-24) REVERSES #48: one explicit lower-camel prelude alias per member -> #155 667155e REPLACES Math.E/e with Math.Exp/exp; dda6ba7 metadata -> #156 04b5fc8 (08-29) EXTENDS natives + qualified Math.X as direct callables -> 8aac3eb lifting context fix; G-24 Math.cos(1) lexical fallback -> audit #8 ad6d6bf (09-23) REFINES identity-based recognition, alias and member distinct bindings sharing one algorithm

**Surviving semantics:** 21 canonical PascalCase members only inside Math, each with one explicit lower-camel prelude alias that is an ordinary shadowable prelude binding (beats opens, dot fallback, higher-order use, reserved against host ops); alias and canonical member are distinct bindings sharing one algorithm object; qualified Math functions are first-class callables; bare Math alias lifts (S = abs), opened canonical does not; entire surface is C#-only (not in Lean).

#### Builtins as ordinary prelude bindings (identity, value demand, aliasing)

**Steps:** #59 04fedfe PROPOSES no specially treated builtins (.string and load remain exceptions) -> #131 7e1085e FIXES spread into if -> #159 0243678 (SYN-05) CHANGES FUNDAMENTAL RULE: select ONE identity without arity, no spelling branches, complete shadowing -> 9f6cdfb (09-13) DECIDES builtin value slots use zero-argument value demand -> 2d47a93 (09-22) eligibility follows call arity -> forwarded-callable (09-23) invoking slots read algorithm channel -> #170 ebf623e (09-27) builtin value slots read property cache (reverses B1) ; standing asymmetry: #114 c1e19b1 alias lifting only for Math (S = sum, T = if stay zero-parameter)

**Surviving semantics:** Builtins are prelude properties at the outermost property level of the owner walk, selected by identity, shadowable, no overloading by arity or input kind, arity checked at evaluation; every builtin value slot demands via the zero-argument law, invoking slots receive the callable; builtins passed as arguments are first-class (F(sum)). Bare alias of a non-Math builtin does not forward its signature (unpinned).

#### Builtin diagnostics (non-constitutional)

**Steps:** #65 4e19be6 (04-25) ADDS dotted reduce initial-accumulator hint -> 8db1801/ba0d196/7590933 (05-10) signature-based arity messages -> 68b3607 (09-21) DELETES the dotted reduce hint (SEMANTIC-ALIGNMENT.md:336)

**Surviving semantics:** Dotted and plain wrong-arity builtin calls report the identical ordinary ArityMismatch naming the signature. Open: ArityMismatch.Expected payload placeholder 0 for non-if builtins; BadArity vs IllegalInEval vs BadIndex error-kind non-uniformity.


## Part 2 — Per-issue entries (chronological)

### #1 — Inline parametrized algorithm call syntax broken in v0.7+
- **Dates:** created 2026-03-08 · closed 2026-03-11
- **Problem / question:** `Algo = func(9)` followed by `Algo{a + 1}` (pass an inline, parameter-inferring brace algorithm to a higher-order callee) did not work after v0.7.
- **Decision / intended invariant:** Trailing-brace call sugar: `Algo{e}` ≡ `Algo({e})` — a same-line `{…}` after a call target is ONE argument slot holding the brace algorithm; its free names become its implicit parameters; the callee receives it on the higher-order (algorithm) channel. Zero-parameter blocks evaluate as values; a parametrized block is not silently executed (commit 61e191b).
- **Rationale:** inline anonymous algorithms must participate in higher-order binding like named ones.
- **Examples:** `Algo = func(9)` / `Algo{a + 1}` → `10`.
- **Lineage:** refined by #113 (reaffirms — dot-call trailing block must not be whitespace-sensitive, e75ec7d); generalized by #37 (brace callbacks for map/filter/reduce); refined by #143 (braces = `AlgorithmExpr` identity, parentheses = capture, not algorithm).
- **Classification:** CURRENT
- **Surviving part / superseded by:** whole rule survives; the "argument-wrapper algorithm" lowering was replaced by a single `Expr.algorithmExpr` bundle slot (no wrapper), same observable behavior.
- **Current evidence:** `lean/KatLang.lean:7257-7300` ("Trailing brace-block call sugar": `Algo{e} ≡ Algo({e})`, lowered to `call (resolve "Algo") [Expr.algorithmExpr inlineAlg]`); `KatLang.ebnf:593` `BraceArgs = "{" Algorithm "}"`; tests `EvaluatorHigherOrderTests.Eval_InlineBlock_TrailingBrace_SingleArg` / `_ZeroParam` / `_ArityMismatch` (lines 696-710), `OutputBundleSplitTests.TrailingBraceCall_LowersToOneAlgorithmExprSlot` (line 119); AGENTS line rule "a same-line `(`/`{` after a callable is a call delimiter".
- **Probe:** `Algo = func(9)` / `Algo{a + 1}` → `10`; also `Algo {a + 1}` and `Algo({a + 1})` → `10`; `map([1, 2], {x * 2})` → `[2, 4]`.
- **Topics:** SYN, ALG, HO, CALL

### #2 — Fix combining operator ';'
- **Dates:** created 2026-03-08 · closed 2026-03-10
- **Problem / question:** the v0.6 semicolon "combining operator" was unsupported in v0.7+.
- **Decision / intended invariant (at the time):** `;` = value-level structural combining: evaluate both sides, concatenate their top-level items, normalize (flat, no grouping layer) — commit 9f3a0f9 added `Expr.combine`/`Result.toItems` to Lean and C#.
- **Rationale:** restore v0.6 join capability.
- **Examples:** `(1, 2); (3, 4)` → `1, 2, 3, 4` (then). Current equivalent: `(A*, B*)` (spread into a capture) → `(1, 2, 3, 4)`.
- **Lineage:** refined by #62 (perf), #71 (flatten only via explicit `;`); redesigned by #75 ("result join", 23d9a0c); replaced by #104 (`...` sequence-supply operator, 0e9b41f/97867d0); #120/#122/#123 (join vs supply precedence); removed by #125 ("Remove semicolon expression syntax", ad75720); `...` later replaced by postfix `*` spread (#139/#140).
- **Classification:** REMOVED
- **Surviving part / superseded by:** nothing of `;` survives — it is a parse error. Its concatenation role is served by the spread marker inside a capture (`(A*, B*)`), per #125/#140.
- **Current evidence:** `DiagnosticCode.UnsupportedSemicolon` (src/KatLang/DiagnosticCode.cs:54), message const `Parser.UnsupportedSemicolonExpressionMessage` (src/KatLang/Parser.cs:1638); spec case `semicolon-not-expression-syntax` (LanguageSpecCorpus.cs:3172); AGENTS "Semicolon `;` is not supported as expression syntax"; `sequences-lists-and-calls.md` spread section (`A* ; B` is invalid semicolon syntax).
- **Probe:** `(1, 2); (3, 4)` → parseFailure `UnsupportedSemicolon`; `A = 1, 2` / `B = 3, 4` / `(A*, B*)` → `(1, 2, 3, 4)`, `(A, B)` → `((1, 2), (3, 4))`.
- **Topics:** SYN, SUP, SEQ
- **Lineage review (phase 2) corrections/addenda:**
  - [supply-spread] REMOVED; evidence says '9f3a0f9 added Expr.combine/Result.toItems' and 'nothing of ; survives' → REMOVED (classification unchanged). Corrected evidence: Expr.combine pre-existed for `open A; B` and algorithm combining (combineAlg merged params, props and opens), and 9f3a0f9 added only the value-level `.combine` eval arm plus Result.toItems. Result.toItems survives, and the Combine node is the direct ancestor of Expr.SequenceSpread.. Evidence: `git show 9f3a0f9^:KatLang.lean` shows `| combine : Expr -> Expr -> Expr` (line 102), `combineAlg`/`combineAlgOpensClosed` (448-458), and the `open A; B` Combine comment (line 15). The 9f3a0f9 message says 'No changes to lexer, parser, AST ... infrastructure already existed from open-declaration combine support'. Node lineage from the Lean diffs: combine -> resultJoin (23d9a0c) -> binary sequenceSupply (0e9b41f) -> unary (4b32111) -> sequenceSpread (b568c66). Result.toItems is at lean/KatLang.lean:1263.

### #3 — Check conditional loop simplified example
- **Dates:** created 2026-03-08 · closed 2026-04-06
- **Problem / question:** `A = x + 1, x < 6` works as a `while` step (`A.while(0)`), but hand-nesting `A(A(A(A(A(A(0))))))` fails because the step also outputs the continuation flag. Should KatLang add a mechanism to drop an output part?
- **Decision / intended invariant:** No shape-transforming feature. A `while` step is a specialized algorithm: its outputs are the next state followed by the continuation flag (last output). Manual reuse must select explicitly (`A(…):0`) or use a step designed for direct calls (`A = x + 1`).
- **Rationale:** a shape-transforming feature would raise cognitive load and hurt performance.
- **Examples:** `A = x + 1, x < 6` / `A.while(0)` → `6`; `A(A(A(A(A(A(0):0):0):0):0):0):0` → `6`.
- **Lineage:** refined by #96 (variadic loop steps / explicit state slots, 6469363); refined by #132 (property/call results are one value — so unselected nesting `A(A(0))` passes the pair as one argument); refined by #165 (flag must be a Boolean); related #64 (loop syntax; open at the snapshot, CLOSED 2026-10-20 by META-S3-3, `9c8623f2`; this entry's `A.while(0)` reads `A(0).while` since then).
- **Classification:** CURRENT
- **Surviving part / superseded by:** survives unchanged in principle; the flag is now Boolean-only (#165).
- **Current evidence:** Lean `.whileBuiltin` arm (lean/KatLang.lean:5885-5897: `splitContSlots`, `true` continues, `false` returns the current state); `builtinAcceptsArity` `.whileBuiltin, n => n >= 2` (KatLang.lean:597); tutorial "Looping While a Condition Holds" (tutorial.md:1554); `evaluator-and-hosting.md` § Boolean values ("while continuation flag (the step's last output)").
- **Probe:** i03a `A.while(0)` → `6`; i03b selection-nested form → `6`; i03c `A(A(0))` → `TypeMismatch` (the pair `(1, true)` is one value); i03d `A = x + 1` six-fold nesting → `6`.
- **Topics:** LOOP, VAL, SEQ, BOOL
- **Lineage review (phase 2) corrections/addenda:**
  - [loops] CURRENT; 'survives unchanged in principle; the flag is now Boolean-only (#165)' → CURRENT, noting that the pre-#165 single-output step semantics were REMOVED. The lone numeric atom used to be both state and a truthy flag (0 stops); a single-output while step must now emit a Boolean.. Evidence: git show e4d19cc -- lean/KatLang.lean deletes '| [slot] => match slot with | .atom n => pure ([slot], n)' and 'expectInt last' in splitContSlots. The ledger #165 probe Step(x) = x - 1 / while(Step, 3) gives TypeMismatch; probe p03 (A = x + 1, 1) gives TypeMismatch on the flag.

### #4 — Fix KatLang examples that worked in v06 and does not work in v07+
- **Classification:** DOCUMENTATION ONLY — closed NOT_PLANNED: Project Euler 4/6 web examples were rewritten (AI-generated integer `Reverse` works), and the maintainer declined adding a `Reverse`/string builtin ("builtins should be designed carefully"); no builtin was added. Probe: Euler 6 (`Add = a + 1, sum1 + a, sum2 + a^2` …) → `25164150`; the fast Euler 4 translated to braces + Boolean flags → `906609` (the original numeric-flag `and`/`if(…,1,0)` style is now invalid after #165).
- **Topics:** COLL, LOOP

### #5 — Decide about adding explicit property Output (continue to support implicit output definition).
- **Dates:** created 2026-03-08 · closed 2026-03-13
- **Problem / question:** output was implicit (trailing rows); add an explicit `Output = expr` form for readability and to allow defining output mid-body?
- **Decision / intended invariant (at the time):** Add `Output = expr` as an alternative (commit 49640ea): lowers to the same `Algorithm.output`; at most once; no mixing implicit/explicit; `public Output` rejected; `Output` reserved in assignment position.
- **Rationale:** readability; allow output definition anywhere among properties.
- **Examples:** `Algo = 6` / `Output = Algo`. Current equivalent: `Algo = 6` / `Algo` (a row), or `Output = Algo` / `Output` (ordinary property + row).
- **Lineage:** refined by #52 (6f1f40d, Output not externally accessible, no params); superseded by #63 ("Removed implicit Output support", 8cf85f5, 2026-07-31 — actually removed EXPLICIT `Output =`), because output rows may now interleave with definitions anywhere.
- **Classification:** SUPERSEDED
- **Surviving part / superseded by:** superseded by #63 / 8cf85f5: one output mechanism — every non-definition expression row contributes output, rows may be interleaved with definitions; `Output`/`output` are ordinary identifiers. The "output in the middle" goal survives via interleaved rows.
- **Current evidence:** AGENTS "There is no output keyword; `Output` and `output` are ordinary identifiers"; spec cases `output-is-ordinary-property` (LanguageSpecCorpus.cs:405), `output-rows-interleave-definitions` (:3156), `output-dotted-access-ordinary` (:2283); memory `explicit-output-removal.md` (removed `EvalError.SpecialOutputAccess`, reserved-name classification).
- **Probe:** `Algo = 6` / `Output = Algo` → no program output (engine `NoProgramOutput`; evaluator paths `MissingOutput` — same outcome, different surface type); adding row `Output + 1` → `7`.
- **Topics:** SYN, PROP

### #6 — Check 'open' builtin design
- **Dates:** created 2026-03-08 · closed 2026-03-08
- **Problem / question:** is `open` (forms `open A`, `open Lib.Sub`, `open load('url')`, `open 'url'`) the right single construct, vs. Lean/Python/Rust-style separate import + open?
- **Decision / intended invariant:** Keep ONE `open` construct (KatLang has only algorithms, so no separate import); `open` is an import-like preamble that must appear before any property or output row of its algorithm (commit 599fe16).
- **Rationale:** consistency with Python imports / Rust `use` at scope top; two constructs are pointless when everything is an algorithm.
- **Examples:** `open Lib.Sub`, `open 'https://katlang.org/algorithm.kat'` (sugar for `open load('…')`).
- **Lineage:** refined by #18 (non-public head may be opened); #51 (static string-literal aliases in open targets); #93/#116/#117; later refined into one comma-separated target list per algorithm, static-open ownership (SYN-03), open-target validity and ambiguity (audit #8), K1-08 public-member exposure.
- **Classification:** CURRENT
- **Surviving part / superseded by:** all four forms and the top-of-body rule survive; now additionally "at most one `open` declaration per algorithm, comma-separated targets".
- **Current evidence:** Parser.cs:1430-1446 (`InvalidOpenDeclaration`: "Only one 'open' declaration is allowed per algorithm." / "'open' declaration must appear before any properties or output expressions."); `KatLang.ebnf:51` (`OpenTarget = StringLiteral (* sugar: open 'url' → open load('url') *)`); `syntax.md` § The `open` declaration; test `ParserTests.Parse_OpenAfterOutputLine_KeepsDeclarationBoundaryAndPlacementDiagnostic` (ParserTests.cs:2347), `DiagnosticProvenanceTests` (line 220).
- **Probe:** open after a property → parseFailure `InvalidOpenDeclaration`; `open Lib.Sub` first → `2`/`3`; `open 'https://mods.test/Lib'` and `open load('https://mods.test/Lib')` (with `--modules`) → `3`.
- **Topics:** MOD, SYN
- **Lineage review (phase 2) corrections/addenda:**
  - [open-ownership-modules] CURRENT (lineage: 'later refined into one comma-separated target list per algorithm') → CURRENT (lineage text fix only). Evidence: The one-open-per-algorithm comma list predates #6. 27f6d78 (2026-03-07) Lean header reads 'Each algorithm may contain at most ONE open declaration with a comma-separated list of targets', and the parser there reports 'Only one open declaration is allowed per algorithm.'. Also record the placement gap: an open after a clause definition is accepted (Parser.cs:1440 checks only properties/output; probe o1.kat).

### #7 — Broken result grouping
- **Dates:** created 2026-03-08 · closed 2026-03-10 (NOT_PLANNED)
- **Problem / question:** v0.7 displayed root rows `1 + 2, 2 + 3` / `3 + 4` / `4 + 5, 5 + 6, 6 + 7` flattened; reporter expected v0.6 per-row grouping.
- **Decision / intended invariant:** From v0.75 the correct output is FLAT — no "magic grouping" of written root rows: comma slots at root output are separate top-level output slots.
- **Rationale:** grouping should come from values, not from row layout.
- **Examples:** the three rows → `3 5 7 9 11 13` (six rows).
- **Lineage:** reaffirmed by root-output-is-an-item-supply rule; refined by #90 (display makes sequence values visible, fd3cabe) and #132 (property/call boundaries return ONE sequence value, so `A = 1+2, 2+3` / `A` displays `(3, 5)`).
- **Classification:** CURRENT
- **Surviving part / superseded by:** survives for written root slots; a NAMED multi-output property/call is now one sequence value (#132), displayed with parentheses (#90).
- **Current evidence:** spec case `supply-three-rows` (LanguageSpecCorpus.cs:522: "A comma expression list at root output creates three top-level output slots — an item supply, not one sequence value"); AGENTS "NOT value boundaries: root/body output accumulation".
- **Probe:** the issue's program → `S[3, 5, 7, 9, 11, 13] n=6`; `A = 1 + 2, 2 + 3` / `A` / `3 + 4` → `S[S[3, 5], 7] n=2` (display `(3, 5)` then `7`).
- **Topics:** VAL, SEQ, RUN
- **Lineage review (phase 2) corrections/addenda:**
  - [sequences-lists-values] Lineage: '#132 (property/call boundaries return ONE sequence value, so A = 1+2, 2+3 / A displays (3, 5))' → Lineage: '#125 (ad75720, 2026-06-17) made lexical zero-arg property access re-count to one value, so A displays (3, 5); #132 generalized the boundary to user calls, structural dot and builtins.' Classification stays CURRENT.. Evidence: git show ad75720 -- lean/KatLang.lean adds `pure (counted.fst, Result.valueCount counted.fst)` to the .resolve zero-arg property access arm; the #132 body itself says lexical property access and if (#130) already returned one grouped value.

### #8 — KatLang web page produces error on numbers exceeding decimal limit
- **Dates:** created 2026-03-08 · closed 2026-03-13
- **Problem / question:** `2/999999999999999999999999999999` crashed (literal exceeded `System.Decimal` range).
- **Decision / intended invariant:** An out-of-range number literal is a positioned lexer diagnostic with recovery, never an unhandled exception (commit 8a34693: `TryParse` + placeholder token).
- **Rationale:** robustness of the language core, not a web-page matter.
- **Examples:** `2/999999999999999999999999999999`.
- **Lineage:** range widened by #153 (Decimal128, 7f0bab0) and #97 (scientific notation); related #13.
- **Classification:** BUG FIX / REAFFIRMED EXISTING RULE
- **Surviving part / superseded by:** the "too-large literal → diagnostic" rule survives as `NumberLiteralTooLarge`; the original example is no longer out of range (Decimal128, 34 digits, exponent ±6144). Note: a literal with more than 34 significant digits is silently ROUNDED (not diagnosed).
- **Current evidence:** `Lexer.cs:257-270` (`TryParseNumberLiteral`, `DiagnosticCode.NumberLiteralTooLarge`, "Number literal is too large."); tests `LexerNumericLiteralConversionTests` (`1e6145` → NumberLiteralTooLarge, line 285), `DiagnosticCodeTests` ("number-too-large", line 120).
- **Probe:** `2/999999999999999999999999999999` → `0.000000000000000000000000000002000000000000000000000000000002000`; `1e7000` → parseFailure `NumberLiteralTooLarge @[1:1,1:7)`; 40-digit literal → rounded to 34 digits `1234567890123456789012345678901235000000`.
- **Topics:** OP, SYN
- **Lineage review (phase 2) corrections/addenda:**
  - [random-numerics] Lineage: range widened by #153 and #97 → Lineage: range widened by #153 only (classification unchanged). Evidence: Same evidence as #13: cadb441 kept System.Decimal literal parsing; Decimal128 parsing and the rounding of excess digits arrived only with 7f0bab0.

### #9 — Math.Tan abnormal results
- **Dates:** created 2026-03-09 · closed 2026-03-17 (NOT_PLANNED)
- **Problem / question:** `Math.Tan(Math.Pi/2)` gave `618986325617924`, `Math.Tan(Math.Pi)` a tiny nonzero.
- **Decision / intended invariant:** Won't fix: tan(π/2) is undefined; near a singularity KatLang returns a (large) finite approximation, not a special error; higher trig rigor is out of scope. (Side fix 9dff45e: high-precision `Pi`/`E` literals.)
- **Rationale:** numeric functions are approximations of a rounded argument.
- **Examples:** `Math.Tan(Math.Pi/2)`, `Math.Tan(Math.Pi)`.
- **Lineage:** followed by #11 (near-zero normalization — later removed); rationale replaced by #153 (Decimal128, 7f0bab0; "floating-point" no longer applies); related f9e4825 (asin/acos stability), numeric audit #6.
- **Classification:** CURRENT
- **Surviving part / superseded by:** the policy (finite approximation near a singularity, no domain error) survives and is pinned; the double-precision rationale and specific numbers are superseded by Decimal128 (tan(Pi/2) is now ≈ −1.79e33 because `Pi` rounds up at 34 digits).
- **Current evidence:** `EvaluatorMathTests.Eval_MathTan_NearSingularity_ReturnsLargeMagnitude` (EvaluatorMathTests.cs:192, asserts |value| > 1e30 and negative); tutorial.md:1979 (Math results computed to full precision, `pi` rounded to 34 digits).
- **Probe:** `Math.Tan(Math.Pi/2)` → `-1792431373312990339055441025239161`; `Math.Tan(Math.Pi)` → `1.158…e-34`.
- **Topics:** OP

### #10 — Remove self
- **Dates:** created 2026-03-12 · closed 2026-03-12
- **Problem / question:** `self` was a redundant feature.
- **Decision / intended invariant:** Remove `self` entirely (commit 890fcd4: `Expr.self`, token, EBNF production removed); lexical lookup covers its use; `self` is an ordinary identifier.
- **Rationale:** lexical lookup fully covers what `self` did; no zombie features.
- **Examples:** `self = 3` / `self + 1` → `4` (ordinary identifier today).
- **Lineage:** none later; consistent with the six-rule ownership-first lookup model.
- **Classification:** REMOVED
- **Surviving part / superseded by:** nothing of `self` survives; name-based recursion/lookup is the mechanism.
- **Current evidence:** keyword table `Lexer.cs:15-26` (div, mod, and, or, xor, not, public, open, true, false — no `self`); no `Self` in `src/KatLang/Ast*.cs` or `lean/KatLang.lean`; tutorial "Recursion" (tutorial.md:1611) uses the algorithm's own name.
- **Probe:** `self = 3` / `self + 1` → `4`; `F = self + 1` / `F(4)` → `5` (implicit parameter named `self`).
- **Topics:** RES, SYN

### #11 — Trigonometric functions lose precision due to Double conversion
- **Dates:** created 2026-03-17 · closed 2026-04-06
- **Problem / question:** Math functions ran through `System.Double` in a `decimal` language; `Math.Sin(Math.Pi)` = 1.22e-16. Should results be normalized / constants special-cased?
- **Decision / intended invariant (at the time):** normalize double-based Math results: round to 15 significant digits and snap |x| < 1e-15 to 0 (`NormalizeDoubleResult`, commit 10fbd40).
- **Rationale:** hide floating-point residue from users.
- **Examples:** `Math.Sin(Math.Pi)` → `0` (then).
- **Lineage:** follows #9; superseded by #153 (Decimal128 core numerics, 7f0bab0 deleted `NormalizeDoubleResult`).
- **Classification:** SUPERSEDED
- **Surviving part / superseded by:** superseded by #153: every Math function computes natively in Decimal128 (no double stage) and results are NEVER rounded to "nice" values; transcendental results are only quantum-canonicalized (value-preserving). `sin(pi)` is a ~1e-34 residue.
- **Current evidence:** `evaluator-and-hosting.md` § Numerics ("every Math function compute[s] in it natively … no `decimal` or `double` stage"; "Transcendental Math results are quantum-canonicalized"); tutorial.md:1979; tests `EvaluatorMathTests.Eval_MathSin_Pi_ReturnsTinyRoundingResidual` (:390), `…_ViaOpen_ReturnsTinyRoundingResidual` (:445); `git log -S NormalizeDoubleResult` → removed in 7f0bab0.
- **Probe:** `Math.Sin(Math.Pi)` → `-0.0000…01158028306006248941790250554076922` (≈ −1.16e-34); `Math.Cos(Math.Pi/2)` → ≈ −5.58e-34.
- **Topics:** OP, FORMAL

### #12 — Algorithm (accepting one or more parameters) call without arguments should result in error
- **Dates:** created 2026-03-23 · closed 2026-03-23
- **Problem / question:** `A = x` / `A` produced nothing and no error; the error had a null span.
- **Decision / intended invariant:** A bare reference to an algorithm that needs arguments, used as a value, is an arity error located at the reference (commit ebb4dab fixed the null span).
- **Rationale:** silent empty output hides a missing-argument bug.
- **Examples:** `A = x` / `A` → error at `A`.
- **Lineage:** generalized by the zero-argument value-demand law (SYN-05 builtin identity; "Zero-argument value demand follows actual call arity", September 2026 / F4): a callable satisfies a value demand iff an ordinary call with ZERO supplied arguments can bind it (so `Only(*xs) = xs` is a valid bare value); refined by #83 (no-output program is an error) and the span rules (one coordinate space; `SourceSpan?`).
- **Classification:** CURRENT
- **Surviving part / superseded by:** fully survives; the eligibility criterion is now "minimum supplied slots == 0", not "declared parameter list empty".
- **Current evidence:** `Evaluator.AcceptsZeroSuppliedArguments` (src/KatLang/Evaluator.cs:1219), `ZeroArgumentValueDemandRejection` (Evaluator.cs:1314); Lean `Algorithm.acceptsZeroSuppliedArguments` (KatLang.lean:2714), `zeroArgumentDemandError?` (:3576); tests `ZeroArgumentDemandArityTests`, `LazySlotZeroArgumentDemandTests`; spec `zero-argument-demand-follows-actual-call-arity` (LanguageSpecCorpus.cs:4946); `ownership-and-lookup.md` § Zero-argument value demand follows actual call arity.
- **Probe:** `A = x` / `A` → `ArityMismatch @[2:1,2:2): Property 'A' expects 1 parameter, but was called with 0 arguments. An implicit parameter 'x' was inferred at [1:5].`; `A(x) = x` / `A` → same; `A()` → `ArityMismatch @[2:1,2:4)`.
- **Topics:** CALL, PAR, PROP, TOOL

### #13 — Large Number should be able to be handled, for instance, in scientific notation, whatever
- **Dates:** created 2026-03-26 · closed 2026-03-26
- **Problem / question:** `2 * 10 ^ 30` (astronomy problem) overflowed `System.Decimal`.
- **Decision / intended invariant (at the time):** values beyond the decimal range are unsupported; surface a clear `EvalError.NumericOverflow` (commit 12e278a).
- **Rationale:** C# `decimal` has 28-29 digits.
- **Examples:** `sunHydrogen = sunMass * hydrogenFraction` / `sunHydrogen(2 * 10 ^ 30, 0.75)`.
- **Lineage:** superseded by #97 (scientific notation literals, cadb441) and #153 (Decimal128 core type, 7f0bab0, which removed `NumericOverflow`).
- **Classification:** SUPERSEDED
- **Surviving part / superseded by:** no overflow error remains: Decimal128 range ±~10^6144; arithmetic overflow produces a signed Infinity (IEEE ordinary value); only an unrepresentable LITERAL is a front-end `NumberLiteralTooLarge`.
- **Current evidence:** `evaluator-and-hosting.md` § Numerics ("overflow produces a signed infinity … NaN/±Infinity/−0 are ordinary values"); spec `overflow-produces-infinity` (LanguageSpecCorpus.cs:4100, C#-only with `LeanExclusionReason`); `git log -S NumericOverflow` → removed in 7f0bab0.
- **Probe:** `sunHydrogen(2 * 10 ^ 30, 0.75)` → `1500000000000000000000000000000.00`; full lifetime program → `9.732203969883641341546885694729637`; `2e30 * 0.75` → `1500000000000000000000000000000`; `10 ^ 7000` → `Infinity`.
- **Topics:** OP, SYN
- **Lineage review (phase 2) corrections/addenda:**
  - [random-numerics] Lineage: superseded by #97 (scientific notation, cadb441) and #153 → Lineage: superseded by #153 (7f0bab0) only; #97 is literal syntax and did not widen the range (classification SUPERSEDED unchanged). Evidence: cadb441 still parsed literals with decimal.TryParse(…, NumberStyles.Float, …) (git show cadb441 -- src/KatLang/Lexer.cs), so 2e30 stayed NumberLiteralTooLarge and 2*10^30 stayed NumericOverflow until 7f0bab0 deleted NumericOverflow (git log -S NumericOverflow).

### #14 — Dot-call syntax is not working on constants
- **Dates:** created 2026-03-30 · closed 2026-03-30
- **Problem / question:** `A = 5` / `A.Square` worked, `5.Square` did not.
- **Decision / intended invariant:** Extension (dot) calls apply to ANY value-producing receiver: `5.Square` ≡ `Square(5)`, `(2 + 3).Square` ≡ `Square(5)` (commit d901280; Lean `dotCall` already accepted any `Expr` receiver — C#-only gap).
- **Rationale:** uniform `receiver.F(args) = F(receiver, args)`.
- **Examples:** `Square = n * n` / `5.Square` → `25`.
- **Lineage:** generalized by #74, #89/#105/#112/#144 (receiver binding), #147 (fallback reuses ordinary callable resolution), #162 (structural member first), "dot-call passes a value" (Sep 21 2026: `R.F(args)` is exactly `F(R, args)`), G-24.
- **Classification:** CURRENT
- **Surviving part / superseded by:** survives; now within the three dot classes (structural member first, `.string` intrinsic, extension fallback), fallback composing along chains (`3.A.B` = `B(A(3))`).
- **Current evidence:** Lean `prepareLexicalDotCallArgs` (KatLang.lean:4337), `resolveDotReceiver` (:4724), `callLexicalWithReceiverCounted` (:6359); C# `Evaluator.DotCalls.cs:51` `BuildLexicalReceiverCallArgs`, `:368` `ResolveDotReceiver`; spec `dot-chain-extension-fallback-composes` (LanguageSpecCorpus.cs:2181, probe `Q(x) = x + 1` / `3.Q` → 4), `dot-receiver-passes-a-value` (:1220); tests `DotCallValueBoundaryTests`, `ChainedDotStructuralPrecedenceTests`.
- **Probe:** `Square = n * n` / `5.Square` / `(2 + 3).Square` / `A = 5` / `A.Square` → `25, 25, 25`.
- **Topics:** DOT, CALL

### #15 — Two argument form builtin if
- **Dates:** created 2026-03-30 · closed 2026-03-30
- **Problem / question:** support `if(condition, value)` that yields nothing when false (so `10 + if(1 == 2, 5)` = 10 via an operator ignoring a missing operand)?
- **Decision / intended invariant (at the time):** implemented (commit 5a6c550, Lean + C#).
- **Rationale:** shorter loop examples.
- **Examples:** `10 + if(1 == 1, 5)` → 15, `10 + if(1 == 2, 5)` → 10 (then).
- **Lineage:** removed by #49 (93a036d, "remove 2-argument if and standardize builtin if to arity 3"); its enabling behaviour (empty as operator identity) removed by SYN-01 (a8bcae7, Sep 10 2026); reaffirmed by #159 (if resolved by identity, not spelling/arity); conditions made Boolean by #165.
- **Classification:** REMOVED
- **Surviving part / superseded by:** nothing survives: `if` has exactly one signature `if(condition, whenTrue, whenFalse)`; wrong count is an evaluation-time `ArityMismatch`; `()` is not an operator identity (`10 + ()` is `TypeMismatch`).
- **Current evidence:** Lean `builtinAcceptsArity` `.ifBuiltin, 3 => true` (KatLang.lean:596); spec `if-arity-is-uniform-across-spellings` (LanguageSpecCorpus.cs:4802, source `if(true, 2)` → arity error); #49 rationale (predictability; no builtin overloads; empty result inside an expression was a leaky abstraction).
- **Probe:** `10 + if(1 == 1, 5)` → `ArityMismatch: Callable if(condition, whenTrue, whenFalse) expects 3 arguments, but was called with 2`; `10 + ()` → `TypeMismatch`.
- **Topics:** BOOL, CALL, VAL

### #16 — Implement conditional algorithms feature.
- **Dates:** created 2026-04-02 · closed 2026-04-02
- **Problem / question:** v0.6 had conditional parameters and a parameter-ignorance operator `#`; v0.8 needed a pattern-matching alternative able to express the K combinator (accept a parameter without using it).
- **Decision / intended invariant:** Conditional algorithms = ordered branches with patterns (bind, integer literal, group) tried top to bottom (commit d7b0f6c, `when` syntax); a singleton group pattern `(b)` matches a single (normalized) value but not a pair `(2, 3)`. No ignorance operator.
- **Rationale:** pattern matching instead of switch-like conditional parameters.
- **Examples (original):** `F when (0) = …`. Current equivalent: `F(0) = 10` / `F(1) = 20` / `F(n) = n * 2`; K combinator `K(x, y) = x`.
- **Lineage:** refined by #19, #20 (string patterns), #21/#23 (closed branch inputs), #22, #24/#25 (uniform pattern/output arity); syntax replaced by #26 (d194100, clause shorthand) and #27 (dc5b9ad, `when` removed); refined by #39, #70, #99, #121 (repeated binders), #165 (Boolean patterns); `#` became the comment marker (#142).
- **Classification:** PARTIALLY CURRENT *(revised in lineage review; ledger batch said CURRENT)*
- **Surviving part / superseded by:** the feature and ordered first-match semantics survive; the `when` keyword was replaced by clause syntax (#26/#27); single-clause binder forms elaborate to ordinary `Algorithm.User`.
- **Current evidence:** Lean `inductive Pattern` (KatLang.lean:672), `CondBranch` (:980), `elaborateClauseGroup` (:1851), `matchCallBranches` (:3726); tutorial "Pattern Matching" (tutorial.md:1587-1724); spec `conditional-singleton-head-binds-its-argument-whole`, `conditional-sequence-pattern-matches-sequence-values-only`; `EvaluatorConditionalTests`, `ClauseGroupElaborationTests`.
- **Probe:** clause family `F(0)=10 / F(1)=20 / F(n)=n*2` → `10, 20, 14`; `K(x, y) = x` / `K(1, 2)` → `1`; `F(0) = 0` / `F((b)) = b` / `F((2, 3))` → `NoMatchingBranch` (matches the original singleton rule); `F when (0) = 10` → parseFailure `UnseparatedSameLineItem` (`when` is no longer syntax).
- **Topics:** PAT, CALL, PAR
- **Lineage review (phase 2) corrections/addenda:**
  - [conditional-patterns] CURRENT → PARTIALLY CURRENT. Evidence: The delivered `when` branch syntax (d7b0f6c 'Parser: parse when branches') was removed by #27 (dc5b9ad; probe `F when (1) = 100` -> parseFailure UnseparatedSameLineItem), and the delivered call-matching mechanism (matching the normalized shape of ALL arguments, `Result.normalize (Result.group argResults)`) was replaced by #70 (fe1e3fb diff adds matchCallPattern/matchCallBranches over explicit argument slots). Only ordered first-match and the singleton (b) adaptation (patternSequenceValueMembers?) survive.

### #17 — Think how to simplify KatLang code execution from C#
- **Classification:** HOST/API ONLY — introduced the `KatLangEngine` façade and closed `RunResult` union (commit a771142); today `KatLangEngine.Run`/`RunAsync`/`EvaluateToAtoms` (src/KatLang/KatLangEngine.cs:422, 518, 685), layered public surface pinned by `PublicApiBaselineTests`.
- **Topics:** API

### #18 — Non-public algorithms cannot be opened
- **Dates:** created 2026-04-02 · closed 2026-04-02
- **Problem / question:** `Lib = ( public Pi = 3.14159 )` / `open Lib` failed unless `Lib` itself was public.
- **Decision / intended invariant:** `open` may target any algorithm visible in the current context (the target need not be public); `open` imports only the target's PUBLIC members (commit a362ba3).
- **Rationale:** `Lib` is visible as part of the parent's own structure.
- **Examples:** current equivalent: `open Lib` / `Lib = {` / `    public Pi = 3.14159` / `}` / `Pi` → `3.14159` (open must now be first; bodies use braces).
- **Lineage:** refined by K1-08 (selection never depends on exposure; one accessibility check), audit #8 (static open-target validity: every target must resolve, dotted steps must be public), SYN-03 (a parameter head is `OpenTargetIsParameter`), #93.
- **Classification:** CURRENT
- **Surviving part / superseded by:** survives; additionally dotted open steps must be public (`NotPublicProperty`), and structural `Lib.Pi` (non-open) selects declared members including private ones.
- **Current evidence:** `ownership-and-lookup.md` § Open, exposure, and accessibility (K1-08) ("`open Name` may target a lexically visible private head, but open-provided names and dotted open steps select PUBLIC members"); tests `EvaluatorOpenVisibilityTests.Eval_Open_LocalNonPublicAlgorithm_CanBeOpened` (:879), `Eval_Open_NonPublicMember_NotImported` (:909), `Eval_Open_PrivateMemberRemainsHidden` (:273).
- **Probe:** private `Lib`, public `Pi`, `open Lib` → `3.14159`; private `Pi` → `UnresolvedImplicitParams` ("Did you mean 'pi'?"); `Lib.Pi` with private `Pi` → `3.14159`.
- **Topics:** MOD, RES
- **Lineage review (phase 2) corrections/addenda:**
  - [open-ownership-modules] CURRENT → CURRENT (add Lean lag). Evidence: The C# fix a362ba3 (2026-04-02) preceded Lean alignment d80208b (2026-04-15, 'Lean: allow private lexical heads in open resolution', which deletes lookupLexicalDirectUnwiredPublic). Lean and C# diverged for 13 days; dotted open steps stayed public-only throughout.

### #19 — Property is not seen when used inside conditional algorithm body
- **Dates:** created 2026-04-04 · closed 2026-04-04
- **Problem / question:** a conditional branch body could not see sibling properties (`Unknown name: ApplePrice`).
- **Decision / intended invariant:** a selected branch body is lexically nested in its family's owner: it is wired to the callee scope exactly like an ordinary property body, so sibling/ancestor properties resolve (commit fa8500f fixed Lean and C# together).
- **Rationale:** branches are ordinary lexical children.
- **Examples:** `Expense when (2, qty) = ApplePrice * qty`; current equivalent `Expense(2, qty) = ApplePrice * qty` / `Expense(2, 3)` → `2.40`.
- **Lineage:** reaffirmed by ownership-first lookup (owner walk); related #54 (conditional nested properties local-only).
- **Classification:** BUG FIX / REAFFIRMED EXISTING RULE
- **Surviving part / superseded by:** survives.
- **Current evidence:** Lean `wireSelectedBranchBody` (KatLang.lean:2346) used in `evalConditionalCallCounted` (:6284ff), `Algorithm.childOf` (:1919); tests `EvaluatorConditionalTests.Eval_Conditional_BranchBody_AccessesSiblingProperty` (:454), `_AllBranches` (:468), `_AccessesGrandparentProperty` (:484), `_BinderAndSiblingCombined` (:503).
- **Probe:** i19 (clause syntax) → `2.40`.
- **Topics:** PAT, RES

### #20 — Consider supporting string literals in conditional algorithm pattern matching and in algorithm calls
- **Dates:** created 2026-04-04 · closed 2026-04-06
- **Problem / question:** allow `'text'` literals as patterns and as call arguments.
- **Decision / intended invariant:** single-quoted strings are first-class values: passable, returnable, `==`/`!=` exact case-sensitive, arithmetic on strings is an error, string-literal patterns match by exact value (commit 9408e73: `Result.str`, `Pattern.litString`).
- **Rationale:** readable categorical keys (`'apples'`) instead of numeric codes.
- **Examples:** `Price('apples') = 0.80` / `Expense = Price(item) * quantity` / `Expense('apples', 3)` → `2.40`.
- **Lineage:** refined by #31 (type-mismatch messages), #32 (number→string, `.string` intrinsic), open #36 (string operations); structural equality #127; Boolean literal patterns (#165) follow the same shape.
- **Classification:** CURRENT
- **Surviving part / superseded by:** survives; no ordering/coercion of strings.
- **Current evidence:** Lean `Result.str` (KatLang.lean:1144, "exact equality, no ordering/coercion"), `Expr.stringLiteral` (:824), `Pattern.litString` (:675); tutorial "Matching Text" (tutorial.md:1635); spec `string-equality-exact` (LanguageSpecCorpus.cs:3645), `string-displays-unquoted` (:3660); `KatLang.ebnf` PatternAtom includes StringLiteral.
- **Probe:** the issue's program (i20) verbatim → `2.40`.
- **Topics:** VAL, PAT, CALL

### #21 — In conditional algorithm branch - all parameters should be declared in when (...) braces and Grace~ operator should be forbidden
- **Dates:** created 2026-04-05 · closed 2026-04-05
- **Problem / question:** branch bodies could infer implicit parameters and reorder them with Grace.
- **Decision / intended invariant:** a branch pattern is the COMPLETE input specification of its branch: branch bodies infer no implicit parameters (free names must resolve lexically, otherwise they are errors), and Grace `~` is rejected in branch patterns and bodies (commit 6dbcc0c).
- **Rationale:** a family's call interface must be explicit and consistent.
- **Examples (original):** `Expense when (2, a, qty) = ~a * qty`. Current equivalent: `Expense(2, qty) = ~a * qty` → `InvalidGraceMarker` + `UndeclaredIdentifier`.
- **Lineage:** enforced statically by #23; syntax replaced by #26/#27; generalized by 6c64e66 (2026-05-08: every EXPLICIT parameter list is closed) and F10 (Grace must be effective: Grace under a closed explicit list is `InvalidGraceMarker`).
- **Classification:** CURRENT
- **Surviving part / superseded by:** survives with `when` replaced by clause heads; now a special case of "explicit parameter lists are closed".
- **Current evidence:** `ParameterDetector.cs:1644-1665` (`CreateConditionalBranchUndeclaredIdentifierDiagnostic`, `FormatExplicitParameterUndeclaredIdentifier`: "Explicit parameter lists are closed"); `Parser.cs:1563-1572` ("Grace is not allowed in conditional branch bodies"); tests `ParserTests.Parse_ClauseHead_PrefixGraceInPattern_ReportsError` (:5481) … `Parse_Conditional_GraceInNestedBodyExpr_ReportsError` (:5523), `EvaluatorConditionalTests.Eval_Conditional_ExtraImplicitParam_Rejected` (:551), `Eval_Conditional_FreeIdResolvedLexically_Succeeds` (:574); `GraceEffectivenessTests`.
- **Probe:** i22 → `InvalidGraceMarker @[6:19,6:21)` + `UndeclaredIdentifier @[6:20,6:21)`; `F(x) = x + y` / `F(1)` → `UndeclaredIdentifier` ("Explicit parameter lists are closed"); `F(x) = ~y + x` → `UndeclaredIdentifier` + `InvalidGraceMarker`.
- **Topics:** PAT, PAR, SYN

### #22 — Wrong Grace~ error location
- **Classification:** BUG FIX / REAFFIRMED EXISTING RULE — diagnostic span fix: the Grace-in-branch error was reported one line late; now located from the AST (`FindGraceSpan`, commit 01ffdd4); pinned by `ParserTests.Parse_Conditional_GraceInBody_ErrorSpanPointsToGraceLine` (ParserTests.cs:5531); probe i22 reports line 6 (the graced line).
- **Topics:** TOOL, PAT

### #23 — Pattern matching checks if all parameters are explicit only for branches which are used in calls
- **Dates:** created 2026-04-05 · closed 2026-04-05
- **Problem / question:** an undeclared identifier in an UNUSED branch went unnoticed because the check happened only on the evaluated branch.
- **Decision / intended invariant:** the closed-branch-input rule (#21) is a compile-time (front-end) check over EVERY branch, independent of which branches a run selects (commit f647dac: `ParameterDetector` reports free identifiers).
- **Rationale:** a latent error must not depend on call values.
- **Examples:** `Expense when (1, qty) = a * qty` / `Expense when (2, a, qty) = a * qty` / `Expense(2, 0.80, 3)`. Current equivalent: `Expense(1, qty) = a * qty` / `Expense(2, qty) = ApplePrice * qty` / `Expense(2, 3)` → front-end error (arity-uniform translation needed after #24).
- **Lineage:** refines #21; reaffirmed by "every front-end error blocks source-based evaluator entry".
- **Classification:** CURRENT
- **Surviving part / superseded by:** survives.
- **Current evidence:** `ParameterDetector.cs:1640-1658` (per-region `UndeclaredNames` → `DiagnosticCode.UndeclaredIdentifier`); `KatLangEngineTests.Run_ConditionalBranch_FreeIdentifier_ReturnsParseFailure` (:1285); `EvaluatorConditionalTests.Eval_Conditional_ExtraImplicitParam_Rejected` (uses `SourceProvenance.ExpectFrontEndError`); AGENTS Editor Semantics "Every front-end error blocks source-based evaluator entry".
- **Probe:** i23 → parseFailure `UndeclaredIdentifier @[4:19,4:20)` although only branch 2 is called.
- **Topics:** PAT, PAR

### #24 — All branches of the same conditional algorithm must have the same top-level pattern arity
- **Dates:** created 2026-04-05 · closed 2026-04-05
- **Problem / question:** branches with different parameter counts (`(1, qty)` vs `(2, a, qty)`) silently worked and could fail when call values changed.
- **Decision / intended invariant:** all branches of one conditional algorithm share one top-level pattern arity (nested structure may vary); violation is a pre-evaluation error (commit b034c4b: `Pattern.topLevelArity`, `Error.branchArityMismatch`, `validateBranchArities`). Arity never distinguishes branches.
- **Rationale:** one consistent outer call interface.
- **Examples:** current equivalent: `Expense(1, qty) = TomatoPrice * qty` / `Expense(2, a, qty) = a * qty` → `BranchArityMismatch`.
- **Lineage:** extended by #25 (uniform top-level OUTPUT arity, a68c51f); syntax changed by #26/#27; related #39, #70.
- **Classification:** CURRENT
- **Surviving part / superseded by:** survives.
- **Current evidence:** Lean `Pattern.topLevelArity` (KatLang.lean:698), `Algorithm.validateBranchArities` (:1932), `Error.branchArityMismatch` (:335); `Parser.cs:1594` (`DiagnosticCode.BranchArityMismatch`); spec `conditional-clauses-share-top-level-arity` and `conditional-clauses-share-top-level-output-arity` (LanguageSpecCorpus.cs:1702, :1719); `ConditionalBranchArityValidationTests`; `ParserTests.Parse_Conditional_SameArity_NestedStructureDiffers_Valid`; tutorial "Rules for Clauses" (tutorial.md:1698).
- **Probe:** i24 → `BranchArityMismatch @[5:1,5:29): … Expected 2 (from first branch), but branch 2 has arity 3`; `F((a, b), c) = a + b + c` / `F(x, y) = x * y` → `F((1, 2), 3)` = 6, `F(2, 3)` = 6 (nested structure may differ).
- **Topics:** PAT, CALL

### #25 — Restrict conditional algorithm all branches to have the same top level output shape
- **Dates:** created 2026-04-05 · closed 2026-04-05
- **Problem / question:** A clause family whose branches emit different numbers of top-level outputs makes the result shape depend on which branch matched (`Expense … = TomatoPrice * qty, 2` vs `… = ApplePrice * qty`).
- **Decision / intended invariant:** All branches of one conditional algorithm must have the same TOP-LEVEL OUTPUT ARITY (number of written top-level output slots); nested structure inside a slot may differ. Violations are a static error (front end at clause elaboration; Lean pre-evaluation validation).
- **Rationale:** "one algorithm, one output interface"; predictable result shape.
- **Examples:** original `Expense when (1, qty) = TomatoPrice * qty, 2` / `Expense when (2, qty) = ApplePrice * qty` → error. Current equivalent: `Expense(1, qty) = TomatoPrice * qty, 2` / `Expense(2, qty) = ApplePrice * qty`. A pair is legal as ONE captured slot: `F(0) = 1` / `F(x) = (1, 2)`.
- **Lineage:** companion of #24 (same top-level PATTERN arity; same day); refines #16 (conditional algorithms). Syntax of the example replaced by #26/#27. Later #132 (property/call boundary returns one sequence value) did NOT remove the check; #168 (redundant parentheses) keeps `(1, 2)` a one-slot capture, so the "write the pair as one captured slot" advice is still valid.
- **Classification:** CURRENT
- **Surviving part / superseded by:** whole rule survives unchanged.
- **Current evidence.** Lean's `Algorithm.validateBranchOutputArities` compares the lengths of the branch output lists, and `validateConditionalBranchArities` raises `Error.branchOutputArityMismatch`. C#'s `CondBranch.TopLevelOutputArity()` reads `Body.Output.Count`. The parser reports `DiagnosticCode.BranchOutputArityMismatch` at the disagreeing clause. The tracked conformance case `conditional-clauses-share-top-level-output-arity` and the Lean and C# validation tests pin the rejection. [Lean model](../../lean/KatLang.lean) · [C# AST](../../dotnet/src/KatLang/Ast.cs) · [Parser](../../dotnet/src/KatLang/Parser.cs) · [Clause dispatch cases](../../conformance/features/clause-dispatch.json) · [ConditionalBranchArityValidationTests](../../dotnet/tests/KatLang.Tests/ConditionalBranchArityValidationTests.cs) · [Lean conditional guards](../../lean/CoreTests/Conditionals.lean)
- **Probe:** `TomatoPrice = 1.20 / ApplePrice = 0.80 / Expense(1, qty) = TomatoPrice * qty, 2 / Expense(2, qty) = ApplePrice * qty / Expense(1, 3)` → `parseFailure BranchOutputArityMismatch`. `F(0) = 1 / F(x) = (1, 2) / F(5) / F(0)` → `ok S[S[1, 2], 1] n=2`.
- **Topics:** PAT, SEQ
- **Lineage review (phase 2) corrections/addenda:**
  - [conditional-patterns] CURRENT (rationale: unpredictable output shape) → CURRENT (rule enforced; rationale obsolete at runtime since #132). Evidence: #132 (9a4c70f) made the conditional call result a value boundary (reCountValueBoundary added to evalConditionalCallCounted), so a multi-row branch is one value to its caller; the check now only rejects written rows (`F(x) = 1, 2` rejected, `F(x) = (1, 2)` accepted, probes p07 and spec probe). Classification unchanged; ledger should note the rationale gap.
  - [Q-48, owner decision 2026-11-28] CURRENT (rule enforced; rationale obsolete at runtime since #132) → CURRENT (rule kept by owner decision; the rationale is structural). The rationale recorded above, "one algorithm, one output interface", stands. The decision retains the rule because the declared outer layout is part of the algorithm's structure: `F((x, y))` and `F(z)` both declare one input slot, and `(1, 2)` and `0` each occupy one written output slot. An omitted row can be diagnosed at the declaration, while runtime result kinds and the number of items a value contains may vary. The brief also records that the owner originally chose the restriction for symmetry with input parameters and to help authors present a consistent interface. #132 made an ORDINARY call result one value, so an ordinary caller does not see how many rows the selected clause wrote. A family used as a loop step supplies its selected clause's rows directly. `while` reads its flag first, and `repeat` takes the supplied items as its next state. For example, `Countdown(0) = 0, false` / `Countdown(n) = n - 1, true` / `Countdown(3).while` gives `0`, and `Two(0) = 9, 9` / `Two(n) = n, n` / `repeat(Two(1), 2)` is `ArityMismatch`. Evidence: Lean `Algorithm.validateBranchOutputArities`; C# `CondBranch.TopLevelOutputArity()`, the parser's clause-family check and the pre-evaluation walker; `ConditionalBranchArityValidationTests`; conformance `conditional-clauses-share-top-level-output-arity`, `loop-step-family-while` and `loop-step-clause-family`. Classification unchanged. `constitution.md` PAT-03, `open-questions.md` Q-48, `decision-lineages.md` § Q-48.

### #26 — Add support for conditional algorithm syntax without keyword 'when'
- **Dates:** created 2026-04-05 · closed 2026-04-05
- **Problem / question:** `F when (1) = 100` is verbose; proposal: equational sugar `F(1) = 100`, call syntax unchanged.
- **Decision / intended invariant:** A clause is written `Name(pattern) = body`; several same-name clauses form one conditional algorithm (clause family) tried top-to-bottom; calls are ordinary `F(1)`.
- **Rationale:** shorter, mathematical, equational definitions.
- **Examples:** `F(1) = 100` / `F(x) = 0` / `F(1)` → 100, `F(999)` → 0.
- **Lineage:** replaces syntax of #16 (`when` form) as an alternative; immediately refined by #27 (same day) which made it the ONLY form. Later generalized by the clause elaboration rule introduced with #39 (a single flat clause is an ordinary explicit-parameter algorithm), then sequence-value/collecting heads (Lean docstring `KatLang.lean:1040-1042`; related #99, #138) and #121 (repeated-name constraints).
- **Classification:** CURRENT
- **Surviving part / superseded by:** the clause syntax survives as the canonical (only) form; its original status as "sugar next to `when`" ended with #27.
- **Current evidence:** `KatLang.ebnf:135` `ClauseDefinition = [ "public" ] Identifier "(" Pattern ")" "=" OutputBundle`; Lean `Algorithm.elaborateClauseGroup` (`KatLang.lean:1851`), clause elaboration rule docstring (`:1035-1048`); C# `Ast.cs:1735` `ElaborateClauseGroup`; tests `ClauseGroupElaborationTests`, `EvaluatorConditionalTests`; tutorial § Clauses (`tutorial.md:1589`). Commit d194100.
- **Probe:** `F(1) = 100 / F(x) = 0 / F(1) / F(999)` → `ok S[100, 0] n=2`.
- **Topics:** PAT, SYN

### #27 — Remove keyword 'when' from conditional algorithm definition syntax
- **Dates:** created 2026-04-05 · closed 2026-04-05
- **Problem / question:** Keep two spellings of clause definitions or only the equational one?
- **Decision / intended invariant:** `when` is removed; clause style `F(1) = 100` is the only conditional-branch syntax and `when` is an ordinary identifier.
- **Rationale:** shorter, more elegant, more mathematical, better fit for nested patterns, one less keyword, clauses feel like equational definitions.
- **Examples:** `F(1) = 100` / `F(x) = 0` (valid); `F when (1) = 100` (no longer syntax).
- **Lineage:** removes the `when` syntax of #16/#21; refines #26. Consistent with later keyword-minimal decisions (#5/#63 explicit `Output` removal, #142 comments). Prediction "better fit for future nested patterns" realized by sequence-value patterns (#99 etc.).
- **Classification:** CURRENT
- **Surviving part / superseded by:** all.
- **Current evidence:** `src/KatLang/Lexer.cs:15-26` `KeywordDefinitions` = `div mod and or xor not public open true false` (no `when`); EBNF keyword/identifier claims checked by `EbnfLexicalSyncTests`; `KatLang.ebnf:135`. Commit dc5b9ad (removes `TokenKind.KeywordWhen`).
- **Probe:** `F when (1) = 100 / F when (x) = 0 / F(1)` → `parseFailure UnseparatedSameLineItem,UnseparatedSameLineItem` (now just juxtaposed names); `when = 5 / when + 1` → `ok 6`.
- **Topics:** SYN, PAT

### #28 — Error is not detected in the inner call
- **Classification:** BUG FIX / REAFFIRMED EXISTING RULE — error span of a failing nested call (`Inner(param)` inside `Outer`) must stay at the inner call site, not be overwritten by the outer call; today this is the attach-if-missing law (`Evaluator.AtSpanIfMissing`, `Evaluator.cs:1089`; `evaluator-and-hosting.md` § Explicit value-type source locations). Probe `Inner = 5 / Outer = param - Inner(param) / Outer(50000)` → `ArityMismatch @[2:17, 2:29): while evaluating call to Outer: Callable 'Inner' expects 0 arguments, but was called with 1 argument.` (fix commit 66dc3cd).
- **Topics:** TOOL, RUN

### #29 — Property redefinition is ignored, but should cause error
- **Dates:** created 2026-04-05 · closed 2026-04-06
- **Problem / question:** `A = 5` / `A = 6` silently kept the first definition; a duplicate clause/branch was silently ignored.
- **Decision / intended invariant:** Properties are immutable, each name is bound once per algorithm: a second definition of the same property name (any mix of property/clause forms) is an error `Property 'X' is already defined`; two match-equivalent branch patterns in one clause family (e.g. `F(x)` and `F(y)`, `F(0)` twice) are a `DuplicateBranchPattern` error. Checked by the front end (with spans) AND by the core evaluator for host-built ASTs.
- **Rationale:** immutability; silent shadowing hides errors; duplicate patterns are unreachable under first-match.
- **Examples:** `A = 5` / `A = 6` → error; `B = x + 1` / `B = x + 2` → error; `F(x) = 1` / `F(y) = 2` → error.
- **Lineage:** reaffirms immutable-binding model; related to #23/#24 (static clause-family checks). Later refined by the owner-walk collision rules (parameter/property collisions `ParameterPropertyCollisionValidator`, SYN-03) and #121 (repeated names inside ONE pattern are equality constraints, not duplicates — a different mechanism).
- **Classification:** CURRENT
- **Surviving part / superseded by:** all; message unified by 59b0250, runtime enforcement by fe613f6.
- **Current evidence:** Lean `Error.duplicateProperty` / `Error.duplicateBranchPattern` (`KatLang.lean:337-338`), `Algorithm.findDuplicatePropName` (`:1980`), `Algorithm.hasDuplicateBranchPatterns` (`:1994`, uses `Pattern.isMatchEquivalent`), runtime checks at `:5179`, `:5251`, `:5436`, `:6078`, `:6289`. Tests `ClauseGroupElaborationTests`, `EvaluatorDefensiveBranchTests`, `ParserTests`, `KatLangErrorCodeTests`. Tutorial § Names Are Bound Once (`tutorial.md:274-282`) and § Rules for Clauses (`:1722`). No `LanguageSpecCorpus` case pins duplicates (gap, not a contradiction).
- **Probe:** `A = 5 / A = 6 / A` → `parseFailure DuplicateProperty @[2:1,2:2)`; `B = x + 1 / B = x + 2 / B(1)` → `DuplicateProperty`; `F(x) = 1 / F(y) = 2 / F(3)` → `DuplicateBranchPattern`; `F(0) = 1 / F(0) = 2` → `DuplicateBranchPattern`; `A = 5 / A(x) = 6` → `DuplicateProperty`.
- **Topics:** PROP, PAT, RES

### #31 — Improve type mismatch error messages
- **Dates:** created 2026-04-06 · closed 2026-04-06
- **Problem / question:** String/number misuse reported `Bad arity` / `Arity mismatch`; `Sin('a')` reported an arity mismatch.
- **Decision / intended invariant:** Value-kind misuse is a distinct `typeMismatch` error kind (Lean + C#): string operands with arithmetic, unary on string, numeric extraction from a string (incl. Math arguments). A root program whose output depends on an unresolved implicit parameter reports `unresolvedImplicitParams` (commit c7d15fd), since `Sin` is not `Math.Sin` and becomes an implicit parameter.
- **Rationale:** errors must describe the actual problem in KatLang terms.
- **Examples:** `'apples' * 3` → TypeMismatch; `Math.Sin('a')` → TypeMismatch; `A = 'x'` / `B = 10` / `A == B` → (then) TypeMismatch; `Sin('a')` → unresolved implicit parameter.
- **Lineage:** successor #127 (structural equality: "different value kinds ⇒ false, not a type mismatch") REVERSES the `==` part; #165 (Booleans) reaffirms total equality (`true == 1` is `false`); #44/#68 further diagnostics work; #154 adds `sin` alias (now suggested by the unresolved-name diagnostic).
- **Classification:** PARTIALLY CURRENT
- **Surviving part / superseded by:** Survives: `typeMismatch` as the error kind for string arithmetic/ordering/unary and for numeric extraction from strings (`expectInt`); `unresolvedImplicitParams` for the root. Superseded: `'x' == 10` is no longer an error — equality is total structural equality returning `false` across kinds (#127, commit bc383c3; reaffirmed #165).
- **Current evidence:** Lean `expectInt` (`KatLang.lean:2373-2379`: string → `typeMismatch "Expected a number, got a string"`, Boolean → typeMismatch); spec `string-equality-exact` (`LanguageSpecCorpus.cs:3645`), `boolean-values-and-equality` (`:116`, `true == 1` → false), `unresolved-implicit-parameter` (`:3634`); commits 1d1526c, c7d15fd.
- **Probe:** `A = 'x' / B = 10 / A == B` → `ok false`; `'apples' * 3` → `TypeMismatch: Cannot apply operator to string and non-string operands`; `'a' + 'b'` / `'a' < 'b'` → `TypeMismatch: Strings only support == and != operators`; `-'x'` → TypeMismatch; `Math.Sin('a')` / `sin('a')` → `TypeMismatch: Expected a number, got a string`; `Sin('a')` → `UnresolvedImplicitParams … Did you mean 'sin'?`.
- **Topics:** OP, CMP, TOOL

### #32 — Consider implementing builtin support for number to string conversions
- **Dates:** created 2026-04-06 · closed 2026-04-06
- **Problem / question:** No way to turn a number into a first-class string.
- **Decision / intended invariant:** `x.string` is a builtin value INTRINSIC on dot syntax: evaluates the receiver and converts an atomic numeric value to its canonical string; any other value (sequence, list, string, Boolean) is `typeMismatch`.
- **Rationale:** strings are first-class values; conversion expressed with dot syntax.
- **Examples:** `123.string` → `'123'`.
- **Lineage:** related open #36 (strings). Refined by: Decimal128 migration #153 (number text owned by KatLang, quantum kept: `1.20.string` is `'1.20'`); `.string` receiver made a zero-argument value demand and routed through the property cache (#170, commit ebf623e; SYN-05 lazy-slot work); arguments to `.string` rejected (`dot-string-intrinsic-rejects-arguments`). Dot-resolution classes (structural member / intrinsic / extension fallback) formalized later (#147, #162, dot-call-passes-a-value).
- **Classification:** CURRENT
- **Surviving part / superseded by:** all; mechanism refined (value demand, cache transparency).
- **Current evidence:** Lean `resultToString` (`KatLang.lean:2363-2366`), `evalDotCallCounted` checks `name = "string"` BEFORE structural lookup (`:6467-6476`), `evalDotStringReceiverValue` (`:6404`); C# `Evaluator.ResultToString` (`Evaluator.cs:2091`, `ValueTextRenderer.FormatNumberInvariant`), `EvalDotStringReceiverAlgOutput` (`Evaluator.Builtins.cs:2022`) + async mirror; spec `dot-string-receiver-is-a-zero-argument-value-demand` (`:4929`), `dot-string-intrinsic-rejects-arguments` (`:5022`); tutorial § Converting a Number to Text (`tutorial.md:675`). Commit 6869338.
- **Probe:** `123.string` → `'123'`; `1.5.string` → `'1.5'`; `1.20.string` → `'1.20'`; `(-0).string` → `'-0'`; `(1, 2).string`, `[1, 2].string`, `true.string`, `'ab'.string` → `TypeMismatch: builtin property 'string' expects a numeric receiver`; `string(x) = x + 1 / 3.string / string(3)` → `S['3', 4]` (intrinsic beats a lexical `string`); file `dotstring.kat`: `A = { string = 7 ⏎ 5 }` / `A.string` → `'5'` (intrinsic beats even a declared structural member named `string`).
- **Observation:** AGENTS.md's "structural lookup first" wording for dot-call has this deliberate exception: `.string` is dispatched before structural members (Lean `:6472`). AGENTS lists `.string` as its own class, so not a contradiction, but the precedence is only visible in Lean/code.
- **Topics:** DOT, VAL, OP

### #34 — Add aggregation builtins over outputs: sum, min, max, avg, count
- **Dates:** created 2026-04-06 · closed 2026-04-09
- **Problem / question:** Aggregations needed hand-written `repeat`/`while`; how should `(1, 2, 3).sum` vs `sum((1, 2, 3))` work?
- **Decision / intended invariant:** Prelude builtins `sum`, `min`, `max`, `avg`, `count`, each taking ONE collection argument, usable as `sum(collection)` or `collection.sum`. At introduction (cccffea): top-level numeric elements, grouped elements not flattened, empty `sum` is 0, a single number is a one-element collection.
- **Rationale:** reduce boilerplate for humans and generated code.
- **Examples:** `(1, 2, 3).sum`, `sum((1, 2, 3))`, `range(1, 10).filter(IsEven).sum`.
- **Lineage:** #57 temporarily added the variadic spelling `order(3, 4, 2, …)` "in all builtins requiring list"; #56/#58/#59/#69/#71/#72/#76/#88 reworked counting/argument boundaries; #135 (commit 0ca55e9) REVERSES #57 and restores #34's shape: ONE fixed `collection` parameter, nothing opened before binding, exact-list results; #147 (dot-call fallback reuses ordinary callable resolution) and the 2026-09-21 "dot-call passes a value" rule (AGENTS.md; no issue number found) keep `A.sum ≡ sum(A)`; #170 makes `sum(A)`/`A.sum` read the property cache; numeric audit #6 made `avg` the correctly rounded exact mean; `min`/`max` IEEE signed-zero rule (C#-only).
- **Classification:** CURRENT
- **Surviving part / superseded by:** the builtin set, one-collection-argument convention, both call styles, empty-sum 0, scalar = one-element collection, no recursive flattening all survive; the intervening variadic form (#57) is gone.
- **Current evidence:** `sequences-lists-and-calls.md` § Collection builtins (line 49; `count(7)` is 1, `sum(A*, B*)` arity error, re-group `sum((A*, B*))`); Lean `preludeAlg` (`KatLang.lean:7375-7398`), `builtinCollectionItems` (`:2665`), `makeCollectionListResult` (`:2842`); spec `builtin-fixed-collection-arity` (`:2967`), `count-family`, `count-dotcount-agree`, `sum-of-range-collection`, `avg-is-the-correctly-rounded-exact-mean`, `min-max-signed-zero`; tutorial § One Collection Argument (`tutorial.md:1186-1211`).
- **Probe:** `(1, 2, 3).sum / sum((1, 2, 3)) / (1, 2, 3).min / .max / .avg / .count` → `S[6, 6, 1, 3, 2, 3]`; `sum(1, 2, 3)` → `ArityMismatch`; `sum(5) / count(5) / sum(())` → `S[5, 1, 0]`; `sum(((1, 2), (3, 4)))` → `ArityMismatch … each collection element to be a single numeric value`; `Numbers = 3, 5, 9 / Numbers.sum / sum(Numbers) / Numbers.count` → `S[17, 17, 3]`.
- **Topics:** COLL, DOT, VAL
- **Lineage review (phase 2) corrections/addenda:**
  - [dot-call] CURRENT (lineage: dot-call passes a value has 'no issue number found') → CURRENT (lineage: dot-call passes a value = #167, commit 68b3607). Evidence: Commit 68b3607's subject is 'Make dot-call pass values without implicit spreading #167'. The #167 body revision of 2026-09-21 11:23 added rule 3 'Dot-call is ordinary receiver injection', per the #167 ledger evolution notes.
  - [builtin-surface] CURRENT; lineage '#57 temporarily added the variadic spelling' → CURRENT; lineage: #57 replaced the one-collection model and inverted lone-group opening (04-17..06-17); #125 restored, d2837f4 normalized, #135 fixed. Evidence: Introduced behavior count(((1, 2), (3, 4))) = 2 (tutorial at 9b3f1ff) was lost at 2f27fba and restored at ad75720 (tutorial: count((1, 2, 3)) is 3). Classification unchanged.

### #35 — Add built-in range for sequence generation
- **Dates:** created 2026-04-06 · closed 2026-04-08
- **Problem / question:** Generating a sequence of integers requires manual loops.
- **Decision / intended invariant:** `range(start, end)` builtin: inclusive integer sequence, ascending or descending (commit b3c39bc "Add inclusive range builtin").
- **Rationale:** most collection calculations start from a generated sequence; pairs with filter/map/reduce/atoms.
- **Examples:** `range(1, 5)`; `range(5, 1)`.
- **Lineage:** extended by #45 (proposal `range(start, finish, transform)` NOT adopted; `1..10` syntax rejected); result kind changed by #135 (collection-producing builtins return ONE exact list, so `range(3, 3)` is `[3]`); Decimal128 (#153) added bound quantum canonicalization; optimizer range fusion is implementation-only.
- **Classification:** PARTIALLY CURRENT *(revised in lineage review; ledger batch said CURRENT)*
- **Surviving part / superseded by:** inclusive, bidirectional, fixed arity 2; result now an exact list rather than a sequence (refinement by #135).
- **Current evidence:** Lean `.rangeBuiltin, [startAlg, stopAlg]` (`KatLang.lean:5925-5930`: `expectInt` both bounds, `inclusiveRange`, `makeCollectionListResult`), arity 2 (`:600`, `:622`); spec `range-inclusive` (`:2716`), `range-single-value`, `range-integral-bound-quantum`; tutorial § Ranges (`tutorial.md:1091-1102`).
- **Probe:** `range(1, 5) / range(5, 1) / range(3, 3)` → `S[L[1, 2, 3, 4, 5], L[5, 4, 3, 2, 1], L[3]]`; `range(1, 5, {x * 2})` → `ArityMismatch`.
- **Topics:** COLL, SEQ
- **Lineage review (phase 2) corrections/addenda:**
  - [sequences-lists-values] CURRENT → PARTIALLY CURRENT. Evidence: The issue's commit b3c39bc documented 'If start == stop, it returns a single value' and pinned Eval_Range_SingletonWhenEqual range(5, 5) -> 5 (an emitted sequence 'for sequence generation'). #132 (9a4c70f) made the result one sequence value and #135 (0ca55e9) ONE exact list; current probe range(5, 5) -> L[5], range(5, 5) == 5 -> false. Only the inclusive, bidirectional, fixed-arity-2 range survives; the stated result kind is superseded.
  - [builtin-surface] CURRENT → PARTIALLY CURRENT. Evidence: Issue decided a builtin for sequence generation and b3c39bc returned a sequence; since #135 0ca55e9 range returns an exact list (Lean KatLang.lean:5925-5930 makeCollectionListResult; probe range(3, 3) -> L[3]). Inclusive, bidirectional, 2-ary parts survive.

### #37 — Add collection transforms over multi-output values: map, filter, and reduce
- **Dates:** created 2026-04-06 · closed 2026-04-08
- **Problem / question:** Common transformation patterns required hand-written loops despite higher-order algorithms existing.
- **Decision / intended invariant:** Builtins `map(collection, transform)`, `filter(collection, predicate)`, `reduce(collection, step, initial)` over top-level collection elements, left to right; transform/step must return exactly one value; usable in dot form.
- **Rationale:** natural extension of higher-order algorithms; three restricted abstractions preferred over one general loop (#40).
- **Examples:** `range(1, 5).map{x * 2}`, `filter((1, 2, 3, 4, 5, 6), IsEven)`, `reduce(xs, {x + acc}, 0)`.
- **Lineage:** replaces the #40 `foreach` proposal; refined by #41 (predicate result shape), #53/#65/#80/#92/#102 (callback binding, reduce arity, variadic accumulator), #135 (map/filter return exact lists), #165 (predicate must be Boolean), and the THE CALLBACK LAW of "values stay values" (#167 / C-full, 2026-09-23): each element is ONE ordinary argument, `reduce` calls `f(element, accumulator)`; the reducer's accumulator-slot opening and flat-callback row convention were deleted.
- **Classification:** PARTIALLY CURRENT *(revised in lineage review; ledger batch said CURRENT)*
- **Surviving part / superseded by:** the three builtins, element order, single-value callback result; binding details superseded by the callback law. *(Q-25, 2026-10-10: the single-value callback result is SUPERSEDED — a callback returns its ordinary call result, `constitution.md` HO-03.)*
- **Current evidence:** Lean `evalReduceCounted` (`KatLang.lean:5671`), `evalFilterCounted` (`:5710`), `evalMapCounted` (`:5748`); `sequences-lists-and-calls.md` § Collecting parameter lists, deconstruction, and callbacks; spec `filter-keeps-matching`, `map-transforms-items`, `map-pair-callback`, `reduce-accumulates-value`, `reduce-empty-initial-is-one-value`, `callback-element-is-one-argument`; tests `ExplicitValueOpeningTests`, `CallbackNestedPatternBindingTests`; tutorial § Callbacks Receive One Element / Folding with `reduce` (`tutorial.md:1245-1288`). Commits b2eb2b5, 83eccae, a66564b.
- **Probe:** `range(1, 5).map{x * 2} / range(1, 5).filter{x mod 2 == 0} / range(1, 5).reduce({x + acc}, 0)` → `S[L[2, 4, 6, 8, 10], L[2, 4], 15]`; `map((1, 2), {x, x})` → `ArityMismatch: map transform must return a single element`; `reduce((1, 2), {x, acc}, 0)` → `ArityMismatch: reduce step must return a single accumulator value`.
- **Topics:** HO, COLL
- **Lineage review (phase 2) corrections/addenda:**
  - [builtin-surface] CURRENT → PARTIALLY CURRENT. Evidence: Result kinds changed: map/filter returned sequences, now exact lists (0ca55e9; range(1,5).map{x*2} -> L[...]); predicate numeric truth replaced by Boolean-only (e4d19cc; P(x)=1 -> TypeMismatch). Lineage fix: C-full 702e7d7 RESTORED #37's original element binding (a66564b tutorial 'Swap((a, b)) = (b, a) works'; 83eccae 'step(element, accumulator) receives each whole top-level element'); what was superseded was #58's row convention (c9a43fa:937 'write Swap(a, b) = (b, a)').

### #38 — bug: Grace~ operator is ignored when applied on parameter which is callable algorithm
- **Dates:** created 2026-04-07 · closed 2026-04-07
- **Problem / question:** In `Filter = if(predicate~(x), x)` the postfix Grace on a directly-called implicit parameter was dropped by the parser, so parameter order stayed `(predicate, x)`.
- **Decision / intended invariant:** Grace applies to a bare-name occurrence also when that name is the callee of a direct call (`predicate~(x)` is a call whose callee is `Grace(predicate)`); it reorders implicit parameters exactly as for value occurrences, so `Filter(3, IsEven)` binds `x = 3`, `predicate = IsEven`.
- **Rationale:** Grace must not depend on whether the parameter is used as a value or as a callable.
- **Examples:** `IsEven = x mod 2 == 0` / `Filter = if(predicate~(x), x)` / `Filter(3, IsEven)` → empty (then). Current equivalent (3-argument `if`, #49): `Filter = if(predicate~(x), x, 0)` → `0`.
- **Lineage:** predecessors #21 (Grace forbidden in clause branches), #22 (Grace error location); successors: GRACE MUST BE EFFECTIVE (F10 — Grace on a fixed binding is `InvalidGraceMarker`), Grace-in-redundant-group rule (#168), Grace/dot composition and #152 (`a~t` shorthand).
- **Classification:** BUG FIX / REAFFIRMED EXISTING RULE
- **Surviving part / superseded by:** behavior intact; Grace eligibility later narrowed by F10 (does not affect this case: `predicate` is an unfixed implicit parameter).
- **Current evidence:** `ParserTests.Parse_PostfixGrace_CanBeDirectCallee` (`ParserTests.cs:3288`), `EvaluatorHigherOrderTests.Eval_HigherOrder_GraceReordersCallableParameter` (`EvaluatorHigherOrderTests.cs:138`); `ownership-and-lookup.md` § Grace (F10). Commit 022abc4.
- **Probe (translated):** `IsEven = x mod 2 == 0 / Filter = if(predicate~(x), x, 0) / Filter(3, IsEven) / Filter(4, IsEven)` → `S[0, 4]`; without Grace `Filter(3, IsEven)` → `NotAnAlgorithm: Parameter 'predicate' is not callable here` (order `(predicate, x)`), `Filter(IsEven, 4)` → 4.
- **Topics:** PAR, HO

### #39 — bug: Conditional algorithm does not work well -- i suppose it do not like parameter call in conditional algorithm branch
- **Dates:** created 2026-04-07 · closed 2026-04-09
- **Problem / question:** `Filter(x, predicate) = if(predicate(x), x)` with `Filter(3, IsEven)` failed with `Unknown name: y` (IsEven's own implicit parameter), because a clause head made `Filter` a conditional algorithm whose parameter could not be invoked higher-order.
- **Decision / intended invariant:** CLAUSE ELABORATION RULE: a same-name clause group with exactly ONE clause whose head is a plain capture parameter list elaborates to an ordinary algorithm (`Algorithm.mk`) with an explicit (closed) parameter list; multi-clause or literal/mixed heads stay conditional. Ordinary call semantics then apply, including calling a parameter bound to an algorithm (the argument algorithm binds its own implicit parameters).
- **Rationale:** `Name(a, b) = body` must mean an ordinary function definition; the ordinary-vs-conditional split is decided for the whole family, not per clause.
- **Examples:** `IsEven = y mod 2 == 0` / `Filter(x, predicate) = if(predicate(x), x)` / `Filter(3, IsEven)`. Current equivalent: `… = if(predicate(x), x, 0)`.
- **Lineage:** builds on #26/#27; introduced `elaborateClauseGroup`, `flatBinderUserEquivalent?`, `clauseGroupDefinitionKind` (commit 419100a). Generalized later to "recursive capture/sequence-value parameter pattern" heads (`PairSum((x, y))`, `CountSequenceValue((*values))`; related #99, #138 — exact generalizing commit not pinned in this batch); variant-owned `HasExplicitParameterList` (API cleanup, 2026-09); callbacks use `flatBinderUserEquivalent?` (callback law, 2026-09).
- **Classification:** CURRENT
- **Surviving part / superseded by:** rule survives and was generalized; the literal `Choose(x, predicate) = if(predicate(x), x, 0)` example is in the Lean docstring.
- **Current evidence:** Lean `KatLang.lean:1035-1048` (Clause elaboration rule), `clauseGroupDefinitionKind` (`:1825`), `elaborateClauseGroup` (`:1851`, docstring names `Choose(x, predicate)`), `flatBinderUserEquivalent?` (`:2677`); C# `Ast.cs:1735` `ElaborateClauseGroup`; tests `EvaluatorHigherOrderTests.Eval_HigherOrder_FlatMultiBinderClause_UsesOrdinaryBinding` (`:150`), `…_FalsePredicate_UsesElseBranch` (`:162`), `KatLangEngineTests.cs:1317-1331`, `ClauseGroupElaborationTests`.
- **Probe (translated):** `IsEven = y mod 2 == 0 / Filter(x, predicate) = if(predicate(x), x, 0) / Filter(3, IsEven) / Filter(4, IsEven)` → `S[0, 4]`; the original 2-argument form now → `ArityMismatch: Callable 'if(condition, whenTrue, whenFalse)' expects 3 arguments`.
- **Topics:** PAT, CALL, HO, PAR
- **Lineage review (phase 2) corrections/addenda:**
  - [parameter-inference-grace] CURRENT (decision text: single clause elaborates to an ordinary algorithm with an explicit (closed) parameter list) → CURRENT (decision text: explicit parameter list, OPEN at the time; closedness came from 6c64e66 on 2026-05-08). Evidence: The 419100a ParameterDetector diff reads 'start with any parser-declared params (used by plain-binder clause elaboration), then infer additional implicit params from free identifiers', so inferred names were appended and Grace reordered the whole list. Closed explicit lists arrived with 6c64e66 ('Enforce closed explicit parameter lists ...', ReportUndeclaredExplicitParameterNames; the Lean doc became 'Surface front-ends must not append inferred implicit parameters'). '(closed)' in the #39 entry is anachronistic, and #39's lineage should name 6c64e66.

### #40 — Add foreach iteration over multi-output collections
- **Dates:** created 2026-04-08 · closed 2026-04-08 (DUPLICATE)
- **Problem / question:** Add a general `foreach` step construct (collection-driven iteration beside `repeat`/`while`) as the foundation for sum/map/filter/etc.
- **Decision / intended invariant:** Rejected: no `foreach`. KatLang uses separate restricted abstractions (`map`, `filter`, `reduce`) plus `repeat`/`while`; closed as duplicate of #37.
- **Rationale:** one abstract construct is a worse abstraction, awkward to use, harder to formalize in Lean than three restricted ones.
- **Examples:** proposed `foreach(list, step)` — never implemented.
- **Lineage:** duplicate of / superseded in favor of #37; consistent with #45 (no laziness, no special syntax) and #64 (loop syntax; open at the snapshot, CLOSED 2026-10-20 by META-S3-3, `9c8623f2`, which adds no `foreach`).
- **Classification:** CURRENT
- **Surviving part / superseded by:** the rejection stands (no `foreach` builtin in Lean or C#).
- **Current evidence:** Lean `preludeAlg` (`KatLang.lean:7375-7398`) lists `if while repeat atoms range filter map order orderDesc count contains first last distinct take skip min max sum avg reduce` — no `foreach`.
- **Probe:** `foreach((1, 2), {x})` → `UnresolvedImplicitParams` (`foreach` is just an unresolved name).
- **Topics:** LOOP, HO, COLL

### #41 — Predicate returning value should be single atomic value 0 or 1
- **Dates:** created 2026-04-08 · closed 2026-04-08
- **Problem / question:** `P(x) = 1, 1` was accepted as a filter predicate (multi-output flattened to a truth value).
- **Decision / intended invariant (then):** a filter predicate must return EXACTLY ONE atomic numeric value (0 = false, nonzero = true); multi-output, grouped, empty and string results are rejected, never flattened (`SingleAtomicTruthValue`).
- **Rationale:** predicate results must be unambiguous; no silent flattening.
- **Examples:** `P(x) = 1, 1` / `range(1, 5).filter(P)` → error.
- **Lineage:** superseded in its value model by #165 (first-class Booleans, numeric truthiness removed; commit e4d19cc); shape rule reaffirmed by the ONE Boolean view `Result.asBool?` (a Boolean or a redundant singleton boundary around one). Related #49 (if), #131.
- **Classification:** PARTIALLY CURRENT
- **Surviving part / superseded by:** Survives: the predicate result must be ONE truth value; multi-item sequences, empty, strings, lists are rejected (typeMismatch), no flattening. Superseded by #165: "0 or nonzero number" — numbers now have no truth value; only `true`/`false` qualify (`P(x) = 1` is now an error too).
- **Current evidence:** Lean `Result.asBool?` (`KatLang.lean:1215-1229`), filter check (`:5720-5731`), `booleanRequiredMessage` (`:2428`); `evaluator-and-hosting.md` § Boolean values; spec `boolean-predicates-and-patterns` (`:128`), `boolean-predicate-rejects-visible-empty` (`:151`); tests `BooleanValueTests`; tutorial `tutorial.md:1184`. Commit ee8180c.
- **Probe:** `P(x) = 1, 1 / range(1, 5).filter(P)` → `TypeMismatch: filter predicate result must be a Boolean value (true or false), but was a sequence value with 2 sequence elements: (1, 1)`; `P(x) = 1` → `TypeMismatch … but was numeric value 1`; `P(x) = (x > 2, true)` → TypeMismatch; `P(x) = (x > 2)` → `L[3, 4, 5]`.
- **Topics:** BOOL, HO, COLL

### #42 — Optimize repeated property evaluation with per-run memoization
- **Dates:** created 2026-04-10 · closed 2026-04-22 (reopened once)
- **Problem / question:** Immutable zero-parameter properties were re-evaluated at every reference (`Values` used twice); the first memoization key was too context-sensitive (0 hits across contexts).
- **Decision / intended invariant (then):** per-run memoization of zero-parameter property evaluation, reused across evaluation contexts for a closed lexical property — framed as an OPTIMIZATION.
- **Rationale:** avoid repeated work; immutable bindings should not be recomputed.
- **Examples:** `Values = range(1, 100)` / `SquaresTotal = Values.map{x*x}.sum` / `Values.sum ^ 2 - SquaresTotal`.
- **Lineage:** 5a37525 + 6fea03c (2026-04-10) → removed 4a77f87 (2026-04-21, "cleanup architecture first", issue reopened) → 6fe4f51 "Stage 1 zero-arg property result cache" (2026-04-22, closed) → #109/#110 (random: `A` cached vs `A()` fresh; recursive cache avoidance rejected; commits d7629b6 reverted by 1cac168, 489b77f) → d843523 "Model zero-parameter property caching in Lean" (2026-05-18: becomes semantics) → 31f7c76 (2026-09-12 cache scope/exposure) → #170 (2026-09-27, ebf623e) "caching by semantic binding identity", explicitly a follow-up of #42.
- **Classification:** PARTIALLY CURRENT
- **Surviving part / superseded by:** Survives: a zero-parameter property is evaluated once per run and reused across every consumer/context. Superseded by #170 (and #110): it is OBSERVABLE SEMANTICS modeled in Lean, not an optimization; cache identity = resolved binding identity (shadowing ⇒ separate entry); `A()` is a fresh evaluation that neither reads, populates nor replaces the entry; consumption path (builtins, dot, callbacks, `.string`) never affects caching.
- **Current evidence:** `evaluator-and-hosting.md` § Zero-argument property cache (line 94); Lean CoreTests `zeroArg*`, `PropertyCacheConsumers`; tests `ZeroArgPropertyCacheScopeTests`, `PropertyCacheConsumerTransparencyTests`; tutorial § Reading and Calling (`tutorial.md:285-316`, `Roll == Roll` is `true`).
- **Probe:** `Values = trace(range(1, 5)) / SquaresTotal = Values.map{x*x}.sum / Values.sum ^ 2 - SquaresTotal` → `ok 170`, host log `[trace(L[1, 2, 3, 4, 5])]` (evaluated once); `A = tick() / A / A / A() / A` → `S[1, 1, 2, 1]`, `[tick#1, tick#2]`; `A = tick() / F = A + 0 / G(y) = A + y / F / G(0) / sum((A, A))` → `S[1, 1, 2]`, one tick; `A = tick / A / A / A() / A` → `S[1, 1, 1, 1]` (fresh `A()` re-runs A's body, whose own read of the prelude binding `tick` stays cached — no recursive cache avoidance, per #110).
- **Topics:** PROP, RUN, FORMAL
- **Lineage review (phase 2) corrections/addenda:**
  - [property-caching] PARTIALLY CURRENT; surviving: 'evaluated once per run and reused across every consumer/context' → PARTIALLY CURRENT; surviving: exported bindings are evaluated once per run per declaring scope, local-only bindings once per declaring-owner activation (F3, 31f7c76), and failures are never stored. Lineage should add: the Stage-1 cache 6fe4f51 keyed on environment reference identity and so reintroduced the context-sensitivity that #42 comment 1 rejected, fixed only in 31f7c76; dfd97c6 fixed structural-owner aliasing. Evidence: evaluator-and-hosting.md:94 (local-only keys use the declaring owner's ParameterActivation); SEMANTIC-ALIGNMENT.md:570 (F3); memory f3-zero-arg-cache-scope-law (root cause: environment-reference keys re-evaluated an exported Big on every call, and opened properties never hit); dfd97c6 diff (process-wide owner sentinel aliased different owners); probe p2 G(1), G(1) -> 6, 8 vs F(10), F(20) with one tick.

### #43 — Need to improve pow operator ^ precision
- **Dates:** created 2026-04-10 · closed 2026-04-10
- **Problem / question:** `^` used `Math.Pow` (double) and lost precision converting to/from `decimal`.
- **Decision / intended invariant (then):** exact decimal power for integer exponents (incl. negative), `Math.Pow` fallback only for fractional exponents (commit a90fdd4).
- **Rationale:** KatLang is a precise calculation language.
- **Examples:** `2 ^ -2` → `0.25`.
- **Lineage:** predecessor #11 (trig precision via double), #13 (large numbers); superseded by #153 (Decimal128 core numeric type, commit 7f0bab0), then ec48b91 (Decimal128 integer power accuracy), 869c1bc (zero-base negative powers are errors), numeric audit #6 (log1p band, `Evaluator.DelegatedPower` sign symmetry); precedence commit 065152c (2026-08-29, `^` binds tighter than prefix `-`/`not`; no issue number found).
- **Classification:** PARTIALLY CURRENT *(revised in lineage review; ledger batch said SUPERSEDED)*
- **Surviving part / superseded by:** the goal (accurate `^`) survives; the decimal/`Math.Pow` mechanism is replaced by the Decimal128 implementation (#153). Numeric details are a C#-only reviewed tier (Lean core uses `Int`).
- **Current evidence:** `Evaluator.cs:3252-3369` (`DelegatedPower`, Decimal128.Pow / log1p reformulation; `Math.Pow` appears only in doc comments naming the KatLang member); `evaluator-and-hosting.md` § Numerics; spec `pow-integer-exponent-inexact-accuracy` (`:4144`), `pow-zero-base-negative-exponent` (`:4167`), `negative-near-one-base-power-is-sign-symmetric` (`:5225`), `power-unary-precedence` (`:160`).
- **Probe:** `2 ^ -2 / 2 ^ 0.5 / 1.1 ^ 20 / (-8) ^ 3` → `S[0.25, 1.414213562373095048801688724209698, 6.72749994932560009201, -512]` (engine); `0 ^ -1` → `IllegalInEval: zero cannot be raised to a negative exponent`.
- **Topics:** OP
- **Lineage review (phase 2) corrections/addenda:**
  - [operators-comparisons] SUPERSEDED → PARTIALLY CURRENT. Evidence: The ledger says only the goal survives, and it credits 869c1bc with making zero-base negative powers errors. In fact a90fdd4, #43's own fix commit, added IllegalInEval 'zero cannot be raised to a negative integer exponent' in DecimalPow. That rule survived continuously: the 869c1bc diff shows it still present behind a Decimal128.IsInteger(exp) guard, and 869c1bc only generalized it to all negative exponents (Evaluator.cs:3273 today). The issue's request to remove Math.Pow is also fully met today: there is no double Math.Pow( call in src/KatLang, and DelegatedPower (Evaluator.cs:3369) uses Decimal128.Pow. Only the decimal plus Math.Pow-fallback mechanism is superseded. The lineage should say '869c1bc generalizes the a90fdd4 zero-base rule'.
  - [random-numerics] SUPERSEDED → PARTIALLY CURRENT. Evidence: The decision that integer exponents (negative included) are computed exactly rather than via a floating Pow survives in refined form. Only the decimal/double mechanism was replaced. Evidence: Evaluator.cs:3238-3242 ('results round the exact input power once to Decimal128 … 2^10 is 1024') and the certification contract at :3276-3285; memory decimal128-numeric-migration ('integer exponents = exact by-squaring'); spec pow-integer-exponent-inexact-accuracy (LanguageSpecCorpus.cs:4144); probe 2 ^ -2 -> 0.25 (the issue's example).

### #44 — Improve error messages
- **Classification:** PARTIALLY CURRENT *(revised in lineage review; ledger batch said IMPLEMENTATION ONLY)* — diagnostic wording/span improvements (missing output, arity, unresolved implicit params, branch pattern errors; commit d5cb0cd); no language rule; later superseded in mechanism by structured `ErrorContext` (#68), `DiagnosticCode`/`KatLangErrorCode`, F3/F5 blame rules.
- **Topics:** TOOL
- **Lineage review (phase 2) corrections/addenda:**
  - [output-syntax-layout] IMPLEMENTATION ONLY → PARTIALLY CURRENT. Evidence: Commit d5cb0cd ('Fix #44 improve error messages and spans') silently introduced a grammar rule in ParseExpression: `if (Current.Line > Previous.Line && !HasSkippedCommentBeforeCurrent()) break;`. An operator at the start of a line no longer continues the previous expression, unless a comment precedes it. `git log -S "Current.Line > Previous.Line"` gives d5cb0cd as the earliest commit, and the v0.7.3 parser (25a8558) has no line checks. The operator-led-line rule is current law (KatLang.ebnf Expression commentary; probe `A` newline `-1` gives two rows, `A` newline `+1` gives UnexpectedToken). The comment exception was reversed by 007917a (#123), which deleted HasSkippedCommentBeforeCurrent. **Q-65 revision, 2026-10-14:** The quoted strict operator-led rule and UnexpectedToken observation are historical. SYN-08 now allows grammar-priority leading continuation: `A` newline `+1` continues addition, while attached `-1` remains independent. The issue classification and historical comment-exception account are unchanged.

### #45 — Add collection utility builtins for more intuitive everyday use
- **Dates:** created 2026-04-11 · closed 2026-04-19
- **Problem / question:** Collection work felt incomplete; which helpers (sort, distinct, first, last, take, skip, contains)? Should `range` take a `transform` to avoid intermediate allocation (no laziness)?
- **Decision / intended invariant:** Add `order` / `orderDesc` (SQL-like naming instead of `sort`), `distinct`, `first`, `last`, `take`, `skip`, `contains` as ordinary named prelude builtins. No special range syntax (`1..10` rejected: "everything is algorithm"), no lazy evaluation in the language/Lean core, and `range(start, finish, transform)` not adopted.
- **Rationale:** familiarity (C#/SQL), uniform algorithm model; laziness would complicate Lean and risk LINQ-style perf debt.
- **Examples:** `order((3, 4, 2, 1, 3, 3))`, `Scores.orderDesc.take(3)`, `Scores.contains(88)`.
- **Lineage:** extends #34/#35/#37; #57 (variadic spelling) later reversed by #135 (one fixed collection argument, exact list results); #165 (`contains` returns Boolean); selection-value-boundary (2026-09-21: `first(A) ≡ A:0`, `last(A) ≡ A:(A.count - 1)`, chooses a value, never opens it); `order` stable sort (`order-is-stable`); `distinct` uses structural equality (#127); loop/sequence optimizer fusions (#86/#87) are implementation-only.
- **Classification:** PARTIALLY CURRENT *(revised in lineage review; ledger batch said CURRENT)*
- **Surviving part / superseded by:** all seven builtins exist with the chosen names; non-adoption of range-with-transform and of laziness stands (range arity 2). Result kinds refined by #135; `contains` value kind by #165; `first`/`last` by selection law.
- **Current evidence:** Lean `evalOrderCounted` (`KatLang.lean:4156`), `evalOrderDescCounted` (`:4168`), `evalContainsCounted` (`:4190`), `evalDistinctCounted` (`:4204`), `evalFirstCounted` (`:4215`), `evalLastCounted` (`:4224`), `evalTakeCounted` (`:4238`), `evalSkipCounted` (`:4255`), `sortIntsAsc` (`:2463`); `sequences-lists-and-calls.md` § Collection builtins, § Value boundaries; spec `order-sorts-atoms`, `order-is-stable`, `order-rejects-non-numeric`, `distinct-preserves-first`, `distinct-structural-pairs`, `take-prefix`, `skip-prefix`, `selection-forms-agree`; tutorial § Common Operations (`tutorial.md:1137-1184`). Commits 27d3f57, 3b0dad3, c410c2f, 902e530, aa4ce72.
- **Probe:** `order((3, 1, 2)) / orderDesc((3, 1, 2)) / distinct((1, 1, 2)) / first((5, 6)) / last((5, 6)) / take((5, 6, 7), 2) / skip((5, 6, 7), 2) / contains((5, 6), 6)` → `S[L[1, 2, 3], L[3, 2, 1], L[1, 2], 5, 6, L[5, 6], L[7], true]`; `first(())` → `ArityMismatch: first requires a non-empty collection`; `range(1, 5, {x * 2})` → `ArityMismatch`; `1..10` → parse failure.
- **Topics:** COLL, SEQ
- **Lineage review (phase 2) corrections/addenda:**
  - [builtin-surface] CURRENT → PARTIALLY CURRENT. Evidence: Lower confidence (scope judgement). Names, no range-transform, no '..', no laziness survive; shipped result contracts did not: take/skip/order/orderDesc/distinct sequences -> exact lists (#135 0ca55e9), contains 1/0 -> true/false (e4d19cc; generator .github/agents/katlang-generator.agent.md:932 still says 'Empty collections return 0'), first/last -> selection value boundaries (874625a).

### #46 — Improve KatLang generator
- **Classification:** DOCUMENTATION ONLY — generator style guidance (final executable call, readable structure, idiomatic builtins; commit 033651c); lives in `.github/agents/katlang-generator.agent.md` / `experimental/prompts/katlang-generator.txt`, not a language rule.
- **Topics:** TOOL

### #48 — Decide if some Math functions can be made available directly without prefix Math.
- **Dates:** created 2026-04-11 · closed 2026-04-12
- **Problem / question:** Should `round`, `floor`, `ceil`, … (or all Math functions) be available without the `Math.` prefix?
- **Decision / intended invariant (then):** No: Math functions only as `Math.X` (or after `open Math`); fix the generator to prefer `Math.Sqrt` over opening Math for a single use (commit 9c4e063).
- **Rationale:** least surprise / no name collisions for newcomers; Math is not in the Lean model, so keep it separate from the core prelude.
- **Examples:** `Math.Sqrt(2)` preferred over `open Math` + `Sqrt(2)`.
- **Lineage:** REVERSED by #154 (2026-08-24, commit b3738b9): every Math member gets a predefined lower-camel-case PRELUDE alias (`sqrt`, `round`, `pi`, …) that is an ordinary, shadowable prelude binding; #155 replaced `Math.E` by `Math.Exp`/`exp`; audit #8 (Math members recognized by identity); generator guidance now PREFERS the aliases.
- **Classification:** SUPERSEDED
- **Surviving part / superseded by:** superseded by #154. Residual facts still true: canonical PascalCase members exist only inside `Math` (`Math.cos` is not a member; `open Math` exposes PascalCase names only); no implicit `open Math`; Math is still absent from the Lean model (`KatLang.lean` has no Math members; `preludeAlg` lacks them); collisions are handled by ordinary shadowing rather than by withholding names.
- **Current evidence:** `ownership-and-lookup.md` § Math members, host operations, and the prelude in every layer (lines 50-56); spec `ownership-parameter-beats-prelude-alias` (`:4450`); tutorial § Math Functions (`tutorial.md:186-224`: "These names are shortcuts for the members of the built-in Math algorithm"); generator `.github/agents/katlang-generator.agent.md:40`, `:1298-1303`; tests `MathAliasSemanticModelTests`.
- **Probe:** `open Math / round(2.567, 2) / Math.Round(2.567, 2) / Round(2.5, 0) / sqrt(16)` → `S[2.57, 2.57, 3, 4]`; `round = 5 / round + 1` → `6` (alias shadowable); `Math.round(2.5, 0)` → `ArityMismatch: Callable 'round(value, digits)' expects 2 arguments, but was called with 3` (no lowercase member in Math; dot falls back lexically to `round(Math, 2.5, 0)`).
- **Topics:** MOD, RES, OP

### #49 — Think about removing support of 2 argument 'if' builtin
- **Dates:** created 2026-04-12 · closed 2026-04-13
- **Problem / question:** `if(c, v)` silently produced an empty result when false, which is unpredictable inside `*`, `/`, `div`, `mod`, and made `if` the only overloaded builtin.
- **Decision / intended invariant:** Remove the 2-argument form; builtin `if` has exactly one signature `if(condition, whenTrue, whenFalse)` (arity 3). All builtins have a single syntactic form.
- **Rationale:** predictability over brevity; 2-argument `if` was a leaky abstraction (the only way to inject emptiness into a value position); range/filter/sum removed the need.
- **Examples:** `F = a * if(7 < 6, 1, 0)` / `F(2)` → 0; `F = a * if(7 < 6, 1)` → (then) 2, now an error.
- **Lineage:** reverses #15 (introduced the 2-argument form); reaffirmed by #159 (resolve `if` by callable identity, not spelling or arity; `if` is an ordinary shadowable prelude binding, no overloading by arity, SYN-05); condition must be Boolean (#165); the "empty as operator identity" behavior #15 relied on was itself removed (SYN-01: empty is not an operator identity); explicit `()` literal exists (#81/#128) and `if(false, 1, ())` is legal but `() * 3` is a type error.
- **Classification:** PARTIALLY CURRENT *(revised in lineage review; ledger batch said CURRENT)*
- **Surviving part / superseded by:** all.
- **Current evidence:** Lean `Builtin.ifBuiltin` arity 3 (`KatLang.lean:596`, `:618`, `:632`), dispatch `.ifBuiltin, [c,t,e]` (`:5865`), `preludeAlg` `publicProp "if"` (`:7377`); `ownership-and-lookup.md` § Builtin identity and the zero-argument value demand (SYN-05); spec `if-arity-is-uniform-across-spellings` (`:4802`), `if-composition-forms-agree` (`:4790`), `if-value-boundary` (`:2952`), `if-laziness-follows-the-resolved-identity`, `empty-sequence-is-not-an-operator-identity` (`:3525`); tests `IfBuiltinArityPayloadTests`, `BuiltinCallableIdentityTests`. Commit 93a036d.
- **Probe:** `if(true, 1)` → `ArityMismatch: Callable 'if(condition, whenTrue, whenFalse)' expects 3 arguments, but was called with 2`; `F = a * if(7 < 6, 1, 0) / F(2)` → `0`; `10 + if(1 == 2, 5, ())` → `TypeMismatch`; `if(1, 10, 20)` → `TypeMismatch: if condition must be a Boolean value`.
- **Topics:** BOOL, CALL, SYN
- **Lineage review (phase 2) corrections/addenda:**
  - [booleans-conditions] CURRENT → PARTIALLY CURRENT. Evidence: 'Surviving part: all' overclaims. Survives: removal of the 2-argument form and the single arity-3 if signature with no overloading. Superseded: the enforcement mechanism. 93a036d implemented the rule as the C# parse-time spelling gate Parser.ValidateIfArity requiring exactly 3, reported as a parser error ('Builtin 'if' expects 3 arguments: condition, whenTrue, whenFalse. Got N'; #131's body quotes it). #159/0243678 (SYN-05) deleted that gate: git log -S'ValidateIfArity' -- src/KatLang/Parser.cs shows 5a6c550 introducing it and 0243678 removing it. Today a wrong-arity if is an evaluation-time ArityMismatch against the resolved identity and is inert when unevaluated. Probe: if(true, 1) gives an ArityMismatch evaluation error, not a parseFailure; 'P = if(true, 1)' then '5' gives 5. Pinned by spec if-arity-is-uniform-across-spellings and DiagnosticCodeTests.NoFrontEndPath_ProducesTheParseTimeArityCode. #49's numeric-condition examples are also obsolete (#165), and its premise that if was the only way to inject emptiness relied on the empty-operand identity that SYN-01 (a8bcae7) removed.

### #50 — Implement reusable semantic-analysis infrastructure for editor tooling
- **Classification:** HOST/API ONLY — added the editor-facing semantic model (`SemanticModel`, PropertyInfo, span fixes for `open 'url'`; commits e18a14e, 0285340, 2070eef) for Monaco highlighting; today `src/KatLang/Semantics/` built from `ParseResult`, explicitly "not the evaluator and not the normative semantics layer" (AGENTS.md; `editor-semantics.md`; `SemanticModelTests`).
- **Topics:** TOOL, API

### #51 — Implement support for static string-literal aliases in 'open' targets
- **Dates:** created 2026-04-14 · closed 2026-04-14 (NOT_PLANNED)
- **Problem / question:** `open 'https://…/algorithm.kat'` works, but `open Lib` with `Lib = 'https://…'` does not; should a property holding a string literal act as a load alias for `open`?
- **Decision / intended invariant:** Not planned. Only a string literal written directly in the `open` target list is load sugar; a property whose value is a string is not an open/load alias.
- **Rationale:** maintainer comment: "~140 lines of Lean code … too big price for this feature".
- **Examples:** `open Lib` / `Lib = 'https://katlang.org/algorithm.kat'` / `X` → `X` becomes an implicit parameter (the issue's error); `open Lib` / `Lib = { public Double = x * 2 }` / `Double(5)` works.
- **Lineage:** follows #6 (open design) and #18 (non-public algorithms cannot be opened); `open 'url'` string-load sugar later hardened (module-loading audit #13: one `ModuleLoadTarget`; async-only `RunOptions.DownloadCode`; missing-module analysis state). No later issue reopened the alias idea.
- **Classification:** CURRENT (the rejection stands)
- **Surviving part / superseded by:** whole decision survives.
- **Current evidence:** `docs/design/language-rules/syntax.md` § The `open` declaration (targets = resolve / argumentless dot path / block / string-load sugar in single quotes); AGENTS.md "`open 'url'` is front-end sugar for load elaboration, not a core AST construct"; `KatLang.ebnf:30` (`OpenDeclaration`); `ModuleLoader` (internal).
- **Probe:** (`--modules mods`, `mods/lib.kat` = `public Double = x * 2`) `open 'https://mods.test/lib.kat'` / `Double(5)` → 10; `open Lib` / `Lib = 'https://mods.test/lib.kat'` / `Double(5)` → UnresolvedImplicitParams ('Double' promoted to implicit parameter; `open Lib` of a string-valued zero-parameter property silently provides no names — no targeted diagnostic); block form → 10.
- **Topics:** MOD

### #52 — Cleanup Output semantics: forbid external Output usage and require parameters on algorithm level
- **Dates:** created 2026-04-15 · closed 2026-04-15
- **Problem / question:** the explicit `Output` property (introduced by #5) had loose, surprising uses.
- **Decision / intended invariant:** (1) `Algo.Output(6)` forbidden; (2) `Output` may not declare explicit parameters; (3) `Output` may not be conditional/multi-branch; (4) algorithm-level (explicit) parameters are the only explicit direct-call interface (`Algo(x) = { Output = x + 1 }` or `Algo(x) = x + 1`). Implemented in 6f1f40d.
- **Rationale:** keep `Output` a special single output slot and give an algorithm one call interface.
- **Examples:** `Algo.Output(6)` (not allowed then); `Algo = { Output(x) = x + 1 }` (not allowed then); `Algo(x) = x + 1` / `Algo(6)`.
- **Lineage:** refines #5 (explicit `Output` added); superseded by #63 (8cf85f5, 2026-07-31), which removed explicit `Output` altogether and made `Output` an ordinary identifier.
- **Classification:** PARTIALLY CURRENT *(revised in lineage review; ledger batch said SUPERSEDED)*
- **Surviving part / superseded by:** superseded by #63. Rules 1–3 are void (there is no special `Output`); rule 4 survives only trivially (an algorithm is called through its own parameter list, explicit or inferred).
- **Current evidence:** LanguageSpec case `output-is-ordinary-property` (`tests/KatLang.Tests/LanguageSpec/LanguageSpecCorpus.cs:405`, probe `Output(x) = x * 2\nOutput(4)` → 8); `EvaluatorProgramOutputTests.Eval_OutputProperty_IsOrdinary` (`EvaluatorProgramOutputTests.cs:335`); AGENTS.md "There is no output keyword; `Output` and `output` are ordinary identifiers."
- **Probe:** `Algo = {\n Output(x) = x + 1\n Output(1)\n}\nAlgo.Output(6)` → 7 (the once-forbidden form is now ordinary structural member access); `Algo(x) = x + 1\nAlgo(6)` → 7.
- **Topics:** SYN, PROP, CALL
- **Lineage review (phase 2) corrections/addenda:**
  - [output-syntax-layout] SUPERSEDED → PARTIALLY CURRENT. Evidence: Rules 1-3 (special Output) are void since #63/8cf85f5. Rule 4 ('algorithm-level explicit parameters are the only explicit direct-call interface') was hardened the same day by 9764de1 ('Disallow explicit params on no-output algorithms'); its tutorial diff directly extends #52's rule-4 paragraph. It survives unchanged as ExplicitParametersRequireOutput: Lean explicitParamsRequireOutput/validateExplicitParamOutputInvariant (lean/KatLang.lean:339, 2021-2034), C# Parser.cs:567, DiagnosticCode.ExplicitParametersRequireOutput=22, ExplicitParameterOutputValidationTests, DiagnosticCodeTests 'explicit-params-require-output'. Probe `Algo(x, y) = { Prop = 7 }` gives parseFailure ExplicitParametersRequireOutput.

### #53 — filter operation fails when arguments for filter call are received as enclosed property parameters
- **Dates:** created 2026-04-15 · closed 2026-04-15
- **Problem / question:** `filter((1, 2), {n mod 2 == 0}).count` worked, but the same call abstracted behind implicit parameters (`OccurrenceCount = filter(values, predicate).count`, `OccurrenceCount((1, 2), {n mod 2 == 0})`) failed.
- **Decision / intended invariant:** abstracting a working call over implicit parameters must not change it: a sequence-valued argument binds as one value and a block argument keeps its callable (algorithm-channel) identity when forwarded through a parameter into a higher-order builtin slot (fix b627c21 "preserve grouped higher-order argument binding").
- **Rationale:** implicit parameters are a transparent abstraction mechanism.
- **Examples:** `OccurrenceCount = filter(values, predicate).count` / `OccurrenceCount((1, 2), {n mod 2 == 0})`.
- **Lineage:** follows 58c227b (2026-04-15 nested implicit-parameter capture); sibling of #54; reaffirmed and generalized by the September 2026 forwarded-callable rule (invoking builtin slots read the parameter's algorithm channel; `ResolvedArgumentAlgorithm.invoked`) and the parameter-channel rules. The predicate's `n mod 2 == 0` is now a Boolean (#165, e4d19cc).
- **Classification:** BUG FIX / REAFFIRMED EXISTING RULE
- **Surviving part / superseded by:** the invariant survives.
- **Current evidence:** `EvaluatorHigherOrderTests.Eval_HigherOrder_SequenceValueBeforeAlgorithmOnlyArg_KeepsFilteredGroupCountAsOne` (`EvaluatorHigherOrderTests.cs:95`); spec case `forwarded-callable-keeps-its-algorithm-channel` (`LanguageSpecCorpus.cs:2597`); `ownership-and-lookup.md` § Parameter channels and shadowing; Lean `resolveArgAlgExpr` (`lean/KatLang.lean:4769`).
- **Probe:** `OccurrenceCount = filter(values, predicate).count\nOccurrenceCount((1, 2), {n mod 2 == 0})` → 1.
- **Topics:** HO, CALL, PAR, FWD

### #54 — Preserve ancestor implicit-parameter capture in nested properties, but make captured and conditional nested properties local-only
- **Dates:** created 2026-04-16 · closed 2026-04-16
- **Problem / question:** after 58c227b nested scopes capture ancestor implicit parameters; which algorithm owns such a name, and may a nested property that depends on it be accessed from outside?
- **Decision / intended invariant:** nested scopes may use ancestor parameters transitively; nearest scope wins on shadowing; in a non-conditional algorithm an identifier used in the algorithm's own top-level output belongs to that algorithm; nested properties that depend on ancestor-owned parameters are local-only (not externally accessible); properties inside conditional algorithms are local-only; no staged binding (`Algo(6).Prop`, `Outer(...).Mid(...).Inner`); consistent Lean + C# with clear diagnostics (fix 6d7617e).
- **Rationale:** a public member must not pretend to own a parameter it borrows from its owner; externally reusable behavior belongs at top level or in self-contained algorithms.
- **Examples:** valid: `Algo(x) = { Prop = x + 1\n Prop * 2 }`; invalid: `Algo = { Prop = x + 1\n x }` / `Algo.Prop`.
- **Lineage:** follows 58c227b; refined by c58ce3a (2026-06-04, public export through local helper captures), by K1-08 (7300596, 2026-09-14: selection never depends on exposure; ONE post-selection accessibility law — a member requiring ancestor-owned names is usable exactly where an activation of every required owner is lexically available, i.e. inside its owner), and by the owner walk (SYN-03, #158 / 3f57517).
- **Classification:** PARTIALLY CURRENT *(revised in lineage review; ledger batch said CURRENT)*
- **Surviving part / superseded by:** all stated points survive; K1-08 made "local-only" precise (accessible inside the owner, refused outside) and moved the check after selection.
- **Current evidence:** `ownership-and-lookup.md` § Open, exposure, and accessibility (K1-08) and § The owner walk; Lean `memberAccessible?` (`lean/KatLang.lean:2316`); C# `Evaluator.IsAccessibleFrom` (`src/KatLang/Evaluator.cs:559`); conditional message `src/KatLang/KatLangError.cs:871`; `EvaluatorHigherOrderTests.Eval_ConditionalBranchProperty_IsLocalOnly` (`:471`); `LocalMemberAccessTests`; spec cases `dot-local-only-member-outside-owner` (`LanguageSpecCorpus.cs:2106`), `open-local-only-member-inside-owner` (`:2074`); `ParameterDetectorTests.cs:115` (OccurrenceCount ancestor capture).
- **Probe:** `Algo = {\n Prop = x + 1\n x\n}\nAlgo.Prop` → LocalOnlyProperty ("local-only because it depends on parameter 'x', and a required owner activation is unavailable in this lexical context"); same with `Algo(5)` → 5; `Algo(x) = {\n Prop = x + 1\n Prop * 2\n}\nAlgo(6)` → 14; `OccurrenceCount(values, target) = filter(values, {item == target}).count\nOccurrenceCount((1, 2, 1), 1)` → 2; `F(0) = {\n P = 10\n P\n}\nF(n) = n\nF.P` → LocalOnlyProperty ("properties defined inside conditional algorithms are not publicly visible"); when only the nested property uses the name (`Algo = {\n Prop = x + 1\n Prop * 2\n}`), `x` belongs to `Prop`: `Algo(3)` → 8 and `Algo.Prop(3)` → 4; `Algo(x) = {…}\nAlgo(6).Prop` → UnresolvedImplicitParams (no staged binding: `Prop` falls back lexically and is unresolved).
- **Uncertainty:** the ownership rule "used in the algorithm's own output ⇒ owned by that algorithm" is confirmed by probes, but I did not trace the exact general formulation in `ParameterDetector` (`ShouldRewriteAsParam` / `ParameterOwnership`); reading that code would settle the precise statement.
- **Topics:** RES, PAR, PROP, PAT, MOD
- **Lineage review (phase 2) corrections/addenda:**
  - [property-caching] CURRENT; lineage lists only accessibility refinements → CURRENT; lineage addendum: since F3 (31f7c76, 2026-09-12) the local-only/exported classification also decides cache scope (per run vs per declaring-owner activation), and F3 closed an exposure hole (a MAY-selected dot fallback reading an enclosing parameter) that the cache scope would have turned into stale values. Evidence: AGENTS.md diff in 31f7c76; memory f3-zero-arg-cache-scope-law; ZeroArgPropertyCacheScopeTests.CapturedLocalProperty_IsEvaluatedOncePerActivation_NeverAcrossActivations; probe p2.
  - [open-ownership-modules] CURRENT → PARTIALLY CURRENT. Evidence: Goals survive (ancestor capture, local-only members unusable outside their owner, conditional members not exposed, no staged binding), but the mechanism was replaced by K1-08 (7300596, 2026-09-14). Before it, exposure filtered SELECTION: Lean lookupPropDefPublic? required `p.isPublic && p.exposure.isExported`, and structural access had `if !p.exposure.isExported then` error arms; 7300596 removed both. Observable changes: `Outer(n) = { Inner = { public X = n }  Inner.X }` / `Outer(4)` now gives 4 (probe k2.kat; refused before, per memory k1-08-exposure-fixed-point.md), and `open A, B` with a local-only A.X is now AmbiguousOpen where B.X used to be read (probe k1.kat).
  - [parameter-inference-grace] CURRENT → PARTIALLY CURRENT. Evidence: The intent survives: ancestor capture, nearest wins, the owner's-output rule, local-only captured members, local-only family members, no staged binding. The mechanism was replaced. 6d7617e implemented local-only as exported-only SELECTION: its Lean diff adds lookupPropDefExportedAny? filtering on p.exposure.isExported, plus lookupExportedProp. K1-08 (7300596, 2026-09-14) made selection independent of exposure and added one post-selection accessibility law (ownership-and-lookup.md § Open, exposure, and accessibility; memory k1-08-exposure-fixed-point: 'the premise ... that a local-only member is universally invisible — was itself the bug'). Behaviour changed too: Outer(n) = { Inner = { public X = n }  Inner.X } is now accessible inside its owner (probe: Outer(5) gives 5), while Outer.Inner.X gives LocalOnlyProperty.

### #56 — length is inconsistent with count on computed collections
- **Dates:** created 2026-04-16 · closed 2026-04-17
- **Problem / question:** `Sorted = List.order; Sorted.length` gave 1 while `Sorted.count` gave 3.
- **Decision / intended invariant:** rename the `length` intrinsic to `arity` = structural count of top-level output slots, keep `count` = number of top-level values the expression denotes when evaluated; keep both (`T = (1, 2, 3)`: `T.arity` 1, `T.count` 3). Implemented in 732549d.
- **Rationale:** the two notions differ; practical use of `arity` was uncertain but kept.
- **Examples:** `List = 3, 1, 2\nSorted = List.order\nSorted.count // 3`; `T = (1, 2, 3)\nT.arity // 1\nT.count // 3`.
- **Lineage:** builds on #34 (count builtin); `arity` removed entirely by #59 (04fedfe, next day); `count` later redefined as a fixed-arity collection builtin with a one-level post-binding view by #135 (0ca55e9).
- **Classification:** PARTIALLY CURRENT
- **Surviving part / superseded by:** survives: `count` gives 3 for computed collections, and the arity/count distinction survives as maintainer terminology (AGENTS.md "Builtins And Spread Conventions": "`arity` means the structural count of top-level output slots … Do not treat `arity` and `count` as interchangeable"). Superseded: the `length`/`arity` builtin (#59).
- **Current evidence:** spec `count-dotcount-agree` (`LanguageSpecCorpus.cs:2941`: `T = (1, 2, 3)\nT.count` → 3), `count-family` (`:2915`); builtin list `src/KatLang/BuiltinRegistry.cs:314-336` and Lean `BuiltinId` (`lean/KatLang.lean:448`) have no `arity`/`length`.
- **Probe:** `List = 3, 1, 2\nSorted = List.order\nList.count\nSorted.count\nSorted` → 3, 3, [1, 2, 3]; `(1, 7).arity` → UnresolvedImplicitParams.
- **Topics:** COLL, SEQ

### #57 — Decide what to do with builtins accepting list in input
- **Dates:** created 2026-04-17 · closed 2026-04-17
- **Problem / question:** `order((3, 4, 2, 1, 3, 3))` needs "ugly double braces"; should list-consuming builtins accept multiple outputs directly?
- **Decision / intended invariant:** support both `order((…))` and `order(3, 4, 2, 1, 3, 3)` in all builtins requiring a list (2f27fba, variadic builtin input).
- **Rationale:** nicer call syntax.
- **Examples:** `order((3, 4, 2, 1, 3, 3))`, `order(3, 4, 2, 1, 3, 3)`.
- **Lineage:** generalized/stressed by #58, #61, #71; removal attempted by #72 (reverted); user-level analogue #73; reversed by #135 (0ca55e9, 2026-07-17: every collection builtin takes ONE fixed `collection` argument; items are supplied only by explicit spread and re-grouping).
- **Classification:** SUPERSEDED
- **Surviving part / superseded by:** superseded by #135. Only the pre-existing grouped form survives; the inline variadic form is now an ordinary ArityMismatch (re-group spreads: `order((A*, B*))`).
- **Current evidence:** spec `builtin-fixed-collection-arity` (`LanguageSpecCorpus.cs:2967`; probe `count(1, 2, 3)` → err arity); `sequences-lists-and-calls.md` § Collection builtins; `BuiltinRegistry.cs:314-336` (`Sequence(...)` descriptors with one collection parameter).
- **Probe:** `order((3, 4, 2, 1, 3, 3))` → [1, 2, 3, 3, 3, 4]; `order(3, 4, 2, 1, 3, 3)` → ArityMismatch "Callable `order(collection)` expects 1 argument, but was called with 6 arguments."
- **Topics:** COLL, CALL, SUP
- **Lineage review (phase 2) corrections/addenda:**
  - [builtin-surface] SUPERSEDED; decision recorded as 'support both order((...)) and order(3, 4, 2, 1, 3, 3)' → SUPERSEDED; decision as implemented: variadic items per argument AND a lone grouped argument counts as ONE item (count((1, 2, 3)) = 1, order((1, 2, 3)) invalid, first((1, 2, 3)) = (1, 2, 3)), i.e. it reversed #34's one-level opening. Evidence: Tutorial at 2f27fba line 919 ('order((1, 2, 3)) ... are invalid') and line 1016 ('count((1, 2, 3)) also returns 1'); count(((1, 2), (3, 4))) example rewritten to count((1, 2), (3, 4)). The one-level opening was restored by #125 ad75720 and made principled by #135 0ca55e9. Same inaccuracy exists in variadic-forwarding.md Chain 1 step 1 and sequences-lists-values.md Chain H step 2.

### #58 — Test how unwrapping works with builtins, especially count and arity
- **Dates:** created 2026-04-17 · closed 2026-04-18
- **Problem / question:** how many levels do `count`/`arity` unwrap (`count((1, 7))`, `((1, 7)).arity`)?
- **Decision / intended invariant:** (c9a43fa) `count((1, 7))` → 1 and `((1, 7)).arity` → 1 (extra parenthesized layers preserved; no auto-unwrap of double-paren receivers or named grouped helpers); dot-call sequence-builtin receivers routed through the same algorithm-argument path as plain calls; `:` projects the selected item's content one level; filter/map/reduce callback items bound by the same `S:i`-style one-level projection.
- **Rationale:** one shared one-level projection model for receivers, selection and callbacks across Lean and C#.
- **Examples:** `count((1, 7)) // 1 after fix`; `count(Data) // 2` with `Data = 1, 7`; `((1, 7)).arity // 1`.
- **Lineage:** follows #56/#57; regression fixed by #60; arity removed by #59; count result reversed by #135 (fixed collection + `builtinCollectionItems` one-level view); double-paren preservation reversed by #168 (50c74c1, redundant parentheses are syntax); selection projection reversed by "selection is a value boundary" (#167, 874625a); callback projection replaced by the callback law (5d6d60b / 702e7d7).
- **Classification:** SUPERSEDED
- **Surviving part / superseded by:** only the principle "the dotted spelling goes through the same call path as the plain call" survives (now: dot-call passes the receiver as an ordinary leading argument through ONE funnel). Every concrete result is reversed: `count((1, 7))` is 2, `((1, 7))` ≡ `(1, 7)`, `:` returns the stored element as ONE value, callbacks bind each element as one ordinary argument.
- **Current evidence:** spec `count-family` (`:2915`), `parentheses-group-syntax` (`:1314`), `index-selects-one-value` (`:3054`), `callback-element-is-one-argument` (`:1293`); Lean `builtinCollectionItems` (`KatLang.lean:2665`), `select?` (`:1344`) with `select_is_stored_element` (`lean/KatLangArityLaws.lean:1118`); `RedundantParenthesesTransparencyTests`, `SelectionValueBoundaryTests`.
- **Probe:** `count((1, 7))` → 2; `Data = 1, 7\n((1, 7)).count` → 2; `Data.count` → 2; `count(1, 7)` → ArityMismatch; `S = ((1, 2), 3)\nS:0` → (1, 2) (one value, not projected content).
- **Topics:** COLL, SEQ, DOT, HO, VAL
- **Lineage review (phase 2) corrections/addenda:**
  - [calls-arguments] Lineage omits the March rule it reversed; #143 lineage omits Track D's 'PERMANENT' capture policies → Record c647330 (2026-03-22: '((expr)) is equivalent to (expr) in all positions') as the rule #58/c9a43fa reversed and #168/50c74c1 restored; record Track D (bundled in 7075071) as declaring (Obj).V capture suppression and open (M) rejection permanent, both reversed by 50c74c1 (no classification change). Evidence: git show -s c647330 (message: 'Ordinary parentheses now always mean ordinary grouping — ((expr)) is equivalent to (expr) in all positions'); git show -s c9a43fa ('preserve extra parenthesized grouped receiver layers instead of auto-unwrapping ... double-paren receivers'); memory track-d-boundary-policies.md ('D4: (Obj).V/((Obj)).V capture-receiver suppression PERMANENT', 'D1 open (M) REJECTED'); current probe open (M) -> 5, (Obj).V -> 5.

### #59 — Investigate if arity should be made full citizen of KatLang builtins
- **Dates:** created 2026-04-17 · closed 2026-04-18
- **Problem / question:** `arity` was a special intrinsic property usable only as `(...).arity`, not `arity(...)`.
- **Decision / intended invariant:** remove `arity` from KatLang completely (04fedfe) so no builtin receives special treatment.
- **Rationale:** it behaved like `count` where it worked and was the only special-cased builtin.
- **Examples:** `(...).arity` (removed); `arity(...)` never supported.
- **Lineage:** removes what #56 introduced; the "no specially treated builtins" direction is reaffirmed by SYN-05 / #159 (0243678: builtins are ordinary prelude bindings, identity not spelling).
- **Classification:** CURRENT
- **Surviving part / superseded by:** whole decision survives.
- **Current evidence:** `BuiltinRegistry.cs:314-336` and Lean `BuiltinId` (`KatLang.lean:448`) contain no `arity`; AGENTS.md BUILTIN CALLABLES ARE ORDINARY PRELUDE BINDINGS; `ownership-and-lookup.md` § Builtin identity and the zero-argument value demand.
- **Probe:** `(1, 7).arity` and `((1, 7)).arity` → UnresolvedImplicitParams ("Identifier 'arity' does not resolve …").
- **Topics:** COLL, RES
- **Lineage review (phase 2) corrections/addenda:**
  - [builtin-surface] CURRENT; 'whole decision survives' → CURRENT; removal survives but the premise 'no specially treated builtins' does not fully hold. Evidence: .string (6869338, 2026-04-06, predating #59) is a dot-only spelling-dispatched intrinsic that beats even a declared structural member: probe A = { string = 7 / 5 } ; A.string -> '5'; Lean evalDotCallCounted checks name = "string" at KatLang.lean:6472 before structural lookup at :6495; string(5) -> UnresolvedImplicitParams.

### #60 — Regression related to group unwrapping
- **Dates:** created 2026-04-18 · closed 2026-04-18
- **Problem / question:** `Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)`: `(Data:0).count` and `Data:0.count` returned 1.
- **Decision / intended invariant:** counting a selected sequence counts its members: 5 (fix 22788b9).
- **Rationale:** regression of #58's receiver refactoring.
- **Examples:** `(Data:0).count // expected 5`.
- **Lineage:** regression of #58 (c9a43fa); today's mechanism differs (selection returns the stored element as one value — #167 874625a; `count` opens its one bound collection one level — #135) but the observable result is the same.
- **Classification:** BUG FIX / REAFFIRMED EXISTING RULE
- **Surviving part / superseded by:** observable rule survives with a different mechanism.
- **Current evidence:** spec `count-family` (`LanguageSpecCorpus.cs:2915`) contains exactly `Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)\n(Data:0).count` → 5; spec `index-selects-one-value` (`:3054`, probe `(Pairs:0).count` → 2); `sequences-lists-and-calls.md` § Value boundaries.
- **Probe:** `(Data:0).count` → 5; `Data:0.count` → 5.
- **Topics:** SEQ, COLL, DOT

### #61 — Passing an expression as an argument should not implicitly spread its emitted values into the surrounding sequence
- **Dates:** created 2026-04-19 · closed 2026-04-19
- **Problem / question:** `contains(3, 4, range(1, 5), 7, 5)` returned 1 and `filter(1, 2, range(3, 6), IsEven)` returned 2, 4, 6 although `List = 3, 4, range(1, 5), 7` keeps `range(1, 5)` as one slot.
- **Decision / intended invariant:** "passing an expression as an argument does not implicitly spread its emitted values into the surrounding sequence"; spreading must be explicit (then only via the `;` combining operator: `List = 3; 4; range(1, 5); 7`). Fix 17e34bd.
- **Rationale:** argument boundaries must follow the written comma structure.
- **Examples:** `contains(3, 4, range(1, 5), 7, 5)`; `List = 3; 4; range(1, 5); 7` (current equivalent: `List = 3, 4, range(1, 5)*, 7`).
- **Lineage:** refines #57; extended to all sequence builtins by #71; continued by #101 (no implicit final-argument unpacking in flat fixed calls), #103/#104 (explicit `...` supply), #125 (`;` removed), #132 (call boundaries return one value), #135 (fixed collection builtins), #140 (postfix `*` spread), and generalized to every receiver by "values stay values" (#167 / 702e7d7).
- **Classification:** PARTIALLY CURRENT
- **Surviving part / superseded by:** the core invariant survives in strengthened form: every non-spread argument slot is exactly ONE item and only the postfix spread marker `expr*` opens a value. Superseded: `;` as the explicit spreading mechanism (removed #125, replaced by `*` #140); the variadic builtin forms in the examples are now arity errors (#135).
- **Current evidence:** `sequences-lists-and-calls.md` § Call argument assembly and written-slot reification; Lean `collectVariadicCallItems` (`KatLang.lean:6020`); C# `BuildCallArgumentInputs` (`src/KatLang/Evaluator.ParameterBinding.cs:1549`); spec `fixed-call-preserves-boundaries` (`:775`), `values-stay-values` (`:1260`); theorem `receivers_never_same_on_lone_seq` (`lean/CoreArityAlgebraProofs.lean:1289`).
- **Probe:** `List = 3, 4, range(1, 5), 7\nList\ncontains(List, 5)\n(3, 4, range(1, 5), 7).contains(5)` → (3, 4, [1, 2, 3, 4, 5], 7), false, false; `contains(3, 4, range(1, 5), 7, 5)` → ArityMismatch (`contains(collection, item)` expects 2, got 5); `filter(1, 2, range(3, 6), IsEven)` → ArityMismatch; translated `List = 3, 4, range(1, 5)*, 7` → (3, 4, 1, 2, 3, 4, 5, 7) and `contains(List, 5)` → true.
- **Topics:** SUP, CALL, COLL, SEQ

### #62 — Think about improving combining operator performance by moving its processing to lexer when possible
- **Classification:** IMPLEMENTATION ONLY — performance/stack-safety of the `;` combine evaluator (d53eec8 made combine evaluation stack-safe in evaluator + Lean; the lexer idea was not adopted); the `;` operator itself was later removed (#125, ad75720; `A = 1; 2` → parse error UnsupportedSemicolon).
- **Topics:** SYN, RUN

### #63 — Research if explicit Output is still needed
- **Dates:** created 2026-04-19 · closed 2026-07-31
- **Problem / question:** is `Output = …` still needed now that output rows may appear anywhere in a body?
- **Decision / intended invariant:** remove explicit `Output = ...`; one output model: every non-definition expression row contributes to the algorithm's output, rows may interleave with property definitions; `Output` is no longer reserved and is an ordinary identifier (8cf85f5).
- **Rationale:** explicit output added no capability once implicit output was no longer restricted to the final expression; it only brought a second syntax with special rules.
- **Examples:** `Output = 5\nOutput` → 5; `A = 3\nOutput = A + 2` → no output.
- **Lineage:** reverses #5 (explicit Output added) and supersedes #52; related SYN-12 tutorial pins.
- **Classification:** CURRENT
- **Surviving part / superseded by:** whole decision survives.
- **Current evidence:** AGENTS.md "Algorithm output is written as expression rows … There is no output keyword"; `KatLang.ebnf:13,169` (`OutputLine = OutputBundle`, no Output keyword); spec `output-is-ordinary-property` (`LanguageSpecCorpus.cs:405`), `output-rows-interleave-definitions` (`:3156`); `EvaluatorProgramOutputTests.Eval_OutputProperty_IsOrdinary` (`:335`); `ParserTests.cs:4187` section.
- **Probe:** `Algo = {\n Output = 5\n}\nAlgo` → MissingOutput ("Property 'Algo' has no defined output"); `Algo = {\n Output = 5\n Output + 1\n}\nAlgo\nAlgo.Output` → 6, 5.
- **Topics:** SYN, PROP

### #65 — Improve error reporting for reduce builtin call with less arguments than required
- **Classification:** SUPERSEDED — diagnostic fix (4e19be6) for the variadic-`reduce` era; since #135 `reduce(collection, reducer, initial)` is fixed-arity and `reduce(1, 2, 3, Add)` is the ordinary ArityMismatch "Callable `reduce(collection, reducer, initial)` expects 3 arguments, but was called with 4 arguments" (probed; `reduce((1, 2, 3), Add, 0)` with `Add = x + total` → 6).
- **Topics:** TOOL, COLL
- **Lineage review (phase 2) corrections/addenda:**
  - [builtin-surface] SUPERSEDED (no superseding commit named) → SUPERSEDED by 68b3607 (2026-09-21). Evidence: The dotted-reduce hint ReduceInitialAccumulatorRequiresValueError introduced by 4e19be6 was deleted by 68b3607 (git log -S shows the removal; SEMANTIC-ALIGNMENT.md:336 lists 'the dot-only reduce initial-accumulator hint' among DELETED items). Also resolves the UNCERTAIN note in ledger #135 about which commit removed the hint.

### #66 — Introduce shared AST walker and small reusable helpers in C# front-end passes
- **Classification:** IMPLEMENTATION ONLY — C# refactoring (e36f758); `src/KatLang/AstWalker.cs` still exists and is the runtime-guarded statement-form walk named in AGENTS.md § Traversal exhaustiveness.
- **Topics:** TOOL

### #67 — Make the C# front-end/elaboration boundary explicit
- **Classification:** HOST/API ONLY — separated raw syntax parsing from elaboration (a8ba1ff, `FrontEndPipeline`); current form: `Parser.Parse`/`KatLangEngine` are the complete pipeline, the stages (`Parser.ParseSyntax`, `ParameterDetector`, …) are internal (`evaluator-and-hosting.md` § Elaboration boundary; `FrontEndElaborationBoundaryTests`, `PublicElaborationSurfaceTests`; tightened by the public API audit #11, 3613d58).
- **Topics:** API, TOOL

### #68 — Replace string-based evaluator error context with structured error context
- **Classification:** HOST/API ONLY — diagnostics carried as typed data instead of prose (b062fdd); today `ErrorContext` is a public closed record hierarchy (`src/KatLang/ErrorContext.cs:21`) with `EvalError.WithContext`, per AGENTS.md § Traversal exhaustiveness. No language-semantic content.
- **Topics:** TOOL, API

### #69 — Bug sum(P) and sum(range(1, 100)) is failing
- **Dates:** created 2026-04-22 · closed 2026-04-23
- **Problem / question:** `P = range(1, 100)`; `sum(P)` and `sum(range(1, 100))` failed ("item 0 was grouped value"), while `P.sum` worked; "affects all builtins".
- **Decision / intended invariant:** a collection builtin must consume a named or call-produced collection argument; plain-call and dot-call spellings agree (fix d3ee6d7 "plain-call sequence builtin inputs").
- **Rationale:** `f(x)` ≡ `x.f`.
- **Examples:** `P = range(1, 100)\nF = sum(P) + x\nF(1)`; `sum(range(1, 100))`.
- **Lineage:** d3ee6d7 triggered the #71 debate (it made builtins open each argument's content); mechanism now: #135 fixed `collection` parameter + one-level post-binding view (`builtinCollectionItems`); range returns an exact list (#135).
- **Classification:** BUG FIX / REAFFIRMED EXISTING RULE
- **Surviving part / superseded by:** observable behavior survives; mechanism replaced by #135.
- **Current evidence:** spec `sum-of-range-collection` (`LanguageSpecCorpus.cs:2899`: `sum(range(1, 3))` → 6, `sum(range(1, 3)*)` → err arity); Lean `builtinCollectionItems` (`KatLang.lean:2665`); C# `BuiltinCollectionItems` (`Evaluator.ParameterBinding.cs:1663`).
- **Probe:** `P = range(1, 100)\nF = sum(P) + x\nF(1)` → 5051; `sum(range(1, 100))` → 5050.
- **Topics:** COLL, CALL, DOT

### #70 — Grouping in conditional algorithm is broken
- **Dates:** created 2026-04-23 · closed 2026-04-23
- **Problem / question:** `MarkGroupedRange((a, b, c)) = 1` / `MarkGroupedRange(x) = 0` was rejected: "branches must have the same top-level pattern arity. Expected 3 … branch 2 has arity 1".
- **Decision / intended invariant:** a nested sequence-value pattern occupies ONE top-level slot; the clause-family arity check counts top-level patterns, not the inner group's members (fix fe1e3fb).
- **Rationale:** follows the #24 rule (all branches share top-level pattern arity) applied correctly.
- **Examples:** `MarkGroupedRange((a, b, c)) = 1\nMarkGroupedRange(x) = 0\nMarkGroupedRange(5)`.
- **Lineage:** corrects the application of #24; later generalized by #99 (recursive parameter patterns, af92bad) and the per-level arity facts (`ParameterPattern.MinimumSuppliedSlots`, F4, Sep 2026); lists do not match sequence-value clauses (#134/#135 era).
- **Classification:** CURRENT *(revised in lineage review; ledger batch said BUG FIX / REAFFIRMED EXISTING RULE)*
- **Surviving part / superseded by:** survives.
- **Current evidence:** spec `conditional-clauses-share-top-level-arity` (`LanguageSpecCorpus.cs:1702`) and `conditional-sequence-pattern-matches-sequence-values-only` (`:1682`); `EvaluatorHigherOrderTests.Eval_ClauseGroup_DoubleParenSequenceValuePattern_MatchesSingleBinderArity` (`:588`, the renamed issue example) plus the list fall-through/spread-match siblings (`:599`, `:614`); Lean `matchCallBranches` (`KatLang.lean:3726`).
- **Probe:** `MarkGroupedRange(5)` → 0; `MarkGroupedRange((1, 2, 3))` → 1.
- **Topics:** PAT, CALL
- **Lineage review (phase 2) corrections/addenda:**
  - [conditional-patterns] BUG FIX / REAFFIRMED EXISTING RULE → CURRENT. Evidence: fe1e3fb introduced still-current rules rather than only fixing the arity count: pattern parentheses structural at every nesting level (Parser.cs diff '(x) -> Group([x]); ((a, b)) -> Group([Group([a, b])])') and family heads matched against EXPLICIT argument slots (matchCallPattern docstring, KatLang.lean:3698ff), replacing #16's normalized-shape matching under which F(n) absorbed F(1, 2); pinned by spec conditional-clause-head-rejects-extra-arguments (bb43c8a). Note its own guard test151oa (M(range(1,3)) -> 1) was later flipped to 0 by #135 (lean/CoreTests/CollectionBuiltins.lean:1493-1505).

### #71 — Sequence builtins should preserve comma argument boundaries and flatten only via explicit combining operator usage ';'
- **Dates:** created 2026-04-23 · closed 2026-04-23
- **Problem / question:** `filter(1, 2, range(3, 6), {x mod 2 == 0})` gave 2, 4, 6: variadic builtins silently unfolded each argument's emitted items although `1, 2, range(3, 6)` keeps three slots.
- **Decision / intended invariant:** after first calling it "not a bug" (sequence operations and indexing are content-based), the maintainer set the rule: "comma separates output slots. Sequence-producing expressions occupy one output slot and may return their result in grouped form. Sequence-oriented operations and index access are content-based consumers: they operate on the top-level content of such a result rather than on its grouping wrapper." So `filter(1, 2, range(3, 6), …)` → 2; flattening only by explicit `;` (`filter(1; 2; range(3, 6), …)` → 2, 4, 6). Fix c876d28.
- **Rationale:** behavior must be predictable from syntax; grouped items in scalar builtins should error rather than silently flatten.
- **Examples:** `count(1, 2, range(3, 6)) // 3`; `count(1; 2; range(3, 6)) // 6`; `sum(1; 2; range(3, 6)) // 21`. Current equivalents: `count((1, 2, range(3, 6)))`, `count((1, 2, range(3, 6)*))`, `sum((1, 2, range(3, 6)*))`.
- **Lineage:** extends #61 to all sequence builtins; responds to d3ee6d7 (#69); triggers #72; `;` replaced by `...` (#104, 0e9b41f) then removed (#125, ad75720) with `*` spread (#140); builtin variadics replaced by one fixed collection (#135); "index returns content" replaced by "selection chooses a value" (#167, 874625a).
- **Classification:** PARTIALLY CURRENT
- **Surviving part / superseded by:** survives: comma separates slots; a sequence-producing expression occupies one slot and is one value; no builtin silently unfolds an ordinary argument; flattening only by an explicit operator; collection builtins read their (one) bound collection one level ("content-based"); indexing reads its TARGET's positions; grouped items in `sum` are a clear error. Superseded: `;` (now postfix `*`); the variadic builtin call forms (now arity errors, #135); "index returns the content of the selected item rather than its wrapper" (selection now returns the stored element as ONE value).
- **Current evidence:** `sequences-lists-and-calls.md` § Collection builtins, § Value boundaries, § Call argument assembly; Lean `builtinCollectionItems` (`:2665`), `projectionItems` (`:1327`), `select?` (`:1344`); spec `count-family` (`:2915`), `builtin-fixed-collection-arity` (`:2967`), `index-selects-one-value` (`:3054`).
- **Probe:** `1, 2, range(3, 6)` → 1, 2, [3, 4, 5, 6]; `filter((1, 2, range(3, 6)*), {x mod 2 == 0})` → [2, 4, 6]; `count((1, 2, range(3, 6)))` → 3; `count((1, 2, range(3, 6)*))` → 6; `sum((1, 2, range(3, 6)*))` → 21; `filter((1, 2, range(3, 6)), {x mod 2 == 0})` → TypeMismatch on the list element; `sum((1, 2, range(3, 6)))` → ArityMismatch "item 2 was list value".
- **Topics:** SUP, COLL, SEQ, SYN

### #72 — Remove support of variadic parameters
- **Dates:** created 2026-04-23 · closed 2026-04-23
- **Problem / question:** with variadic builtins, `,` and `;` became confusing (`count(range(1, 3), 4)` and `count(range(1, 3); 4)` both 4).
- **Decision / intended invariant:** remove builtin variadic parameters (f2898cb, 2026-04-23) — REVERTED the next day (4367f57) because `(1, 2, 3, 4).sum` worked while `sum(1, 2, 3, 4)` needed `sum(1; 2; 3; 4)`; the maintainer chose to keep variadics and make them a general language feature (→ #73), rejecting a first-class sequence type ("[ ] would basically be syntax sugar for (( ))").
- **Rationale:** symmetry of `f(x)` and `x.f`; avoiding a separate sequence type that "starts breaking other KatLang areas".
- **Examples:** `count(range(1, 3), 4)`; `(1, 2, 3, 4).sum` vs `sum(1, 2, 3, 4)`.
- **Lineage:** reacts to #71; reverted → #73. The END STATE it wanted (non-variadic builtins) was later reached by #135 (0ca55e9) under the opposite design the revert had rejected: first-class sequence values (#132), `[]` lists (#134), one fixed collection argument, and symmetry restored by "dot-call passes a value" (`(1, 2, 3, 4).sum` ≡ `sum((1, 2, 3, 4))`, 68b3607).
- **Classification:** SUPERSEDED
- **Surviving part / superseded by:** the removal was reverted (4367f57); builtin shape now set by #135; user variadics survive as collecting parameters (#73 → #140).
- **Current evidence:** spec `builtin-fixed-collection-arity` (`:2967`), `dot-receiver-passes-a-value` (`:1220`); `sequences-lists-and-calls.md` § Collection builtins, § The dot-call receiver.
- **Probe:** `(1, 2, 3, 4).sum\nsum((1, 2, 3, 4))` → 10, 10; `sum(1, 2, 3, 4)` → ArityMismatch; `count(range(1, 3), 4)` → ArityMismatch; `count((range(1, 3), 4))` → 2; `count((range(1, 3)*, 4))` → 4.
- **Topics:** VAR, COLL, SUP, DOT

### #73 — Research how to add variadic parameter as KatLang feature
- **Dates:** created 2026-04-24 · closed 2026-05-04
- **Problem / question:** variadic parameters existed only as a builtin special case; make them a user-level feature without breaking other areas.
- **Decision / intended invariant:** (3bc2a29) `name...` captures zero or more top-level items at call binding; fixed parameters before it bind from the front, after it from the back, it takes the middle; nested groups preserved (no recursive flattening, unlike `atoms`); ordinary parameters unchanged; at most one per explicit list; any position; explicit only (never inferred); no `~` reordering; not allowed in explicit `Output`; parser diagnostics for `Bad(a..., b...)` and `Bad(a~...)`.
- **Rationale:** the only design found that makes `(1, 2, 3, …).Something` and `Something(1, 2, 3, …)` agree within the existing rules (a separate sequence type and ad-hoc `if`s were tried and drifted); syntax alternatives `[ ]` and `params` rejected.
- **Examples:** `Arg = 1, 2, 3\nGroup(list...) = list\nArg.Group.count // 3`; `Scale(values..., factor) = values.map{n * factor}\nArg.Scale(10) // 10, 20, 30`. Current equivalents: `Group(*list) = list` with `Arg*.Group.count` → 3; `Scale(*values, factor) = …` with `Arg*.Scale(10)` → [10, 20, 30].
- **Lineage:** follows #72/#57; commenters propose `unwrap` → #91 `ungroup` → #98 `content` → removed #129; refined by #88, #89, #99 (variadic group destructuring in patterns), #102 (variadic reduce accumulator), #105/#106/#108/#111/#112 (receiver/forwarding regressions), #126 (movable-rest deconstruction); result kind changed to exact list by #138 (ab7d2f5); syntax replaced by prefix `...name` (#139, eab2468) then `*name` (#140, 73648e9); receiver supply fixed by #144 then reversed by #167 C-full "values stay values" (702e7d7).
- **Classification:** PARTIALLY CURRENT
- **Surviving part / superseded by:** survives: one collecting parameter per pattern level; front/back fixed allocation first, collector takes the (possibly empty) middle; nested structure preserved; ordinary parameters unchanged; collecting bindings cannot take `~`. Superseded: syntax `name...` → `*name` (#139/#140); collected value is an exact list (#138); a lone sequence argument/receiver is ONE collected item — so `Arg.Group.count` is now 1, not 3 (exact collector law, #167/702e7d7); "explicit only" narrowed — an alias of a collecting callable elaborates to an inferred collecting parameter (`Alias = Cnt` ⇒ `Alias(*xs) = Cnt(xs*)`); the `Output` restriction is moot (#63).
- **Current evidence:** `tutorial.md:1326-1413` § Collecting Parameters; `sequences-lists-and-calls.md` § Collecting parameters and § Collecting parameter lists; `Parser.cs:3006` ("Only one collecting binding is allowed per pattern level."), `Parser.cs:3270` ("Collecting bindings cannot use `~` reordering."); Lean `collectSegment` (`KatLang.lean:2889`), `bindParameterPatternList` (`:4933`); C# `CollectSegment` (`Evaluator.ParameterBinding.cs:561`); laws `collector_lone_sequence_is_one_item` (`KatLangArityLaws.lean:592`), `collector_collects_spread_items_exactly` (`:644`); spec `variadic-grouped-and-spread` (`:1102`), `values-stay-values` (`:1260`), `mixed-collecting-parameter` (`:1349`); `EvaluatorCollectingParameterTests.Eval_CollectingParameter_BeforeSuffix_SupportsSequenceStyleScale` (`:156`).
- **Probe:** (translated `x...` → `*x`) `Arg = 1, 2, 3\nGroup(*list) = list\nArg.Group.count\nArg*.Group.count\nGroup(Arg)\nGroup(Arg*)` → 1, 3, [(1, 2, 3)], [1, 2, 3]; `Arg*.Scale(10)` → [10, 20, 30]; `Arg.Scale(10)` → TypeMismatch (`values` = [(1, 2, 3)]); `Arg = (1, 2), (3, 4)`: `Arg*.Group.count` → 2, `atoms(Arg*.Group).count` → 4; `Bad(*a, *b) = b` → InvalidCollectingBinding; `Bad(*a~) = a` → InvalidGraceMarker "Collecting bindings cannot use `~` reordering."; `F(x, *middle, z) = middle`: `F(0, 1, 2, 3)` → [1, 2], `F(0, 3)` → []; comment-8 `Error = list.sum / list.count\nError(range(1, 3))` → 2 (was a Bad-arity error in the issue's era); `CorrectedError(*list) = …`: `CorrectedError(Arg*)` → 2, `CorrectedError(Arg)` → ArityMismatch; `Cnt(*xs) = xs.count\nAlias = Cnt\nAlias()\nAlias((1, 2))\nAlias(1, 2, 3, 4)` → 0, 1, 4.
- **Topics:** VAR, PAR, CALL, DOT, FWD, SYN

### #74 — Fix Extension property call (dot-call) receiver boundary semantics
- **Dates:** created 2026-04-25 · closed 2026-04-25
- **Problem / question:** with `F = a + b`, `(3).F(7)` is fine but `(3, 7).F` also worked — a grouped receiver satisfied two fixed parameters.
- **Decision / intended invariant:** a dot-call receiver is ONE leading argument; a grouped multi-item receiver must not fill several fixed parameters ("this behaviour is reserved for variadic parameters for sequence builtins"). Fix b3af83b.
- **Rationale:** `R.F(args)` should mean `F(R, args)`.
- **Examples:** `(3).F(7)` ok; `(3, 7).F` should fail.
- **Lineage:** related #14 (dot-call on constants); receiver exceptions for variadics added by #89 (5cf09fc) and #144 (f12af0f, receiver segment feeds a collecting parameter its items), aligned with plain calls by #112 (4685ba0); #147/#162 (resolution); the variadic carve-out was reversed by #167 (68b3607, 702e7d7): "dot-call passes a value" for every callee shape.
- **Classification:** PARTIALLY CURRENT *(revised in lineage review; ledger batch said CURRENT)*
- **Surviving part / superseded by:** the fixed-parameter rule survives and is now universal; the "reserved for variadic parameters" carve-out did not survive (collecting parameters also collect the receiver as ONE item; only `R*.F` opens it).
- **Current evidence:** `sequences-lists-and-calls.md` § The dot-call receiver; Lean `prepareLexicalDotCallArgs` (`KatLang.lean:4337`); laws `dot_receiver_is_ordinary_leading_argument` (`KatLangArityLaws.lean:485`), `dot_receiver_fixed_binds_value` (`:545`), `dot_receiver_count_never_satisfies_arity` (`:564`); C# `BuildLexicalReceiverCallArgs` (`src/KatLang/Evaluator.DotCalls.cs:51`); spec `dot-receiver-passes-a-value` (`:1220`); `DotCallValueBoundaryTests`, `DotCallCollectingReceiverTests`.
- **Probe:** `F = a + b\n(3).F(7)\n(3, 7)*.F` → 10, 10; `(3, 7).F` → ArityMismatch "Callable `F(a, b)` expects 2 arguments, but was called with 1 argument." (all five paths); `TotalWithFee(*values, fee) = values.sum + fee`: `(10, 20, 30).TotalWithFee(5)` → ArityMismatch inside `sum` (values = [(10, 20, 30)]), while `(10, 20, 30)*.TotalWithFee(5)` → 65 (probed, all five paths agree; also pinned by `EvaluatorCollectingParameterTests.Eval_CollectingParameter_InlineSequenceSpreadDotCallWithSuffixSuppliesReceiverItems`).
- **Topics:** DOT, CALL, VAR
- **Lineage review (phase 2) corrections/addenda:**
  - [dot-call] CURRENT → PARTIALLY CURRENT. Evidence: The decision included the carve-out 'reserved for variadic parameters for sequence builtins', which b3af83b wrote into AGENTS ('Only sequence/variadic builtin dot-call paths may opt into receiver top-level expansion'). Pickaxe shows that bullet was added in b3af83b and deleted in 68b3607. The preserveArgBoundaries mechanism was replaced in f12af0f and deleted in 68b3607, and #135 removed variadic builtin parameters. Probe p01 shows (1, 2).Coll -> [(1, 2)]. The ledger's own surviving-part text already says the carve-out did not survive.

### #75 — Redesign combining ';' operator to 'result join' operator
- **Dates:** created 2026-04-26 · closed 2026-04-26
- **Problem / question:** `A = 1, 2; F = a; 3; A.F` gave `(1, 2), 3` instead of `1, 2, 3`.
- **Decision / intended invariant:** `;` is the result join operator: evaluates both sides and joins their immediate results at the current output level; creates no new group, merges no properties, does not recursively flatten nested groups; a side with no output is an error; comma separates syntactically, semicolon joins semantically (23d9a0c).
- **Rationale:** separate syntactic slot separation from semantic result joining.
- **Examples:** `A = 1, 2\nF = a; 3\nA.F // 1, 2, 3`. Current equivalent: `F = a*, 3`.
- **Lineage:** successor of #2 (combining operator); stack-safety #62; replaced by the `...` sequence-supply/join operator (#104, 0e9b41f); `;` briefly returned as output join (#122, acbfa7d); `;` removed from expression syntax (#125, ad75720); `...` → postfix `*` spread (#139, #140).
- **Classification:** SUPERSEDED
- **Surviving part / superseded by:** superseded by #104 → #125 → #140. Surviving ideas, now carried by the spread marker: opening is exactly ONE level (never recursive); an operand with no output is an error (`SpreadMissingOutput`), while `()*` legitimately supplies nothing; comma is purely structural.
- **Current evidence:** `Parser.cs:1638` `UnsupportedSemicolonExpressionMessage`; `DiagnosticCode.UnsupportedSemicolon` (`DiagnosticCode.cs:54`); `KatLang.ebnf:187,272`; spec `semicolon-not-expression-syntax` (`LanguageSpecCorpus.cs:3172`), `spread-one-level-only` (`:1873`); `sequences-lists-and-calls.md` § Spread semantics; Lean `spreadItems` (`KatLang.lean:1273`).
- **Probe:** `A = 1, 2\nF = a*, 3\nA.F` → (1, 2, 3) (one sequence value); `F = a, 3` → ((1, 2), 3); `A = 1; 2` → parse UnsupportedSemicolon; `E = {}\n(E*, 3)` → SpreadMissingOutput; `(()*, 3)` → 3.
- **Topics:** SYN, SUP, SEQ
- **Lineage review (phase 2) corrections/addenda:**
  - [supply-spread] lineage: '`;` briefly returned as output join (#122, acbfa7d)' → `;` returned as the output join in 7b5fe7a (2026-06-10, Expr.OutputJoin added). 65301ce (2026-06-11) made it flatten streams with comma priority. acbfa7d (2026-06-11) finalized parsing and display. Classification SUPERSEDED unchanged.. Evidence: `git log -S` / `git show 7b5fe7a -- lean/KatLang.lean` adds `| outputJoin : Expr -> Expr -> Expr`. The 65301ce subject is 'Fix semicolon output-join to flatten streams and prioritize comma'. The acbfa7d diff introduces no outputJoin constructor.

### #76 — Bug: count fails on empty sequence
- **Dates:** created 2026-04-26 · closed 2026-04-26
- **Problem / question:** `(1,5,3).filter{n mod 2 == 0}.count` failed ("Expected 0 parameters, but was called with 0 arguments") — an empty dot-call receiver was treated as zero supplied arguments; check all sequence builtins on empty input.
- **Decision / intended invariant:** an empty result is still one receiver/argument; `count` of an empty collection is 0 (fix 315dd54 "empty sequence dot-call receiver boundary").
- **Rationale:** emptiness of a value must not be confused with absence of an argument.
- **Examples:** `(1,5,3).filter{n mod 2 == 0}.count // 0`.
- **Lineage:** related #81 (empty result definition), #128 (empty sequence representation); `filter` returns `[]` since #135; generalized by "a `()` value's valueCount of zero is NEVER an implicit zero-argument supply" (§ The dot-call receiver) and F5 (output-less written argument ≠ omitted argument).
- **Classification:** BUG FIX / REAFFIRMED EXISTING RULE
- **Surviving part / superseded by:** survives.
- **Current evidence:** `EvaluatorCollectionBuiltinTests.Eval_Count_DotCall_EmptyFilterReceiver_ReturnsZero` (`:200`) and siblings (`:211`, sum/first/last at `:228-233`); spec `filter-none-empty` (`LanguageSpecCorpus.cs:2466`), `empty-count-one-arg` (`:808`); `sequences-lists-and-calls.md` § The dot-call receiver ("`().Coll` collects the one visible `()`; only `()*` supplies nothing").
- **Probe:** `(1, 5, 3).filter{n mod 2 == 0}.count\n(1, 5, 3).filter{n mod 2 == 0}` → 0, [].
- **Topics:** COLL, DOT, VAL
- **Lineage review (phase 2) corrections/addenda:**
  - [dot-call] BUG FIX / REAFFIRMED EXISTING RULE (lineage omits the interruption) → BUG FIX / REAFFIRMED EXISTING RULE (+ lineage: temporarily reversed for collectors by #144 f12af0f 2026-08-11, restored by 68b3607 2026-09-21). Evidence: Memory dot-receiver-segment-supply (#144) records '().Collect supplies zero items' and 'V = () -> V.Collect = []'. 68b3607 restored the rule ('a () value's valueCount of zero is NEVER an implicit zero-argument supply', sequences-lists-and-calls.md § The dot-call receiver). Classification is unchanged; only the lineage is incomplete.

### #77 — Feature: Random Integer and Random Float
- **Dates:** created 2026-04-27 · closed 2026-05-13
- **Problem / question:** add random numbers (Perl-like `Math.Rand` in [0, 1); Python-like `Math.RandInt(a, b)` inclusive, `Math.RandFloat(a, b)`).
- **Decision / intended invariant:** `Math.Rand` and `Math.RandInt` added (238ff20, via PR #107).
- **Rationale:** testing and pseudorandom algorithms.
- **Examples:** `Math.Rand`, `Math.RandInt(a, b)`.
- **Lineage:** re-specified by #109 (489b77f: `RandInt` → `RandomInt(start, end)`, half-open [start, end), whole-number bounds required); zero-parameter `Math.Rand` replaced by parameterized `Math.Random(start, end)` (#110 discussion; zero-arg cache semantics moved into Lean, d843523); lowercase aliases `random`/`randomInt` (#154, b3738b9); run-scoped seedable stream (668ff3c, 2026-09-14; CLI `--random-seed`, 5753e84).
- **Classification:** PARTIALLY CURRENT
- **Surviving part / superseded by:** survives: KatLang has a random decimal and a random integer operation in `Math`. Superseded: names (`Rand`/`RandInt` gone), `RandInt` inclusive upper bound (now half-open), zero-argument `Math.Rand` (now `Math.Random(start, end)`), unseeded ambient generator (now one run-scoped SplitMix64 stream, host-seedable).
- **Current evidence:** `src/KatLang/BuiltinRegistry.cs:372-373` (`Random`/`random`, `RandomInt`/`randomInt`, parameters `start`, `end`); `src/KatLang/Evaluator.Expressions.cs:852,864`; `tutorial.md:220-235`; `evaluator-and-hosting.md` § Seeded randomness; `docs/design/seeded-randomness-2026-09.md`; `RandomIntSamplingTests`, `SeededRandomnessTests`.
- **Probe:** `--seed 42`: `random(0, 1) < 1\nrandomInt(1, 7) < 7\nMath.Random(0, 1) >= 0` → true, true, true; `Math.Rand` → UnresolvedImplicitParams ("Property 'Rand' was not found on `Math`…"); `Math.RandomInt(1.5, 3)` → IllegalInEval "Math.RandomInt bounds must be whole numbers".
- **Topics:** RAND, OP

### #78 — Bug implicit parameter c not detected as implicit argument in Discriminant property call
- **Dates:** created 2026-04-27 · closed 2026-04-27
- **Problem / question:** in an implicit-parameter `Quadratic`, `Discriminant`'s implicit parameters were not lifted into `Root1`/`Root2` because the reference sat inside `Math.Sqrt(Discriminant)`; the issue also noted the implicit parameter ORDER as "another story".
- **Decision / intended invariant:** implicit-parameter lifting must see references inside Math member (dot-call) arguments; `Quadratic` gets all three parameters (fix 8fbc972 "detect implicit Math dot-call dependencies").
- **Rationale:** a strict value position (Math function argument) needs the referenced property's value, so its parameters must be forwarded.
- **Examples:** `Quadratic = {\n Discriminant = b ^ 2 - 4 * a * c\n Root1 = (-b + Math.Sqrt(Discriminant)) / (2 * a)\n …\n Root1, Root2\n}\nQuadratic(1, -5, 6)`.
- **Lineage:** related #114 (builtin callable aliases propagate implicit parameters), the value-context lifting / closed-list strict-value diagnostics (B2/K2, Sep 2026), Math aliases #154; order follows the later-documented rule "first semantic source occurrence plus Grace".
- **Classification:** PARTIALLY CURRENT *(revised in lineage review; ledger batch said BUG FIX / REAFFIRMED EXISTING RULE)*
- **Surviving part / superseded by:** survives. The order question was settled by the general rule, not by special-casing: order is (b, a, c), so the issue's call returns (-1, 1.2), not the explicit-parameter roots (3, 2).
- **Current evidence:** `ImplicitArgumentResolverTests.Resolve_DotCallArgumentDependenciesLiftThroughContainingProperty` (`:197`, asserts `Params` = [b, a, c] for Quadratic, Discriminant, Root1, Root2) and `Eval_ImplicitQuadratic_DotCallArgumentDependencies_ReturnsRoots` (`:461`, expects -1, 1.2); AGENTS.md "registry-strict Math positions lift" and "Implicit-parameter order follows first semantic source occurrence"; `sequences-lists-and-calls.md` § Output bundles (value-context lifting `ProcessValueDemandingArgumentBundle`).
- **Probe:** implicit Quadratic → (-1, 1.2); explicit `Quadratic(a, b, c) = {…}` → (3, 2).
- **Topics:** PAR, DOT, OP
- **Lineage review (phase 2) corrections/addenda:**
  - [parameter-inference-grace] BUG FIX / REAFFIRMED EXISTING RULE → PARTIALLY CURRENT. Evidence: It was not a reaffirmation. Before 8fbc972, call and dot arguments were a never-lifting 'separate scope' (the removed comment reads 'Do NOT recurse into call args — separate scope'), so #78 introduced the Math-argument lifting position. That rule survives and was widened (alias spelling in b3738b9; opened spelling and must-selected fallback in ad6d6bf). Its recognizer IsMathValueDotCall (target is Expr.Resolve { Name: "Math" }, no shadow check) was replaced by the shadow-aware, identity-based AstHelpers.TryGetRegistryProvenMathCalleeFacts (AstHelpers.cs:232-251, 344). Its separate rewrite path was found to bypass the caller's closed-list gate (B2a, 8aac3eb, 2026-09-04). Probe: under a user-defined Math, F = Math.Sqrt(A) no longer lifts (ArityMismatch).

### #79 — Stack overflow when Recursion with list
- **Dates:** created 2026-04-27 · closed 2026-04-27
- **Problem / question:** recursion through a dot-call on a builtin result (`list.skip(1).reduceCollection`) overflowed the stack, while `reduceCollection(skip(list, 1))` worked; suspected dot-call + memoization interaction.
- **Decision / intended invariant:** a recursive dot-call binds the CURRENT activation's argument value exactly like the plain call (fix 9ce4a29 "recursive dot-call builtin binding"); the maintainer deliberately did not wrap the evaluator in try/catch so such bugs stay visible.
- **Rationale:** `x.f` ≡ `f(x)`; per-activation property values must not be reused across recursive activations.
- **Examples:** `reduceCollection(values) = {\n list = atoms(values)\n if(list.count <= 1, list, list.skip(1).reduceCollection)\n}\nreduceCollection((1,2,3,4))` (original used `Output = if(…)`; current equivalent is the bare row).
- **Lineage:** part of the dot-call ≡ call family (#58, #74, #112, #147, #167 68b3607); runtime protection later: dot chains are nested calls for host stack purposes with the `EvaluationStackExhausted` backstop, structural preflight, local-only property cache keyed by activation environment identity.
- **Classification:** BUG FIX / REAFFIRMED EXISTING RULE
- **Surviving part / superseded by:** survives.
- **Current evidence:** `EvaluatorPropertyBindingTests.Eval_RecursiveDotCallArgumentUsesCurrentValueBinding` (`:120`); `sequences-lists-and-calls.md` § The dot-call receiver (implementation paragraph: "A dot chain is therefore a nested call for host stack purposes … `EvaluationStackExhausted` backstop"); AGENTS.md zero-parameter property cache (local-only bindings keyed by the declaring activation's environments).
- **Probe:** translated program → [4] (all five paths); `reduceInt(IntegralValues) = {\n if(IntegralValues <= 1, IntegralValues, (IntegralValues - 1).reduceInt)\n}\nreduceInt(4)` → 1.
- **Topics:** DOT, CALL, PROP, RUN

### #80 — variadic parameters and reduce
- **Dates:** created 2026-04-28 · closed 2026-04-28
- **Problem / question:** `reduce(Right, CountMatchStep, (value, 0))` with a named multi-output `Right` failed, while the inline variadic form and `Right.reduce(...)` worked (AoC 2024 day 1 part 2).
- **Decision / intended invariant:** a named collection argument of `reduce` supplies its items like the dot form; plain and dotted spellings agree (5172e62 "align sequence source boundaries for variadic reduce").
- **Rationale:** `f(x)` ≡ `x.f`.
- **Examples:** `MatchCount = reduce(Right, CountMatchStep, (value, 0)):1` (with `Output=(…)` in the original step; current equivalent uses a bare row).
- **Lineage:** variadic-builtin era (#57, #73); later #102 (variadic reduce accumulator), #135 (`reduce(collection, reducer, initial)` fixed; inline variadic form now an arity error), callback law (reduce binds `F(element, accumulator)`, 5d6d60b / 702e7d7), reduce initial accumulator reified as ONE value.
- **Classification:** PARTIALLY CURRENT *(revised in lineage review; ledger batch said BUG FIX / REAFFIRMED EXISTING RULE)*
- **Surviving part / superseded by:** the named-collection form survives (result 31); the variadic form `reduce(4, 3, 5, 3, 9, 3, CountMatchStep, (value, 0))` from the issue is now an ArityMismatch (#135).
- **Current evidence:** `EvaluatorSequenceCallbackTests.Eval_Reduce_NamedMultiOutputArgument_IteratesEmittedItems` (`:491`, expects 31); Lean `CoreTests/SequenceCallbackBuiltins.lean:467` (`sequenceBoundaryLawAocCountMatchStepAlg`); spec `reduce-accumulates-value` (`:2991`), `reduce-empty-initial-is-one-value` (`:3009`); `sequences-lists-and-calls.md` § Collecting parameter lists, deconstruction, and callbacks (callback law).
- **Probe:** translated AoC program with `reduce(Right, …)` → 31 and with `Right.reduce(…)` → 31 (all paths); `reduce(4, 3, 5, 3, 9, 3, CountMatchStep, (3, 0))` → ArityMismatch (expects 3, called with 8); `reduce((4, 3, 5, 3, 9, 3), CountMatchStep, (3, 0))` → (3, 3).
- **Topics:** COLL, HO, VAR, CALL
- **Lineage review (phase 2) corrections/addenda:**
  - [variadic-forwarding] BUG FIX / REAFFIRMED EXISTING RULE → PARTIALLY CURRENT. Evidence: Fix 5172e62 introduced a new rule rather than reaffirming one: a 'Sequence boundary law: single-source expansion, comma-boundary preservation' for the VARIADIC reduce/sequence builtins (git show 5172e62:lean/KatLang.lean:1466-1478, shouldExpandSequenceSource = sourceCount = 1 || ...). #135 (0ca55e9) replaced that mechanism with one fixed collection parameter plus builtinCollectionItems, under which several sources are an ArityMismatch (the issue's own 'works' example reduce(4, 3, 5, 3, 9, 3, CountMatchStep, ...) is now ArityMismatch per the ledger probe). Only the observable single-source result survives (reduce(Right, ...) == Right.reduce(...) = 31). By the audit criterion 'mechanism later replaced', PARTIALLY CURRENT.

### #81 — Allow empty result definition directly in KatLang code
- **Dates:** created 2026-04-28 · closed 2026-04-29
- **Problem / question:** Programs could already produce an empty result indirectly (`filter(1, 3, 5, IsEven)`, `(0).skip(1)`), but source code had no way to write an empty result on purpose. Should KatLang add a builtin `Empty`, or allow `()`?
- **Decision / intended invariant:** A first attempt allowed `()` (e8f8b10), and it was reverted the same day (b8a24db). Comment 1 gave the reason: "`()` and `{}` are used to define an algorithm", and an algorithm and a result are different categories. The final fix (b950d86, 2026-04-29) added a reserved builtin **`empty`** as the canonical spelling of an intentional empty output. It emits zero top-level values and works with `count`, dot-calls, `==`/`!=`, `filter`, `skip` and result joins. `()` and `{}` stayed no-output algorithm forms, which raise missing-output errors when forced as results, and the diagnostics suggest `empty`.
- **Rationale:** Keep algorithms and results as separate categories. Reserve the name so it can never become an implicit parameter.
- **Examples:** `IsEven = x mod 2 == 0` / `filter(1, 3, 5, IsEven)` → empty. `empty.count` → 0. Current equivalent: the empty value is written `()`.
- **Lineage:** #128 (73cdba2, 2026-06-22) **removes** `empty` and **reverses** comment 1 by making `()` the structural empty sequence value. #143 **generalizes** that reversal: parentheses are a value-capture boundary, not an Algorithm. #168 plus the parentheses-group-syntax rule **narrow** #128's `(())` ≠ `()` claim, so `(())` is now `()`. SYN-01 (`empty-sequence-is-not-an-operator-identity`) **refines** how `()` behaves with operators. #135 changed the motivating examples, which now return the empty LIST `[]`, not an empty sequence.
- **Classification:** SUPERSEDED
- **Surviving part / superseded by:** The capability survives: source can write an explicit empty result, and it is a real, visible value. The spelling `empty` and the claim "`()` is an algorithm" were both superseded by #128 (73cdba2) and #143. Still current from this issue: `{}` is a no-output algorithm, not a value, and forcing it is a missing-output error whose diagnostic points the user at the explicit empty value (now "use `()`").
- **Current evidence:** Lean `Expr.emptySequence` (lean/KatLang.lean:866-869). Spec cases `empty-literal`, `empty-wrapped` (`() == (())` is `true`) and `missing-output-not-a-value` (LanguageSpecCorpus.cs:424-460 and 3462-3474). tutorial.md:902 and 1973 ("`()`, `[]`, and `{}` are different"). `empty` is no longer a name: it resolves as an ordinary implicit parameter.
- **Probe:** `empty` → `UnresolvedImplicitParams` (all paths). `()` → `S[] n=1`, display `()`. `filter((1, 3, 5), IsEven)` → `L[]`. `(0).skip(1)` → `L[]`. `(()) == (), () == [], count(()), ().count` → `true, false, 0, 0`. `X = {}` / `X` → `MissingOutput` "…or use `()` if the empty sequence value was intended."
- **Topics:** VAL, SEQ, SYN

### #82 — Line continuation using backslash
- **Dates:** created 2026-04-29 · closed 2026-05-04 (NOT_PLANNED)
- **Problem / question:** Proposal to add a Python-style `\` line-continuation marker after operators.
- **Decision / intended invariant:** Rejected. Whitespace and newlines are not part of the AST; the parser only uses them to decide whether an expression can end. **A line that ends with an operator is incomplete, so the expression continues on the next line.** A line whose expression is already complete (for example `not 1`) ends there, so a following line that starts with `and` is not a continuation. If a real case appears where the parser cannot continue naturally, the parser rules should be improved rather than adding an explicit continuation character.
- **Rationale:** Python needs `\` because its newlines end statements; KatLang's do not. Adding a character that only affects formatting would enlarge the syntax for no semantic gain.
- **Examples:** `1 + 2 + 3 +` newline `4 + 5` → 15. `not 1 and` newline `not 3 mod 2 == 0` is valid; `not 1` newline `and …` is not. The comment's `Value1;` newline `Value2;` style is obsolete: `;` was removed by #125. Current equivalent of the `not` example: `not true and` newline `not 3 mod 2 == 0`, because Booleans replaced numeric truthiness (#165).
- **Lineage:** **reaffirmed and refined** by the SYN-07A/#160 newline and comma rules, by #119/#123/#125 (continuation and `;` removal), by #161 SYN-07B (a trailing `*` continues like any trailing binary operator), and by F7 plus parser-recovery audit #9 (a declaration head is never the continuation operand).
- **Classification:** CURRENT
- **Surviving part / superseded by:** The whole decision stands: there is no `\` continuation, and trailing operators, `,`, `:`, `.`, prefix `-`/`not`, and a definition `=` continue onto the next line. It has since been refined: postfix continuations (`(`, `:`, `~`, postfix `*`) are same-line only, a leading `.` continues a dot chain, and a next-line declaration head is never taken as the missing operand. Only the `;` part of the comment's style advice is obsolete.
- **Current evidence:** docs/design/language-rules/syntax.md § "Line rules and declaration heads (F7)" (lines 17-27). KatLang.ebnf:296-391 (newline and continuation commentary). `Parser.IsHeadToken` (src/KatLang/Parser.cs:1963), `Parser.RecoverAtOperandStart`. Tests `DeclarationHeadLineRuleTests`, `MalformedSourceRecoveryTests`, spec case `declaration-head-never-spans-lines`.
- **Probe:** `1 + 2 + 3 +` newline `    4 + 5` → `15`. `1 + 2 + 3 + \` newline `    4 + 5` → parseFailure `UnexpectedCharacter '\'`: a single diagnostic, because reported characters are invisible to the grammar and the trailing `+` already continues the line. `not true and` newline `  not 3 mod 2 == 0` → `false`. `not true` newline `and` newline `…` → parseFailure `UnexpectedToken 'and'`.
- **Topics:** SYN

### #83 — Execution of KatLang code without output should return error
- **Dates:** created 2026-04-29 · closed 2026-04-29
- **Problem / question:** A program such as `T = 4` has no output; it is like a library. Running it returned nothing silently instead of an error.
- **Decision / intended invariant:** Commit 1ca8b3f is titled "Distinguish no-program-output from explicit empty output". A program whose root has no output rows is an evaluation error (missing output) and is **distinct from a program that explicitly outputs the empty value**. The host API reports it as its own outcome rather than as success with nothing.
- **Rationale:** Missing output is almost always a mistake, and an explicit empty result must not be confused with "nothing was asked for".
- **Examples:** `T = 4` → error "No output defined…". `()` → success, one visible empty row (current spelling; at the time the explicit empty output was `empty`, see #81).
- **Lineage:** Companion to #81 (same day). **Refined** by #128, whose message now suggests `()` instead of `empty`. #63 removed explicit `Output`, so `Output` is an ordinary identifier (`Run_OutputNamedPropertyAlone_IsNoProgramOutput`). **Reaffirmed** by the public API audit #11 layering (`RunResult` variants).
- **Classification:** CURRENT
- **Surviving part / superseded by:** All of it. Lean: the root is demanded through `evalProgramOutput`, and a `.mk` with an empty output list raises `Error.missingOutput`. C#: `KatLangEngine` projects exactly that top-level shape (`ProgramEvaluationContext` wrapping `MissingOutput`) into `RunResult.NoProgramOutput`. The raw `Evaluator.Run*` entry points return the `MissingOutput` error.
- **Current evidence:** lean/KatLang.lean:5167 `evalProgramOutput`, :5185 (`.mk _ _ _ _ [] _ => .error Error.missingOutput`), :7466-7482 `runResultM`. src/KatLang/KatLangEngine.cs:181-195 (`RunResult.NoProgramOutput`, `DefaultMessage`), :601-602 and :783-788 (`IsTopLevelNoProgramOutput`). Tests `KatLangEngineTests.Run_PropertyOnlyProgram_ReturnsNoProgramOutput`, `Run_MultiplePropertyDefinitionsWithoutOutput_ReturnsNoProgramOutput`, `EvaluateToAtoms_NoProgramOutput_Throws`, and `EvaluatorProgramOutputTests`.
- **Probe:** `T = 4` → engine `noOutput MissingOutput` ("No output defined. … Add an output expression, or use `()` if the empty sequence value was intended."); the generic, optimized and twin paths give `err MissingOutput`, the same kind.
- **Topics:** RUN, VAL, API

### #86 — Optimize while / repeat loops with pre-bound loop execution frames
- **Dates:** created 2026-04-30 · closed 2026-05-01
- **Problem / question:** `while` and `repeat` ran as repeated generic calls, with binding, frame, environment and output-splitting overhead on every iteration. The request was a conservative optimization that pre-binds the loop once and reuses the execution frame.
- **Decision / intended invariant:** Internal optimization only (4ea6bcc: planned loop expressions), with a generic fallback whenever safety is unclear. It must preserve these loop semantics exactly: (1) **simultaneous update**: every next-state output is evaluated against the OLD state, then all are committed together; (2) **the local property cache does not leak across iterations**, so a nested property that depends on the state is recomputed each iteration; (3) **captured parent values are fixed for a loop run** (in `Outer(n)`, `n` is stable while the loop runs).
- **Rationale:** Performance, while loops keep behaving exactly as repeated calls of the step.
- **Examples:** `GcdStep = b, ~a mod b, a mod b != 0` / `GcdStep.while(12, 30):1`. `Step = { A = x` / `A + 1, x < 3 }` / `Step.while(0)`. `Outer(n) = { Step = x + n, x < 10` / `Step.while(0) }`. The issue's swap example `Step = b, a` / `Step.repeat(1, 1, 2)` "expected 2, 1" is mis-stated: implicit parameters are ordered by first occurrence, so `Step` has parameters `(b, a)` and is the identity. The swap needs `Step(a, b) = b, a`.
- **Lineage:** **Followed by** #87 (sequence-pipeline fusion) and #95 (optimizer drift bug, **regression of** this optimization). #96 made collecting steps decline planning (`Eval_OptimizedLoop_VariadicStep_RejectedAtEligibilityGate`). Later hardening: e8c7eed (plan-aware eligibility), 761c3ef (budget parity, temp caching), ad9ea35, 02aa84e, and the M15–M18 optimizer milestones.
- **Classification:** IMPLEMENTATION ONLY
- **Surviving part / superseded by:** The optimization exists under `src/KatLang/Optimizations/Loops/`. Its semantic contract is current: the optimizer is C#-only and must match the Lean and generic loop semantics. The three invariants are pinned: planned exported temps use the run cache, and local-only temps use per-iteration memoization.
- **Current evidence:** `src/KatLang/Optimizations/Loops/{LoopOptimizer,LoopPlan,LoopExprPlan,LoopTempPlan}.cs`. SEMANTIC-ALIGNMENT.md row "Optimized loops" (line 22). evaluator-and-hosting.md § "Zero-argument property cache" (line 94: "Planned exported temps use the run cache; local-only temps use per-iteration memoization"). Tests `EvaluatorLoopTests.Eval_Repeat_SimultaneousUpdate_UsesOldStateForAllOutputs` (:113), `Eval_While_LocalPropertyRecomputesPerIteration` (:681), `Eval_While_NestedStepUsesMutableStateAndCapturedParentValues` (:707), the `LoopPlanned*ParityTests`, and `CorpusExecutionEquivalenceTests`.
- **Probe:** `GcdStep…while(12, 30):1` → `6` (5/5 agree). `Step(a, b) = b, a` / `Step.repeat(1, 1, 2)` / `Step.repeat(3, 1, 2)` → `S[S[2, 1], S[2, 1]]` (generic: loopFallbacks=2; optimized: loopHits=2). The literal `Step = b, a` version → `S[1, 2]`, the identity. Local-cache example → `3` (optimized loopHits=1). `Outer(2)` → `10` (optimized loopHits=1).
- **Topics:** LOOP, RUN, PROP
- **Lineage review (phase 2) corrections/addenda:**
  - [loops] IMPLEMENTATION ONLY; lineage ends at e8c7eed/761c3ef/ad9ea35/02aa84e → IMPLEMENTATION ONLY (unchanged); lineage should add ebf623e (#170, B1, 2026-09-27), which changed the planned (and generic) if-argument temp read from a memo bypass to the ordinary cached read.. Evidence: Memory loop-temp-validity-investigation-2026-09 (2026-09-17): 'a temp passed DIRECTLY as an if argument evaluates fresh (memo bypassed)'. SEMANTIC-ALIGNMENT.md B3 entry: 'Since B1, a property passed directly as an if argument uses the ordinary cached property read inside that argument level on both strategies'. ebf623e removed 72 lines from LoopPlan.cs. Probe p28 gives 8 ticks for 4 iterations (T is read twice per iteration) on all paths, with optimized loopHits=1.

### #87 — Optimize sequence pipeline filter(...).count by fusing into count-where execution
- **Classification:** IMPLEMENTATION ONLY. `source.filter(p).count` is fused into a count-where without building the filtered collection. The code lives in the new `KatLang.Optimizations.Sequences` namespace (020b7ec; now `SequencePipelineOptimizer.cs` and `SequencePipelinePlan.cs` with the closed `FilterCountSourcePlan`). It is C#-only, needs no Lean change, and requires equivalence tests (SEMANTIC-ALIGNMENT.md:23; `FilterCountFusionSpanParityTests`, `EvaluatorSequencePipelineTests`, `SequencePipelineDispatchTests`). Probe with the issue program, N=100 → `61` on both paths (optimized: filterCountFusion=1, rangeFusion=1, loopHits=100).
- **Topics:** COLL, HO, RUN
- **Lineage review (phase 2) corrections/addenda:**
  - [loops] IMPLEMENTATION ONLY with no lineage → IMPLEMENTATION ONLY (unchanged); lineage should record the parity repairs: c6e6e13 (depth accounting across budget strategies), 14bb037 (fused predicate preparation), e4d19cc (Boolean predicate), 5d6d60b (forwarded predicate keeps its algorithm channel in the fused pipeline), ebf623e (fused receiver read through the cache).. Evidence: git log subjects for c6e6e13/14bb037 and --stat touching Optimizations/Sequences/SequencePipelineOptimizer.cs; memory budget-crosstalk-always-active (fusion elided depth levels); SEMANTIC-ALIGNMENT forwarded-callable entry names 'the fused filter->count pipeline in both spellings'; stale comment Evaluator.DotCalls.cs:151-155; probes p30 and p31 agree with filterCountFusion>0.

### #88 — The behaviour of `count` seems to be eccentric.
- **Dates:** created 2026-05-04 · closed 2026-05-04
- **Problem / question:** In `Qmean_err = Math.Sqrt(atoms(list).map{x * x}.sum / list.count)`, the call `Qmean_err(Arg)` with `Arg = range(1, 10)` computed `list.count = 1`, giving 19.62 instead of the RMS 6.20.
- **Decision / intended invariant:** Comment 1 said this is not a bug: `Arg` is passed as ONE argument, so the parameter receives one group and "group.count results to 1". Using `atoms` to unwrap was rejected as costly and structure-destroying. The stated fix was a variadic parameter `list...` that "captures the top-level outputs of the provided argument", a parameter-level one-level ungroup. Comment 2 declared the issue fixed by #73, with `Qmean_err(list...) = …` and `Qmean_err(Arg)`.
- **Rationale:** A single-argument boundary should hold, but user code needed a way to open the argument's top-level outputs.
- **Examples:** `Arg = 1, 2, 3` / `Group = list` / `Arg.Group.count` → 1 at the time. `Group(list...) = list` / `Arg.Group.count` → 3 at the time. Current syntax: `Group(*list) = list`.
- **Lineage:** Predecessors: #58/#60 (group unwrapping), #71/#72, and #73 (the variadic design this issue fed). Successors: #91 (the `ungroup` idea from comment 1), #89/#105/#106/#108/#111/#112/#144 (variadic receivers and forwarding in the same spirit, later reversed). #132 (a call boundary returns one sequence value) and #135 (collection builtins take ONE fixed `collection` argument and read it through a one-level view) **reverse** the diagnosis: `count` of a bound sequence now counts its elements. #138/#140 **replace syntax** (`*list` collects an exact list). #167 plus 702e7d7 (2026-09-23, "values stay values", C-full) **reverse** the #73 fix: a collecting parameter collects exactly the supplied arguments, so `F(Arg)` collects `[Arg]`.
- **Classification:** SUPERSEDED
- **Surviving part / superseded by:** Survives: one written argument is one value (the argument boundary is never opened implicitly), and `atoms` is the separate recursive projection. Both halves of the resolution are superseded. (a) The ordinary-parameter program now gives the RIGHT answer, because `count` opens its bound collection one level (`builtinCollectionItems`, #135). (b) The collecting-parameter "fix" now gives the originally WRONG answer, because `*list` collects `[Arg]` (C-full, 702e7d7). Current idioms are an ordinary parameter with `list.count`, or `Q(Arg*)` / `Arg*.Q` with a collecting parameter.
- **Current evidence:** lean/KatLang.lean:2665 `builtinCollectionItems`, :2889 `collectSegment`. docs/design/language-rules/sequences-lists-and-calls.md § "Collecting parameters" and § "Collection builtins". Spec cases `count-family` (LanguageSpecCorpus.cs:2915), `values-stay-values` (:1260; `Cnt((10, 7))` is 1 but `CntValue((10, 7))` is 2), `builtin-fixed-collection-arity`.
- **Probe:** Original program, with `//` translated to `#` → `10, 6.2048…, 6.2048…` (the "err" variant is now correct). `Arg = 1, 2, 3` / `Group = list` / `Arg.Group.count` → `3`. `Group2(*list) = list` / `Arg.Group2.count` → `1`; `Arg*.Group2.count` → `3`; `Qmean_var(*list) = …` / `Qmean_var(range(1, 10))` → `19.6214…`; `Qmean_var(range(1, 10)*)` → `6.2048…`. All paths agree.
- **Topics:** VAL, CALL, VAR, COLL, SUP

### #89 — Inline grouped dot-call receiver does not bind correctly to user-defined variadic parameter
- **Dates:** created 2026-05-04 · closed 2026-05-04
- **Problem / question:** With `TotalWithFee(values..., fee) = values.sum + fee`, the named receiver `Data.TotalWithFee(5)` gave 65, but the inline `(10, 20, 30).TotalWithFee(5)` failed.
- **Decision / intended invariant:** Commit 5cf09fc ("Variadic dot-call receiver binding drift") made the inline grouped receiver bind **exactly like the named receiver**: both had the variadic collect the receiver's top-level items (65). An extra layer, `((10, 20, 30)).TotalWithFee(5)`, stayed one grouped value and failed (`Eval_VariadicParameter_NestedInlineTupleDotCallPreservesGroup`).
- **Rationale:** A receiver's binding must not depend on whether it is written inline or through a property.
- **Examples:** `Data = 10, 20, 30` / `Data.TotalWithFee(5)` and `(10, 20, 30).TotalWithFee(5)` → 65 at the time. Current syntax: `TotalWithFee(*values, fee)`.
- **Lineage:** Follows #73/#88. **Reaffirmed** in the same direction by #105 (b8a1bca), #112 and #144 (f12af0f: "receiver segments"). #167 (68b3607 "Make dot-call pass values without implicit spreading") and 702e7d7 **reverse** the receiver expansion: `R.F(args)` is exactly `F(R, args)`, so a collecting parameter collects the receiver as ONE item. #168 (parentheses group syntax) **removes** the `((…))` vs `(…)` difference.
- **Classification:** SUPERSEDED *(revised in lineage review; ledger batch said PARTIALLY CURRENT)*
- **Surviving part / superseded by:** Survives: named and inline receivers bind identically, because dot-call passes the receiver as an ordinary leading argument whatever its spelling. Superseded by #167 (68b3607) and 702e7d7: the collector no longer receives the receiver's top-level items, and both spellings now collect `[(10, 20, 30)]` and fail in `values.sum`. The current idiom is the fluent spread receiver `Data*.TotalWithFee(5)` / `(10, 20, 30)*.TotalWithFee(5)` → 65. Also superseded: the double-parenthesis distinction, since `((10, 20, 30))` is now the same value as `(10, 20, 30)`.
- **Current evidence:** docs/design/language-rules/sequences-lists-and-calls.md § "The dot-call receiver". Lean `prepareLexicalDotCallArgs` → `callLexicalWithReceiverCounted`; C# `BuildLexicalReceiverCallArgs` (src/KatLang/Evaluator.DotCalls.cs:51). Spec case `dot-receiver-passes-a-value` (LanguageSpecCorpus.cs:1220; `(1, 2, 2.718).Mean` → `err arity`, `(1, 2, 2.718)*.Mean` → 1.906). Tests `EvaluatorCollectingParameterTests.Eval_CollectingParameter_InlineTupleSpreadDotCallMatchesNamedReceiver` and `Eval_CollectingParameter_NestedInlineTupleDotCall_ReceiverIsOneArgument` (:193-235).
- **Probe:** `Data.TotalWithFee(5)` and `(10, 20, 30).TotalWithFee(5)` → the same `ArityMismatch` ("sum expects each collection element to be a single numeric value; item 0 was sequence value"). `Data*.TotalWithFee(5)`, `(10, 20, 30)*.TotalWithFee(5)` and `TotalWithFee(10, 20, 30, 5)` → `65` each. `Coll(*values, fee) = values, fee` / `Data.Coll(5)` and `(10, 20, 30).Coll(5)` → both `([(10, 20, 30)], 5)`.
- **Topics:** DOT, VAR, CALL, SUP
- **Lineage review (phase 2) corrections/addenda:**
  - [dot-call] PARTIALLY CURRENT → SUPERSEDED. Evidence: The decision itself (an inline grouped receiver feeds its items to the variadic like a named receiver, giving 65) was reversed by 68b3607 + 702e7d7. (10,20,30).TotalWithFee(5) -> ArityMismatch, and the dot-receiver-passes-a-value probe (1,2,2.718).Mean gives err arity. Its ((...)) distinction was reversed by #168. The only survivor listed is the spelling-symmetry goal, for which the ledger classifies the sibling #105 as SUPERSEDED. Moderate confidence (consistency judgment).

### #90 — Improve result display to make grouping structure visible
- **Classification:** HOST/API ONLY. The display must distinguish one sequence-valued result `(10, 20, 30)` from three top-level rows, "without changing evaluation semantics" (fd3cabe). This is current: a sequence row displays as `(…)`, a list as `[…]`, and several emitted values as separate rows (`KatLangEngineTests.RunResult_ToDisplayString_OrdinaryDotCallReceiver_ShowsSingleSequenceValueResult`, `…_MixedTopLevelOutput_DisplaysRows`, `…_NestedSequenceValueOutputs_PreservesParentheses`; formatters under `src/KatLang/Formatting/`). The issue's semantic examples are outdated. `Group(list) = list.count` / `(10, 20, 30).Group` is now 3, not 1 (see #88), and the variadic receiver example now yields ONE collected value `[(10, 20, 30)]` (`RunResult_ToDisplayString_VariadicDotCallReceiver_ShowsOneCollectedValue`, :863). Probes: `(10, 20, 30).Group` → display `(10, 20, 30)`; `10, 20, 30` → three rows.
- **Topics:** TOOL, API, VAL

### #91 — Add ungroup builtin for one-level group removal
- **Dates:** created 2026-05-05 · closed 2026-05-05
- **Problem / question:** `atoms` flattens recursively. A separate operation was needed to remove exactly ONE grouping level while keeping deeper groups.
- **Decision / intended invariant:** 5d1b52c added the builtin `ungroup(value)` / `value.ungroup`. It projects a group's direct content one level, never recursively; `ungroup(1, 2, 3)` is an arity error; `atoms` stays the recursive projection. It was mirrored in Lean.
- **Rationale:** Make structural intent explicit and keep one-level opening distinct from recursive flattening.
- **Examples:** `((1, 2), (3, 4)).ungroup` → `(1, 2), (3, 4)`. `((1, 2), (3, 4)).atoms` → `1, 2, 3, 4`. Current equivalent: `((1, 2), (3, 4))*` (postfix spread) and `atoms(...)`.
- **Lineage:** Suggested in #88 comment 1. **Renamed** to `content` by #98 (7ad022c). #103/#104/#111 **added** the postfix `...` spread, which `content...` composed with. #129 (7458502, 2026-06-26) **removes** `content` in favour of the postfix spread (`Group...`). #124 made spread postfix-only and unary, and #140 **replaces the syntax** of `...` with `*`. #136 gave `atoms` its list semantics.
- **Classification:** SUPERSEDED
- **Surviving part / superseded by:** The builtin is gone (#98 rename, then #129 removal). The concept survives in the explicit spread marker `v*`: it opens exactly ONE sequence or list boundary (`spreadItems`), never recursively, and spread-produced items are never reopened. `atoms` remains the separate recursive projection and now returns one exact list.
- **Current evidence:** lean/KatLang.lean:1273 `spreadItems`, :1185 `languageAtoms`. docs/design/language-rules/syntax.md § "The spread marker (SYN-07B)" and sequences-lists-and-calls.md § "Spread semantics". Spec cases `atoms-recursive-flatten`, `repeated-spread-singleton-opens`, `spread-capture-count`.
- **Probe:** `X = ((1, 2), (3, 4))` / `X*` → rows `(1, 2)` and `(3, 4)`. `X.atoms` → `[1, 2, 3, 4]`. `(1, 2, 3).ungroup`, `(1, 2, 3).content` and `content((1, 2, 3))` → `UnresolvedImplicitParams` (no longer names).
- **Topics:** SEQ, SUP, COLL

### #92 — Recursive algorithms do not work with `map`
- **Dates:** created 2026-05-06 · closed 2026-05-06
- **Problem / question:** `Factorial = if(n == 0, 1, Factorial(n-1)*n)` worked when called directly but overflowed the stack in `(0, 1, 2, 3, 4).map(Factorial)`.
- **Decision / intended invariant:** Root cause, from commit 3997ad6: `map` bound the callback item in `CountedParamEnv`, and `Param(n)` resolved that OUTER callback binding before the newer recursive-call binding of `n`, so recursion never reached the base case. The fix makes every user-call, conditional-branch and loop-step parameter scope **shadow any inherited binding of the same name**. A newer call frame's parameter always wins over an outer callback binding. Mirrored in Lean with `CountedParamEnv.shadow`.
- **Rationale:** Lexical and call-frame correctness: a callback is an ordinary call and must not leak its binding into nested calls of the callee.
- **Examples:** `Factorial = if(n == 0, 1, Factorial(n-1)*n)` / `(0,1,2,3,4).map(Factorial)`. The issue's `//` comments are now `#`.
- **Lineage:** **Generalized** by the ONE shadowing helper (`EvalCtx.bindParameters` / `ShadowInheritedParameterEnvironments`): "a BOUND PARAMETER OWNS ITS NAME ON EVERY CHANNEL" (value, counted and algorithm tiers; the B2/K2 September work). Sibling bug #95 hit the same rule in the optimizer. #156 (native callback lookup) is a related later fix. The C-full callback law (702e7d7) **reaffirms** that a callback element is ONE ordinary argument.
- **Classification:** BUG FIX / REAFFIRMED EXISTING RULE
- **Surviving part / superseded by:** Fully current and since generalized to all three environment tiers and every binding site (both engines and the async twin).
- **Current evidence:** lean/KatLang.lean:1600-1627 `EvalCtx.bindParameters` (with `AlgEnv.shadow` :1398 and `CountedParamEnv.shadow` :1417); `runStepSlots` (:5206) uses it. src/KatLang/Evaluator.cs:357 `ShadowInheritedParameterEnvironments`. docs/design/language-rules/ownership-and-lookup.md § "Parameter channels and shadowing". Lean `CoreTests/SequenceCallbackBuiltins.lean:785-808` (`factorialMapAlg85a`, `#guard test85a`). C# `EvaluatorSequenceCallbackTests.Eval_Map_RecursiveCallback_UsesCurrentValueBinding` (:1176), `KatLangEngineTests.Run_MapRecursiveFactorial_Succeeds` (:1383).
- **Probe:** `(0, 1, 2, 3, 4).map(Factorial)` → `[1, 1, 2, 6, 24]`. Direct calls give `1, 24, 5040`, and `map([0,1,2,3,4], Factorial)` gives the same list (5/5 paths agree). The iterative clause-family version with `range(0, 7).map(Factorial)` → `[1, 1, 2, 6, 24, 120, 720, 5040]`.
- **Topics:** HO, CALL, RES, PAR

### #93 — Why is built-in algorithms like `sum`, and `Math`, not visible inside "libraries"
- **Dates:** created 2026-05-06 · closed 2026-05-06
- **Problem / question:** Members of an opened library (`open Vec`, with `Vec = { public … }`) could not see prelude builtins (`sum`, `Math`, `if`) when they were called through the open.
- **Decision / intended invariant:** Commit 4131b6d fixed it. **Calling an opened member is runtime-equivalent to the owner-qualified call** (`open Vec` + `Test(...)` ≡ `Vec.Test(...)`). The member evaluates in its DECLARING lexical context, so it sees its own siblings and the prelude, but it does **not** see the opener's scope ("caller-site isolation"). Comment 3 also clarified two existing rules. `open` must be the first declaration of its algorithm. A free name in a library member that matches a property of an enclosing scope resolves to that property: `open Vec` / `x = 10` / `Vec = { public Test = x > 0 }` makes `Test` take 0 parameters, so `Test(35)` is an arity error.
- **Rationale:** Open is static name exposure, not dynamic scoping, and the prelude is the outermost scope of every lexical chain.
- **Examples:** `A = 10` / `Vec = { public Test = A + x }` / `Scope = { open Vec` / `A = 100` / `Test(5) }` / `Scope` → 15.
- **Lineage:** Predecessors: #6 and #18 (open design and visibility), #51 (open string aliases). 55d5672 (2026-05-27, "Preserve prelude for opened block libraries") **refines** the fix for inline and load-elaborated block opens (`wireOpenBlockToGlobalScope`). It was later **reaffirmed and generalized** by K1-08 (selection before accessibility), SYN-03 (static-open ownership), name-resolution audit #8 (the six-rule model: opens consulted only after the whole owner walk), and SYN-05 (the prelude as ordinary outermost bindings).
- **Classification:** BUG FIX / REAFFIRMED EXISTING RULE
- **Surviving part / superseded by:** All of it: the prelude is visible in opened members, opened members are isolated from the opener, `open` comes first, and a free name resolves to the nearest enclosing property. The open-target syntax later became ONE comma list per algorithm.
- **Current evidence:** lean/KatLang.lean:2352 `wireOpenBlockToGlobalScope`, :4374-4376 (block opens "keep isolation from the opener while retaining the global call-stack base"), :4467 `resolveAllOpens`. src/KatLang/Parser.cs:1444 ("'open' declaration must appear before any properties or output expressions."). docs/design/language-rules/ownership-and-lookup.md § "The resolution model in one place" and § "Open, exposure, and accessibility (K1-08)". syntax.md § "The `open` declaration". Tests `EvaluatorOpenVisibilityTests.Eval_Open_PublicMemberBodyCanCallBuiltinIf/Math/Sum` (:174-200), `Eval_Open_PublicMemberCallMatchesOwnerQualifiedCall` (:213), `Eval_Open_PublicMemberDoesNotSeeOpenerLocalShadow` (:255), `Eval_Open_LibraryIsolatedFromOpenerScope` (:334).
- **Probe:** The Vec library program → `98, 7.0710678…`. `open Vec` / `Vec = { public Test = if(x > 0, 1, 0) }` / `Test(35)` → `1`. `x = 10` placed before `open` → parseFailure `InvalidOpenDeclaration`. `open Vec` / `x = 10` / … / `Test(35)` → `ArityMismatch` ("`Test` expects 0 arguments"). The isolation example → `15`.
- **Topics:** MOD, RES
- **Lineage review (phase 2) corrections/addenda:**
  - [open-ownership-modules] BUG FIX / REAFFIRMED EXISTING RULE (surviving: all of it) → BUG FIX / REAFFIRMED EXISTING RULE (surviving: direct-call equivalence only). Evidence: 'open Vec + Test(...) is runtime-equivalent to Vec.Test(...)' holds for direct calls only. In algorithm position Box.G is a zero-parameter dot wrapper: map([1,2], Box.G) gives ArityMismatch while open Box; map([1,2], G) gives L[10,20] (w1-suspicions [C6]/[L1], probed). Separately, `open 'u'` is isolated to the prelude while `open M` with M = load(u) sees the declaration site (probes m1 vs m2). *(Constitution audit, 2026-10-23: both halves are superseded — Model C (2026-10-02) and Q-18 C-B3 (2026-10-05) make `map([1, 2], Box.G)` `[10, 20]` like the opened spelling, an argumentless structural path being its member's own callable in every position, and Q-31 H-P (2026-10-06) roots `M = load(u)` at the prelude like `open 'u'`; MOD-06, MOD-08.)*

### #94 — `Math.Atan2` should be added?
- **Dates:** created 2026-05-07 · closed 2026-05-13
- **Problem / question:** Add the two-argument arctangent (common in other languages, and it handles the ±90° cases).
- **Decision / intended invariant:** 20fc773 ("Add Math.Atan2 to KatLang core", via PR #107) added `Math.Atan2` with the conventional order **`atan2(y, x)`**. 17d480b (2026-08-08) later corrected the signature METADATA to `Atan2(y, x)`. The runtime had already forwarded the first argument as `y`; the editor and display names had used the default `(x, y)`.
- **Rationale:** Standard library completeness (Rosetta Code "mean angle").
- **Examples:** `Math.Atan2(1, 0)` → π/2. `Math.Atan2(0, 1)` → 0.
- **Lineage:** Arrived with #77/#107 (random functions, PR #107). The lowercase alias `atan2` came from #154. #153 made the value type Decimal128, and numeric audit #6 found Atan2 ≤ 0.5 ulp (memory note, secondary). Not affected by #109/#110 (Rand changes).
- **Classification:** CURRENT
- **Surviving part / superseded by:** All of it. This is library surface, not a constitutional law. Lean does not model the Math surface (SEMANTIC-ALIGNMENT.md: "C#-only: Lean has no Math"), so Atan2 is C#-only.
- **Current evidence:** src/KatLang/BuiltinRegistry.cs:369 (`new("Atan2", MathMemberKind.BinaryFunction, "atan2", ParameterNames: ["y", "x"])`). tutorial.md:218. Tests `EvaluatorTests.Eval_MathAtan2_BindsArgumentsInConventionalYXOrder`, `BuiltinRegistryParityTests`. No Lean definition (grep finds none in lean/KatLang.lean).
- **Probe:** `Math.Atan2(1, 1), atan2(1, 0), atan2(0, -1), Math.Atan2(-1, -1)` → `0.785398…, 1.570796…, 3.141592…, -2.356194…` (engine and generic agree).
- **Topics:** OP
- **Lineage review (phase 2) corrections/addenda:**
  - [random-numerics] Evidence: EvaluatorTests.Eval_MathAtan2_BindsArgumentsInConventionalYXOrder → Evidence: EvaluatorMathTests.Eval_MathAtan2_BindsArgumentsInConventionalYXOrder (tests/KatLang.Tests/EvaluatorMathTests.cs; classification CURRENT unchanged). Evidence: grep finds the method only in EvaluatorMathTests.cs, whose class is declared as 'public class EvaluatorMathTests' at line 10.

### #95 — Implicit parameter and Collection Issue
- **Dates:** created 2026-05-07 · closed 2026-05-07
- **Problem / question:** An emirp program using `filter(IsEmirp)` was wrong only when the callback's implicit parameter was named `n`, the same name as the implicit parameter of an inner loop step (`Reverse`'s `Step = Math.Floor(n / 10), rev * 10 + n mod 10, n > 0`).
- **Decision / intended invariant:** This was an optimizer drift bug. Per comment 1, "Lean and the generic evaluator agreed". The planned loop step read the OUTER callback binding of `n` instead of its own loop-state parameter `n`. Commit 37c6898 restored the rule that **loop-state parameters shadow outer (callback) bindings of the same name**, bringing the optimized path back to parity with Lean and the generic evaluator.
- **Rationale:** Optimizations must be semantically invisible, and a bound parameter owns its name.
- **Examples:** `IsEmirp = n > 11 and IsPrime(n) and IsPrime(Reverse(n))` / `(11,12,13,14,15,16,17).filter(IsEmirp)`. In the current version the loop continuation and `and` operands are Booleans; the program already uses comparisons, so it runs unchanged.
- **Lineage:** **Regression of** #86 (planned loops) and a sibling of #92, the same shadowing rule in a different engine. **Generalized** by the one-helper parameter shadowing law (`ShadowInheritedParameterEnvironments` / `EvalCtx.bindParameters`, used by generic AND planned loop steps). Later optimizer parity work includes `CorpusExecutionEquivalenceTests` and `OptimizerEquivalenceSweepTests`.
- **Classification:** BUG FIX / REAFFIRMED EXISTING RULE
- **Surviving part / superseded by:** Fully current.
- **Current evidence:** docs/design/language-rules/ownership-and-lookup.md § "Parameter channels and shadowing" ("generic and planned loop steps"). lean/KatLang.lean:5206-5209 `runStepSlots` → `ctx.bindParameters`. Tests `EvaluatorLoopTests.Eval_LoopPlanner_LoopStateShadowsOuterCountedCallbackParameterInWhile/InRepeat/InFilter/InReduce` (:1037-1121), `Eval_LoopPlanner_DifferentOuterNameKeepsInnerStateBinding` (:1179), `Eval_LoopPlanner_RenamedInnerStateAvoidsCallbackNameCollision` (:1205).
- **Probe:** The failing program plus `IsEmirp(13), IsEmirp(17)` → `[13, 17], true, true` on all 5 paths. The optimized path was actually used (loopHits=27).
- **Topics:** LOOP, HO, RES, RUN

### #96 — Shouldn't it `Step.repeat(1, [PARAMETERS])` be equivalent to `Step([PARAMETERS])` ?
- **Dates:** created 2026-05-07 · closed 2026-05-07
- **Problem / question:** A step with a growing history failed with `TestStep.repeat(1, LIST)`, although calling `TestStep(LIST)` directly worked.
- **Decision / intended invariant:** Commit 6469363 made two decisions. (1) `while`/`repeat` steps may declare a **variadic (now collecting) parameter** that receives however many state slots the loop currently has, through the same binding model as ordinary calls. (2) **Initial loop arguments preserve their written boundaries**: `Step.repeat(3, a, b)` starts with two state slots, and `Step.repeat(3, Pair)` starts with ONE slot even when `Pair` holds several values. Step outputs define the next state's slots, so the grouping of the step result matters: a bare join emits several slots and a parenthesized join emits one.
- **Rationale:** Loop state should follow the ordinary call and variadic model, with no special unpacking.
- **Examples:** `TestStep(history...) = history; FindNext(history)` / `TestStep.repeat(2, 1, 2, 4)`. `TestStep = (history; FindNext(history))` / `TestStep.repeat(2, List)`. Current equivalents: `TestStep(*history) = history*, FindNext(history*)` / `TestStep.repeat(2, List*)`, and `TestStep = (history*, FindNext(history*))` / `TestStep.repeat(2, List)`.
- **Lineage:** Related to #86 (collecting steps later **excluded** from planning). **Extended** by #99 (sequence-value patterns in loop steps) and #102 (variadic accumulator in `reduce`). #125 **removes** the `;` join used in the model ("bare `;` joins, `(A; B)` keeps one group"). #138/#140 **replace the syntax** (`*history` collects an exact list). C-full (702e7d7) **reaffirms** it: "Loop state slots unchanged" (memory note values-stay-values; the rule doc says loop state slots are the established items of multi-slot state, never a callback element).
- **Classification:** PARTIALLY CURRENT
- **Surviving part / superseded by:** Survives: collecting step parameters over multi-slot loop state; one initial state slot per written argument (a spread initial argument supplies its items); step outputs define the next slots; a captured step output is one slot. Superseded: the `;`-join formulation (removed by #125, now comma plus explicit spread) and the `...` spelling (→ `*`, #139/#140). The answer to the title question survives only for the slot assembly: `repeat(Step, 1, (1, 2))` with `Step(*xs) = xs.count` is 1, exactly like `Step((1, 2))`.
- **Current evidence:** lean/KatLang.lean:5211-5217 `evalInitialLoopStateSlots` (docstring states the rule), :5066 `bindLoopStepState` (collecting and pattern branches). src/KatLang/Evaluator.Loops.cs:57 `EvalInitialLoopStateSlots`, :328 `BindLoopStepState`. sequences-lists-and-calls.md § "Collecting parameter lists, deconstruction, and callbacks" (loop state clause; "collecting step signatures explicitly decline planning"). Tests `EvaluatorLoopTests.Eval_VariadicLoopStep_*` (:1510-1647), `Eval_LoopInitial_SequenceValuePropertyArgIsOneSlot` (:1893), `Eval_LoopInitial_MultiOutputPropertyArgIsOneSlot` (:2035), `Eval_VariadicLoopStep_ImplicitOrdinaryRepeatStillFails` (:1543), `Eval_OptimizedLoop_VariadicStep_RejectedAtEligibilityGate` (:225).
- **Probe:** The translated FindNext/TestStep program: `TestStep.repeat(2, List*)` and `TestStep.repeat(2, 1, 2, 4)` → `(1, 2, 4, 5, 6)` each. The captured-step form `TestStep = (history*, FindNext(history*))` / `TestStep.repeat(2, List)` → `(1, 2, 4, 5, 6)`. `Step(*xs) = xs.count`: `repeat(Step, 1, (1, 2))` → `1` and `repeat(Step, 1, 1, 2)` → `2`. `Cnt(*xs) = xs.count, 0` / `Cnt.repeat(1, Pair)` → `(1, 0)`. All paths agree.
- **Topics:** LOOP, VAR, SUP, VAL
- **Lineage review (phase 2) corrections/addenda:**
  - [loops] PARTIALLY CURRENT; lineage says #138/#140 'replace the syntax (*history collects an exact list)' → PARTIALLY CURRENT (classification unchanged). #138 (ab7d2f5, 2026-07-18) is a SEMANTIC change to collecting loop steps, not only a syntax change. Add to Superseded: 'a collecting step captures a lone multi-valued slot as that value'; the resolution's own TestStep.repeat(2, List) example has failed since #138.. Evidence: Memory rest-collects-exact-lists lists 'variadic loop-step state' as collecting exact lists. Probe p08 (TestStep(*history) = history*, FindNext(history*) / TestStep.repeat(2, List)) gives BadIndex on all 5 paths; p07 with List* gives (1, 2, 4, 5, 6).

### #97 — Number Extension: support numbers in scientific notation
- **Dates:** created 2026-05-07 · closed 2026-05-28
- **Problem / question:** Allow literals such as `7e-3` (= 0.007) for physics calculations. A request for hex literals was withdrawn (struck through in comment 1).
- **Decision / intended invariant:** cadb441 (2026-05-26, "Number extension", PR #115) added an optional exponent (**lowercase `e`**, optional sign) and `_` digit separators to number literals. There are no hex literals. A decimal point needs digits on both sides.
- **Rationale:** Scientific-notation data entry.
- **Examples:** `7e-3` → 0.007. `6.674e-11`. `1_000_000`.
- **Lineage:** **Refines** #13 (large numbers; its answer at the time was the C# `decimal` range limit). #153 (Decimal128) **generalizes** the value range to about 9.999e6144, and literals parse directly into Decimal128 with round-half-even at 34 digits.
- **Classification:** CURRENT
- **Surviving part / superseded by:** All of it. Only lowercase `e` is accepted. `1.5E3` is not a number literal (lexed as `1.5` followed by an identifier).
- **Current evidence:** KatLang.ebnf:696-697 (`Number = /[0-9](_*[0-9])*(\.[0-9](_*[0-9])*)?(e[+-]?[0-9](_*[0-9])*)?/`). src/KatLang/Lexer.cs:8 and :234-244 (exponent scan with backtrack when no digit follows `e`). tutorial.md:176. `LexerTests.Tokenize_ScientificNotation_*` (:457-483), `Tokenize_IntegerWithUnderscores_*`.
- **Probe:** `7e-3, 1.5e3, 6.02e23, 1_000_000, 6.674e-11` → `0.007, 1500, 602000000000000000000000, 1000000, 0.00000000006674`. `2e+2` → `200`. `1.5E3` → parseFailure `UnseparatedSameLineItem`. `0xff` → parseFailure `UnseparatedSameLineItem`.
- **Topics:** SYN, OP

### #98 — Rename ungroup builtin to content
- **Dates:** created 2026-05-08 · closed 2026-05-08
- **Problem / question:** `ungroup` is a verb, which reads poorly as a projection next to the noun `atoms` (`history.ungroup.contains(c)`).
- **Decision / intended invariant:** 7ad022c renamed `ungroup` to **`content`**: "the immediate contents of one explicit group boundary". `atoms` remained the recursive atomic projection.
- **Rationale:** A noun reads as a structural view and pairs with `atoms`.
- **Examples:** `((1, 2), 3).content` → `(1, 2), 3`; `((1, 2), 3).atoms` → `1, 2, 3`. Current equivalent: `((1, 2), 3)*` and `atoms(((1, 2), 3))` → `[1, 2, 3]`.
- **Lineage:** **Replaces the syntax** of #91. The postfix spread `...` (#103/#104/#111) composed with it (`Pair.content...`). #129 (7458502, 2026-06-26) **removes** `content` because `Group...` covers it. #140 then **replaces the syntax** of `...` with the postfix `*`.
- **Classification:** REMOVED
- **Surviving part / superseded by:** Nothing of the name survives; the builtin was deleted by #129 (7458502). Its one-level opening role lives in the spread marker `v*` (Lean `spreadItems`, lean/KatLang.lean:1273).
- **Current evidence:** 7458502 removed it from `BuiltinRegistry.cs`, Lean, tutorial and generator files. `BuiltinRegistry.cs` has no `content` entry, and the name no longer resolves.
- **Probe:** `(1, 2, 3).content` and `content((1, 2, 3))` → `UnresolvedImplicitParams`.
- **Topics:** SEQ, SUP, COLL, SYN

### #99 — Add variadic group destructuring in parameter patterns
- **Dates:** created 2026-05-08 · closed 2026-05-08
- **Problem / question:** Stateful loops such as the Yellowstone sequence needed to keep a growing history as ONE state slot while binding its items in the step, without verbose `history.content`.
- **Decision / intended invariant:** af92bad ("Generalize recursive parameter patterns") added nested parameter patterns with a variadic (now collecting) inner binding. `(history...)` consumes ONE argument slot and binds that group's IMMEDIATE items: one level only, with nested groups preserved. It combines with other parameters (`F((xs...), a, b)`) and works in loop steps ("open on input, close on output"). The ellipsis is explicit. `F(1, 2, 3)` against `F((xs...))` must NOT match. `F((x))` is a one-item group pattern, not "bind all contents". A Stage 2 for conditional branches (`Classify((items...)) = …` / `Classify(x) = …`) was proposed.
- **Rationale:** No implicit flattening. Keep the loop-state shape stable and avoid materializing an intermediate `content` result.
- **Examples:** `F((xs...)) = xs.count` / `F((1, 2, 3))` → 3. `F(((1, 2), 3))` → 2. `YSStep((history...), pre2, pre1) = { Next = FindNext(history, pre1, pre2)` / `history; Next, pre1, Next }` / `YSStep.repeat(27, (1, 2, 3), 2, 3):0`. Current equivalent: `YSStep((*history), pre2, pre1) = { Next = FindNext(history*, pre1, pre2)` / `(history*, Next), pre1, Next }`.
- **Lineage:** **Extends** #96 (collecting loop steps) and replaces #98's `.content` idiom. **Refined** by #102 (the `reduce` accumulator: `Append(item, (*history))`), #121 (repeated bind names), #126 (movable-rest deconstruction) and #138/#140 (syntax `(*xs)`; collected items form an exact list). **Narrowed and redefined** by the parentheses-group-syntax rule and #168 (Sep 22 2026): the pattern opens the argument's VALUE, and the #99-era written-slot view `explicitGroupItems?` is deleted. S3 (Sep 22 2026) **generalizes** the scalar one-item fallback to every group size. #134 means lists open too.
- **Classification:** PARTIALLY CURRENT
- **Surviving part / superseded by:**
  - **Survives:** a nested sequence-value pattern with a collecting binding, e.g. `F((*xs))`. It consumes ONE argument slot and opens its value exactly ONE level; nested structure is preserved. It mixes with fixed parameters, works for loop state, and a multi-argument call is an arity error. `(x)` stays a one-item pattern: a pair is rejected.
  - **Changed:** "explicit group required" as a written-slot property is gone. Patterns now open the VALUE: a sequence or list opens, and a scalar is a one-item supply (`F(7)` → `xs = [7]`). At #99 time the scalar fallback applied only to one-item group patterns (af92bad `bindParameterPattern` `.group` arm).
  - **Removed:** the `;` join in the examples (#125), and the `...` spelling (→ `*`).
  - **Never landed:** Stage 2. A multi-clause family with collecting bindings is rejected with `InvalidCollectingBinding` "Collecting bindings are only supported in ordinary explicit parameter lists" (src/KatLang/Parser.cs:1558, a rule dating from 3bc2a29/#73). A single-clause definition elaborates to an ordinary user algorithm and does support nested collecting patterns. *(2026-11-28, current-rule pointer: since the owner decision of 2026-11-27 (Q-47, RESOLVED BY DECISION) a clause family collects inside a list or sequence pattern of an argument, and only a collector directly among a family's call arguments is `InvalidCollectingBinding`, with a new wording; `constitution.md` PAT-04, `open-questions.md` Q-47.)*
- **Current evidence:** lean/KatLang.lean:4881-4926 `bindParameterPattern` `.sequenceValue` arm ("PATTERN PARENTHESES ARE CALL-SHAPE SYNTAX, NOT A RUNTIME BOUNDARY"), :1304 `sequenceValuePatternItems`, :1285 `structureItems?`, :181 `minimumSuppliedSlots`. src/KatLang/Evaluator.ParameterBinding.cs:766 `SequenceValuePatternItems`. Spec cases `supply-vs-value-patterns` (LanguageSpecCorpus.cs:1437; `CountSequenceValue((*values))` over `(1, 2, 3)` → 3 versus `CountValues(*values)` → 1) and `redundant-call-parens-canonical` (:1607). `EvaluatorLoopTests.Eval_SequenceValueVariadicLoopStep_YellowstoneHistoryNeedsNoCleanup` (:1481; first 30 Yellowstone numbers). Lean `CoreTests/HigherOrderCalls.lean:717-821` (YSStep). `CallbackNestedPatternBindingTests`.
- **Probe:** `F((*xs)) = xs.count`: `F((1, 2, 3))` → 3, `F(((1, 2), 3))` → 2, `F(7)` → 1, `F([1, 2, 3])` → 3. `G((*xs)) = xs:0` / `G(((1, 2), 3))` → `(1, 2)`. `H((*xs), a, b) = xs.count, a, b` / `H((1, 2, 3), 4, 5)` → `(3, 4, 5)`. `F(1, 2, 3)` → `ArityMismatch` ("`F((*xs))` expects 1 argument, … 3"). `F((x)) = x` / `F((1, 2))` → `ArityMismatch` ("`(x)` expects 1 value, but received 2"). `Step((*history), previous) = (history*, previous + 1), previous + 1` / `Step.repeat(2, (1, 2), 2):0` → `(1, 2, 3, 4)`. `Classify((a, *items)) = …` / `Classify(0) = 100` → parseFailure `InvalidCollectingBinding`. All paths agree.
- **Topics:** PAT, VAR, LOOP, SUP
- **Lineage review (phase 2) corrections/addenda:**
  - [conditional-patterns] PARTIALLY CURRENT (lineage: 'S3 generalizes the scalar one-item fallback to every group size') → PARTIALLY CURRENT (lineage: ordinary binder generalized by 416e9c7/#126 on 2026-06-19; S3 only fixed the counted callback binder). Evidence: `git log -S "A non-grouped scalar is a one-item stream"` shows 416e9c7 (#126) introduced the every-size scalar fallback in the non-counted bindParameterPattern while explicitly leaving the counted callback binder strict ('Callback deconstruction is intentionally deferred'); memory note s3-callback-nested-pattern-binding-2026-09 confirms S3 found only the callback binder singleton-only. Classification unchanged.

### #100 — Unify callable signatures and binding layout metadata
- **Classification:** IMPLEMENTATION ONLY — internal refactor (commit 4d55777) introducing `CallableSignature` / `CallableArityFacts` / `CallableBindingPlan` with "no runtime semantics change"; the models survive as internal machinery in `src/KatLang/Signatures/` (`CallableBindingPlan.cs:3`, `CallableSignature.cs:24`, `internal closed record CallableBindingNode` at `CallableBindingPlan.cs:307`), deliberately non-public per AGENTS.md "signature and binding planners (`Signatures/`)" pinned by `HostApiContractTests`. The one semantic distinction it restated (a grouped pattern `PairSum((x, y))` consumes ONE top-level slot; flattened captures ≠ argument slots) is the rule later formalized as F4 `ParameterPattern.MinimumSuppliedSlots` / Lean `minimumSuppliedSlots`, but #100 did not decide it. Its `values...` spellings are obsolete (`*values`).
- **Topics:** CALL, VAR, TOOL

### #101 — Reconsider implicit final-argument unpacking in flat fixed calls
- **Dates:** created 2026-05-11 · closed 2026-05-13
- **Problem / question:** A flat fixed callee silently unpacked a single multi-output/grouped final argument into several fixed parameters (`Add(Pair)` with `Pair = (10, 20)` gave 30), coupling binding to the evaluated output shape instead of the written argument structure.
- **Decision / intended invariant:** Remove implicit final-argument unpacking: a flat fixed call binds SOURCE argument slots; one argument expression is one argument whatever its value shape. `Add(Pair)` is a bad-arity call ("expects 2 arguments, but got 1"). Multi-value supply must be explicit (at the time `;` join; `.content` opens a group level but is not argument spreading — commit 5555cd1 message).
- **Rationale:** coherence between flat fixed calls, grouped parameter patterns, loop state slots, and group preservation; binding must not depend on evaluated shape.
- **Examples:** `Pair = (10, 20)` / `Add(x, y) = x + y` / `Add(Pair)` → arity error; workaround in the issue `Add(Pair.content:0, Pair.content:1)`. Current equivalent: `Add(Pair*)` or `Add(Pair:0, Pair:1)` (`.content` no longer exists).
- **Lineage:** generalizes #61 (an argument expression does not implicitly spread into the surrounding sequence) and #74 (dot-call receiver boundary) to fixed user-call binding; immediately motivated #103 (explicit spread operator, reverted) and #104 (`...` supply replacing `;`); #111 later re-opened values only at FLAT VARIADIC slots (never fixed ones); #132 (property/call boundary returns one sequence value) reaffirms; #167 + C-full commit 702e7d7 (2026-09-23, "values stay values") generalizes the invariant to every receiver — callbacks included (the flat-callback row convention that still let `map([(1, 2)], Add)` open a pair was deleted then); #129 removes the `.content` workaround; #140 replaces the spread spelling with `*`.
- **Classification:** CURRENT
- **Surviving part / superseded by:** The invariant survives unchanged for fixed parameters and was generalized. Only the surrounding syntax of the issue's workaround is obsolete (`.content` removed by #129; `;`-join removed by #125; spread is `Pair*`).
- **Current evidence:** Lean `bindParams` (lean/KatLang.lean:2479, length check before zipping; payload = complete inputs) and C# `BindParams`; spec case `fixed-call-preserves-boundaries` (tests/KatLang.Tests/LanguageSpec/LanguageSpecCorpus.cs:775–787, probes `Add(Pair*)` and `Add(Pair:0, Pair:1)` → 30) and `values-stay-values` probe `Add((1, 2))` → err arity (LanguageSpecCorpus.cs:1284); `docs/design/language-rules/sequences-lists-and-calls.md` § Call argument assembly and written-slot reification, § Arity error payloads, § Collecting parameter lists ("a fixed position never opens a sequence or list argument"); law `collector_fixed_parameter_binds_value_unchanged` (lean/KatLangArityLaws.lean:899); tests `ExplicitValueOpeningTests`.
- **Probe:** `Pair = (10, 20)` / `Add(x, y) = x + y` / `Add(Pair)` → err ArityMismatch ("Callable `Add(x, y)` expects 2 arguments, but was called with 1 argument."); same with `Pair = 10, 20` → err ArityMismatch; `Add(Pair*), Add(Pair:0, Pair:1)` → `S[30, 30]`; `Add(Pair.content:0, Pair.content:1)` → err UnresolvedImplicitParams (`content` is no longer a builtin).
- **Topics:** CALL, SUP, VAL, SEQ

### #102 — Support variadic accumulator-state binding in `reduce` callbacks
- **Dates:** created 2026-05-11 · closed 2026-05-11
- **Problem / question:** `Append(item, history...) = (history; item)` with `reduce(2, 3, 4, Append, 1)` produced nested groups `((1, 2), 3), 4` because the accumulator reached the variadic `history...` as ONE grouped argument; the issue wanted parity with variadic loop-step state (#96).
- **Decision / intended invariant (at the time):** `reduce` owns its callback invocation model: when the reducer's accumulator side has a top-level variadic parameter, the accumulator's top-level items are spread into those variadic state slots (`Append(3, 1, 2)`); a non-variadic accumulator parameter keeps the accumulator as one structural slot; ordinary variadic call binding unchanged (commit 33b318a).
- **Rationale:** reduce as a state-transition construct should mirror `while`/`repeat` variadic step-state binding.
- **Examples:** `Append(item, history...) = (history; item)` / `reduce(2, 3, 4, Append, 1)` → expected `1, 2, 3, 4`; `Sum(item, total) = total + item` → 10. Current equivalent of the intended program: `Append(item, (*history)) = (history*, item)` / `reduce((2, 3, 4), Append, 1)`.
- **Lineage:** refines #80 (variadic parameters and reduce) and follows #96 (variadic loop steps); narrowed/reworded through #135 (collection builtins take one fixed collection; reduce keeps "accumulator order and callback contract") and #138 (collecting bindings collect exact lists); the Sep 2026 collector supply-boundary law (memory note collector-supply-boundary-law-2026-09, commit dada1b6) still treated reducer accumulator slots as "final items"; REVERSED by #167 / C-full (commit 702e7d7, 2026-09-23), which deleted Lean `reducerAccumulatorSideHasTopLevelCollecting` and `evalReducerAccumulatorVariadicCallbackCallCounted` (visible in `git show 702e7d7 -- lean/KatLang.lean`) and made the reducer an ordinary two-argument call.
- **Classification:** SUPERSEDED
- **Surviving part / superseded by:** Superseded (reversed) by THE CALLBACK LAW of #167 / C-full 702e7d7: `reduce(xs, R, init)` calls `R(element, accumulator)` with each ONE ordinary argument; an accumulator-side collector `Acc(x, *acc)` collects `[acc]`; only an explicit structural pattern opens the accumulator (`Append(item, (*history)) = (history*, item)`). What survives from #102: scalar reducers unchanged; a non-variadic accumulator parameter binds the whole accumulator.
- **Current evidence:** Lean `evalSequenceReduceStepCounted` (lean/KatLang.lean:5500–5516, docstring "a structured accumulator is opened only by the reducer's own explicit pattern") and `evalReduceCounted` (5656–5700); C# `EvalSequenceReduceStepCounted` (src/KatLang/Evaluator.Builtins.cs:420) and async mirror (Evaluator.Async.cs:2941); `sequences-lists-and-calls.md` § Collecting parameter lists, deconstruction, and callbacks ("The reducer's accumulator is one argument too … `Append(item, (*history)) = (history*, item)`"); spec case `callback-element-is-one-argument` probe `Acc(x, *acc) = acc` / `reduce([9], Acc, (1, 2))` → `[(1, 2)]` (LanguageSpecCorpus.cs:1307); theorem `callback_accumulator_is_one_ordinary_argument` (lean/CoreArityAlgebraProofs.lean:889); tutorial.md:1273 (`reducer(element, accumulator)`).
- **Probe:** `Append(item, *history) = (history*, item)` / `reduce((2, 3, 4), Append, 1)` → `S[S[S[1, 2], 3], 4]` (the nesting #102 called wrong is current law); `Append(item, (*history)) = (history*, item)` / same call → `S[1, 2, 3, 4]`; `Sum(item, total) = total + item` → 10 and non-variadic `Append(item, history) = (history, item)` → `S[S[S[1, 2], 3], 4]`.
- **Topics:** HO, VAR, COLL, LOOP, SUP

### #103 — Add explicit result-stream spread operator for call argument supply
- **Dates:** created 2026-05-12 · closed 2026-05-12
- **Problem / question:** After #101 removed implicit unpacking, an explicit way was needed to use a multi-output expression as an argument stream.
- **Decision / intended invariant (at the time):** postfix `expr...` = explicit stream expansion, allowed only in stream-supply contexts; `;` remains the ONLY stream join; comma must NOT join a spread with a following argument (`Sum(Values..., 7)` invalid, write `Sum(Values...; 7)`); `.content` opens a group level but never spreads; dot-call receiver spread allowed only when the callee's receiver parameter is top-level variadic (`(Pair...).Add` invalid for `Add(x, y)`), preserving `receiver.P(args) == P(receiver, args)`.
- **Rationale:** restore ergonomic multi-output supply without undoing #101: "single expression boundary = one argument; explicit `...` = expansion; explicit `;` = joining". Comments: users would write `Add(Pair; empty)`; maintainer proposed `x...y` as the single join/spread construction and removing `;` — this became #104.
- **Examples:** `Pair = 10, 20` / `Add(Pair...)` → 30; `Pair = (10, 20)` / `Add(Pair.content...)` → 30; `Sum(Values...; 7)` → 37; `(Values...).Sum` valid only for a variadic `Sum`. Current equivalents: `Add(Pair*)`, `Sum(Values*, 7)`, `Values*.Sum`.
- **Lineage:** follows #101; implementation 40f7745 was REVERTED the next morning (a025cbe, 2026-05-13) and replaced by #104 (`...` as general supply + join, `;` removed); the spread concept was then reshaped by #119, #122 (split output join from supply), #124 (postfix-only, unary), #125 (semicolon removed for good), #139 (prefix/postfix ellipsis roles) and #140 (star syntax: postfix `expr*`); `.content` removed by #129.
- **Classification:** SUPERSEDED
- **Surviving part / superseded by:** Superseded by #104 (same day, after revert) and ultimately by the postfix spread marker `expr*` (#140; `syntax.md` § The spread marker). Surviving idea only: explicit postfix spread is the single general way to open a value into an argument supply, and `Add(Pair)` stays an arity error. Reversed specifics: comma after a spread is now the REQUIRED separator (`Sum(Values*, 7)` = 37); dot-call receiver spread is allowed for ANY callee (`A*.F` ≡ `F(A*)`, so `Pair*.Add` = 30); `;` and `.content` no longer exist. Note: `(Pair*).Add` is still an arity error today, but for a different reason — `(A*)` is a CAPTURE receiver, i.e. one argument (`(A*).F` ≡ `F((A*))`).
- **Current evidence:** `docs/design/language-rules/syntax.md` § Star roles and § The spread marker (SYN-07B); `sequences-lists-and-calls.md` § Spread semantics ("A comma is REQUIRED between a spread and a following item") and § The dot-call receiver; Lean law `spread_dot_receiver_is_ordinary_spread_argument` (lean/KatLangArityLaws.lean:496); `Expr.SequenceSpread` (unary) in C#/Lean `sequenceSpread`; tests `StarSyntaxTests`, `MarkerAttachmentTests`, `DotCallValueBoundaryTests`.
- **Probe:** `Values = 10, 20` / `Sum(*values) = values.sum` / `Sum(Values*, 7)` → 37; `Sum(Values, 7)` → err ArityMismatch (sum rejects the sequence element); `Pair = 10, 20` / `Add(x, y) = x + y` / `Pair*.Add, (Pair*).Sum2` (with `Sum2(*v) = v.count`) → `S[30, 1]`; `(Pair*).Add` → err ArityMismatch.
- **Topics:** SUP, SYN, CALL, DOT, VAR

### #104 — Consider replacing semicolon result join with ellipsis stream join
- **Dates:** created 2026-05-13 · closed 2026-05-13 (comment update 2026-05-14)
- **Problem / question:** `,` and `;` looked alike and often gave the same visible result; unify explicit supply and joining in one construction.
- **Decision / intended invariant (at the time):** `...` is the "sequence supply operator": infix `x...y` supplies x's result sequence followed by y's; postfix `x...` ≡ `x...empty`; `;` result join removed; `,` separates structural segments; `()` preserves grouping; `{}` creates scope; no general auto-spreading — a normal comma segment contributes one argument item, a `...` segment its result sequence (so `Sum(Values..., 7)` is valid). One narrow exception: VARIADIC CAPTURE STREAM FORWARDING — a bare reference to a binding created by a variadic capture (`values...`, `(history...)`, `(head, tail...)`) carries stream provenance and expands only when allocated to the callee's flat top-level variadic capture (name-independent; never into fixed/suffix/grouped positions). Comment (2026-05-14, #111): segments assigned to a flat variadic capture additionally supply their emitted top-level items (`Qmean(Vector)` ≡ `Qmean(Vector...)`), while fixed/prefix/suffix/grouped positions keep boundaries.
- **Rationale:** ellipsis reads as "many values / continuation"; removes the `,`/`;` confusion; keeps #101's boundary cleanup; forwarding exception for ergonomics.
- **Examples:** `Tail = 2, 3` / `Use(1, Tail)` → bad arity, `Use(1, Tail...)` → 6, `Use(1...Tail)` → 6; `A = 1...{ 2, 3 }` → `1, 2, 3` vs `A = 1, { 2, 3 }` → `1, (2, 3)`; `1; 2` → use `1...2`. Current equivalents: `Use(1, Tail*)`; `A = (1, { 2, 3 }*)`; no infix join.
- **Lineage:** replaces syntax of #75 (semicolon redesigned as result join) and supersedes #103; its forwarding exception is the subject of #106/#108; refined by #111 (variadic-slot supply) and #112 (dot receiver follows the same allocation); then #119 (newline after postfix `...`), #122 reverses the `;` removal (brings `;` back as output join, keeps `...` for supply only), #123/#124 (supply postfix-only and unary; binary `x...y` removed), #125 removes `;` again for good; #128 removes `empty`; #138 removes stream-provenance forwarding (exact-list collection + ordinary list spread); #139/#140 respell `...` as prefix collect `*name` / postfix spread `expr*`; #167 + C-full (702e7d7) removes the last trace of the #111 variadic-slot opening.
- **Classification:** PARTIALLY CURRENT
- **Surviving part / superseded by:** Survives: `;` is not KatLang expression syntax (current parser diagnostic `UnsupportedSemicolon`, reached after the #122 round-trip); explicit postfix spread is the only general opener (spelling `*` since #140); a spread followed by a comma is a spread slot plus ordinary slots (`Sum(Values*, 7)` = 37, comma required); a plain argument/property/block is one boundary (`Use(1, Tail)` arity error; nested block stays `1, (2, 3)`); grouped/fixed/suffix positions never expand. Superseded: the `...` spelling (#140); infix `x...y` join and `x...` ≡ `x...empty` (#124, `empty` removed by #128); variadic-capture stream-provenance forwarding (removed by #138, commit ab7d2f5, which deleted `VariadicStreamEnv` — rule doc says it "must never be reintroduced"); the #111 comment's flat-variadic segment opening (`Qmean(Vector)` now fails; `Count(Values)` is 1, not 2) — removed by #167 / C-full 702e7d7.
- **Current evidence:** Parser message src/KatLang/Parser.cs:1639 ("Semicolon is not supported as an expression separator…"), `DiagnosticCode.UnsupportedSemicolon` (src/KatLang/DiagnosticCode.cs:54), KatLang.ebnf:270–272; `syntax.md` § The spread marker; `sequences-lists-and-calls.md` § Spread semantics and § Collecting parameters ("there is no hidden raw-supply metadata … a `variadicSupplyEnv`/`VariadicStreamEnv` … must never be reintroduced"); spec cases `variadic-grouped-and-spread` (LanguageSpecCorpus.cs:1102: `G(A)` with `G(*x) = x.count` → 1, `G(A*)` → 5) and `values-stay-values` (1260); law `forwarding_resupplies_the_collected_items` (KatLangArityLaws.lean:658); `git log -S VariadicStreamEnv` last touches ab7d2f5 (17 removed lines, only comment mentions remain).
- **Probe:** `1; 2` → parseFailure UnsupportedSemicolon; `1...2` and `(1, 2)...` → parseFailure UnexpectedToken; `empty` → err UnresolvedImplicitParams; `Use(1, Tail*)` → 6, `Use(1, Tail)` → err ArityMismatch; `A = 1, { 2, 3 }` / `B = (1, { 2, 3 }*)` / `A` / `B` → `S[S[1, S[2, 3]], S[1, 2, 3]]`; `Sum(*values, val) = values.sum + val` → `Sum(Values*, 7), Sum(Values*)` → `S[37, 30]`; `Sum(*values, val) = values.count` / `Sum(Values, 7)` → 1; `Qmean(*args) = …` / `Qmean(Vector)` → err TypeMismatch, `Qmean(Vector*), Vector*.Qmean` → both 6.2048…; `Count(*args) = args.count` / `Count(Values), Count(Values*)` → `S[1, 2]`.
- **Topics:** SUP, SYN, CALL, VAR, FWD, SEQ

### #105 — Regression in KatLang user-defined variadic dot-call receiver binding.
- **Dates:** created 2026-05-13 · closed 2026-05-13
- **Problem / question:** After #104, `Mean(vector...) = vector.sum` accepted `Mean(1, 2)` but `(1, 2).Mean` failed.
- **Decision / intended invariant (at the time):** `(1, 2).Mean` should behave like `Mean(1, 2)`: a lexical dot-call receiver expands into the leading flat variadic parameter stream when the binding plan confirms that shape; grouped receivers keep their boundary for non-variadic and patterned callees (commit b8a1bca).
- **Rationale:** symmetry between fluent and plain call syntax for variadic callees (earlier established by #89).
- **Examples:** `Mean(vector...) = vector.sum` / `(1, 2).Mean` → 3 expected. Current: `(1, 2)*.Mean` → 3; `(1, 2).Mean` ≡ `Mean((1, 2))` → error.
- **Lineage:** regression of #89 (inline grouped dot-call receiver binding to variadic parameter, fixed 5cf09fc); refined by #112 (receiver = ordinary leading segment, variadic opening only after prefix/variadic/suffix allocation); reaffirmed by #144 (2026-08-11, collecting parameter consumes the receiver segment's emitted items); REVERSED by #167 — commit 68b3607 "Make dot-call pass values without implicit spreading" (2026-09-21) and C-full 702e7d7 (2026-09-23), which deleted the receiver-segment machinery (`CollectingSegmentEmittedCount` / `collectingSegmentCount?`, `CallArgumentAssembly`).
- **Classification:** SUPERSEDED
- **Surviving part / superseded by:** Superseded (reversed) by "DOT-CALL PASSES A VALUE" (#167, 68b3607) plus the exact collector law (C-full 702e7d7): `R.F(args)` is exactly `F(R, args)` with the receiver ONE ordinary leading argument, so `(1, 2).Mean` collects `vector = [(1, 2)]`; only `R*.F` opens the receiver. What survives is the symmetry goal itself — fluent and plain calls agree — but in the opposite direction (`(1, 2).Mean` ≡ `Mean((1, 2))`, not `Mean(1, 2)`).
- **Current evidence:** `sequences-lists-and-calls.md` § The dot-call receiver; Lean `prepareLexicalDotCallArgs` (lean/KatLang.lean:4337); C# `BuildLexicalReceiverCallArgs` (src/KatLang/Evaluator.DotCalls.cs:51); laws `dot_receiver_is_one_collected_item` (KatLangArityLaws.lean:509) and `dot_call_uses_same_collector_binding_as_plain_call` (684); spec case `dot-receiver-passes-a-value` (LanguageSpecCorpus.cs:1220; probe `(1, 2, 2.718).Mean` → err arity, `(1, 2, 2.718)*.Mean` → 1.906, `(1, 2).Collect` → `[(1, 2)]`); tests `DotCallValueBoundaryTests`, `DotCallCollectingReceiverTests`.
- **Probe:** `Mean(*vector) = vector.sum` / `Mean(1, 2), (1, 2)*.Mean` → `S[3, 3]`; `(1, 2).Mean` → err ArityMismatch ("sum expects each collection element to be a single numeric value; item 0 was sequence value"); `Coll(*vector) = vector` / `(1, 2).Coll, Coll(1, 2)` → `S[L[S[1, 2]], L[1, 2]]`.
- **Topics:** DOT, VAR, SUP, CALL

### #106 — Regression: variadic parameter forwarding now requires explicit sequence supply
- **Dates:** created 2026-05-13 · closed 2026-05-13
- **Problem / question:** After #104, `CountItem(values, candidate)` inside `Mode(values...)` (forwarding a variadic parameter to `CountItem(values..., item)`) no longer worked without writing `values...`; the reporter called requiring `...` on both declaration and supply sides a "bad approach".
- **Decision / intended invariant (at the time):** a bare reference to a top-level variadic parameter forwards its captured stream into a compatible flat variadic capture without explicit supply; ordinary values, fixed parameters, grouped/patterned variadics, callback items and dot receivers stay non-spreading (commit 75f0d2b).
- **Rationale:** ergonomics of variadic-to-variadic forwarding.
- **Examples:** `CountItem(values..., item) = values.filter{value == item}.count` / `Mode(values...) = { Freqs = values.distinct.map{CountItem(values, candidate)} … }` / `Mode(1, 1, 2, 4, 4)` → `1, 4`. Current equivalent: `CountItem(*values, item)`, `Mode(*values)`, and forwarding written `CountItem(values*, candidate)`.
- **Lineage:** exception introduced in #104; generalized by #108 (provenance env, grouped captures, name-independent); REVERSED by #138 (2026-07-18, commit ab7d2f5: "No special provenance-based forwarding behavior should be necessary … `Target(items)` → pass one list argument; `Target(items...)` → forward the captured argument slots"), respelled by #140 (`Forward(*items) = Target(items*)`), reaffirmed by C-full 702e7d7 ("no … forwarding mechanism silently spreads a value").
- **Classification:** SUPERSEDED
- **Surviving part / superseded by:** Superseded (reversed) by #138: a collecting binding holds one exact list and a bare written reference passes that ONE list; forwarding is the explicit ordinary spread `values*` (`spread(collect(S)) = S`). Narrow related survivor (not the #106 rule): when the FRONT END synthesizes an implicit forwarding call for a bare callable reference (implicit-argument lifting, e.g. `Use(*items) = CountItems` or `Alias = CountItems`), it inserts an explicit spread iff both destination and source bindings are collecting (`ImplicitArgumentResolver.ForwardAsSpread` / `BuildPatternArgument`, src/KatLang/ImplicitArgumentResolver.cs:1885–1908) — this is elaboration into ordinary `items*`, not runtime provenance. Risk note: the original program now silently computes a different answer rather than failing.
- **Current evidence:** `sequences-lists-and-calls.md` § Collecting parameters ("Forwarding is ordinary list spread … passing the collected list unspread passes one list argument; there is no hidden raw-supply metadata"); tutorial.md:1409–1428 (§ Forwarding Collected Arguments, spec marker `variadic-forwarding-list-spread`); law `forwarding_resupplies_the_collected_items` (KatLangArityLaws.lean:658); spec case `values-stay-values` probe `Forward(*xs) = Target(xs*)` (LanguageSpecCorpus.cs:1286); `ExplicitValueOpeningTests` (aliases and forwarding matrices).
- **Probe:** translated Mode program with bare `CountItem(values, candidate)` → `L[1, 2, 4]` (wrong-but-silent: each call collects `[[1, 1, 2, 4, 4]]`, counts 0); with `CountItem(values*, candidate)` → `L[1, 4]`. `CountItems(*items) = items.count` / `Use(*values) = CountItems(values), CountItems(values*)` / `Use(1, 2, 3)` → `S[1, 3]`. Implicit forwarding: `Use(*items) = CountItems` / `Alias = CountItems` / `Use(1, 2, 3), Alias(1, 2, 3), Use((1, 2, 3))` → `S[3, 3, 1]`.
- **Topics:** FWD, VAR, CALL, SUP

### #108 — Regression variadic parameter should work without sequence supply operator usage
- **Dates:** created 2026-05-13 · closed 2026-05-14
- **Problem / question:** The #106 fix only covered top-level variadic names; a binding from a GROUPED variadic capture `(history...)` passed bare to `FindNext(history..., pre1, pre2)` still produced wrong results (Yellowstone-sequence program).
- **Decision / intended invariant (at the time):** generalize to a variadic stream provenance environment populated by every actual variadic capture (grouped and nested ones included); a bare reference carries provenance and expands only when flat variadic binding assigns its slot to the callee's variadic capture; independent of parameter names; fixed/suffix/grouped-pattern/callback/ordinary boundaries preserved; mirrored in Lean (commit fd1a975).
- **Rationale:** consistency with #106; forwarding "based on capture provenance, not syntax shape or name equality" (#104 body).
- **Examples:** `YSStep((history...), pre2, pre1) = { Next = FindNext(history, pre1, pre2) … }` / `YSStep.repeat(27, (1, 2, 3), 2, 3):0`; `CountItems(items..., last) = items.count` / `Use((history...), last) = CountItems(history, last)` → 3. Current equivalent: `(*history)` pattern and explicit `FindNext(history*, pre1, pre2)`.
- **Lineage:** generalizes #106; REMOVED/reversed by #138 (commit ab7d2f5 deleted `VariadicStreamEnv` / Lean `variadicSupplyEnv`; `git log -S VariadicStreamEnv` shows fd1a975 introduced it and ab7d2f5 last touched it); syntax respelled by #139/#140; reaffirmed as forbidden by C-full 702e7d7 and the rule docs.
- **Classification:** SUPERSEDED
- **Surviving part / superseded by:** Superseded by #138's exact-list collection + ordinary list spread (`history*`). The negative boundaries #104/#108 listed (no expansion into fixed, suffix, or grouped-pattern positions) remain true, trivially, since nothing expands implicitly any more. The stream-provenance mechanism itself is explicitly banned ("a `variadicSupplyEnv`/`VariadicStreamEnv` … must never be reintroduced", sequences-lists-and-calls.md § Collecting parameters; AGENTS.md collecting-parameter bullet).
- **Current evidence:** as #106; plus spec case `values-stay-values` (LanguageSpecCorpus.cs:1260) and nested collecting pattern `(*history)` opening one level (`bindParameterPattern` / `Result.sequenceValuePatternItems`, § Collecting parameter lists, deconstruction, and callbacks).
- **Probe:** `CountItems(*items, last) = items.count` / `Use((*history), last) = CountItems(history, last), CountItems(history*, last)` / `Use((10, 20, 30), 99)` → `S[1, 3]`; non-expansion boundaries `Group(history), TakeLast(0, history), CountGroup(history)` → `S[3, 3, 3]` (history is one list value). Full Yellowstone program translated (`FindNext(*history, pre1, pre2)`, `YSStep((*history), pre2, pre1)` returning `(history*, Next), pre1, Next`, `YSStep.repeat(12, (1, 2, 3), 2, 3):0`): with `FindNext(history*, pre1, pre2)` → `S[1, 2, 3, 4, 9, 8, 15, 14, 5, 6, 25, 12, 35, 16, 7]` (correct A098550 prefix); with bare `FindNext(history, pre1, pre2)` → `S[1, 2, 3, 2, 3, 2, 3, …]` — silently wrong, exactly the symptom #108 reported.
- **Topics:** FWD, VAR, PAT, CALL, SUP, LOOP

### #109 — Remove `Math.RandInt`
- **Dates:** created 2026-05-14 · closed 2026-05-17
- **Problem / question:** `Math.RandInt` (added in 238ff20 for #77) accepted fractional bounds (`RandInt(2.99, 3.2)` → 2 or 3) and was limited to C# `int` (unhandled error at `2147483647`, overflow near decimal max).
- **Decision / intended invariant:** keep an integer generator but renamed `Math.RandomInt(start, end)`: half-open interval (start inclusive, end exclusive — per maintainer comment, matching .NET conventions), both bounds must be whole numbers (error otherwise), result is a whole number (commit 489b77f, also fixing #110). `RandInt` is gone.
- **Rationale:** meaningless fractional bounds; a real integer type was deemed future work, so validation is the pragmatic fix; exclusive upper bound is easier to adjust than inclusive.
- **Examples:** `Math.RandInt(2147483647, 2147483647)` → crash (old); current: `Math.RandomInt(1, 7)` → die roll 1–6; `Math.RandomInt(2.99, 3.2)` → error.
- **Lineage:** narrows #77 (Python-style inclusive `RandInt(a, b)`); companion of #110 (seed / caching concerns, `Math.Rand` → `Math.Random(start, end)`); later refinements: #153 (Decimal128 numerics → bounds limited to ±1e34), #154 (lowercase alias `randomInt`), seeded-randomness work (commit 668ff3c, 2026-09-14; CLI `--random-seed` 5753e84); the issue's `Math.Floor`-of-scaled-draw implementation was replaced by exact bounded-rejection sampling (`SampleUniformInteger`, whose comment explains flooring a scaled draw is biased).
- **Classification:** CURRENT
- **Surviving part / superseded by:** The decision survives intact (name, half-open interval, whole-number bounds, whole-number result, plus `start < end`). Implementation details changed (uniform 128-bit rejection sampling instead of floor; bound domain ±1e34; run-scoped seedable SplitMix64 stream).
- **Current evidence:** src/KatLang/Evaluator.Expressions.cs:864–878 (whole-number, ±1e34, `start < end` checks) and `SampleUniformInteger` (≈1097); registry entry `new("RandomInt", MathMemberKind.BinaryFunction, "randomInt", ParameterNames: ["start", "end"])` (src/KatLang/BuiltinRegistry.cs:373); `docs/design/seeded-randomness-2026-09.md` §5 (`Math.RandomInt(start, end)` algorithm); `docs/design/language-rules/evaluator-and-hosting.md` § Seeded randomness; tests `EvaluatorMathTests.Eval_MathRandomInt_*` (e.g. `RejectsDecimalBounds` with `Math.RandomInt(2.99, 3.2)`, `DoesNotUseInt32RangeLimits`, `RejectsEmptyOrReversedRange`) and `Eval_MathRandInt_IsUnknownMember` (tests/KatLang.Tests/EvaluatorMathTests.cs:289–342); tutorial.md:220–235. No Lean counterpart (randomness is C#-only host/runtime configuration).
- **Probe (seed 42):** `Math.RandInt(1, 7)` → err UnresolvedImplicitParams (unknown member falls back lexically, G-24); `Math.RandomInt(2.99, 3.2)` → err IllegalInEval; `randomInt(3, 3)` → err IllegalInEval; `randomInt(5, 6), Math.RandomInt(-5, -4)` → `S[5, -5]`; `Math.RandomInt(2147483647, 2147483648)` → 2147483647; `Math.RandomInt(79228162514264337593543950334, 79228162514264337593543950335)` → 79228162514264337593543950334; `randomInt(1, 7)` ×3 → `S[6, 1, 5]`.
- **Topics:** RAND, OP

---

## Notes for the constitution

- Laws confirmed current by this batch: (1) a non-spread argument is exactly one argument item whatever its value (from #101, generalized by #167 / C-full); (2) the explicit postfix spread `expr*` is the only general opener, one level (from #103/#104, respelled by #140); (3) `;` is not expression syntax (#104 → #122 round-trip → #125); (4) dot-call passes the receiver as one ordinary leading argument (reverses #105); (5) forwarding is explicit list spread, with no runtime provenance (reverses #106/#108); (6) callbacks, the reducer's accumulator included, are ordinary calls with one argument per element/accumulator (reverses #102); (7) `Math.RandomInt` is half-open over whole-number bounds (#109).
- Reversal pattern worth recording: #102, #105, #106, #108, and the #111 refinement in #104's comment all added convenience opening/forwarding for variadic callees within four days (May 11–14 2026). All of it was removed by #138 (July) and #167 / C-full (September 23). The old programs from #106 and #108 now evaluate SILENTLY to different results instead of failing (probes above), which may deserve a migration or diagnostic note.
- AGENTS.md agreement check: its claims about dot-call receivers, collector exactness, forwarding (`variadicSupplyEnv`/`VariadicStreamEnv` banned), the reducer accumulator (`Acc(x, *acc)` collects `[acc]`), the semicolon diagnostic, and the random stream all matched code, Lean, spec cases, and probes. I found no disagreement.

### #110 — Concern random seed for `Math.Rand`
- **Dates:** created 2026-05-14 · closed 2026-06-16
- **Problem / question:** `Pair = (Math.Rand, Math.Rand)` printed the same random number twice ("unexpected twins"), while `ParameterizedPair = (rand(0), rand(0))` printed different numbers. The problem was not the seed. It was the per-run zero-argument property result cache (introduced for #42, 6fe4f51). A zero-parameter builtin or property read by name was memoized, and `Math.Rand()` was not. Randomness is observably impure, so the question was how caching should interact with it.
- **Decision / intended invariant:** The rule converged over 13 comments:
  1. Property-style access `A` of a zero-parameter property is cached per run. An explicit call `A()` asks for a fresh evaluation.
  2. Freshness is LOCAL. `B()` re-evaluates only `B`; the nested `A` inside `B = A, A` keeps its cached meaning (comment 10). This reversed comment 9's proposal of recursive freshness.
  3. There is no purity or side-effect tracking and no builtin exclusion from the cache. d7629b6 "Exclude builtins from zero-arg property cache" was reverted by 1cac168.
  4. Random generation is redesigned as a parameterized call `Math.Random(start, end)` over a half-open interval `[start, end)`, so it can never be a cached zero-parameter property. The companion is `Math.RandomInt(start, end)` (#109).
  5. Because caching is now observable, the zero-parameter cache is core semantics and is modeled in Lean (comment 12, d843523).
- **Rationale:** Zero-parameter properties should read like variables and be cheap without the user thinking about it. The call shape `()` is the explicit freshness marker. Impurity tracking was judged too complex for its benefit. A library author must be able to reason locally from a property body, independent of how callers invoke the outer property. `Random(start, end)` avoids offering both a "right" and a "wrong-looking" spelling, and one symmetric half-open API avoids the .NET `Next`/`NextDouble` asymmetry.
- **Examples:**
  - Original: `Fun = Math.Rand(), Math.Rand()` then `Fun, Fun` gives the same pair twice, while `Fun(), Fun()` gives two different pairs.
  - Current equivalent: `A = Math.Random(0, 1)` / `B = A, A` / `A, A` / `A(), A()` / `B(), B()`.
- **Lineage:**
  - Refines #42 (per-run memoization, which introduced the cache) and #77 (Random feature).
  - Sibling of #109: `RandInt` was renamed to `RandomInt` with a half-open interval and integer checks. Both were closed by 489b77f.
  - Reverses its own interim fix d7629b6 (reverted by 1cac168) and the recursive-freshness proposal (e0599ba "Keep zero-arg call freshness local").
  - Generalized by d843523 (cache modeled in Lean).
  - Refined by 31f7c76 (2026-09-12, cache keyed by binding and exposure).
  - Refined by 2d47a93 (2026-09-22, zero-argument demand follows call arity, so `Only(*xs) = xs` is cacheable).
  - Refined by #170 / ebf623e (2026-09-27): cache identity follows semantic binding identity, and how a value is consumed never affects caching.
  - Host seeding, which the title literally names, was added much later and separately: 668ff3c (2026-09-14, seeded SplitMix64 stream, `RunOptions.RandomSeed`), and 5753e84 (`--random-seed`).
- **Classification:** CURRENT
- **Surviving part / superseded by:** The final decision survives in full: cached `A`, locally fresh `A()`, no impurity tracking, parameterized `Random(start, end)` over `[start, end)`, and the cache as Lean-modeled semantics. The interim ideas are gone: builtin exclusion from the cache, recursive freshness, and the zero-parameter `Math.Rand` / `Math.RandInt`. #170 strengthened the rule. Consumers such as `sum(A)`, `A.sum`, and `if(c, A, B)` all read the one cached entry, and purity is explicitly irrelevant.
- **Current evidence:**
  - `docs/design/language-rules/evaluator-and-hosting.md` § Zero-argument property cache ("an explicit call `A()` … neither reads nor replaces A's entry … while the property reads nested inside that fresh evaluation keep their own rules"; "purity is irrelevant").
  - The same file, § Seeded randomness.
  - Lean `lean/KatLang.lean:1467` `ZeroArgPropertyCacheKey`, `:1478` `ZeroArgPropertyCache`, `:3905` `isCacheableZeroArgPropertyAlgorithm`, `:5404` `evalZeroArgPropertyAccessCounted`, plus `lean/CoreTests/PropertyCacheConsumers.lean`.
  - C#: `src/KatLang/Evaluator.Builtins.cs:314` `GetOrEvaluateZeroArgPropertyResult`, `src/KatLang/Evaluation/Caching/ZeroArgPropertyResultCache.cs:64` `ZeroArgPropertyCacheKey`, `src/KatLang/BuiltinRegistry.cs:372-373` (`Random` / `RandomInt`, `ParameterNames: ["start", "end"]`), and `Evaluator.Expressions.cs:1085` `ScaleRandomUnitFractionToHalfOpenRange`.
  - Tests in `ZeroArgPropertyResultCacheTests`: `Evaluator_ZeroArgPropertyCaching_PropertyStyleAccessReusesRandomPropertyResult`, `…ExplicitZeroArgCallBypassesCache`, `…ExplicitZeroArgCallKeepsNestedPropertyStyleAccessCached`, and `…OuterFreshCallsDoNotForceNestedPropertyFreshness`. Also `PropertyCacheConsumerTransparencyTests` and `ZeroArgPropertyCacheScopeTests`.
  - `tutorial.md:305-316` (`Roll = randomInt(1, 7)`, `Roll == Roll` is `true`, while `Roll() == Roll()` rolls twice).
- **Probe:**
  - `p110a.kat` run with `--seed 42`: `A = Math.Random(0, 1)` / `B = A, A` / `A, A` / `A(), A()` / `B(), B()` gives:
    - `A, A` → `0.79457…, 0.79457…` (cached twins);
    - `A(), A()` → `0.39283…, 0.01532…` (fresh, distinct);
    - `B(), B()` → `(0.79457…, 0.79457…)` twice (B re-evaluated, but its nested `A` stays cached).
  - AGREE on all five paths.
  - `Math.Rand` → `UnresolvedImplicitParams` (the member no longer exists). `Math.Random()` → `ArityMismatch`.
- **Topics:** PROP, RAND, CALL, FORMAL, RUN
- **Lineage review (phase 2) corrections/addenda:**
  - [property-caching] CURRENT; lineage: 'reverses … the recursive-freshness proposal (e0599ba)' → CURRENT; lineage: recursive freshness was IMPLEMENTED in 489b77f (2026-05-17) and REVERTED by e0599ba (2026-05-18); 489b77f also recorded the cache as a C#-only runtime policy, which d843523 reversed the next day. Evidence: git show 489b77f: FreshZeroArgCallContext -> ctx.WithZeroArgPropertyResultCache(UncachedZeroArgPropertyResultCache.CreateForRun()), and the commit body says 'Add regression coverage for recursive fresh evaluation'. The 489b77f SEMANTIC-ALIGNMENT diff says 'Lean currently does not model … the C# zero-argument property cache'. e0599ba body: 'instead of recursively disabling cache use'. #110 comment 11: 'Reverted recursive freshness'.
  - [random-numerics] Lineage: recursive freshness was a comment-9 'proposal' reversed by e0599ba → Lineage: recursive freshness was IMPLEMENTED in 489b77f (FreshZeroArgCallContext) and REVERTED in e0599ba the next day (classification CURRENT unchanged). Evidence: git show 489b77f adds FreshZeroArgCallContext at the user/conditional call sites; the e0599ba commit message reads 'Make Fun() bypass only Fun's own zero-argument cache entry instead of recursively disabling cache use'; issue #110 comment 11 says 'Reverted recursive freshness'.

### #111 — Improve variadic calls with variadic-slot sequence supply
- **Dates:** created 2026-05-14 · closed 2026-05-14
- **Problem / question:** Given `Qmean(args...) = …`, the call `Qmean(Vector)` with `Vector = range(1,10)` failed. `Qmean(Vector...)` and `range(1,10).Qmean()` worked. This was an asymmetry between normal calls and dot calls.
- **Decision / intended invariant:** "Variadic-slot sequence supply" (4c9877d):
  1. First allocate argument SEGMENTS to the prefix, variadic, and suffix slots.
  2. Then any ordinary segment that landed in a FLAT variadic capture supplies its emitted top-level items.
  3. Fixed, prefix, and suffix parameters still receive one item each.
  4. Visible parenthesized groups stay one item.
  5. Explicit `...` remains the stronger pre-binding supply.
  6. Provenance forwarding of actual variadic captures (#106, #108) coexists with this rule.
- **Rationale:** Make `F(V)`, `F(V...)` and `V.F()` agree for flat variadic callees without introducing general auto-spreading into fixed parameters.
- **Examples:**
  - Original: `Values = 10, 20` / `Count(args...) = args.count` / `Count(Values)` was expected to give 2. `Pair = (10, 20)` / `Count(Pair)` was expected to give 1. `Sum(values..., last) = values.sum + last` / `Sum(Values, 7)` was expected to give 37.
  - Current equivalent: `Count(*args) = args.count`, and spread is written `Values*`.
- **Lineage:**
  - Refines #105 (b8a1bca, flat variadic dot-call receiver), #106 (75f0d2b), and #108 (fd1a975, variadic provenance forwarding).
  - Follow-up #112 (4685ba0) extended it to dot-call receivers.
  - Superseded by #125 (ad75720, 2026-06-17). #125 explicitly lists "flat variadic capture consumes emitted top-level items after allocation" as the model it replaces, with variadic parameters becoming strict sequence destructuring.
  - Reversed decisively by #138 (ab7d2f5, 2026-07-18). Every collecting binding collects the arguments actually supplied as one exact list, so `F(A)` and `F(A...)` always differ and `Vector.Qmean` became a numeric-element error.
  - Syntax replaced by #139 (eab2468, prefix `...name`) and then #140 (73648e9, `*name` / `expr*`).
  - The dot-receiver remnant ("receiver segment" supply, revived by #144 f12af0f) was removed by #167 / 68b3607 "Make dot-call pass values without implicit spreading".
  - A narrow echo, the "collector supply-boundary law" (dada1b6, 2026-09-21), let a lone written sequence open one level at a collector. It was superseded two days later by 702e7d7, "values stay values" (C-full, 2026-09-23).
- **Classification:** SUPERSEDED
- **Surviving part / superseded by:**
  - Survives only as an independent coincidence: fixed parameters never open an argument (`Add(Pair)` is an arity error, and `Add(Pair*)` is required), and explicit spread is the way to supply items.
  - The core rule, that a segment assigned to a collector supplies its items, is superseded by THE EXACT COLLECTOR LAW: a non-spread argument supplies exactly ONE item whatever its value, and only `v*` opens. See `docs/design/language-rules/sequences-lists-and-calls.md` § Collecting parameters; commits ab7d2f5 and 702e7d7.
  - The "visible grouping `Pair = (10, 20)` differs from `Values = 10, 20`" distinction is also gone. Parentheses are group syntax (#168), so both properties hold the same sequence value.
- **Current evidence:**
  - AGENTS "VALUES STAY VALUES — THE EXACT COLLECTOR LAW" (checked; matches the probes).
  - Lean `lean/KatLang.lean:2889` `collectSegment`, `lean/KatLangArityLaws.lean:592` `collector_lone_sequence_is_one_item`, and `lean/CoreArityAlgebraProofs.lean:565` (same name, algebra layer).
  - `tests/KatLang.Tests/ExplicitValueOpeningTests.cs`, spec case `values-stay-values` (`LanguageSpecCorpus.cs:1260`), and `lean/CoreTests/ExplicitValueOpening.lean`.
- **Probe:** translated to current syntax (`*args`, `V*`), `--paths engine`:
  - `Vector = range(1,10)` / `Qmean(*args) = Math.Sqrt(args.map{x * x}.sum / args.count)`:
    - `Qmean(Vector*)` → `6.2048…`, and `Vector*.Qmean` → `6.2048…`.
    - `Qmean(Vector)` → `TypeMismatch` ("left operand was a list value with 10 elements"), and `Vector.Qmean` gives the same error.
  - `Values = 10, 20` / `Count(*args) = args.count`: `Count(Values)`, `Count(Values*)`, `Values.Count`, `Values*.Count` → `1, 2, 1, 2`.
  - `Pair = (10, 20)` / `Add(x, y) = x + y`: `Add(Pair)` → `ArityMismatch`, and `Add(Pair*)` → `30`.
- **Topics:** VAR, SUP, CALL, DOT, FWD
- **Lineage review (phase 2) corrections/addenda:**
  - [calls-arguments] Surviving-part text attributes the disappearance of the 'Pair = (10, 20) vs Values = 10, 20' distinction to #168 (parentheses are group syntax) → Attribute it to the property value boundary (lexical/user-call re-count to valueCount, in force by #130 daf8a4c / #132 9a4c70f) and the exact collector law (#138 ab7d2f5, 702e7d7); #168 does not apply. Evidence: Parser.IsRedundantGrouping (src/KatLang/Parser.cs:4743-4750) erases only groups with exactly ONE non-spread slot; (10, 20) has two slots and survives #168 as Expr.Capture. The #111-era difference was an emitted-count difference between a two-row body and a one-row capture body, which reCountValueBoundary (lean/KatLang.lean:2910, introduced by 9a4c70f per git log -S) removes.

### #112 — Dot-call receiver expansion should follow flat variadic-slot allocation rules
- **Dates:** created 2026-05-14 · closed 2026-05-15
- **Problem / question:** After #111, with `Values = 10, 20` and `Sum(values..., last) = values.sum + last`, the dot form `Values.Sum` succeeded because the receiver was expanded before binding, while `Sum(Values)` failed. The dot receiver had a stronger pre-binding expansion than the canonical call.
- **Decision / intended invariant:** `receiver.Property(args...)` must behave like `Property(receiver, args...)`. The receiver is an ordinary LEADING ARGUMENT SEGMENT, never an implicit `receiver...`. The #111 variadic-slot supply then applies only after prefix/variadic/suffix allocation (4685ba0 "Align dot-call receiver binding with canonical calls").
- **Rationale:** Dot syntax must not carry a stronger expansion rule than the equivalent call. `Values.Sum` ≡ `Sum(Values)`, not `Sum(Values...)`.
- **Examples:**
  - Original: `Sum(Values)` and `Values.Sum` should both fail. `Sum(Values, 7)` and `Values.Sum(7)` should both give 37. `Sum(Values...)` should give 30.
  - Current equivalent: `Sum(*values, last) = values.sum + last`, with spread written `Values*`.
- **Lineage:**
  - Refines #105 (b8a1bca) and #111 (4c9877d).
  - Regressed and re-fixed within the receiver-segment era: #144 (f12af0f, 2026-08-11) had a collector consume the receiver segment's "top-level output supply".
  - Reaffirmed and strengthened by #167's "DOT-CALL PASSES A VALUE" (68b3607, 2026-09-21). That change deleted `CallArgumentAssembly` and the receiver-segment machinery, so `R.F(args)` is exactly `F(R, args)` and `R*.F` is exactly `F(R*)`.
  - Its variadic-slot half is superseded by #125, then #138, then 702e7d7 (see #111).
- **Classification:** PARTIALLY CURRENT
- **Surviving part / superseded by:**
  - SURVIVES, strengthened: the dot receiver is an ordinary leading argument, and `R.F` ≡ `F(R)`, never `F(R*)`. The same collector binding applies to both spellings.
  - SUPERSEDED: "segments allocated to the flat variadic capture supply their emitted top-level items". Under the exact collector law (702e7d7), `Values.Sum(7)` binds `values = [(10, 20)]`, and the issue's expected 37 is now a `sum` error. Only `Values*.Sum(7)` gives 37.
  - `Sum(Values)` still fails, but differently: `values = []` and `last = (10, 20)`, which gives a `+` TypeMismatch, not a bad arity.
- **Current evidence:**
  - `docs/design/language-rules/sequences-lists-and-calls.md` § The dot-call receiver.
  - Lean `lean/KatLangArityLaws.lean:485` `dot_receiver_is_ordinary_leading_argument`, `:509` `dot_receiver_is_one_collected_item`, and `:684` `dot_call_uses_same_collector_binding_as_plain_call`.
  - `DotCallValueBoundaryTests` and `DotCallCollectingReceiverTests`.
  - Spec case `dot-receiver-passes-a-value` (`LanguageSpecCorpus.cs:1220`).
- **Probe:** translated to current syntax, `--paths engine`. With `Values = 10, 20` and `Sum(*values, last) = values.sum + last`:
  - `Sum(Values)` → TypeMismatch ("right operand was a sequence value … (10, 20)"), and `Values.Sum` gives the identical error.
  - `Sum(Values*)`, `Values*.Sum` → `30, 30`.
  - `Sum(Values*, 7)`, `Values*.Sum(7)` → `37, 37`.
  - With `.count` in place of `.sum`: `Sum(Values, 7)`, `Values.Sum(7)` → `8, 8`, so the receiver collects as one item.
- **Topics:** DOT, VAR, CALL, SUP

### #113 — Dot-call trailing block parsing is accidentally whitespace-sensitive
- **Dates:** created 2026-05-15 · closed 2026-05-15
- **Problem / question:** `range(0, n div 6).filter{ … }.count` worked, but the same code with a space, `.filter { … }`, did not parse as a call with a trailing block.
- **Decision / intended invariant:** The parser must not be whitespace-sensitive here. A same-line `{` (and `(`) after a callable, including a dot-call member, is the call delimiter whether or not whitespace precedes it (e75ec7d).
- **Rationale:** Whitespace within a line should not change the parse.
- **Examples:**
  - Original: `range(0, n div 6).filter { … }.count` ≡ `range(0, n div 6).filter{ … }.count`.
  - Current: the same, except that a filter predicate must now be Boolean.
- **Lineage:**
  - Generalized by #123 (007917a), which states "Same-line whitespace before `(` or `{` call delimiters is allowed". #123 also adds the counterpart: "a physical newline ends a closed expression", so `F` newline `(1, 2)` is not a call.
  - Reaffirmed by the F7 line-rule consolidation (`syntax.md` § Line rules and declaration heads).
  - SYN-07A (#160, 2b03c0b) keeps non-callable targets out of the call gate, so `2 (3)` is a separator error.
- **Classification:** CURRENT *(revised in lineage review; ledger batch said BUG FIX / REAFFIRMED EXISTING RULE)*
- **Surviving part / superseded by:** Fully current as a rule: "A `(` or `{` after a callable target on the same physical line is a call delimiter even across whitespace, while a physical newline never continues a closed expression into a call."
- **Current evidence:**
  - `docs/design/language-rules/syntax.md` § Line rules and declaration heads (F7), first paragraph.
  - `src/KatLang/Parser.cs:4654-4663` `IsCallArgumentStart` (comment: "Same-line whitespace continues a call (`F (1, 2)`, `A.B (1)`, `values.map { ... }`)"), and `Parser.cs:4341-4350`.
  - Tests: `ParserTests.Parse_DotCall_TrailingBlockWithSpace_AttachesAsDotCallArgs` (ParserTests.cs:446) and `EvaluatorCollectionBuiltinTests.Eval_Filter_DotCallTrailingBlockSpacing_ReturnsEquivalentResults` (:204).
- **Probe:** `p113.kat` is the issue's program with `filter {` spacing. The inner and outer `.count` were translated to `.count > 0`, because numeric truthiness was removed by #165. It gives `43` on engine and generic, AGREE. `p113b.kat` (`F(x) = x + 1` / `F (2)` / `[1, 2].map {x * 10}`) gives `3`, `[10, 20]`.
- **Topics:** SYN, DOT
- **Lineage review (phase 2) corrections/addenda:**
  - [output-syntax-layout] BUG FIX / REAFFIRMED EXISTING RULE → CURRENT. Evidence: #113 did not restore an existing rule. It partially reversed a deliberate one, df14e5a (2026-04-02, 'require adjacency between callee and (': the gate `Current.Position == Previous.Position + Previous.Length` for both direct and dot calls). e75ec7d replaced that gate with a same-line check for dot-call argument lists only (IsDotCallArgumentStart). Direct calls kept exact adjacency through 7b5fe7a/65301ce/acbfa7d (Parser.cs:1366/1402/1397 in those commits) until 007917a introduced IsCallArgumentStart. The rule #113 introduced (same-line whitespace before a call delimiter) is current law (ParserTests.Parse_DotCall_TrailingBlockWithSpace_AttachesAsDotCallArgs, spec adjacency-call-across-space). The lineage should name df14e5a as its reversed predecessor.

### #114 — Bare builtin callable aliases do not propagate implicit parameters
- **Dates:** created 2026-05-16 · closed 2026-05-16
- **Problem / question:** User aliases forward implicit parameters (`Test1 = x`, `Test2 = Test1`, `Test2(7)` gives 7), but `RoundB = Math.Round` / `RoundB(1.234, 2)` failed with "expects 0 arguments".
- **Decision / intended invariant:** A bare reference to a builtin CALLABLE in property position forwards the builtin's signature, with the registry's parameter names. `RoundB = Math.Round` elaborates like `RoundB(value, digits) = Math.Round(value, digits)` (c1e19b1: builtin signature reuse during implicit argument resolution, via owner/member lookup).
- **Rationale:** Builtin callables should compose like user callables. An alias should not silently collapse to a zero-argument property.
- **Examples:**
  - Original: `RoundB = Math.Round` / `RoundB(1.234, 2)` gives `1.23`.
  - Current: the same, and also `RoundC = round`.
- **Lineage:**
  - Generalizes user-alias propagation to Math builtins.
  - Extended by #154 (predefined lower-camel-case Math aliases, 2026-08-24): the alias `round` lifts too.
  - Narrowed and clarified by name-resolution audit #8 (`ownership-and-lookup.md` § Math members): "LIFTING a Math function referenced bare as a value is … route-based … owner-walk properties lift (the alias) and so does the qualified `Math.Sin`, while a callable reached through `open` is never implicitly forwarded".
  - Constrained by SYN-05 (builtin identity, never spelling). The recognizer uses spelling only as a registry-metadata key and checks that `Math` is not shadowed.
- **Classification:** CURRENT
- **Surviving part / superseded by:** The issue's case survives for the qualified `Math.X` spelling and the prelude alias spelling. It deliberately does NOT extend to the `open Math` canonical spelling: `open Math` / `RoundD = Round` / `RoundD(1.234, 2)` gives ArityMismatch "expects 0 arguments". It also does not extend to non-Math prelude builtins (see Uncertainty).
- **Current rule pointer (2026-10-01):** the unified formula-lifting law (2026-09-30) extends the issue's title generality to FORMULAS — `C = count + 0`, `open Math` / `R = Round + 0` and `T = trace + 0` lift — while the LONE rows `RoundD = Round` and `C = count` stay as recorded above; their eligibility is open question Q-12. The issue's classification is unchanged.
- **Current evidence:**
  - `src/KatLang/AstHelpers.cs:292` `TryGetRegistryProvenMathAliasFacts` (doc comment: the bare-reference lifting question is route-based).
  - `src/KatLang/ImplicitArgumentResolver.cs:1977` and `:2291`.
  - Tests in `ImplicitArgumentResolverTests`: `Resolve_BareMathCallableAlias_LiftsMemberSignature` (:269, Params `["value", "digits"]`), `Resolve_BareMathCallableAlias_DoesNotUseNativeSignatureWhenMathIsShadowed`, `Resolve_BareBuiltinCallableAlias_DoesNotResolveThroughArbitraryOwnerExpression`, `Eval_BareMathRoundAlias_ForwardsMemberSignature` (:397), and `Eval_BareMathAbsAlias_ForwardsMemberSignature`.
  - `docs/design/language-rules/ownership-and-lookup.md` § Math members, host operations, and the prelude in every layer.
- **Probe:** all `--paths engine`:
  - `RoundB = Math.Round` / `RoundB(1.234, 2)` → `1.23`.
  - `RoundC = round` / `RoundC(1.234, 2)` → `1.23`.
  - `open Math` / `RoundD = Round` / `RoundD(1.234, 2)` → ArityMismatch "Callable `RoundD` expects 0 arguments".
  - `P = Math.Pow` / `P(2, 10)` / `Q = pow` / `Q(2, 3)` → `1024, 8`.
  - `Add(x, y) = x + y` / `A = Add` / `A(1, 2)` → `3`.
  - `S = sum` / `S((1,2,3))` → ArityMismatch "Callable `S` expects 0 arguments".
  - `C = count` / `C([1,2])` → the same kind of error.
- **Uncertainty:** The issue title speaks of "builtin callable aliases" generally, but the fix and every test target Math function members. Non-Math prelude builtins do not lift: `S = sum` evaluates `sum` under the zero-argument value demand ("`sum(collection)` expects 1 argument"), while a user alias `A = Add` does lift. No test, doc, or spec case pins or explains this asymmetry. Settling it needs a maintainer statement, or a test or doc clause declaring whether `S = sum` should be `S(collection) = sum(collection)`.
- **Topics:** PAR, RES, ALG, CALL
- **Lineage review (phase 2) corrections/addenda:**
  - [parameter-inference-grace] CURRENT (decision recorded as: any bare builtin CALLABLE reference forwards the builtin's signature) → CURRENT (decision narrowed: only Math FUNCTION members via qualified Math.X or prelude alias lift; non-Math prelude builtins and open-provided spellings never lift). Evidence: c1e19b1's BuiltinRegistry.TryGetBuiltinCallableSignature returns a signature only when ownerName == "Math". The alias spelling was added by b3738b9. Audit #8 (ad6d6bf) documents lifting as route-based: ownership-and-lookup.md:52 and AstHelpers.TryGetRegistryProvenMathAliasFacts (AstHelpers.cs:292-306). Probes: S = sum; S((1,2,3)) gives ArityMismatch 'expects 0 arguments'; open Math; RoundD = Round; RoundD(1.234, 2) gives ArityMismatch; RoundB = Math.Round and RoundC = round give 1.23.
  - [builtin-surface] CURRENT (general 'builtin callable aliases') → CURRENT for Math function members only; non-Math builtin aliases do not lift. Evidence: Probes: S = sum; S((1, 2, 3)) -> ArityMismatch 'Callable S expects 0 arguments'; T = if; T(true, 1, 2) -> same; while S = abs; S(-3) -> 3. Fix c1e19b1 and all tests target Math members (AstHelpers.TryGetRegistryProvenMathAliasFacts); no doc/test/spec pins the non-Math asymmetry.

### #116 — Parser generates too many errors for from open statement
- **Classification:** IMPLEMENTATION ONLY. f032be3 made a `load` URL that returns HTML produce one clear load-site diagnostic (`ModuleLoader.cs:1910-1918` `BuildLoadedSourceParseErrorMessage` / `:1941` `LooksLikeHtml`). The commit's extra "preserve a follow-on evaluation error after load failure" was later replaced by "every front-end error blocks evaluation" and "a missing module is an analysis state". Probe `p116.kat`, where the module is HTML and the program is `A = load('https://mods.test/example.kat')` / `A.X`, gives exactly one `InvalidLoadedSource` "the URL returned HTML instead of KatLang source", on engine and engineAsync.
- **Topics:** MOD, TOOL
- **Lineage review (phase 2) corrections/addenda:**
  - [open-ownership-modules] IMPLEMENTATION ONLY (follow-on behavior 'later replaced') → IMPLEMENTATION ONLY (follow-on behavior removed by 2a140c9). Evidence: The 'preserve a follow-on evaluation error after load elaboration fails' half of f032be3 was removed in 2a140c9 (2026-09-23). That commit deleted test Run_LoadedHtml_ReportsLoadSiteAndFollowingEvaluationError and introduced 'every front-end error blocks source-based evaluator entry'; 0eb66db (09-26) then made missing modules an analysis state.

### #117 — Add reserved private metadata properties for KatLang libraries
- **Dates:** created 2026-05-28 · closed 2026-05-29
- **Problem / question:** The proposal was to standardize the private, string-valued library metadata properties `Author`, `Version`, and `Description` for tooling. These properties could not be public and would not be visible through `open`.
- **Decision / intended invariant:** It was implemented in 7feb4b1 and then REVERTED by c5c762e. Final decision (comment 3): KatLang reserves NO metadata names. `Name`, `Version`, `Author`, and `Description` are ordinary, freely usable property names. `__Name__`-style dunder names were rejected as un-KatLang. A `License` field was rejected as legally misleading. Licensing is repository-level (MIT for KatLangLib). Descriptive metadata belongs in comments, READMEs, or ordinary properties.
- **Rationale:** Useful domain names must not be stolen. The metadata was not functionally important. A per-file license label gives a false sense of compliance.
- **Examples:** `Author = 'FirstName LastName'` / `Version = '1.0'` / `public X = 20` was the proposed metadata. Today these are ordinary properties.
- **Lineage:** Reverses its own 7feb4b1 (via c5c762e). The general principle "no reserved-name mechanism of any kind" was later reaffirmed at the language level by SYN-05 (builtin identity, never spelling), and the only reserved words are true lexer keywords, such as `true`/`false` from #165.
- **Classification:** REMOVED
- **Surviving part / superseded by:** Nothing of the feature survives. The surviving rule is its negation: these names carry no special meaning, and `public Author` is legal.
- **Current evidence:** `git show --stat c5c762e` deletes `src/KatLang/LibraryMetadataProperties.cs` and the parser, exposure, and semantic-model hooks. A grep for `"Author"`, `"Version"`, and `"Description"` string literals in `src/KatLang/*.cs` finds nothing.
- **Probe:** `public Author = 1` / `Version = 2` / `Obj = { public Description = 3 }` / `Author + Version + Obj.Description` → `6` (`--paths engine`).
- **Topics:** MOD, RES, SYN

### #118 — Add display-only decimal formatting for final output
*(Constitution catch-up, 2026-11-15: the classification is unchanged, and the entry describes the rule of its date. Since the owner decision of 2026-11-12 (`1d3e1354`, "Replaces #118") `DisplayDecimals` has no display meaning: the settings are `MinDecimalPlaces` and `MaxDecimalPlaces`, composed per setting by the minimum of the source and host values — `constitution.md` RUN-06; `open-questions.md` Q-10.)*
- **Dates:** created 2026-05-30 · closed 2026-05-30
- **Problem / question:** Users wanted readable decimal output without changing calculation semantics.
- **Decision / intended invariant:** A top-level ordinary property `DisplayDecimals = n` sets how many decimal places FINAL rendering shows (233a2ae):
  - It is display-only: intermediate values, stored values, comparisons, caching, and evaluation are unchanged.
  - It applies recursively to numeric leaves of displayed structures.
  - It is readable like any property.
  - Duplicate definitions follow ordinary rules.
  - An invalid value (negative, non-integer, or non-numeric) is a clear diagnostic.
  - It is not modeled in Lean, because it is rendering.
- **Rationale:** Readability without semantic rounding. Keep it an ordinary property rather than new syntax.
- **Examples:**
  - Original: `DisplayDecimals = 2` / `A = Math.Pi` / `B = A * 1000` / `A` / `B` displays `3.14` and `3141.59`, while internal values stay full precision.
  - `Vector = (Math.Pi, Math.E)` displays `(3.14, 2.72)`. Current equivalent: `Math.E` was replaced by `Math.Exp(1)` / `exp` (#155).
- **Lineage:**
  - Refined by 96092a6 (2026-09-24, audit #12): ONE effective setting per run through `KatLangEngine.ResolveDisplayOptions`, with this precedence: a declared root property wins, even when it is invalid or fails; otherwise `RunOptions.DefaultDisplayDecimals` / CLI `--display-decimals`; otherwise canonical display.
  - The range is 0..99, owned by `RunOptions.MaxDisplayDecimals`, and is a validity bound, never a clamp.
  - Midpoints round away from zero (spec case `display-decimals-rounds-ties-away-from-zero`).
  - Values with no decimal places are shown as they are.
  - The issue's "per-value annotations override global" and `DisplaySignificantDigits`/`DisplayScientificDigits` ideas were never implemented (nothing found in `src/KatLang`, `tutorial.md`, or `docs/design/language-rules`).
- **Classification:** CURRENT
- **Surviving part / superseded by:** Everything specified survives. The unimplemented suggestions (per-value annotations, other display properties) are absent. Only the root's OWN property counts; a nested or opened `DisplayDecimals` is not the setting.
- **Current evidence:**
  - `docs/design/language-rules/evaluator-and-hosting.md` § Display decimals and the host default.
  - `src/KatLang/KatLangEngine.cs:754` `ResolveDisplayOptions`.
  - `src/KatLang/Rendering/ValueTextRenderer.cs:134` `FormatAtom`.
  - `tests/KatLang.Tests/Hosting/DefaultDisplayDecimalsTests.cs` and `DisplayDecimalsHostileReviewTests.cs`.
  - `KatLangEngineTests.RunResult_ToDisplayString_DisplayDecimals_PreservesPrecisionForCalculations`.
  - Spec `display-decimals-rounds-ties-away-from-zero` (`LanguageSpecCorpus.cs:5158`).
  - `tutorial.md:318-340`.
- **Probe:** all `--paths engine`:
  - `p118.kat` (`DisplayDecimals = 2`, `A = Math.Pi`, `B = A * 1000`, `Vector = (Math.Pi, Math.Exp(1))`; rows `DisplayDecimals`, `A`, `B`, `Vector`, `B == 3141.59`) → display `2`, `3.14`, `3141.59`, `(3.14, 2.72)`, `false`. The raw values stay at 34 digits.
  - `DisplayDecimals = -1` → IllegalInEval "must be a non-negative integer".
  - `DisplayDecimals = 1.5` → "must be an integer".
  - `DisplayDecimals = 'x'` → "must be a single numeric value".
- **Topics:** RUN, PROP, API

### #119 — Parser: treat newline after postfix ... as continuation unless followed by explicit comma
- **Dates:** created 2026-06-04 · closed 2026-06-04
- **Problem / question:** At the time a newline normally inserted an implicit comma, but `...` also served as a binary output-join or "continue" operator (#104). A leading `...A` continued the previous line, but a line-final `A...` did not.
- **Decision / intended invariant:**
  - A physical line ending in postfix `...` does NOT insert an implicit comma; the next line continues the same output expression.
  - Write `A...,` to end it.
  - ac15218 parsed `A...` newline `A` as the binary `Expr.SequenceSupply(A, A)`, and `A...,` newline `A` as `SequenceSupply(A, empty)` followed by `A` (tests `Parse_LineEndingPostfixEllipsis_ContinuesSequenceSupplyOnNextLine` and `…WithExplicitComma_KeepsNextLineSeparate`, added in ac15218).
- **Rationale:** `...` visually reads as "continues". It also restores symmetry with a leading `...` continuation and gives an explicit `...,` escape hatch.
- **Examples:**
  - Original: `A...` newline `A` is one expression, and `A...,` newline `A` is two outputs.
  - Current equivalent: `A*` newline `A` is MULTIPLICATION `A * A`, and `A*,` newline `A` is a spread row followed by a row.
- **Lineage:**
  - Refines #104 (`...` as stream join).
  - REVERSED by #122 (acbfa7d, 2026-06-11). #122's plan says "Existing newline continuation after postfix `...` should be removed. Postfix `...` does not force continuation by itself." `...` became spread-only and `;` the join.
  - #124 (4b32111) made supply unary and postfix-only, so `...` "never consumes a right operand". This deleted the binary `SequenceSupply(left, right)` that #119 relied on.
  - #125 (ad75720) removed `;` and output joining.
  - Syntax replaced by #140 (73648e9, `expr*`).
  - #161 (cb6cfda, SYN-07B) made the line-final star layout-independent. A following operand makes the star infix multiplication, which is a structural echo of "a line-final marker continues" with an entirely different meaning.
- **Classification:** SUPERSEDED
- **Surviving part / superseded by:**
  - Superseded by #122, then #124, #125, and #140/#161 (`syntax.md` § The spread marker (SYN-07B)).
  - The "continue the supplied expression" meaning and the binary supply node are gone.
  - Only the surface shape coincidentally survives: after a line-final postfix star, a line starting with an operand continues the expression (now as multiplication), and an explicit comma (`A*,`) is required to end a spread before a following item (AGENTS: "A comma is REQUIRED between a spread and a following item (`A*, B`, or `A*,` newline `B`)").
- **Current evidence:**
  - `docs/design/language-rules/syntax.md` § The spread marker (SYN-07B) ("`a*` newline `b` … multiply"; "`A*,` newline `B` … spreads"), and § Star roles ("there is no ellipsis token (`...` lexes as three dot tokens …)").
  - `StarSyntaxTests` and `MarkerAttachmentTests`.
- **Probe:** translated to star syntax, `--paths engine`:
  - `A = 3` / `A*` / `A` → `9` (multiplication).
  - `A = 1, 2` / `A*,` / `A` → `S[1, 2, S[1, 2]]`, n=3.
  - `A = 1, 2` / `A*` / `B = 5` → `S[1, 2]`, n=2 (spread row before a declaration head).
  - `A = 1, 2` / `A` / `*A` → parse failure `InvalidCollectMarker` (no leading-marker continuation exists).
- **Topics:** SYN, SUP

### #120 — Output joining gives different results depending if is used property or inline expression
- **Dates:** created 2026-06-10 · closed 2026-06-12
- **Problem / question:** With `...` as the output join, `A = (1...2, 3)` / `A...4` gave `((1, 2), 3), 4`, while the inline `(1...2, 3)...4` gave `1, 2, 3, 4`. Using a property and writing its inline expression disagreed.
- **Decision / intended invariant:** No direct fix commit. The maintainer's comment says #122's redesign fixes it: `;` becomes the join with LOWER priority than comma, and after that the property and inline forms give the same result (`(1, 2, 3)` then `4` for both). The implied invariant is that naming an expression as a property must not change how an enclosing join or composition treats it.
- **Rationale:** Referential consistency between a property reference and its written body.
- **Examples:**
  - Original: `A = (1...2, 3)` / `A...4` / `(1...2, 3)...4`. Under #122 this became `A = (1;2, 3)` / `A; 4` / `(1; 2, 3); 4`.
  - Current equivalent (no join operator exists): `A = ((1, 2)*, 3)` / `(A*, 4)` / `(((1, 2)*, 3)*, 4)`.
- **Lineage:**
  - A regression of the #104 `...`-join design.
  - Resolved by #122 (acbfa7d).
  - Made moot by #125 (ad75720), which removed `;` and output joining entirely.
  - The underlying consistency is now delivered by #132 (9a4c70f, a property result is ONE value) plus #168 (parentheses are group syntax). A property reference `A` behaves like its PARENTHESIZED body, not like its bare rows spliced into the context.
- **Classification:** PARTIALLY CURRENT *(revised in lineage review; ledger batch said SUPERSEDED)*
- **Surviving part / superseded by:**
  - Superseded by #122, and then by #125 (no join operator; `;` is `UnsupportedSemicolon`).
  - The spirit survives in a different form: property ≡ parenthesized body. A property reference is NOT equivalent to splicing its bare rows (root rows `1, 2` emit 2 rows, while `A = 1, 2` / `A` emits one row `(1, 2)`).
- **Current evidence:**
  - AGENTS "A property/call/builtin RESULT boundary returns ONE value".
  - `docs/design/language-rules/sequences-lists-and-calls.md` § Value boundaries and `syntax.md` § Parentheses group syntax.
  - Spec case `semicolon-not-expression-syntax`.
- **Probe:** all `--paths engine`:
  - `A = ((1, 2)*, 3)` / `(A*, 4)` / `(((1, 2)*, 3)*, 4)` / `(A*, 4) == (((1, 2)*, 3)*, 4)` → `(1, 2, 3, 4)`, `(1, 2, 3, 4)`, `true`.
  - `A = (1, 2), 3` / `A, 4` / `((1, 2), 3), 4` → identical rows `((1, 2), 3)`, `4` twice.
  - `A = 1, 2` / `A` → n=1 `(1, 2)`, versus `1, 2` → n=2.
  - `1; 2` → `UnsupportedSemicolon`.
- **Topics:** SYN, VAL, SEQ, PROP
- **Lineage review (phase 2) corrections/addenda:**
  - [supply-spread] SUPERSEDED (current equivalent translated as `(A*, 4)`) → PARTIALLY CURRENT (current equivalent: `A = ((1, 2)*, 3)` / `A` / `4` ≡ `((1, 2)*, 3)` / `4`). Evidence: The accepted resolution (maintainer comment, via #122) was that both the property and the inline form give `(1, 2, 3)` then `4`, because `;` never flattens explicit groups. Both the invariant and that answer are current: probes `A = ((1, 2)*, 3)`/`A`/`4` and `((1, 2)*, 3)`/`4` both give S[S[1,2,3],4], and `A = (1, 2, 3)`/`A, 4` gives the same. The ledger's translation `(A*, 4)` models `;` as a spread, which contradicts #122's rule ('Semicolon ... must not flatten or extend explicit grouped values'). Only the `;`/`...` syntax is gone.

### #121 — Support repeated bind names as equality constraints in patterns
- **Dates:** created 2026-06-10 · closed 2026-06-10
- **Problem / question:** The request was to allow the same binder name more than once in a parameter pattern, meaning that the matched values must be equal.
- **Decision / intended invariant:** A repeated name is an EQUALITY CONSTRAINT, not a duplicate parameter:
  - `F(x, x) = x` binds the first `x` and requires the second argument to equal it, and the later occurrence never overwrites.
  - This applies at top level, inside grouped (sequence-value) patterns `F((x, x))`, in mixed `F(x, (x))`, and in clause-family heads, where a failed constraint falls through to the next clause (e054a6f, Lean + C#).
- **Rationale:** Enables idioms such as `Equal(x, x) = true` / `Equal(x, y) = false`, `AllSame(x, x, x)`, and `HasRepeatedPair((x, x))`.
- **Examples:** `Equal(x, x) = true` / `Equal(x, y) = false` gives `Equal(1, 1)` → `true` and `Equal(1, 2)` → `false`. `F(x, x) = x` gives `F(1, 1)` → `1`, and `F(1, 2)` fails unless another clause matches. (In June 2026 `true`/`false` were not yet the Boolean literals of #165; the same program works today with real Booleans.)
- **Lineage:**
  - Builds on the pattern and clause-family work (#23, #24, #99, #100).
  - Refined by D1 (Sep 22 2026) and 5d6d60b (2026-09-23 "Unify callback binding, forwarding, and repeated-name semantics"):
    - REPEATED-NAME BINDING IS ORDER-INDEPENDENT. A name is decided once per level, when its last contribution joins, and it binds iff every PAIR of contributions is compatible.
    - Lean failure order applies: binding failures outrank a repeated-name conflict in the same range.
    - Algorithm-channel contributions must carry a value and share one callable identity (declaration plus captured activations). "Repeated bind equality is not supported for algorithm-only arguments."
  - Parentheses-group-syntax (#168) makes `(x)` in `F(x, (x))` read the value of the argument itself.
- **Classification:** PARTIALLY CURRENT *(revised in lineage review; ledger batch said CURRENT)*
- **Surviving part / superseded by:** The whole decision survives. It was later sharpened (order independence, pairwise compatibility, callable identity, and failure-order precedence), not reversed. The mismatch error is observably `ArityMismatch` "Bad arity", because Lean `repeatedNameFailure` returns `Error.badArity` for an unequal value.
- **Current evidence:**
  - Lean `lean/KatLang.lean:2625` `repeatedNameFailure`, `:2642` `settlePatternRange`, `:2595` `sameRepeatedCallableIdentity`, and `lean/KatLangArityLaws.lean:1422` `repeated_name_complete_binding_is_permutation_invariant`.
  - C#: `src/KatLang/Evaluator.ParameterBinding.cs:1083` `FindRangeRepeatedNameFailure` and `:1185` `RepeatedNameAggregate`.
  - `PatternBindingErrorPrecedenceTests` (e.g. `RepeatedEqualBinders_StillBind`).
  - Spec cases `repeated-name-binding-is-order-independent` (`LanguageSpecCorpus.cs:1500`), `binding-failure-outranks-repeated-name-conflict` (:1479), and `repeated-equal-values-require-one-callable-identity` (:1522).
  - `docs/design/language-rules/sequences-lists-and-calls.md` § Collecting parameter lists, deconstruction, and callbacks (D1 paragraph).
  - `tutorial.md:1682-1685` (`Same(x, x) = true`).
- **Probe:** all `--paths engine`:
  - `F(x, x) = x`: `F(1, 1)` → `1`, and `F(1, 2)` → ArityMismatch "Bad arity".
  - `F((x, x)) = x`: `F((1, 1))` → `1`, and `F((1, 2))` → ArityMismatch.
  - `F(x, (x)) = x`: `F(1, (1))` → `1`, and `F(1, (2))` → ArityMismatch.
  - `Equal(1, 1)`, `Equal(1, 2)` → `true, false`.
  - `AllSame(2,2,2)`, `AllSame(2,2,3)`, `HasRepeatedPair((4,4))`, `HasRepeatedPair((4,5))` → `true, false, true, false`.
- **Topics:** PAT, CALL, CMP
- **Lineage review (phase 2) corrections/addenda:**
  - [conditional-patterns] CURRENT → PARTIALLY CURRENT. Evidence: Mechanism replaced and one observable acceptance reversed: e054a6f's pairwise fold merge (mergeEqualValEnv/mergePatternAlgEnv, which accepted two algorithm-channel bindings whenever both carried equal values) was replaced by repeatedNameFailure/settlePatternRange (introduced in 5d6d60b, per `git log -S repeatedNameFailure`); distinct callables with equal values now reject even for two occurrences (sequences-lists-and-calls.md:39 'deliberately tightens the former two-occurrence rule'; spec repeated-equal-values-require-one-callable-identity; probe A = 5 / B = 5 / P(f, f) = f / P(A, B) -> TypeMismatch); D1 removed 3+-occurrence fold-order dependence. Equality-constraint core and family fall-through survive.

### #122 — Design: split output joining and sequence supply semantics for `...`
- **Dates:** created 2026-06-10 · closed 2026-06-12
- **Problem / question:** At the time, postfix `...` meant BOTH "output continuation/join" and "sequence supply" (after #104 replaced `;` with `...`, and #119 made a line ending in `...` continue onto the next line). Report-style code had to end every row with `...` (`SalaryExpenses(3800, 1, 0)...` / `''...` / `SalaryExpenses(50, 0, 0)`), which was visually noisy, and #120 showed that `A...4` (property) and `(1...2, 3)...4` (inline) gave different results.
- **Decision / intended invariant:** Give each symbol one role: bring back `;` as the explicit OUTPUT-JOIN operator (concatenating top-level output streams), keep postfix `...` ONLY as sequence supply/spread, never a binary join. Newlines between body rows are implicit output joins (`A`⏎`B`⏎`C` ≈ `A ; B ; C`), not implicit commas. Comma binds tighter than `;` (`1, 2 ; 3` → flat stream `1, 2, 3`), and `;` never flattens or extends explicit groups (`(1, 2) ; 3` → group `(1, 2)` then `3`). `X(a ; b...)` means `X((a ; b)...)`. The newline-continuation-after-`...` from #119 is removed; an explicit trailing `;` may continue across a newline. Same-line adjacency `1 2` should be a missing-separator diagnostic. The result-window display (`RunResult.ToDisplayString`) shows top-level outputs on separate rows, but visual rows are presentation only and never semantic grouping. No migration path (no user base yet).
- **Rationale:** readability of report-style output; one symbol, one meaning; one call or several joined calls should look the same; commas are structural, `;` is output composition.
- **Examples:** `1, 2 ; 3` → `1, 2, 3`; `(1, 2) ; 3` → `(1, 2)`, `3`; `X(a ; b...)` ≡ `X((a ; b)...)`. Current equivalent: `1, 2` newline `3` → three rows `1, 2, 3`; `(1, 2)` newline `3` → `(1, 2)`, `3`; `;` is `UnsupportedSemicolon`; `...` is gone (spread is `x*`).
- **Lineage:**
  - regression fix for #120 (the property/inline join discrepancy; the #120 comment says #122 fixes it);
  - reverses #119 (ac15218, newline continuation after postfix `...`);
  - partially reverses #104 (0e9b41f/97867d0, which had replaced the `;` result join with a binary `...`);
  - refined by #123 (007917a), which reversed #122's "same-line adjacency is a missing-separator diagnostic" by making adjacency an implicit `;`;
  - narrowed by #124 (4b32111): `...` became postfix-only and unary;
  - superseded by #125 (ad75720), which removes `;` from expression syntax (`Expr.OutputJoin`, added in 7b5fe7a, was deleted in ad75720) and replaces flat output-stream concatenation with expression-list slots + sequence values;
  - replaced in syntax by #139/#140 (`...` → postfix `*` spread, prefix `*` collect);
  - #160 (2b03c0b, SYN-07A) reaffirms #122's "same-line `1 2` is a missing-separator error" after #123/#125 had reversed it;
  - #132 (9a4c70f) gives each call/property result ONE value, so #122's "one call vs several calls look alike" goal is now met by value boundaries rather than stream flattening.
- **Classification:** PARTIALLY CURRENT
- **Surviving part / superseded by:**
  - **Survives:** (a) the split itself: the spread marker has one role (spread only, never a join or continuation), now spelled `x*` and represented by the unary node from #124; (b) newline-separated root/body rows are separate output contributions with no per-row marker; (c) explicit parenthesized groups stay whole values among rows; (d) `ToDisplayString` prints top-level outputs on separate rows while sequence values keep parentheses, and this is presentation only; (e) same-line adjacency is rejected, via #160/SYN-07A (`UnseparatedSameLineItem`) after two reversals.
  - **Did not survive:** the `;` output-join operator and its comma-over-semicolon precedence (removed by #125); flat concatenation of top-level output streams (replaced by slots + per-call value boundaries, #125/#132); `X(a ; b...)` precedence (both tokens are gone); `...` spelling (#140); "newline joining only in bodies, not in delimited lists" (#123 extended joining into groups, and today a newline separates slots in root output, brace bodies, groups, argument lists, and list literals).
- **Current evidence:**
  - `src/KatLang/Parser.cs:1638-1639` `UnsupportedSemicolonExpressionMessage`, reported as `DiagnosticCode.UnsupportedSemicolon` (Parser.cs:3739);
  - spec case `semicolon-not-expression-syntax` (LanguageSpecCorpus.cs:3172);
  - `docs/design/language-rules/syntax.md` § Comma and same-line items (SYN-07A);
  - `docs/design/comma-output-join-spread-principles.md` principles 4, 5, 7, 10 and line 3 (supersession note);
  - `KatLang.ebnf:170-196` ("Canonical output shape": `;` unsupported);
  - display: `src/KatLang/KatLangEngine.cs:235-252` (`ToDisplayString`: "multiple top-level outputs are separated for readability; sequence values keep parentheses");
  - value boundaries: AGENTS "property/call/builtin RESULT boundary returns ONE value" (#132).
- **Probe:**
  - p01 `1, 2`⏎`3`⏎`(1, 2)`⏎`4` → `S[1, 2, 3, S[1, 2], 4]`, n=5; display shows each on its own row, with `(1, 2)` kept in parentheses.
  - p02 `F(x) = x, x + 1`⏎`F(1)`⏎`''`⏎`F(2)` → `S[S[1, 2], '', S[2, 3]]`, n=3 (each call is one value, not flattened).
  - `F(x) = x, x + 1`⏎`F(1)` → `S[1, 2]` n=1, display `(1, 2)`.
  - `1 ; 2` → parseFailure `UnsupportedSemicolon`.
  - `1 2` → parseFailure `UnseparatedSameLineItem`.
- **Topics:** SYN, SEQ, SUP, VAL, RUN
- **Lineage review (phase 2) corrections/addenda:**
  - [supply-spread] evidence: 'Expr.OutputJoin (added in 7b5fe7a) was deleted in ad75720' → Expr.OutputJoin was RENAMED in ad75720 to the internal, never-parser-produced Expr.SequenceConstruct / .sequenceConstruct, which still carries join evaluation semantics (drops () leaves). Classification PARTIALLY CURRENT unchanged.. Evidence: The `git show ad75720 -- lean/KatLang.lean` diff shows `- | outputJoin : Expr -> Expr -> Expr` / `+ | sequenceConstruct : Expr -> Expr -> Expr`. The ledger's #125 entry itself says 'renamed'. Current code: lean/KatLang.lean:852-865 (constructor note), 6635-6662 (evalSequenceConstructCounted drops `()` leaves); SequenceConstructContainmentTests.

### #123 — Normalize implicit semicolon, call continuation, and sequence supply ... precedence
- **Dates:** created 2026-06-12 · closed 2026-06-12 (commit 007917a dated 2026-06-13)
- **Problem / question:** Newline, same-line adjacency, and explicit `;` behaved asymmetrically. Several layout questions were open: whether a newline before `(`/`{`/`:` continues a closed expression; how `...` interacts with an accumulated output chain; how explicit `Output =` mixes with implicit rows; and whether `open` should borrow output-chain syntax. A concrete hazard was that `A = Identity`⏎`(A)` could parse as `A = Identity(A)`, a self-recursive property manufactured by the parser.
- **Decision / intended invariant:** One "parser constitution":
  - Output joining and chains:
    - Adjacent independent expressions are output-joined; same-line adjacency, newline, explicit `;`, and definition-separated rows share ONE canonical output-chain logic (`1 2` ≡ `1`⏎`2` ≡ `1 ; 2`, including inside groups and call arguments: `F(1 2)` is the one-argument `F(1 ; 2)`).
    - Comma is never implicit, and comma binds tighter than output join.
    - Postfix `...` supplies the WHOLE output chain accumulated to its left and never reaches forward: `A ; B... ; C` ≡ `((A ; B)...) ; C`, and `F(1 ; 2, 3...)` ≡ `F((1;2;3)...)` = 6.
  - Layout:
    - Same-line whitespace before `(`/`{` is still a call (`F (1, 2)`, `A.B (1)`, `values.map { x + 1 }`), but a physical newline before `(`/`{` never continues a closed expression into a call; open the delimiter first for multiline calls.
    - Indexing `:` is same-line only.
    - A leading `.` is the one deliberate cross-line chain continuation.
    - Comments are invisible to continuation decisions.
    - No implicit multiplication (`2(3)`); non-callable targets such as `(F) (1)` and `(1 + 2)(3)` never become calls.
    - Parsing never depends on callable arity.
  - Declarations:
    - Explicit `Output = …` and implicit output rows may not mix.
    - `open` gets a dedicated comma-list grammar: at most one `open` per algorithm; the first target on the `open` line; comma continuation (trailing or leading); leading-dot continuation of a dotted target; no `;`, adjacency, or `...` in targets; single-quoted string targets.
- **Rationale:** a simple mental model ("independent adjacent expressions join; commas make items; parentheses group"); calculator-style brevity; above all, definition-boundary safety (a following report row must never be swallowed into a previous definition).
- **Examples:**
  - `Identity = x`⏎`A = Identity`⏎`(A)` — `(A)` is a separate row, not `Identity(A)`.
  - `Pair = 1, 2`⏎`P = Pair`⏎`:0` — rejected; `P` stays bare `Pair`.
  - `(1, 2, 3)`⏎`.map { n * 2 }`⏎`.sum` → 12.
  - `open A`⏎`, B` is valid; `open A ; B` is invalid.
  - Current equivalent of the spread examples: `F((1, 2, 3)*)` / `F((1, 2)*, 3)` → 6.
- **Lineage:**
  - refines #122 (acbfa7d);
  - predecessors for the call-boundary rule: df14e5a (2026-04-02, "require adjacency between callee and '('", i.e. no whitespace at all) and a short-lived cross-newline call continuation that maintainer memory records as reverted because of the `A = Identity`⏎`(A)` recursion (lower-trust source, `memory/separator-semantics.md`);
  - reverses #122's "same-line adjacency is a diagnostic" (makes it an implicit `;`);
  - narrowed by #124 (postfix `...` loses any right operand);
  - superseded in its core model by #125 (ad75720: `;` removed; comma and adjacency both became expression-list separators, so `F(1 2)` became TWO arguments), then by #160 (2b03c0b, SYN-07A: same-line adjacency becomes the error `UnseparatedSameLineItem`);
  - replaced in syntax by #139/#140 (`...` → `*`; spread applies only to its own operand, and chain absorption is gone);
  - explicit-`Output` mixing rule removed by #63 (8cf85f5, 2026-07-31: `Output` is an ordinary identifier);
  - the `(F) (1)` "never a call" non-goal is reversed by #168 (parentheses group syntax: `(F)(1)` is `F(1)`);
  - the leading-`.` and same-line-postfix rules are reaffirmed and extended by F7 (declaration heads line-local) and SYN-07B (a trailing star continues like any operator).
- **Classification:** PARTIALLY CURRENT
- **Surviving part / superseded by:**
  - **Survives (current law):**
    1. Postfix continuations bind on the same physical line only. A same-line `(`/`{` after a callable target is a call delimiter even across whitespace, while a newline never continues a closed expression into a call. `ContinuationPolicy` (`Parser.GetContinuationPolicy`, Parser.cs:862-892; introduced in 007917a and edited in ad75720) gives `(`, `{`, `:`, `~`, and binary operators same-line-only continuation and `.` across-line continuation.
    2. Cross-line `:` is rejected with exactly the diagnostic #123 proposed.
    3. The leading-`.` chain continuation exception.
    4. Definition-boundary safety (`A = Identity`⏎`(5)` keeps `(5)` a separate row).
    5. Parsing never depends on arity; there is no implicit multiplication (`2(3)` is now a separator error rather than an output join).
    6. Comments are invisible to layout decisions.
    7. The dedicated `open` comma-list grammar: one `open` per algorithm; first target on the `open` line; trailing/leading comma continuation; leading-dot continuation; `;` and adjacency rejected with targeted `InvalidOpenTargetList` messages; plain newline never continues `open`; single-quoted strings.
  - **Did not survive:**
    - Adjacency/newline as an implicit `;` output join, and the `1 2` ≡ `1 ; 2` equivalence: `;` removed by #125, same-line adjacency now an error by #160.
    - Newline inside groups and argument lists as a JOIN: a newline now SEPARATES slots, so `F(`⏎`1`⏎`2`⏎`)` is a two-argument call.
    - Chain absorption by postfix `...` (`A ; B...` ≡ `(A ; B)...`, `F(1 2, 3...)` ≡ `F((1;2;3)...)`) and the `A`⏎`P = 1`⏎`B, C...` rule: today `A`⏎`B*` is `A, B*`, and a spread applies only to its own operand (KatLang.ebnf:300-302).
    - The `Output =` no-mixing rule (#63 removed `Output =`).
    - `(F) (1)` not being a call (#168); it is now `F(1)`.
    - `(1 + 2)(3)` as two joined outputs; it is now `UnseparatedSameLineItem`.
    - The parse-time "Sequence supply '...' is not valid in open targets" diagnostic, shared by string targets. Now `open A*` parses as a spread and is rejected by open-form validation (`BadOpenForm`), and a starred STRING target reports the missing-comma diagnostic (`ParserTests.Parse_Open_MarkedStringTarget_ReportsMissingCommaDiagnostic`, ParserTests.cs:4000-4004).
    - The architecture test `ParserSource_OpenTargetListParsing_DoesNotUseOutputPrecedenceParsing` no longer exists in test sources (found only in stale test binaries).
- **Current evidence:**
  - Rules and grammar:
    - `docs/design/language-rules/syntax.md` § Line rules and declaration heads (F7), § The `open` declaration, § Comma and same-line items (SYN-07A);
    - `KatLang.ebnf:294-345` (layout rules), `KatLang.ebnf:536-548` (CallArgs same-line comment);
    - `src/KatLang/Parser.cs:862-892` (`ContinuationPolicy`, `MayContinueClosedExpression`, `IsSamePhysicalLineAsPreviousToken`) and `Parser.cs:1775` `ParseOpenTargetList`.
  - Parser and evaluator tests:
    - `ParserTests.Parse_NewlineBeforeCallDelimiter_IsExpressionListNotCall` (:1527), `Parse_NewlineBeforeDotCallDelimiter_IsExpressionListNotCall` (:1542), `Parse_NewlineBeforeBraceDelimiter_IsExpressionListNotBraceCall` (:2076), `Parse_SameLineCallDelimiterInDefinitionBody_RemainsCall` (:2142);
    - `ParserTests.Parse_SameLineIndexing_RemainsPostfixIndex` (:1561), `Parse_ColonLedLineAfterDefinitionBody_IsRejectedNotBodyContinuation` (:1576), `Parse_ColonLedLineAfterOutputRow_IsRejectedNotPostfixContinuation` (:1600), `Parse_NewlineInsideCallArgs_CreatesArgumentSlots` (:2523);
    - `ParserTests.Parse_Open_*` (:3595-4061, e.g. `Parse_Open_SemicolonSeparator_ReportsCommaDiagnosticNotTwoTargets`, `Parse_Open_SameLineAdjacency_ReportsMissingCommaNotTwoTargets`, `Parse_Open_FirstTargetOnLaterLine_ReportsMissingTargetAndKeepsNextRow`, `Parse_Open_CrossLineSemicolon_DoesNotContinueOpenList`);
    - `EvaluatorExpressionListTests.Eval_NewlineBeforeCallDelimiter_IsExpressionListNotCall` (:328);
    - `SequenceSpreadTests.OrdinaryCompleteExpressionsAcrossNewlines_DoNotBecomeCallArguments` (:167).
  - Spec cases: `dot-chain-continuation` (LanguageSpecCorpus.cs:3440; it is #123's own `(1, 2, 3)`⏎`.map { n * 2 }`⏎`.sum` → 12 example), `newline-ends-property-body` (:3407), `comment-does-not-change-parse`, and `same-line-*` (:558-605).
- **Probe:**
  - Call boundary and newlines in calls:
    - p03 `F(*xs) = xs.count`⏎`F`⏎`(1, 2)`⏎`F (1, 2)`⏎`F(`⏎`  1`⏎`  2`⏎`)` → `S[0, S[1, 2], 2, 2]`. The newline before `(` is not a call; same-line whitespace is a call; newlines inside an open call separate two argument slots (under #123 they would have been ONE joined argument).
    - p09 `Identity(x) = x`⏎`A = Identity`⏎`(5)`⏎`A(7)` → `S[5, 7]` (definition boundary safe).
  - Indexing:
    - p04 `Pair = 1, 2`⏎`P = Pair`⏎`:0`⏎`P` → parseFailure `UnexpectedToken`.
    - `Pair = 1, 2`⏎`Pair`⏎`:0` (engine) → "Unexpected ':'. Indexing is postfix and must follow the indexed expression on the same physical line, as in 'Pair:0'." (verbatim #123 proposal).
    - `Pair = 1, 2`⏎`Pair : 1` → 2.
  - Chains, braces, grouped callees:
    - p05 `A = (1, 2, 3)`⏎`A`⏎`.map({x * 2})`⏎`.sum` → 12.
    - `A = (1, 2)`⏎`A.map`⏎`{ x * 2 }` (engine) → `ArityMismatch` on `map` (the brace line is not a call continuation).
    - p06 `F(x) = x + 1`⏎`(F) (1)`⏎`(F)(2)` → `S[2, 3]`. This REVERSES #123's non-goal; it is now current law via #168.
  - Adjacency and removed syntax:
    - `2(3)`, `2 (3)`, `(1 + 2)(3)`, `F(x) = x`⏎`F(1 2)` → all parseFailure `UnseparatedSameLineItem`.
    - p07 `Output = 1`⏎`3` → `3` (`Output` is an ordinary property; there is no mixing error).
  - Spread:
    - p08 `F(a, b, c) = a + b + c`⏎`F((1, 2, 3)*)`⏎`F((1, 2)*, 3)`⏎`T = 2, 3`⏎`F(1, T*)` → `S[6, 6, 6]` (translation of `F(1 ; 2, 3...)` etc.).
  - `open` (inside `R = { … }` with `M = { public V = 1 }`, `N = { public W = 2 }`; engine path):
    - `open M ; N` → `InvalidOpenTargetList` "Open target lists use ',' separators, not ';'…".
    - `open M N` → `InvalidOpenTargetList` "Expected ',' between open targets…".
    - `open`⏎`M` → "Expected an open target after 'open' on the same physical line."
    - `open M`⏎`open N` → "Only one 'open' declaration is allowed per algorithm."
    - `open M,`⏎`N`⏎`V + W` → 3; `open M`⏎`, N`⏎`V + W` → 3.
    - `open M`⏎`N` → `N` is an output row (MissingOutput for N).
    - `open M*,` → `BadOpenForm` "'spread' is not allowed in open declarations".
    - `open 'x'*, M` → "Expected ',' between open targets".
- **Doc note (disagreement found):** `KatLang.ebnf:544` still says "2 (3) and 2 newline (3) are the expression list 2, 3", which predates SYN-07A. `KatLang.ebnf:278`, `syntax.md` § SYN-07A, and the probe all show that same-line `2 (3)`/`2(3)` is `UnseparatedSameLineItem` (only the RECOVERED tree is `2, 3`). The newline form is correct.
- **Topics:** SYN, MOD, SUP, SEQ, CALL, DOT
- **Lineage review (phase 2) corrections/addenda:**
  - [output-syntax-layout] lineage predecessor: 'a short-lived cross-newline call continuation ... reverted' (stated as history) → memory-only / UNCERTAIN (never committed). Evidence: Classification unchanged. Every commit between df14e5a and acbfa7d keeps the exact-adjacency direct-call gate, including the checkpoints dd4dba1, 3f7c461 and 79edf05 (checked with git show <c>:src/KatLang/Parser.cs). No commit has a newline-continued call, so the experiment in memory/separator-semantics.md existed at most as an uncommitted working-tree state.

### #124 — Make sequence supply postfix-only and unary internally
- **Dates:** created 2026-06-13 · closed 2026-06-13 (label `invalid`, but closed COMPLETED by commit 4b32111; the label looks like a mislabel, since the fix landed)
- **Problem / question:** After #123, `...` was still a "tight-right" BINARY supply at source level (`X...Y`), and internally `SequenceSupply(left, right)` carried a synthetic `empty` tail, binary spine flattening, and left/right-side missing-output diagnostics.
- **Decision / intended invariant:**
  - Sequence supply is POSTFIX-ONLY and never consumes a right operand.
  - The internal node becomes UNARY `SequenceSupply(operand)` in C# and Lean, with no synthetic tail, no binary spine, and a sideless missing-output error.
  - Nested unary supply must be stack-safe in both C# and Lean.
  - `F(X...Y)` is ONE joined argument (`(X...) ; Y`), while `F(X..., Y)` is two argument slots.
  - The sequence-pipeline count/filter optimizer must preserve grouping semantics and must not evaluate sources while probing before falling back.
- **Rationale:** a single meaning for `...` (spread, per #122), a simpler AST that no longer erases the join/supply distinction, one evaluator path, and stack safety.
- **Examples:** `A...B`, `A...empty`, `A...`⏎`B` all parse as `(A...) ; B`; `F(X...Y)` has one argument; `F(X..., Y)` has two. Current equivalent: `C(X*, Y)` → two slots; `C(X*Y)` is multiplication.
- **Lineage:**
  - narrows #123 (007917a) and #104 (binary `x...y` supply/join);
  - completes #122's "keep `...` only as supply";
  - renamed by b568c66 (2026-06-18, SequenceSupply → SequenceSpread terminology);
  - replaced in syntax by #139 (eab2468) and #140 (09382b3, 73648e9): the postfix `...` spelling becomes the postfix star `x*`, still lowering to the same unary node;
  - the "one joined argument" consequence is removed by #125 (ad75720: no output join exists);
  - the unary node is reaffirmed and extended by SYN-07B (#161, layout-independent star classification plus the marker attachment law) and by the compositional repeated-spread law (`value**` = `(value*)*`).
- **Classification:** PARTIALLY CURRENT
- **Surviving part / superseded by:**
  - **Survives (current law):**
    - Spread is postfix-only with no source-level right operand.
    - It is ONE unary AST node, C# `Expr.SequenceSpread(Expr Operand)` (src/KatLang/Ast.cs:715-724) and Lean `| sequenceSpread : Expr -> Expr` (lean/KatLang.lean:870-888), built only by the parser's marker lowering.
    - Its operand is evaluated exactly once.
    - Nested spread is peeled iteratively (Lean `peelSequenceSpreadLayers`, KatLang.lean:2951-2958; C# `EvalSequenceSpreadCounted`).
    - The missing-output error is sideless: C# `EvalError.SpreadMissingOutput()` (EvalError.cs:283), Lean `Error.spreadMissingOutput` (KatLang.lean:341).
    - Optimizer fallback never evaluates a source before committing (`EvaluatorSequencePipelineTests.Eval_SequencePipeline_PlainFilterCountFallback_DoesNotEvaluateNonRangeSource`, `…DotFilterCountFallback_GenericReceiverNotEvaluatedOnPredicateResolutionFailure`, `…DirectRangeNotEvaluatedOnPredicateResolutionFailure`).
  - **Did not survive:**
    - The `...` spelling (→ `*`, #140; `...` now lexes as three dots and fails).
    - The name "sequence supply" (→ spread, b568c66).
    - "`F(X...Y)` is one joined argument": with `;`/output join removed (#125), there is no join. Under SYN-07B, `X*Y` is multiplication, and a spread followed by another slot needs a comma (`X*, Y`).
- **Current evidence:**
  - Docs: `docs/design/language-rules/syntax.md` § Star roles and § The spread marker (SYN-07B); `KatLang.ebnf:550-580` (SpreadMarker); `docs/design/comma-output-join-spread-principles.md` principles 7 and 12.
  - Tests: `EvaluatorSpreadTests.Eval_SequenceSpread_LongChain_IsStackSafeForFlatAndCountedEvaluation` (:207), `Eval_SequenceSpread_SourceDrivenPostfixChainAtParserLimit_IsStackSafe` (:267); `StarSyntaxTests.RepeatedSpread_BuildsDirectlyNestedSpreadNodes_WithDistinctMarkerSpans` (:1079), `RepeatedSpread_BoundedLongChain_IsStackSafeAndStaysAFixedPoint` (:1346).
  - Spec cases: `repeated-spread-fixed-point`, `repeated-spread-singleton-opens`, `spread-not-binary-operand` (LanguageSpecCorpus.cs:3310).
- **Probe:**
  - `C(*xs) = xs`⏎`X = 1, 2`⏎`Y = 3`⏎`C(X*, Y)` → `L[1, 2, 3]` (all paths agree).
  - The same with `C(X*Y)` (engine) → `TypeMismatch` "while evaluating `X * Y`: … operator `*` expects numeric scalar operands".
  - `X = 1, 2`⏎`C(*xs) = xs.count`⏎`C(X**)`⏎`C((X*))`⏎`C(X)` → `S[2, 1, 1]`.
  - `A = 1`⏎`A...` → parseFailure (three `UnexpectedToken` "Expected property name after '.'"); the `...` spelling is dead.
- **Topics:** SUP, SYN, FORMAL, SEQ

### #125 — Remove semicolon, unify comma/adjacency, and tighten variadic calls
- **Dates:** created 2026-06-16 · closed 2026-06-18 (fixed by ad75720, 2026-06-17 "Remove semicolon expression syntax (fixes #125)")
- **Problem / question:** In the #122/#123/#124 model, `;` was an output-join operator (`Expr.OutputJoin`), same-line and newline adjacency were implicit `;`, comma was never implicit, and flat variadic captures absorbed emitted items after allocation (#111/#112). Because `,` and `;` usually displayed the same result, the issue body first proposed making `;` a strict n-ary **sequence-object constructor** (`1 ; 2 ; 3` is one value; `Sum(1 ; 2 ; 3)` rather than `Sum(1, 2, 3)`) with `values...` destructuring ONE sequence-valued argument. The open-decision list in the body answered: newline and same-line adjacency imply `;` ("Yes!"), `Sum(Seq...)` fails, single-group unwrapping is "Not recursive", a property with comma outputs wraps into one sequence value, root output follows the separators the programmer writes, rename `OutputJoin` to `SequenceConstruct`, a sequence value displays like a grouped value, `.content` interacts with sequence objects, and `sum(1, 2, 3)` is invalid. Comment 1 (2026-06-17) added a global comma rule (comma is one structural slot-list separator everywhere, with `open` as the only exception) and proposed that comma bind tighter than `;`/newline, so that `1, 2, 3 ; 4, 5, 6` would be two row values (table syntax). Comment 2 (2026-06-17) then proposed the opposite simplification: make adjacency an implicit COMMA, drop `;` from the core grammar entirely, and use parentheses as the only way to build a sequence value.
- **Decision / intended invariant:** The commit (ad75720) followed **comment 2**, not the body. What landed:
  1. `;` is not expression syntax. It gets a targeted diagnostic and is neither a separator nor a sequence constructor.
  2. Comma is the one global expression-list separator. The surrounding syntax consumes the list: root output reads it as output slots, a call as argument slots, and `open` has its own comma target list.
  3. Adjacency, both same-line and newline, became an implicit expression-list separator. It was no longer an implicit `;`.
  4. Parentheses materialize an expression list as ONE sequence value.
  5. Postfix `...` is explicit unary supply.
  6. Fixed calls never open a value implicitly: `Add(Pair)` fails and `Add(Pair...)` succeeds.
  7. Dot-call is canonical: `receiver.P(args)` is `P(receiver, args)`, never `P(receiver..., args)`.
  8. "Strict variadic binding": `values...` binds exactly ONE sequence-valued argument and destructures it. So `Sum((1, 2, 3))` gives 3 while `Sum(1, 2, 3)` and `Sum(Seq...)` are arity errors. Builtins such as `count`, `sum` and `order` used the same strict one-slot `values...` rule.
  9. Internally, `OutputJoin` / `.outputJoin` was renamed to `SequenceConstruct` / `.sequenceConstruct`, and the parser no longer produces it.
- **Rationale:** Three near-identical ways to combine values (`,`, `;`, and parentheses) cost too much to learn. The replacement is "comma or newline writes several expressions, parentheses make them one value, and `...` opens one value into slots". Comment 1 adds that comma meaning must not depend on context (only `open` is exempt). The body adds that parsing must never depend on callable arity, runtime values, or types.
- **Examples:** (original syntax)
  ```katlang
  1, 2, 3            // three slots
  (1, 2, 3)          // one sequence value
  Sum(values...) = values.count
  Sum((1, 2, 3))     // 3
  Sum(1, 2, 3)       // arity error (strict variadic)
  Pair = 1, 2
  Add(a, b) = a + b
  Add(Pair)          // fail
  Add(Pair...)       // 3
  Reports = (7, 6, 4, 2, 1),
            (1, 2, 7, 8, 9)   // table rows need explicit parentheses
  ```
  Current equivalent: `Sum(*values) = values.count`, `Add(Pair*)`. Same-line `1 2 3` is now a parse error.
- **Lineage:**
  - Predecessors:
    - **Replaces the syntax of and removes** the `;` combining/result-join line: #2 (combining `;`), #75 (`;` as result join), #104 (ellipsis stream join, reversed by #122), #120, #122 (`;` = output join), and #123 (adjacency = implicit `;`). All of these made `;` meaningful; #125 removes `;` altogether.
    - **Reaffirms** #101 (no implicit final-argument unpacking in fixed calls) and #103 (explicit supply).
    - **Reaffirms** #112 (dot receiver is canonical).
    - **Keeps** the unary postfix supply of #124.
    - **Narrows** #111 (flat variadic-slot absorption of emitted items is replaced by strict one-slot destructuring).
  - Successors:
    - #126 (416e9c7, 2026-06-19) **reverses** the strict variadic rule. It introduces singleton-boundary item-stream normalization, so `G(A)`, `G(A...)`, `G(1, 2, 3, 4, 5)` and `G((1, 2, 3, 4, 5))` all give 15 with `G(x...) = x.sum`. Its normalization loop is recursive (`while`), which also reverses the "Not recursive" answer. d2837f4 (2026-06-19, "Unify builtin rest parameters with item-stream binding") extends this to builtins.
    - #129 (7458502) **removes** `.content`.
    - #132 (9a4c70f) **generalizes** "a property with comma outputs is one sequence value" to every property/call/builtin result boundary.
    - #135 (0ca55e9) **re-establishes** builtin strictness by a different mechanism: a fixed `collection` parameter plus a post-binding one-level view, so `sum(1, 2, 3)` and `count(A*)` are ordinary arity errors again.
    - #138 (ab7d2f5) **refines**: collectors collect exact lists.
    - #139 (eab2468) and #140 (73648e9) **replace the syntax of** `...`: first prefix and postfix ellipsis, then `*name` for collecting and `expr*` for spread.
    - #144 (f12af0f) and #167 (dada1b6, 68b3607, 874625a) **refine and then reaffirm** "dot-call passes a value".
    - 702e7d7 (2026-09-23, "values stay values"/C-full) **supersedes** #126's normalization. A non-spread argument is ONE collected item. That makes current behaviour the exact inverse of #125's variadic examples: `Sum(1, 2, 3)` is 3 and `Sum((1, 2, 3))` is 1.
    - #160 (2b03c0b, SYN-07A) **supersedes** same-line adjacency as an implicit comma: `1 2 3` is now `UnseparatedSameLineItem`. Newline separation stays.
    - #168 (50c74c1) **supersedes** the "single-group unwrapping not recursive" answer: redundant parentheses are erased syntactically, so `((1, 2, 3))` is `(1, 2, 3)`.
- **Classification:** PARTIALLY CURRENT
- **Surviving part / superseded by:**
  - **Survives (current law):**
    - `;` is not expression syntax (targeted `UnsupportedSemicolon` diagnostic).
    - Comma is the one global expression-list separator, consumed by context (root rows, call arguments, parentheses make one value). `open` keeps its own comma target list.
    - A newline separates slots at the root and inside open delimiters.
    - Parentheses around several slots make one sequence value. Table rows must be written as explicit parenthesized rows.
    - Fixed calls never open an argument implicitly (`Add(Pair)` is an arity error; `Add(Pair*)` is 3).
    - Dot-call passes its receiver as one ordinary leading argument, with no hidden receiver spread.
    - A property with several outputs is one sequence value (generalized by #132).
    - `sum(1, 2, 3)` is invalid (re-established by #135 with a fixed-parameter mechanism).
    - `SequenceConstruct` survives only as an internal, never-parser-produced node.
  - **Did not survive:**
    - `;` as a sequence constructor. This was the body's proposal and was abandoned in the issue itself. The git log shows no commit that implemented it; whether it ever existed uncommitted is UNCERTAIN and not needed for current law.
    - Comment 1's rule that comma binds tighter than `;`/newline (the row-table syntax).
    - Same-line adjacency as an implicit comma, superseded by #160 / SYN-07A.
    - Strict `values...` destructuring of one sequence argument, reversed by #126 and then superseded by the C-full exact collector law (702e7d7). The superseded consequences are `Sum(1, 2, 3)` failing, `Sum((1, 2, 3))` = 3, `Sum(Seq...)` failing, `F(1, 2, 3, 99)` failing, `Seq.Sum()` = 3, and `F(Seq..., 99)` failing.
    - The `...` spelling, replaced by `*` in #139/#140.
    - `.content`, removed by #129.
    - "Not recursive" single-group unwrapping, superseded by #126 and then #168.
- **Current evidence:**
  - Parser:
    - `src/KatLang/Parser.cs:1638-1639`: `UnsupportedSemicolonExpressionMessage`. Its text matches the AGENTS.md claim word for word; no disagreement found.
    - `src/KatLang/Parser.cs:3709-3718`, `3738-3739`: `ReportUnsupportedSemicolon`.
    - `src/KatLang/Parser.cs:4966-4969`: recovery.
    - `src/KatLang/DiagnosticCode.cs:50-54`: `UnsupportedSemicolon = 5`.
    - `src/KatLang/Lexer.cs:375`: `;` is still lexed, only so the parser can diagnose it.
  - Grammar and docs:
    - `KatLang.ebnf:186-187` and `270-272` ("Semicolon is intentionally absent from ExpressionList").
    - `docs/design/comma-output-join-spread-principles.md` principles 1-6 and 8-10. It opens with "Issue #125 changed the model…", and principle 8 records the exact collector law that superseded the strict rule.
    - `docs/design/language-rules/syntax.md` § Comma and same-line items (SYN-07A).
    - `docs/design/language-rules/sequences-lists-and-calls.md` § Collecting parameters, § The dot-call receiver, § Collection builtins, § Value boundaries.
  - AST (C# and Lean):
    - `lean/KatLang.lean:852-865`: `sequenceConstruct` documented as an internal node the C# surface parser never produces.
    - `src/KatLang/Ast.cs:701`: `Expr.SequenceConstruct`.
  - Lean laws:
    - `lean/KatLang.lean:2889`: `collectSegment`.
    - `lean/KatLangArityLaws.lean:485`: `dot_receiver_is_ordinary_leading_argument`.
    - `lean/KatLangArityLaws.lean:592`: `collector_lone_sequence_is_one_item`.
  - Tests:
    - `SequenceConstructContainmentTests`.
    - `SameLineSeparatorTests.SemicolonDiagnostic_RecommendsCommaOrNewLine_NeverAdjacency` (line 822) and `[InlineData("1 ; 2", "UnsupportedSemicolon")]` (line 387).
    - `ParserTests.Parse_Semicolon_ReportsUnsupportedExpressionSeparator` (line 990).
    - `ExplicitValueOpeningTests`, `DotCallValueBoundaryTests`, `CollectionBuiltinBindingTests`.
  - Spec cases:
    - `semicolon-not-expression-syntax` (LanguageSpecCorpus.cs:3172, `DiagnosticCode.UnsupportedSemicolon`).
    - `same-line-slots-need-comma` and `same-line-call-arguments-need-comma` (lines 558 and 570).
    - `values-stay-values` (line 1260).
  - Historical:
    - At ad75720, `tests/KatLang.Tests/SequenceSupplyTests.cs` added `StrictVariadicSequenceSlot_*`, `SequenceBuiltin_ExplicitSupplyNoLongerProvidesStrictVariadicSlot`, and `SemicolonSyntax_ReportsUnsupportedExpressionSeparator`.
    - The tutorial at ad75720 stated "`CountValues(1, 2, 3)` is an arity error".
- **Probe:** (current syntax; `...` translated to `*` and `values...` to `*values`)
  - `1 ; 2 ; 3` -> parseFailure `UnsupportedSemicolon` ×2
  - `1 2 3` -> parseFailure `UnseparatedSameLineItem` ×2
  - `Sum(*values) = values.count` / `Sum(1, 2, 3)` -> `3` (the issue said fail)
  - Same `Sum` / `Sum((1, 2, 3))` -> `1` (the issue said 3)
  - `Seq2 = 1, 2, 3` / `Sum(Seq2), Sum(Seq2*), Seq2` -> `S[1, 3, S[1, 2, 3]]`
  - `Sum(Seq*)` -> `3` (the issue said fail)
  - `Pair = 1, 2` / `Add(a, b) = a + b` / `Add(Pair)` -> `err ArityMismatch`
  - `Add(Pair*)` -> `3`
  - `Pair.Add()` -> `err ArityMismatch`
  - `(Pair*).Add()` -> `err ArityMismatch` (a capture receiver, no hidden supply)
  - `F(*values, last) = values.count, last` / `F(1, 2, 3, 99), F((1, 2, 3), 99)` -> `S[S[3, 99], S[1, 99]]` (the issue said the first fails and the second gives 3,99)
  - `F(Seq*, 99)` -> `S[3, 99]`
  - `Seq.Sum(), Seq*.Sum()` -> `S[1, 3]`
  - `sum(1, 2, 3)` -> `err ArityMismatch`
  - `sum((1, 2, 3)), count((1, 2, 3))` -> `S[6, 3]`
  - `1` / `2` / `3` on three lines -> 3 rows
  - `Cnt(1` / `2` / `3)` spanning lines -> `3` (newline separates arguments inside an open call)
  - `Add(1 2)` -> parseFailure `UnseparatedSameLineItem`
  - `((1, 2, 3)) == (1, 2, 3)` -> `true`
  - `(1, 2), 3` -> `S[S[1, 2], 3]` n=2
  - `Reports = (7, 6, 4),` / `(1, 2, 7)` / `Reports.count, Reports:1` -> `S[2, S[1, 2, 7]]`
  - `Reports = 7, 6, 4,` / `1, 2, 7` / `Reports.count` -> `6` (flat without row parentheses)
  - `Pair = (1, 2)` / `Pair.content` -> `err UnresolvedImplicitParams` (`content` is no longer a builtin)
- **Topics:** SYN, SEQ, SUP, VAR, CALL, DOT, VAL, COLL, FORMAL

### #126 — Add movable-rest deconstruction and singleton-boundary item-stream binding
- **Dates:** created 2026-06-19 · closed 2026-06-19
- **Problem / question:** Semicolon joining was gone (#125), and comma now built item streams while parentheses built one
  grouped sequence value. Two binding pieces were still missing:
  - a general comma-pattern deconstruction with one movable rest binding;
  - a rule that removes the asymmetry between rest-only parameters and rest parameters that have neighbors.
- **Decision / intended invariant:** one global "item-stream binding" matcher, shared by assignment deconstruction, function
  parameter binding and callable arity metadata.
  - (a) `x, y..., z = RHS` allows at most one rest binding. Fixed bindings are taken from the front and back; the rest takes
    the middle and may be empty. Without a rest the item count must match exactly. Two rests are an error.
  - (b) "Singleton-boundary normalization": before item-stream binding, *while* the supplied stream is exactly one grouped
    sequence value, replace it with that value's contents. Sibling grouped values are never auto-flattened.
  - (c) Rest-only parameters `G(x...)` are the degenerate case of the same matcher, so `G(A)`, `G(A...)`, `G(1,…,5)` and
    `G((1,…,5))` are all equivalent.
  - (d) Single-name capture `c = 1, 2, 3` keeps packing into one sequence value.
  - (e) A lone rest assignment `all... = RHS` stays invalid.
  - (f) The rest binds "one grouped sequence value"; an empty rest is the ordinary empty value.
  - (g) Arity metadata: `G(x...)` has min 0 and no max; `F(x..., y)` has min 1; `H(x, y..., z)` has min 2.
  - (h) Loop state keeps exact counts.
- **Rationale:** one global binding concept instead of local special cases. Value capture preserves values;
  item-stream-consuming patterns consume streams. Explicitly not recursive flattening.
- **Examples:** `A = 1,2,3,4,5` / `x, y..., z = A` → `x=1, y=(2,3,4), z=5`; `G(x...) = x.sum` with `G(A)` → 15;
  `G(A, B)` → `((1,2),(3,4))`.
  - Current equivalent: `x, *y, z = A` gives `1, [2, 3, 4], 5`. `G(*x) = x.sum` with `G(A)` is now an **error**; `G(A*)`
    gives 15.
- **Lineage:**
  - builds on #125 (removed semicolon, tightened variadic calls) and on the #111/#112 variadic-slot supply work;
  - d2837f4 (2026-06-19) generalizes it to builtin rest parameters;
  - e6c2bdc (2026-07-11) **removes** user-call singleton-boundary opening (the Lean helper's docstring now says "Function-call
    parameter binding does not use this normalization");
  - #135 (0ca55e9) **removes** the builtin normalization and replaces it with the post-binding `builtinCollectionItems` view;
  - #138 (ab7d2f5) **supersedes** "rest = one grouped sequence value" with exact lists and drops `G(A)` from the spec case
    `variadic-grouped-and-spread`;
  - #139 (eab2468) **reverses** the ban on lone rest assignment (`...all = 1, 2, 3` becomes valid; spec case
    `decon-lone-rest-rejected` becomes `decon-lone-rest`) and **replaces the syntax** `name...` → `...name`;
  - #140 **replaces the syntax** with `*name`;
  - #144 extends the collecting binding to dot receivers;
  - #167 plus the September 23, 2026 C-full work **reaffirm** that collectors never open (`Coll(A)` is `[A]`);
  - S3/D1 (September 2026) refine the nested-pattern and failure order;
  - open #157 (static deconstruction mismatch) is a pending successor.
- **Classification:** PARTIALLY CURRENT
- **Surviving part / superseded by:**
  - **Survives:**
    - comma deconstruction with at most one movable collecting binding: front/back fixed allocation, possibly empty middle,
      exact-count arity errors, a two-collector error;
    - deconstruction opens one lone RHS sequence value, and since #134 also a lone list, **one level only**;
    - single-name capture packs;
    - sibling structured values are never auto-flattened;
    - one shared prefix/collect/suffix matcher (`bindParameterPatternList`);
    - arity minimum facts (`MinimumSuppliedSlots`).
  - **Did not survive:**
    - (b) singleton-boundary normalization for calls: removed in e6c2bdc and #135; a lone argument is now always one item
      (#138, C-full);
    - (c) the equivalence `G(A)` ≡ `G(A*)`;
    - (e) the ban on lone rest assignment (reversed by #139; `*all = RHS` is valid);
    - (f) the rest as a sequence (it is now an exact list `[..]`, empty `[]`, per #138);
    - the repeated "while exactly one item" loop (opening is now one level via `structureItems?`);
    - the `name...` spelling (#139, #140).
- **Current evidence:**
  - Rules and Lean model:
    - `docs/design/language-rules/sequences-lists-and-calls.md` § Collecting parameters and § Collecting parameter lists,
      deconstruction, and callbacks;
    - Lean `Result.structureItems?` (lean/KatLang.lean:1285), `collectSegment` (:2889), `bindParameterPatternList`
      (:4933), `ParameterPattern.minimumSuppliedSlots` (:181);
    - Lean receiver theorems `receivers_never_same_on_lone_seq` / `lone_collecting_disagrees_on_lone_structure` in
      `lean/CoreArityAlgebraProofs.lean`, per the rules doc.
  - C#:
    - `Evaluator.BindParameterPatternList` (src/KatLang/Evaluator.ParameterBinding.cs:885), `CollectSegment` (:561),
      `ParameterPattern.MinimumSuppliedSlots` (src/KatLang/Ast.cs:507);
    - `DiagnosticCode.InvalidCollectingBinding` (DiagnosticCode.cs:146).
  - Spec cases: `decon-collecting-tail`, `decon-collecting-head`, `decon-collecting-middle`, `decon-empty-collecting`,
    `decon-unpacks-stored-value` (its probe `x, y = [(1, 2)]` gives `err arity`, confirming one-level opening),
    `decon-two-collecting-rejected`, `decon-lone-collecting`, `collecting-minimum-arity`, `values-stay-values`.
  - Tests: `DeconstructionBindingTests` (created by 416e9c7), `EvaluatorCollectingParameterTests`,
    `ExplicitValueOpeningTests`.
- **Probe:**
  - Deconstruction:
    - `A = 1,2,3,4,5` / `x, *y, z = A` / `x` / `y` / `z` → `S[1, L[2, 3, 4], 5]`.
    - `first, *tail = 1` / `*head, last = 1` / `tail` / `head` / `last` → `S[L[], L[], 1]`.
    - `*all = 1, 2, 3` / `all` → `L[1, 2, 3]` (valid).
    - `c = 1, 2, 3` / `A = 1, 2, 3` / `d = A` / `c` / `d` → `S[S[1, 2, 3], S[1, 2, 3]]` (packing unchanged).
  - Collecting parameters:
    - `G(*x) = x.sum` with `G(A*)`, `G(1,2,3,4,5)`, `G((1,2,3,4,5)*)` → `15, 15, 15`.
    - `G(*x) = x` with `G(A)` and `G((1,2,3,4,5))` → `L[S[1,…,5]]` twice.
    - `G(*x) = x.sum` with `G(A)` → `err ArityMismatch` ("sum expects each collection element to be a single numeric value;
      item 0 was sequence value").
    - `F(*x, y) = x.sum + y` with `F(A*)` → 15; `H(x, *y, z) = x + y.sum + z` with `H(A*)` → 15 and `H(1, 2)` → 3.
    - `A = 1, 2` / `B = 3, 4` / `G(*x) = x` with `G(A, B)` → `L[S[1, 2], S[3, 4]]` and `G(A*, B*)` → `L[1, 2, 3, 4]`.
  - Errors:
    - `x, y = 1` → `err ArityMismatch` ("Assignment pattern `x, y` expects 2 values…").
    - `x, *y, z = 1` → `err ArityMismatch`.
    - `*a, *b = 1, 2, 3` → `parseFailure InvalidCollectingBinding`.
- **Topics:** VAR, PAT, CALL, SUP, SEQ, PAR, VAL

### #127 — Make equality structural for first-class sequence values
- **Dates:** created 2026-06-19 · closed 2026-06-21
- **Problem / question:** `==` accepted only numeric scalars, so `A = 1, 2` / `A == A` was a type mismatch. Sequence values
  were first-class enough to bind, pass and print, but could not be compared.
- **Decision / intended invariant:**
  - `==` and `!=` are **total structural value equality**:
    - numbers by value, strings exactly;
    - sequences by length plus recursive pairwise equality;
    - values of different kinds are unequal, never a type error;
    - `!=` is the negation of `==`.
  - Ordering operators (`< > <= >=`) and arithmetic stay numeric-scalar only.
  - No hidden vectorization: `A... == A...` must not become elementwise; it stays invalid, while the grouped form
    `(A...) == A` works.
- **Rationale:** equality asks whether two values are the same value, so a shape difference is simply "false". It keeps
  first-class sequence values consistent.
- **Examples:** `A = 1, 2` / `A == A` → 1; `1 == (1, 2)` → 0; `A = 1,(2,3)` / `C = 1,(2,4)` / `A == C` → 0.
  - Current equivalent: the results are `true`/`false`, and `A* == A*`.
- **Lineage:**
  - #128 **refines** it: `()` vs `(())` (later canonicalized in e6c2bdc), and `{}` is not comparable.
  - #134 **extends** equality to lists (`[1, 2] == (1, 2)` is false, `[] != ()`).
  - #141 (da96a0f) is an implementation fix: stack- and breadth-safe traversal for deep equality.
  - #165 **refines**: `==`/`!=` produce Booleans instead of 1/0, and `true == 1` is false.
  - #166 **refines** the syntax: `==`/`!=` join the one chaining comparison tier.
  - SYN-01 (a8bcae7, 2026-09-10) **reaffirms**: `()` is no longer an identity operand for the other operators, while
    equality stayed total.
- **Classification:** CURRENT
- **Surviving part / superseded by:** the entire equality law survives. Only the result encoding changed: 1/0 became
  `true`/`false` in #165, which is that issue's decision, not a change to #127. Non-vectorization is now enforced at parse
  time: a spread cannot be a scalar operand.
- **Current evidence:**
  - Lean `resultValueEq` (lean/KatLang.lean:2438, derived structural `BEq`) and `applyComparison` (:3510–3513).
  - C# `Evaluator.ApplyComparison` (src/KatLang/Evaluator.Loops.cs:507), `ValueEquals` (src/KatLang/Evaluator.cs:1774)
    through `Result.ValueComparer` (src/KatLang/Result.cs:88).
  - `docs/design/language-rules/evaluator-and-hosting.md` § Boolean values; `syntax.md` § Operator precedence, comparison
    chains.
  - Tests:
    - `EvaluatorOperatorTests.Eval_Equal_SequenceValue_SameReference_ReturnsOne` and
      `Eval_Equal_IndependentSequences_StructurallyEqual_ReturnsOne`. The names are stale ("ReturnsOne"); they now assert
      `true`.
    - `EvaluatorLoopTests.Eval_OptimizedLoop_CapturedSequenceValueEquality_UsesStructuralEquality`.
    - `ComparisonChainEvaluationTests`.
    - Lean `CoreTests/Numerics.lean` `emptyStructuralEqualityUnaffected`.
  - Spec cases `boolean-values-and-equality` and `empty-eq-family`; tutorial.md:904 "Comparing Values".
- **Probe:**
  - `A = 1, 2` / `B = 1, 2` / `C = 1, 3` / `D = 1, 2, 3`, then `A == A`, `A != A`, `A == B`, `A == C`, `A == D`, `A != D`
    → `S[true, false, true, false, false, true]`.
  - Nested and cross-kind:
    - `A = 1, (2, 3)` / `B = 1, (2, 3)` / `C = 1, (2, 4)` / `A == B` / `A == C` gives `true, false`.
    - The same program continues with `1 == (1, 2)` / `1 != (1, 2)` / `'a' == 'a'` / `true == 1` / `[1, 2] == (1, 2)`,
      which gives `false, true, true, false, false`.
    - The combined result is `S[true, false, false, true, true, false, false]`.
  - `A = 1, 2` / `(A*) == A` → `true`.
  - `A = 1, 2` / `A* == A*` → `parseFailure MisplacedSpread` ×2.
  - `A = 1, 2` / `A < A` → `err TypeMismatch` ("operator `<` expects numeric scalar operands"); `A + 1` gives the same
    kind of error.
- **Topics:** CMP, VAL, SEQ, OP, FORMAL

### #128 — Improve empty sequence representation
- **Dates:** created 2026-06-22 · closed 2026-06-22
- **Problem / question:** the `empty` builtin/special name made nested empty structure hard to explain. Is `(())` equal to
  `empty`?
- **Decision / intended invariant:**
  1. `()` is the empty sequence value, written and displayed as `()`.
  2. Nested empties are preserved structurally: `(())` ≠ `()`, `count((()))` is 1, and collection builtins keep a kept
     `(())` item.
  3. An output row that evaluates to `()` stays a visible slot.
  4. Spreading `()` contributes zero items.
  5. `empty` is not special in any way: `empty = 123` works, and a bare `empty` is an ordinary unresolved name.
  6. `()` (an intentionally empty value) is not `{}` (no output). `{}` cannot be compared: `A = {}` / `A == ()` is a
     missing-output error.
  7. `count(())` is 0.
  8. Collection builtins preserve structural items.
- **Rationale:** make the empty value part of the ordinary sequence model rather than a keyword, so that display is
  structural and teachable. "No output is not a value and cannot be compared with values."
- **Examples:** `x, rest... = 1` / `rest` → `()`; `rest...` contributes nothing; `() == (())` → 0;
  `filter((()), AlwaysTrue)` → `(())`.
  - Current equivalent: `x, *rest = 1` / `rest` → `[]`; `() == (())` → `true`; `filter((()), AlwaysTrue)` → `[]`.
- **Lineage:**
  - It **removes** the old `empty` builtin.
  - #127 is the predecessor for equality.
  - e6c2bdc (2026-07-11) **reverses** rule 2: `buildEmptySequenceValue` now ignores depth, and the C# test assertion
    `() == (())` changed from 0 to 1 in that commit's diff of EvaluatorTests.cs.
  - #134 **replaces** exact nested empties with lists (`[[]] != []`; its motivation cites `(()) == ()`).
  - #138 **supersedes** "empty rest is `()`": it is now `[]`.
  - #135 **supersedes** collection-builtin results: they are now exact lists.
  - #168 (September 2026) **reaffirms** the canonicalization at the parser: `(())` elaborates to the very `()` node.
  - SYN-01 (a8bcae7) **refines** `()` as an operand: it is not an identity for arithmetic/ordering.
- **Classification:** PARTIALLY CURRENT
- **Surviving part / superseded by:**
  - **Survives:**
    - rule 1: the `()` literal and its display;
    - rules 3 and 4: the visible empty slot, and a spread of `()` contributes zero items;
    - rule 5: `empty` is an ordinary identifier;
    - rule 6: `{}` has no output and is not comparable (MissingOutput);
    - rule 7: `count(())` is 0.
  - **Reversed or superseded:**
    - rule 2, nested empty distinctness: `(())`/`((()))` normalize to `()`, so `count((()))` is 0. This was e6c2bdc, and
      #168 cemented it. Exact nested empties now require lists (#134).
    - Collection-builtin `(())` preservation: builtins return lists (#135), and `(())` is already `()`.
    - Empty rest display `()`: it is now `[]` (#138).
- **Current evidence:**
  - Lean `buildEmptySequenceValue` (lean/KatLang.lean:2916, "Repeated ordinary parentheses around `()` do not create
    higher-order empty sequence values"). C# `BuildEmptySequenceValue` (src/KatLang/Evaluator.Results.cs:234).
  - `Parser.IsRedundantGrouping` (`syntax.md` § Parentheses group syntax).
  - Lean `CoreTests/OutputSemantics.lean`: `emptyVsNestedEmptyEquality` (:497), `emptyAndNestedEmptyCount` (:509),
    `emptyIsOrdinaryIdentifier` (:528), `missingOutputBodyEqualityStillFails` (:822),
    `filterNestedEmptyInputCanonicalizesToEmptyCollection` (:586).
  - Spec cases `empty-literal`, `empty-wrapped` (probe `() == (())` gives `ok raw=true`), `empty-wrapped-twice`,
    `empty-eq-family`, `empty-capture`, `decon-empty-collecting`, `empty-visible-at-root`, `spread-empty-in-sequence`.
  - tutorial.md:887 "The Empty Sequence".
  - `docs/design/sequence-boundary-audit-2026-07.md` (lines 65 and 145: `(())` gives `S[]`, "canonicalizes, documented").
- **Probe:**
  - `()` / `(())` / `((()))` / `() == ()` / `() == (())` / `() != (())` / `count(())` / `count((()))`
    → `S[S[], S[], S[], true, true, false, 0, 0]`.
  - `empty = 123` / `empty` → 123. A bare `empty` → `err UnresolvedImplicitParams`.
  - `A = {}` / `A == ()` → `err MissingOutput`.
  - `x, *rest = 1` / `rest` / `x` / `rest*, x` / `()*, 1` → `S[L[], 1, 1, 1]`.
  - `AlwaysTrue(x) = true`, then:
    - `filter((()), AlwaysTrue)` → `L[]`;
    - `count(filter((()), AlwaysTrue))` → 0;
    - `filter(((), ()), AlwaysTrue)` → `L[S[], S[]]`;
    - `take((()), 1)` → `L[]`;
    - `distinct(((), ()))` → `L[S[]]`;
    - `[[]] == []` → false.
  - `x = ()` / `x` / `(), 1` → `S[S[], S[], 1]`.
- **Topics:** VAL, SEQ, SUP, CMP, COLL, SYN

### #129 — Remove `content`
- **Dates:** created 2026-06-26 · closed 2026-06-26
- **Problem / question:** the `content` builtin (one-level group removal) duplicated the postfix spread. `Group.content` is
  `Group...`, and for `if`, `if(C, T, F)...` replaces `if(C, T.content, F.content)`.
- **Decision / intended invariant:** delete the `content` builtin. Explicit postfix spread is the only way to open a value
  into items. After removal, `content` is an ordinary, non-reserved identifier.
- **Rationale:** one mechanism for opening values. Once `if` returns one value (#130), spreading its result is sufficient.
- **Examples:** `if(Cond, TrueResult.content, FalseResult.content)` → `if(Cond, TrueResult, FalseResult)...`.
  - Current equivalent: `if(c, T, F)*`.
- **Lineage:**
  - #91 (5d1b52c) added the `ungroup` builtin; #98 (7ad022c) renamed it to `content`. This issue **removes** it.
  - #122–#124 set up the postfix `...` spread that replaced it; #140 **replaces the syntax** `...` → `*`.
  - #135 **reaffirms** the removal ("`content` is no longer a KatLang builtin").
  - SYN-05 (#159) **reaffirms** that builtin names are ordinary prelude bindings with no reserved names.
- **Classification:** CURRENT
- **Surviving part / superseded by:** the removal stands. `content` is absent from the Lean prelude (lean/KatLang.lean:7377–7397
  lists `if`…`reduce`; no `content`) and from `BuiltinRegistry`. Only the spread spelling changed (#140).
- **Current evidence:** `EvaluatorValueBoundaryTests.Eval_Content_NoLongerResolvesAsBuiltin` and
  `Eval_Content_UserDefinedCallable_IsNotReserved` (tests/KatLang.Tests/EvaluatorValueBoundaryTests.cs:231–246);
  `sequences-lists-and-calls.md` § Spread semantics (the spread is the one opener).
- **Probe:**
  - `G = 1, 2` / `content(G)` → `err UnresolvedImplicitParams` ("Identifier 'content' does not resolve…").
  - `content = 5` / `content` → 5.
  - `T = 1, 2, 3` / `F = 10, 20, 30` / `if(true, T, F)*` → `S[1, 2, 3]` n=3.
- **Topics:** SUP, COLL, SYN

### #130 — Unexpectedly lost sequence wrapping
- **Dates:** created 2026-06-26 · closed 2026-06-26
- **Problem / question:** with `X = 1, 2, 3`, `X` displayed `(1, 2, 3)` but `if(1, X, X)` displayed three separate outputs.
  The `if` builtin preserved the raw emitted count of the branch property's body. The maintainer comment notes that Lean had
  the same bug.
- **Decision / intended invariant:** `if` returns the selected branch as ONE value boundary, exactly like value-position
  property access (emitted count 1). Only an explicit spread (`if(…)...`) opens it. This contrasts with `while`/`repeat`,
  whose multi-slot state is intentional. The fix was mirrored in Lean.
- **Rationale:** consistency with ordinary property access. A named multi-item result is referenced as one grouped object
  (the Python tuple analogy in the maintainer comment).
- **Examples:** `BadTrueResult = 1, 2, 3` / `if(1, BadTrueResult, BadTrueResult)` → should be `(1, 2, 3)`.
  - Current equivalent: `if(true, X, X)` → `(1, 2, 3)`.
- **Lineage:**
  - It **reaffirms** the property-access value boundary.
  - It is immediately **generalized** by #132 to all property, call and builtin results.
  - #129 relies on it.
  - #165 **refines** the condition: `if(1, …)` is now a type mismatch, and `true`/`false` are required.
  - #159 **refines** resolution: `if` is chosen by identity, and a shadowing user `if` is complete.
- **Classification:** BUG FIX / REAFFIRMED EXISTING RULE
- **Surviving part / superseded by:** fully current as part of the value-boundary law. Only the numeric condition in the
  examples is obsolete (#165).
- **Current evidence:**
  - Lean `.ifBuiltin` arm (lean/KatLang.lean:5865–5883, `(r.fst, Result.valueCount r.fst)`).
  - C# `Evaluator.Builtins.cs:2268–2292`, with its async twin near `Evaluator.Async.cs:2334`.
  - Lean guards `ifCountedCollapsesMultiOutputTrueBranch` and related guards (lean/CoreTests/ParityGuards.lean:300–360).
  - C# tests:
    - `EvaluatorIfBuiltinTests.Eval_If_MultiOutputBranchProperty_CollapsesToOneSequenceValue`;
    - `EvaluatorIfBuiltinTests.Eval_If_SpreadResult_OpensSelectedBranchIntoItems`;
    - `KatLangEngineTests.Run_IfMultiOutputBranchProperty_DisplaysOneGroupedRow`.
  - Spec case `if-value-boundary`; `sequences-lists-and-calls.md` § Value boundaries ("Lexical zero-arg property access and
    `if` already re-counted this way").
- **Probe:** `TrueResult = 1, 2, 3` / `FalseResult = (10, 20, 30)` / `if(true, TrueResult, TrueResult)` /
  `if(false, FalseResult, FalseResult)` / `TrueResult` → `S[S[1, 2, 3], S[10, 20, 30], S[1, 2, 3]]` n=3.
- **Topics:** VAL, BOOL, SUP, COLL, FORMAL

### #131 — `if` does not support spreading
- **Dates:** created 2026-06-26 · closed 2026-06-26
- **Problem / question:** `if(TrueResult...)` with `TrueResult = 1, 2, 3` failed at parse time ("Builtin 'if' expects 3
  arguments… Got 1"), while the user wrapper `MyIF(a,b,c) = if(a,b,c)` / `MyIF(TrueResult...)` worked. The C# parser
  counted `if`'s written argument slots statically.
- **Decision / intended invariant:** an explicit spread argument has a runtime-only item count. The spread expands into
  ordinary argument slots *before* the builtin's arity check, as for every other callable. Direct `if(X...)` must equal the
  wrapper, and a wrong expanded count is an evaluation-time arity error.
  - The fix (7e1085e) only skipped `Parser.ValidateIfArity` when a slot was a spread. It kept the parse-time error for
    non-spread wrong arity.
  - The Lean guard notes that no Lean evaluator change was needed, since `applyBuiltinCountedResolved` already expanded
    spreads.
- **Rationale:** consistency between builtin and user callables. Arity can be known only after spread expansion.
- **Examples:** `TrueResult = 1, 2, 3` / `if(TrueResult...)` (then an error).
  - Current equivalent: `T = true, 2, 3` / `if(T*)` → 2.
- **Lineage:**
  - It **reaffirms** call-argument assembly: spread slots expand before arity checking, clause selection and binding.
  - #159 (0243678, 2026-09-10, SYN-05) **generalizes** it and **removes** the residual parser gate: `ValidateIfArity` was
    deleted, no layer counts arguments by callee spelling, and `if(true, 2)` is now an evaluation-time `ArityMismatch`.
  - #165 changes the condition to a Boolean.
- **Classification:** BUG FIX / REAFFIRMED EXISTING RULE
- **Surviving part / superseded by:** the rule "spread expands before arity check for builtin `if`" is current. The fix's
  retained parse-time `if` arity diagnostic for non-spread calls was **removed** by #159 (SYN-05).
- **Current evidence:**
  - C# `ExpandSequenceSpreadBuiltinArguments`, called before `switch (builtin, args.Count)` (src/KatLang/Evaluator.Builtins.cs:2262).
  - Lean `expandSequenceSpreadBuiltinArguments` (lean/KatLang.lean:5948) and `applyBuiltinCountedResolved` (:5975).
  - Lean guards at lean/CoreTests/ParityGuards.lean:363ff.
  - C# tests:
    - `EvaluatorIfBuiltinTests.Eval_If_SpreadArgument_OpensIntoThreeArguments`, `_MatchesUserWrapper`,
      `_WrongExpandedArity_FailsAtEvaluation`;
    - `KatLangEngineTests.Run_IfSpreadArgument_OpensIntoThreeArguments` and
      `Run_IfSpreadArgument_WrongExpandedArity_IsEvalFailureNotParseFailure`;
    - `BuiltinCallableIdentityTests`, `IfBuiltinArityPayloadTests`.
  - `grep ValidateIfArity src/` finds no source hits; only stale DemoApp bin DLLs match.
  - AGENTS.md SYN-05 bullet; `ownership-and-lookup.md` § Builtin identity.
- **Probe:**
  - `TrueResult = true, 2, 3` / `MyIF(a, b, c) = if(a, b, c)` / `if(TrueResult*)` / `MyIF(TrueResult*)` → `S[2, 2]`.
  - `Two = true, 2` / `if(Two*)` → `err ArityMismatch` ("Callable `if(condition, whenTrue, whenFalse)` expects 3
    arguments, but was called with 2").
  - `if(true, 2)` → `err ArityMismatch`, an evaluation error rather than a parse error.
  - `if(1, 2, 3)` → `err TypeMismatch` ("if condition must be a Boolean value").
- **Topics:** SUP, CALL, COLL, SYN, RES

### #132 — Make property/call boundaries return one sequence value
- **Dates:** created 2026-06-27 · closed 2026-06-27
- **Problem / question:** results were inconsistent across boundaries. Lexical property access and `if` (#130) returned one
  grouped value. User calls, structural dot access and collection-producing builtins could still leak multi-item emitted
  counts to the caller.
- **Decision / intended invariant:** **every property, call, builtin or structural-dot result boundary is a value
  boundary.** A body that produces several items is observed by the caller as ONE sequence value. Only caller-site postfix
  spread reopens it. Specifically:
  - body spread is local (`F(a...) = a...` still returns one value);
  - root output stays multi-output;
  - lexical access and `if` stay aligned with this rule;
  - collection builtins (`order`, `orderDesc`, `distinct`, `take`, `skip`, `filter`, `map`, `range`, `atoms`) return one
    value;
  - rest capture "should still preserve raw internal counts for forwarding and spreading inside property bodies".
- **Rationale:** regularity. Comma output forms an internal item stream, and the boundary reifies it as one value (Python
  analogy: `return 1, 2, 3` returns one tuple). `...` is the explicit reopening operation.
- **Examples:** `F(a...) = a` / `F(5, 9)` → `(5, 9)`; `F(a...) = a, 0` → `((5, 9), 0)`; `X.order` → `(1, 2, 3)`.
  - Current equivalent: `F(*a) = a` / `F(5, 9)` → `[5, 9]`; `F(*a) = a, 0` → `([5, 9], 0)`; `X.order` → `[1, 2, 3]`.
- **Lineage:**
  - It **generalizes** #130.
  - The e6c2bdc audit (`docs/design/sequence-boundary-audit-2026-07.md`) pins it as a regression class.
  - #134/#135 **refine** it: collection builtin results become one exact *list* (`makeCollectionListResult`).
  - #138 **removes** the "raw internal counts" clause: `variadicSupplyEnv`/`VariadicStreamEnv` were deleted, and forwarding
    is ordinary list spread.
  - 245b10c (2026-07-20) "unify call assembly and value-boundary semantics" **refines** it.
  - The September 2026 work **extends** the rule: selection is a value boundary (`SelectionValueBoundaryTests`), and
    dot-call passes a value.
- **Classification:** PARTIALLY CURRENT
- **Surviving part / superseded by:**
  - **Survives (core law):**
    - every property, call or builtin result is ONE value with emitted count `Result.valueCount` (0 for `()`, else 1);
    - only caller-site spread reopens it;
    - body spread is local;
    - root output and `while`/`repeat` state keep multi-item counts;
    - `if` and lexical access are aligned.
  - **Did not survive:**
    - collection builtin and rest results as *sequence* values (they are now exact lists, via #135 and #138);
    - the "rest capture preserves raw internal counts" clause (removed in #138: a collecting binding stores one exact list
      with count 1, and `spread(collect(xs)) = xs` replaces the raw supply).
- **Current evidence:**
  - Lean `reCountValueBoundary` (lean/KatLang.lean:2910) and `makeCollectionListResult` (:2842).
  - C# `ReCountValueBoundary` (src/KatLang/Evaluator.Builtins.cs:144) and `MakeCollectionListResult`
    (Evaluator.Builtins.cs:87; Evaluator.PatternMatching.cs:833).
  - `sequences-lists-and-calls.md` § Value boundaries; the AGENTS.md "property/call/builtin RESULT boundary" bullet.
  - `EvaluatorValueBoundaryTests`, including `Eval_UserCall_VariadicReturn_IsOneListValue`,
    `Eval_UserCall_VariadicReturnWithBodySpread_IsOneSequenceValue`, `Eval_UserCall_CallerSpread_OpensReturnedValue` and
    `Eval_CollectionBuiltin_IsOneExactListValue`.
  - Lean `CoreTests/ValueBoundary.lean`: `boundaryVariadicReturnIsOneValue`, `boundaryLexicalAccessIsOneValue`,
    `boundaryOrderIsOneValue`, and others.
  - Spec cases `call-value-boundary`, `property-value-boundary`, `property-call-boundary`, `dot-access-value-boundary`.
- **Probe:**
  - `F = 1, 2, 3` / `F` / `F*` → `S[S[1, 2, 3], 1, 2, 3]` n=4.
  - `F(*a) = a` / `F(5, 9)` / `F(5, 9)*` → `S[L[5, 9], 5, 9]`.
  - `F(*a) = a*` / `G(*a) = a, 0` / `H(*a) = a*, 0` with each called on `(5, 9)` → `S[S[5, 9], S[L[5, 9], 0], S[5, 9, 0]]`.
  - `X = 1, 2, 3` / `F(*a) = sum(a)` / `X.order` / `if(true, X, 0)` / `F(5, 9)` / `X.order*`
    → `S[L[1, 2, 3], S[1, 2, 3], 14, 1, 2, 3]`.
  - `1, 2, 3` at root → three rows (n=3).
  - Incidental SYN-07B observation: a first attempt with `X.order*` followed by a newline and an `if(…)` row parsed as the
    multiplication `X.order * if(...)` and failed with a type mismatch. This is the documented layout-independent star
    rule, not related to #132.
- **Topics:** VAL, SUP, SEQ, COLL, VAR, FWD, FORMAL

### #133 — Fix non-canonical singleton sequence values produced by builtins
- **Dates:** created 2026-07-07 · closed 2026-07-07
- **Problem / question:** `T = take(((1,2),(3,4)), 1)` produced a stored value that displayed as `((1, 2))` but was unequal
  to both `(1,2)` and `((1,2))`, and `count(T)` = 1 ≠ `T.count` = 2. Builtin results kept raw singleton boundaries that
  literal construction canonicalized away (a "preserved `(())` hole"), so display, equality, count and navigation
  disagreed. The same flaw existed in the Lean model (`resultValueEq` compared uncanonicalized builtin results). Warning:
  do not over-normalize meaningful top-level boundaries (`distinct((), ())`).
- **Decision / intended invariant:** a builtin result must never be a value that is unequal to every writable literal.
  Display, `==`, `count`, `.count` and navigation must agree on one observable shape. Meaningful sibling boundaries must
  not be erased. The policy is specified in Lean first.
  - Implemented fix (as landed in e6c2bdc): `combineCollectionResult` became shallow singleton-erasing
    (`[] => ()`, `[item] => item`, ≥2 → raw sequence). So `take(((1,2),(3,4)),1)` = `(1,2)`, and `resultValueEq` stayed
    structural; the fix is at construction.
  - Follow-up (memory `post-133-audit`, `empty-sequence-preservation`): the pattern explicit-items path also stopped minting
    orphan singletons.
- **Rationale:** one consistent answer per value across observations. This is the arity-algebra claim, and a data-modeling
  hazard: a single survivor changed `.count` semantics.
- **Examples:** `T = take(((1,2),(3,4)), 1)` / `T` / `count(T)` / `T.count` / `T == (1,2)` / `T == ((1,2))`; guard
  `distinct((), ())`.
  - Current equivalent guard: `distinct(((), ()))`, since `distinct` now takes one collection.
- **Lineage:**
  - It **refines** #128: the builtin `(())` preservation #128 had required is exactly the "hole", and e6c2bdc also
    canonicalized `(())` to `()`.
  - #134 **addresses** the underlying expressiveness gap with exact lists.
  - #135 (0ca55e9) **supersedes** the mechanism: collection builtins materialize ONE exact list via
    `makeCollectionListResult`, and a single survivor is `[item]` (never erased). So `take(((1,2),(3,4)),1)` = `[(1, 2)]`.
  - #135 also **reverses** the `distinct((), ())` form: collection builtins take one fixed `collection`, so two arguments
    are an arity error.
  - Dot-call passes a value (September 2026) **reaffirms** `T.count` ≡ `count(T)`.
  - #168 removed the remaining written-slot pattern view (`explicitItems?`).
- **Classification:** PARTIALLY CURRENT
- **Surviving part / superseded by:**
  - **Survives:** the invariant. No builtin produces a literal-unwritable value; lists are writable, so `[(1, 2)]` is
    written as such. Every observation agrees (`count(T)` = `T.count` = 1). Sibling boundaries are preserved
    (`distinct(((), ()))` → `[()]` keeps `()` as an item).
  - **Superseded:** the concrete fix of shallow singleton erasure to a *sequence* (`take(…,1)` = `(1,2)`) was superseded
    by #135's exact-list results (`[(1, 2)]`, `== (1, 2)` false).
  - **Removed:** the `distinct((), ())` guard form (arity error since #135).
  - The issue's timeline commit 7a7c202 is not on main; the fix reached main inside e6c2bdc.
- **Current evidence:**
  - Lean `makeCollectionListResult` (lean/KatLang.lean:2842: "the one-item collection boundary is NEVER erased, so
    `take(((1, 2), (3, 4)), 1)` yields `[(1, 2)]`").
  - C# `MakeCollectionListResult` (src/KatLang/Evaluator.PatternMatching.cs:833).
  - Spec case `take-single-survivor`, with probes `count(...)` → 1, `== (1, 2)` → false, and spread → `S[1, 2]`.
  - `EvaluatorCollectingParameterTests.cs:715` ("Post-#133 audit follow-up").
  - `docs/design/sequence-boundary-audit-2026-07.md:265` (#133 one-survivor wrappers pinned as a regression class) and
    § "Collection builtin returns".
  - `sequences-lists-and-calls.md` § Collection builtins.
- **Probe:**
  - `T = take(((1, 2), (3, 4)), 1)` / `T` / `count(T)` / `T.count` / `T == (1, 2)` / `T == ((1, 2))` / `T == [(1, 2)]`
    → `S[L[S[1, 2]], 1, 1, false, false, true]`.
  - `distinct((), ())` → `err ArityMismatch` ("Callable `distinct(collection)` expects 1 argument, but was called with
    2").
  - `distinct(((), ()))` / `distinct(((), ())).count` → `S[L[S[]], 1]`.
- **Topics:** VAL, SEQ, COLL, CMP, FORMAL

---

## Observations and disagreements noted during this batch
- AGENTS.md's claims for this batch's topics agreed with code, Lean and probes: the value-boundary bullet, `(())`
  normalizing to `()`, the exact collector law, deconstruction opening one level, and the absence of a parser arity count
  for `if`. I found no contradiction.
- The test method names in `EvaluatorOperatorTests` (`..._ReturnsOne` / `..._ReturnsZero`) predate Booleans (#165), but the
  bodies assert `true`/`false`. This is cosmetic.
- `G(*x) = x.sum` with `G(A)` (a list holding one sequence) reports `KatLangErrorCode` `ArityMismatch` ("…item 0 was
  sequence value: Bad arity") for what is an element-kind problem. It is consistent with the memory note
  `rest-collects-exact-lists` ("err arity" category), so it is not a regression. It does classify a value-kind failure
  under the arity code.
- The Lean AST still carries `Expr.emptySequence (depth : Nat)`, and C# carries `Expr.EmptySequence(int depth)`. The depth
  is ignored by `buildEmptySequenceValue` / `BuildEmptySequenceValue`, a residue of #128's nested-empty model.

### #134 — Add exact immutable list values with [] syntax
- **Dates:** created 2026-07-16 · closed 2026-07-17 (fix commit d202b74, 2026-07-16)
- **Problem / question:** Sequence normalization removes redundant singleton boundaries (`(7) == 7`, `((1, 2)) == (1, 2)`, `(()) == ()`). That suits arity capture, but a sequence cannot hold an exact singleton or nested collection, such as a one-row matrix `((1, 2, 3))` or a JSON array `[1]`. The issue asks for a second persistent collection kind that keeps its exact length, kind and nesting.
- **Decision / intended invariant:** The issue adds an immutable list value with the literal syntax `[e1, …, en]`. It separates three things: sequence `()` is the canonical arity value, list `[]` is the exact collection value, and an item supply is a temporary structure that is not a value. The required rules, as the issue numbers them:
  1. A list literal is ONE value, and sequence normalization never applies to it (`[7] != 7`, `[[1,2]] != [1,2]`, `[[]] != []`).
  2. Lists and sequences are different kinds (`[] != ()`, `[1,2] != (1,2)`), and equality is structural.
  3. Lists are immutable in what a program can observe.
  4. Postfix spread opens exactly one list boundary, as it does for a sequence. `[]` spread supplies zero items.
  5. Spread works inside list literals. Non-spread values stay single elements.
  6. Calls keep a list as one argument unless spread is explicit ("Stored values remain one argument unless postfix spread explicitly opens them").
  7. Multi-target deconstruction opens a lone list, only when the RHS supply is exactly one list or sequence value, and never recursively.
  8. Single-name capture `x = [1,2,3]` keeps the list. `x = value...` opens it and recaptures.
  9. A rest binding always captures a canonical SEQUENCE (`x, rest... = [1,2,3]` gives `rest = (2, 3)`), whatever the items' origin.
  10. Lone-rest assignment `items... = value` stays forbidden.
  11. `F([])` passes one argument. `F([]...)` passes zero. `1, []..., 2` is `1, 2`.

  Out of scope: collection builtins, indexing, mutation, comprehensions and slicing.
- **Rationale:** The discussion in comments 3–9 was between the maintainer (crazyexpert) and E7-87-83. Normalization is intentional and useful for arity, but it is not injective. Capture of the original rest supply shows this: `Algo(x...) = x` returned `(1, 2)` for both `Algo((1, 2))` and `Algo(1, 2)`. So a sequence cannot be a faithful general-purpose collection. The motivating cases were the singleton matrix row, singleton JSON arrays and data interchange. The objection was that R^1 ≅ R mathematically. The maintainer answered that the concern is about representation, not algebra: a container and its element must stay distinguishable when structure is observable or serialized. Immutability was chosen for simplicity, with internal mutable builders allowed. Comment 7 already doubted that rest capture should return a canonical sequence and set that question aside for separate discussion. #138 later resolved it.
- **Examples (original syntax):**
  ```
  A = [1, 2, 3]
  x = A          // [1, 2, 3]
  y = A...       // (1, 2, 3)
  x, y, z = A    // 1, 2, 3
  x, rest... = A // x = 1, rest = (2, 3)
  F(A)           // one list argument
  F(A...)        // three arguments
  [[7]]...       // supplies [7]
  ```
  Current equivalent: `y = (A*)` (or `A*` as a final row), `x, *rest = A` giving `rest = [2, 3]`, `F(A*)`, `[[7]]*`.
- **Lineage:**
  - **Background, not direct predecessors:**
    - #57 is only an informal "list" (tuple-to-builtin) question.
    - #79 is an informal "list" bug.
  - **Predecessors:**
    - #127 (structural equality for first-class sequences): #134 generalizes structural equality to a second value kind.
    - #128 (empty-sequence representation), #132 (property/call boundaries return one sequence value) and #133 (canonical singleton sequences from builtins): #134 reaffirms that sequence normalization stays, and adds lists beside it instead of weakening normalization.
    - #126 (movable-rest deconstruction, singleton-boundary item-stream binding): #134 extends lone-structure deconstruction opening from sequences to lists.
  - **Successors:**
    - #135 (0ca55e9, 2026-07-17) removes the builtin deferral. Collection builtins take one fixed collection object, open a bound list, and return exact lists. At #134's own commit the spec case `list-builtins-deferred` made `count([1, 2, 3])` a type error.
    - #136 (c133952) refines the `atoms` builtin: it walks through list boundaries and returns an exact list.
    - #137 (2c0af18) adds `:` indexing on list targets. #134 had declared indexing out of scope.
    - #138 (ab7d2f5, 2026-07-18) reverses §9: every rest binding now COLLECTS an exact list (`capture`/`collect`/`open` algebra), so `x, rest... = [1, 2, 3]` gives `rest = [2, 3]`.
    - #139 (eab2468, 2026-07-24) reverses §10 and replaces the rest syntax with prefix `...items`. In that commit the spec case `list-lone-rest-assignment-rejected` (ParseError) became `list-lone-rest-assignment` (Evaluates, `...items = [1, 2, 3]` gives `[1, 2, 3]`). The issue #139 body does not discuss this reversal; only the commit diff shows it.
    - 5377b9c (2026-07-27) renames the case to `list-lone-collecting-assignment` as a terminology change only.
    - #140 (09382b3 / 73648e9, 2026-07-28/29) replaces the syntax again: `value...` becomes `value*` and `...items` becomes `*items`.
    - #167 (C-full "values stay values", 2026-09-23) reaffirms and generalizes §6 to every consumer, including collectors (`Coll([1, 2])` is `[[1, 2]]`).
    - d14f4a7 (2026-09-13) narrows §7's claim that `x, y, z = [1, 2, 3]` binds identically to the spread form. That holds for the example but not in general: a singleton list whose element is itself a sequence or list binds differently.
    - #168 (parentheses group syntax) reaffirms that `([1, 2])` is the list itself.
- **Classification:** PARTIALLY CURRENT
- **Surviving part / superseded by:**
  - **Survives:**
    - the list value kind and the `[...]` literal
    - exactness (no singleton or empty-nesting collapse)
    - kind-distinct, recursive structural equality
    - observable immutability
    - spread opens exactly one list boundary; `[]` spread supplies zero items
    - spread elements inside list literals
    - calls never open a list implicitly
    - lone-list opening in multi-target deconstruction, one level only
    - single-name capture keeps the list
    - empty-list call and supply behavior
    - item supply is not a value
  - **Superseded:**
    - §9 (rest captures a canonical sequence), by #138/ab7d2f5. It now collects an exact list.
    - §10 (lone-rest assignment forbidden), by #139/eab2468. `*items = [1, 2, 3]` is now valid and gives `[1, 2, 3]`.
    - The surface syntax `...` / `rest...`, by #139 and then #140 (`*` spread, `*name` collect). `[1, 2]...` and `F(items...) = items` are now parse errors (`UnexpectedToken`).
    - The out-of-scope builtin deferral, by #135. The indexing deferral, by #137.
  - **Narrowed:** §7's "binds identically to the spread form", by d14f4a7.
  - **Also superseded:** the claim in comment 9 that `Algo([1, 2])` gives `[1, 2]` and `Algo(1, 2)` gives `(1, 2)`. By #138 and #167 these are now `[[1, 2]]` and `[1, 2]`.
- **Current evidence:**
  - **Rule doc:** `docs/design/language-rules/sequences-lists-and-calls.md` § Lists (line 27), § Spread semantics (line 15), § Collecting parameters (lines 31–33), § Collecting parameter lists, deconstruction, and callbacks (line 37).
  - **Lean, `lean/KatLang.lean`:**
    - `Expr.listLiteral`, lines 889–896
    - `Result.listValue`, lines 1154–1158
    - `Result.normalize` keeps the list boundary, line 1174
    - `Result.asInt?`: a list never coerces to a number, line 1249
    - `Result.toItems`: a list stays opaque, line 1267
    - `Result.spreadItems`, lines 1273–1275
    - `Result.structureItems?`, lines 1285–1288
    - `evalListLiteralCounted`, around lines 6615–6633
    - `resultValueEq a b := a == b`, line 2438: derived structural BEq, kind-exact
  - **Lean laws:** `lean/KatLangArityLaws.lean` `deconstruct_fixed_single_list_opens` (1567), `lone_collecting_list_call_and_deconstruct_differ` (1605) and `collector_lone_list_is_one_item` (604). `lean/CoreArityAlgebraProofs.lean` has the matching theorems at 572 and 686. Guards are in `lean/CoreTests/ListValues.lean`.
  - **C#:**
    - `src/KatLang/Result.cs:208` `Result.ListValue`, with snapshot construction and a read-only view
    - `Result.SpreadItems` (Result.cs:803) and `StructureItems` (Result.cs:822)
    - `src/KatLang/Parser.cs:1009` `ListLiteralFrom` and :4910
    - `src/KatLang/Evaluator.Expressions.cs:287`, the ListLiteral case of `EvalExpressionSpineCounted`, with its async twin at `Evaluator.Async.cs:1181`
    - Parser.cs:2153–2158 documents the lone-collecting-binding form `*items = RHS`
  - **Tests:**
    - `tests/KatLang.Tests/ListValueTests.cs`, 117 tests, for example `SingletonList_IsNotNormalizedAway`, `Spread_NestedList_OpensExactlyOneBoundary`, `Call_ListWithoutSpread_IsOneArgument`, `Deconstruction_DoesNotOpenRecursively`, `SingleNameCapture_PreservesList`, `CollectingBinding_CollectsExactList`, `LoneCollectingBinding_OfList_CollectsExactList`
    - `ListValueImmutabilityTests.cs`
  - **LanguageSpec cases:** `list-literal`, `list-exactness`, `list-vs-sequence-kind`, `list-redundant-parens-canonicalize`, `list-spread-capture`, `list-spread-edges`, `list-literal-spread-elements`, `list-elements-preserve-boundaries`, `list-empty-spread-neutral`, `list-call-boundary`, `list-lone-deconstruction` (its explanation documents the d14f4a7 narrowing), `list-deconstruction-not-recursive`, `collecting-binding-exact-list`, `list-lone-collecting-assignment`. All are in `tests/KatLang.Tests/LanguageSpec/LanguageSpecCorpus.cs` lines 3671–3999.
  - **Other docs:** `tutorial.md` § Lists (line 923 onward) and `KatLang.ebnf:676` `ListLiteral = "[" [ ExpressionList ] "]"`.
  - AGENTS.md's Lists bullet matches the code, Lean and tests. I found no disagreement.
- **Probe (current syntax, translated from `...`; all five paths AGREE):**
  - p1 `[7] == 7` / `[[1, 2]] == [1, 2]` / `[[]] == []` / `[] == ()` / `[1, 2] == (1, 2)` / `[1, [2, 3]] == [1, [2, 3]]` → `false, false, false, false, false, true`.
  - p2 `A = [1, 2, 3]`; `B = (A*)`; `([]*)`; `([7]*)`; `([[7]]*)`; `[A]`; `[A*]`; `[S*]` and `[0, S*, 4]` with `S = 1, 2, 3`; `[L1, L2]`; `[L1*, L2*]`; `1, []*, 2` → `[1, 2, 3]`, `(1, 2, 3)`, `()`, `7`, `[7]`, `[[1, 2, 3]]`, `[1, 2, 3]`, `[1, 2, 3]`, `[0, 1, 2, 3, 4]`, `[[1, 2], [3, 4]]`, `[1, 2, 3, 4]`, `1`, `2`.
  - p3 `One([1, 2, 3])` → 7. `Three([1, 2, 3]*)` → 6. `Cnt([])` → 1 and `Cnt([]*)` → 0, with `Cnt(*xs) = xs.count`. `Algo([1, 2])` → `[[1, 2]]` and `Algo(1, 2)` → `[1, 2]`, with `Algo(*x) = x`. The last two supersede comment 9.
  - p4 deconstruction:

    | Binding | Result | Note |
    | --- | --- | --- |
    | `x, y, z = [1, 2, 3]` | `1, 2, 3` | |
    | `p, q = [1, 2], 3` | `p = [1, 2]`, `q = 3` | |
    | `h, *r = [[1, 2, 3]]` | `h = [1, 2, 3]`, `r = []` | #134 said `()` |
    | `u, *rest = [1, 2, 3]` | `rest = [2, 3]` | #134 said `(2, 3)` |
    | `v, *rest2 = ([1, 2]*, [3, 4]*)` | `rest2 = [2, 3, 4]` | |
    | `*items = [1, 2, 3]` | `[1, 2, 3]` | forbidden in #134 |
    | `f1, *rs1 = (1, 2), (3, 4)` | `rs1 = [(3, 4)]` | |
    | `f2, *rs2 = (1, 2), 3, 4` | `rs2 = [3, 4]` | |

    The last two rows answer the non-injectivity concern raised in comment 7.
  - Narrowing: `A = [[1, 2]]`; `x, *xs = A`; `y, *ys = (A*)` → `x = [1, 2]`, `xs = []`, `y = 1`, `ys = [2]`.
  - Obsolete syntax: `A = [1, 2]` then `A...` → parseFailure `UnexpectedToken`. `F(items...) = items` → parseFailure `UnexpectedToken`.
  - Probe files: `scratchpad/probes/batch-09/p1_equality.kat`, `p2_spread_capture.kat`, `p3_calls.kat`, `p4_decon.kat`.
- **Topics:** VAL, SEQ, SUP, CALL, VAR, SYN, COLL, FORMAL

### #135 — Make collection builtins accept one fixed collection object and return exact lists
- **Dates:** created 2026-07-17 · closed 2026-07-17 (commit 0ca55e9 "Make collection builtins support immutable lists while preserving ordinary variadic binding (fixes #135)")
- **Problem / question:** After exact lists (#134) landed, collection builtins were still modeled as variadic item-supply callables (registry parameter `values` of `ParameterKind.Variadic`, from d2837f4 "Unify builtin rest parameters with item-stream binding"): (1) a lone sequence/list argument could be opened BEFORE binding and distributed across the variadic collection slot and trailing control parameters (`take([1,2,3])` read as collection `(1,2)`, count `3`); (2) collection-producing builtins returned canonical sequences, so empty/singleton/nested boundaries were erased (`take(Rows,1)` could collapse to the row itself — the #133 hole).
- **Decision / intended invariant:** Every source-collection builtin is an ordinary FIXED-ARITY callable with exactly ONE fixed `collection` parameter followed by fixed control parameters: `count/sum/first/last/min/max/avg/order/orderDesc/distinct(collection)`, `take/skip(collection, count)`, `contains(collection, item)`, `map(collection, mapper)`, `filter(collection, predicate)`, `reduce(collection, reducer, initial)`; `range(start, stop)` stays fixed 2-ary. (a) An unspread sequence or list is ONE argument; nothing is opened before arity checking. (b) Spread keeps only its ordinary meaning (supplies ordinary slots that obey the same fixed arity) — no builtin-specific spread rule. (c) After binding, the bound collection is read through ONE post-binding view `collectionItems`: sequence -> its items, list -> its items, any other value -> one item; exactly one level, never recursive. (d) Collection-producing builtins (`range, filter, map, order, orderDesc, distinct, take, skip`) always return an exact immutable list (`[]`, `[item]`, `[a, b, …]`), never a canonical sequence, and the result kind never depends on the input kind (no overloading). (e) Observers/reducers (`count, contains, first, last, min, max, sum, avg, reduce`) keep scalar/selected results. (f) `A.take(2)` is exactly `take(A, 2)`; no builtin-specific receiver placement. (g) `count()` (arity error) ≠ `count(())` (0). (h) Optimizers must never make an invalid fixed-arity form valid. Scope guards (at the time): user variadic parameters and rest binding stay canonical-sequence-shaped; `atoms` deferred; no list patterns, no list indexing, no list truthiness.
- **Rationale:** Comment 1 (maintainer): singleton-adaptive sequence results are convenient (`take(A,1)` gives the element) but "an operation whose semantic result is a collection should return an exact collection"; the explicit unpacking cost (`result*` or indexing) buys the invariant zero->`[]`, one->`[item]`, many->`[…]`. Fixed arity keeps the call boundary uniform with every other call (no pre-binding opening), and the one-level post-binding view is a builtin-level interpretation of an already-bound value, not an overload.
- **Examples:** `take([1, 2, 3])` -> arity error (count missing); `take((1, 2, 3), 2)` -> `[1, 2]`; `count([1, 2, 3]...)` -> arity error, `count(([1, 2, 3]...))` -> 3 (current equivalent: `count([1, 2, 3]*)` / `count(([1, 2, 3]*))`); `take([[1, 2], [3, 4]], 1)` -> `[[1, 2]]`; `distinct(((), ()))` -> `[()]`.
- **Lineage:**
  - replaces the variadic builtin model of d2837f4 (2026-06-19, "Unify builtin rest parameters with item-stream binding", itself following #126) — the commit deletes `BuiltinItemSupplyBindingTests.cs` and changes the registry parameter `values` (Variadic) to fixed `collection` (`git show 0ca55e9 -- src/KatLang/BuiltinRegistry.cs`);
  - removes the pre-binding lone-group opening lineage (#111 "variadic-slot sequence supply", and the `NormalizeSingletonBoundaryForItemSupply*` / `supplyIsSingleGroupedValue` helpers per the memory note `list-value-surface.md`, secondary evidence);
  - supersedes the result form of #132 (collection-producing builtins returned ONE canonical sequence value) and of #133 (canonical singleton erasure of builtin results, e.g. `take(((1,2),(3,4)),1)`): results are now exact lists;
  - refines #134 (exact lists; #134 explicitly deferred builtins to "a separate GitHub issue" — this one);
  - #137 (same day) adds `:` indexing so `[item]` results can be unpacked; #136 (next day) extends the exact-list result contract to `atoms`;
  - #138 (2026-07-18) reverses #135's scope guard that rest/variadic capture stays canonical-sequence-shaped ("Collection builtins remain fixed-arity operations … must not restore variadic collection-builtin signatures" — reaffirms the builtin part) and fa381ae (2026-07-19) moves the core arity algebra to exact-list rest, reversing #135's "core arity algebra remains sequence-centered";
  - #165 (Booleans) supersedes the "existing true representation" of `contains` and the list-truthiness remarks for `filter`;
  - #167 / 68b3607 "Make dot-call pass values without implicit spreading" reaffirms (f) (dot receiver is an ordinary leading argument, no dot-only builtin path); 874625a makes `first`/`last` selection value boundaries (`first(A) ≡ A:0`), refining "selected-value identity";
  - C-full "values stay values" (Sep 23 2026, AGENTS.md collecting-parameter bullets) supersedes the `Inspect(items...)` examples.
- **Classification:** PARTIALLY CURRENT
- **Surviving part / superseded by:** SURVIVES fully: fixed collection-object arity for all listed builtins; no pre-binding opening; spread obeys ordinary fixed arity (grouped spread `(A*)` to form one collection); post-binding one-level view; scalar as one-element collection; exact-list results for collection producers; observers return scalar/selected values; dotted ≡ plain; no builtin overloading by input kind; optimizer parity (invalid spread forms fall back to the generic arity error); strict single-value map/reduce callback contract. DID NOT SURVIVE: the scope-guard claims that user variadic parameters and rest binding stay canonical sequences (`Inspect(7) // 7`, `Inspect([1,2,3]) // [1,2,3]`, `head, rest... = [1,2,3] // (2, 3)`, "Rest must not preserve list provenance or return lists", "core arity algebra remains sequence-centered") — superseded by #138 (ab7d2f5), fa381ae, and the exact collector law (C-full, AGENTS.md "VALUES STAY VALUES"); `contains` numeric truth result and list-truthiness remarks — superseded by #165; `...` spread / `rest...` syntax — replaced by #139/#140 star markers; `//` comments — #142. The permitted "narrowly targeted" dotted-`reduce` missing-initial hint no longer exists: today `A.reduce({a + b})` and `reduce((1, 2, 3), {a + b})` give the identical ordinary message "Callable `reduce(collection, reducer, initial)` expects 3 arguments, but was called with 2 arguments." (probe; which commit removed the hint was not established — would be settled by `git log -S` on the hint text). *(Q-25, 2026-10-10: the strict single-value map/reduce callback contract is SUPERSEDED — a callback returns its ordinary call result, HO-03.)*
- **Current evidence:**
  - `docs/design/language-rules/sequences-lists-and-calls.md` § Collection builtins (full statement, incl. `sum((A*, B*))`, `count(([], []))` is 2, `Qmean(*args)` example) and § Value boundaries (collection producers via `makeCollectionListResult`).
  - Lean: `lean/KatLang.lean:486` `sequenceBuiltinMetadata?` ("ordinary fixed-arity native callable: exactly one fixed `collection` parameter"); `:5598-5610` `bindSequenceBuiltinArguments` (`expectedArgCount := 1 + metadata.suffixArgs.length`, `Error.arityMismatch`); `:2665` `builtinCollectionItems`; `:2842` `makeCollectionListResult`. Laws in `lean/KatLangArityLaws.lean`: `builtinCollectionItems_sequence` (:115), `builtinCollectionItems_nested_pair_opens_one_boundary` (:118), `builtinCollectionItems_atom` (:124), `builtinCollectionItems_list` (:1491), `builtinCollectionItems_keeps_nested_list_opaque` (:1494), `makeCollectionListResult_exact` (:1502), `makeCollectionListResult_empty` (:1505). CoreTests guard `collectionBuiltinsKeepTheirFixedCollectionParameter` (`lean/CoreTests/ExplicitValueOpening.lean:557`).
  - C#: `src/KatLang/BuiltinRegistry.cs:52` (`new("collection", …)`), `:214` (`FixedArity == count`), `:769` (`fixedArity: 1 + metadata.SuffixArgs.Count`); `src/KatLang/Evaluator.Builtins.cs:1197` `BindSequenceBuiltinCollectionArgument`; `src/KatLang/Evaluator.ParameterBinding.cs:1663` `BuiltinCollectionItems`; `Evaluator.Builtins.cs:87` / `Evaluator.PatternMatching.cs:833` `MakeCollectionListResult`.
  - Tests: `CollectionBuiltinBindingTests` (e.g. `InvalidDirectAndSpreadForms_ReportExactFixedArityAtCallSite`, `SingleCollectionBuiltins_RejectInlineMultiItemCalls`, `Take_TakesCollectionAndCount`, `Reduce_DotReceiverFillsCollection_SpreadFormsNeedRegrouping`), `EvaluatorCollectionBuiltinTests`, `ListValueTests`, `ListValueImmutabilityTests`. Spec cases `builtin-fixed-collection-arity`, `take-prefix`, `take-single-survivor`, `take-zero-empty` (`LanguageSpecCorpus.cs:2388-2425, 2967`).
  - tutorial.md "### One Collection Argument" (line 1186) and "### Results Are Lists" (line 1213). AGENTS.md "Collection builtins are ordinary FIXED-ARITY callables…" bullet — agrees with code/Lean.
- **Probe:** `take([1, 2, 3])` -> err ArityMismatch; `take((1, 2, 3))` -> err ArityMismatch; `take([1, 2, 3], 2)` / `take((1, 2, 3), 2)` -> `L[1, 2]`; `count(1, 2, 3)`, `count()`, `count([1, 2, 3]*)` -> err ArityMismatch; `count(([1, 2, 3]*))` -> 3; `count(())` / `count([])` -> 0; `order(())` -> `L[]`; `take([7]*, 1)` -> `L[7]`; `distinct(((), ()))` -> `L[S[]]`; `take([[1, 2], [3, 4]], 1)` -> `L[L[1, 2]]`; `count(((1, 2), (3, 4)))` -> 2; `count((1, [2], 3))` -> 3; `take(7, 1)` -> `L[7]`; `take(7, 0)` -> `L[]`; `order(7)` -> `L[7]`; `contains(7, 7)` -> `true`; `range(3, 1)` -> `L[3, 2, 1]`; `range(3, 3)` -> `L[3]`; `reduce((1, 2, 3), {a + b}, 0)` and `reduce([1, 2, 3], {a + b}, 0)` -> 6; `reduce((1, 2, 3), {a + b})` -> err ArityMismatch; `Pair(x) = (x, x)` / `map((1, 2), Pair)` -> `L[S[1, 1], S[2, 2]]`; `Two(x) = x, x` / `map((1, 2), Two)` -> err ArityMismatch (multi-output callback still invalid); `count(filter(A, IsOdd)*)` -> err ArityMismatch on all paths incl. optimized; `count(A.filter(IsOdd))` -> 2; `B = [1, 2, 3]` / `B.take(2)`, `B.order`, `B.count` -> `L[1, 2]`, `L[1, 2, 3]`, 3. SUPERSEDED parts: `Inspect(*items) = items` with `Inspect(7)` -> `L[7]` (issue said `7`), `Inspect([1, 2, 3])` -> `L[L[1, 2, 3]]` (issue said `[1, 2, 3]`), `Inspect()` -> `L[]` (issue said `()`), `Inspect([1, 2, 3]*)` -> `L[1, 2, 3]` (issue said `(1, 2, 3)`); `head, *rest = [1, 2, 3]` -> `rest` = `L[2, 3]` (issue said `(2, 3)`); `head, *rest = [1, 2]` -> `L[2]` (issue said `2`); `f, *rest = 1, [2, 3]*, (4, 5)*` -> `L[2, 3, 4, 5]` (issue said `(2, 3, 4, 5)`); `A = take([1, 2, 3], 2)`, `B = A*` -> `S[1, 2]` and with `take(…, 1)` -> `1` (matches the issue's re-entry claim). Probe-writing note: `B = A*` newline `B` parses as multiplication (SYN-07B), so the spread line was placed last.
- **Topics:** COLL, CALL, SEQ, SUP, VAL, DOT, HO, VAR, FORMAL


### #136 — Define list semantics for the atoms builtin
- **Dates:** created 2026-07-17 · closed 2026-07-18 (commit c133952 "Define list semantics for the atoms builtin (fixes #136)")
- **Problem / question:** #135 deliberately left `atoms` untouched; `atoms` still treated lists as opaque and returned a canonical sequence (`atoms([1, 2])` -> `()`, `atoms(((1, 2), [3, 4]))` -> `(1, 2)`), so it composed badly with the new list-producing builtins (`[1, 2, 3].skip(1).atoms` -> `()`).
- **Decision / intended invariant:** `atoms(value)` recursively traverses BOTH sequence and list boundaries (depth-first, left to right) and ALWAYS returns one exact list: `atoms(number) = [number]`, `atoms(sequence xs)` / `atoms(list xs)` = concatenation of `atoms(x)`, `atoms(other) = []`. The result kind never depends on the atom count (no singleton erasure: `atoms(7)` is `[7]`, not `7`; `atoms((1, 2))` is `[1, 2]`, not `(1, 2)`). `atoms` is a collection-producing operation, not an arity-capture operation; users select (`A:0`) or spread (`A*`) the result explicitly.
- **Rationale:** Consistency with #135's exact-collection principle and direct composition with list-producing builtins without a spread-and-recapture workaround. The implementing commit kept the language collector separate from the host projection and (at the time) from the truth-testing view, so lists acquired no truth value through `atoms` (commit c133952 adds `Result.languageAtoms` distinct from `Result.atoms` / `Result.hostAtoms`, plus `TruthValueNonRegressionTests.cs`, `HostAtomsNonRegressionTests.cs`).
- **Examples:** `atoms([(1, 2), [3, [4]], 5])` -> `[1, 2, 3, 4, 5]`; `atoms([[], (), [1]])` -> `[1]`; `atoms('text')` -> `[]`; `[1, 2, 3].skip(1).atoms` -> `[2, 3]`; `A...` (current equivalent: `A*`).
- **Lineage:**
  - refines #135 (which deferred `atoms` with explicit open questions: recursion through lists, list vs sequence result) — answers all of them;
  - supersedes the #132 result form for `atoms` (one canonical sequence value) and the pre-#136 list-opaque `atoms`;
  - distinct from, and later than, the one-level `ungroup`/`content` builtins (#91, #98) that were removed by #129 — `atoms` stays the recursive flattener while one-level opening is the spread marker;
  - #165 (first-class Booleans) superseded the commit-level "truth view stays list-opaque" arrangement: there is no numeric truth at all now, and `Result.atoms` (the truth view) no longer exists in `lean/KatLang.lean` (grep finds no `def atoms`; `TruthValueNonRegressionTests.cs` no longer exists in `tests/KatLang.Tests`); Booleans fall into `atoms(other) = []` (`atoms_bool` law);
  - reaffirmed by the exact-list rest work (#138 lists `atoms` results among published `ListValue`s under the immutability contract).
- **Classification:** CURRENT
- **Surviving part / superseded by:** Entire issue contract survives unchanged. Only spelling changes: `A...` -> `A*` (#139/#140). The implementation-level separation of `atoms` from a numeric truth view is moot after #165 (Booleans only); the separation from host flattening (`hostAtoms`) survives.
- **Current evidence:**
  - `docs/design/language-rules/sequences-lists-and-calls.md` § Lists ("The `atoms` builtin recursively collects numeric atoms through BOTH sequence and list boundaries … `atoms(7)` is `[7]`, `atoms([1, [2]])` is `[1, 2]`, `atoms('text')` is `[]` — the result kind never depends on the input"), § Value boundaries (`atoms` in the collection-producing list).
  - Lean: `lean/KatLang.lean:1185` `Result.languageAtoms` (atom/str/bool/sequenceValue/listValue arms), `:1202` `Result.hostAtoms` (separate host projection), `:5923` dispatch `pure (makeCollectionListResult ((Result.languageAtoms r).map Result.atom))`. Laws `lean/KatLangArityLaws.lean:2093-2142`: `atoms_number`, `atoms_string`, `atoms_bool`, `atoms_sequence`, `atoms_list`, `atoms_empty_sequence`, `atoms_empty_list`, `atoms_order_preserved`, `atoms_nested_sequence`, `atoms_nested_list`.
  - C#: `src/KatLang/Result.cs:431` `LanguageAtoms` / `:450` `TryLanguageAtoms` (bounded), `:565` `ToHostAtoms`; `src/KatLang/Evaluator.Builtins.cs:101` `MakeLanguageAtomsResult` (sync dispatch `:2331`, async twin `Evaluator.Async.cs:2375`).
  - Tests: `AtomsBuiltinTests` (e.g. `Atoms_Number_IsSingletonList`, `Atoms_String_IsEmptyList`, `Atoms_MixedStructures_FlattenRecursively`, `Atoms_ResultKind_IsExactList`), `HostAtomsNonRegressionTests`. Spec cases `atoms-recursive-flatten`, `atoms-exact-list-result`, `atoms-list-traversal`, `atoms-mixed-traversal`, `atoms-list-composition`, `atoms-no-truthiness` (`LanguageSpecCorpus.cs:2791-2877`).
  - tutorial.md "### Flattening with `atoms`" (line 1290, `<!-- spec:atoms-recursive-flatten -->`).
- **Probe:** `atoms([1, 2])` -> `L[1, 2]`; `atoms(((1, 2), [3, 4]))` -> `L[1, 2, 3, 4]`; `atoms(7)` -> `L[7]`; `atoms('text')` -> `L[]`; `atoms(())` -> `L[]`; `atoms([])` -> `L[]`; `atoms([(1, 2), [3, [4]], 5])` -> `L[1, 2, 3, 4, 5]`; `atoms((1, [2, (3, [4])]))` -> `L[1, 2, 3, 4]`; `atoms([[], (), [1]])` -> `L[1]`; `[1, 2, 3].skip(1).atoms` -> `L[2, 3]`; `[[1, 2], [3, 4]].take(1).atoms` -> `L[1, 2]`; `range(1, 3).atoms` -> `L[1, 2, 3]`; `atoms((true, 1, false))` -> `L[1]` (post-#165 addition: Booleans contribute nothing); `atoms(1, 2)` -> err ArityMismatch (fixed one-argument builtin); `atoms([10, 20]):1` -> 20.
- **Topics:** COLL, SEQ, VAL, BOOL, FORMAL


### #137 — Add `:` indexing support for exact immutable lists
- **Current-rule note (Q-81, 2026-10-12):** the `:` spelling and the rejection of bracket indexing are superseded by variadic postfix selection `A[s1, …, sn]`; the list-target positions, the zero-based index rules and the stored-element rule established here survive (SEQ-04, SEQ-05).
- **Dates:** created 2026-07-17 · closed 2026-07-17 (commit 2c0af18 "Add `:` indexing support for exact immutable lists (fixes #137)")
- **Problem / question:** `:` positional projection worked on sequences but lists were opaque to it (#134 deferred list indexing). With #135 making collection producers return `[item]`, users needed an explicit way to select an element (`take([1, 2, 3], 1):0`).
- **Decision / intended invariant:** Extend the ONE existing `:` projection uniformly: `sequence:i` -> immediate sequence element, `list:i` -> immediate list element, with identical zero-based indexing, index validation, bounds rules, error category, diagnostics, chaining and parsing. Indexing selects exactly ONE immediate element and returns it as stored — never recursively flattened, spread, canonicalized, re-wrapped, or kept in a singleton list (`[[1, 2], [3, 4]]:0` is `[1, 2]`; `[(1, 2), (3, 4)]:0` is `(1, 2)`); nested structures index one level per `:`; empty / past-the-end positions are the same out-of-range error as sequences (never `()`, `[]`, or a default); index-value validation is shared (no list-specific coercion or negative-index semantics); scalar/string/other projection behavior is unchanged; no second indexing subsystem; no bracket indexing `A[0]` (brackets stay list-literal syntax). Indexing (select one position) and spread (open the whole list) are distinct operations.
- **Rationale:** Keeps exact-list results (#135) exact while giving an explicit, cheap element selection; "Do not change collection-producing builtins back to singleton-erasing sequence results merely to make their values easier to consume." Reusing the sequence path guarantees parity.
- **Examples:** `[1, 2, 3]:2` -> 3; `Rows = [[1, 2], [3, 4]]`, `Rows:0:1` -> 2; `[]:0` -> out-of-range error; `take([1, 2, 3], 1):0` -> 1; `[[1, 2]]:0 == (1, 2)` -> `0` (current: `false`).
- **Lineage:**
  - refines #134 (which listed "list indexing and update syntax" as out of scope);
  - complements #135 (selection is the explicit unpacking of `[item]` results);
  - the implementation at the time (2c0af18) still "projected" a selected SEQUENCE element's content one level (`projectSelectedContent`); 874625a ("Unify indexing, first, last, and callback value boundaries #167", 2026-09-21) replaced that with SELECTION IS A VALUE BOUNDARY — `Result.select?` returns the stored element as ONE value, re-counted by `Result.valueCount` — which completes the issue's own "retain its original kind and structure" requirement for sequence elements too and adds `first(A) ≡ A:0`, `last(A) ≡ A:(A.count - 1)`;
  - #140 (star syntax) added the `A*:0` rejection (selection cannot operate on an item supply; repairs `(A:0)*` / `(A*):0`);
  - #165 changed equality results from `1`/`0` to `true`/`false`;
  - its aside "rest binding continues capturing … canonically as sequences … Do not make rest return a list" was reversed by #138 the next day (rest collects exact lists); the non-interference requirement (indexing does not affect rest) still holds.
- **Classification:** CURRENT
- **Surviving part / superseded by:** The whole list-indexing contract survives. Refined (not reversed) by #167/874625a (selection is a value boundary; no content projection of any selected element). Stale only in incidental text: the rest-binding aside (superseded by #138), numeric equality results (superseded by #165), `A...` spelling (#139/#140).
- **Current evidence:**
  - `docs/design/language-rules/sequences-lists-and-calls.md` § Lists ("Indexing `:` reads its TARGET's positions through the position view `Result.projectionItems` … `[1, 2, 3]:0` is 1 under the same zero-based index rules as sequence selection … a selected list is one opaque list") and § Value boundaries (SELECTION IS A VALUE BOUNDARY). `syntax.md` § Comma and same-line items (line 15: `A[1]` is the SYN-07A `UnseparatedSameLineItem` error, so `[` never begins indexing) and § The spread marker (line 35: a spread as an indexing target/selector is a targeted parse error, hence `A*:0` is rejected).
  - Lean: `lean/KatLang.lean:1327` `Result.projectionItems` (`listValue rs => rs | r => r.toItems`) and the following `Result.select?` (`r.projectionItems[i]?`). Laws `lean/KatLangArityLaws.lean`: `projectionItems_listValue` (:1034), `projectionItems_sequenceValue` (:1038), `projectionItems_empty_list` (:1042), `projectionItems_atom` (:1047), `select_list_first` (:1052), `select_list_last` (:1058), `select_list_chained` (:1075), `select_list_past_end_out_of_range` (:1099), `select_is_stored_element` (:1118), `first_is_select_zero` (:1158), `last_is_select_last` (:1169). CoreTests guards `listIndexingSelectsElement`, `listIndexingNestedElementStaysList`, `listIndexingChainedSelectsOneLevelAtATime` (`lean/CoreTests/ListValues.lean:421-458`).
  - C#: `src/KatLang/Result.cs:842` `ProjectionItems`, `:865` `Index`.
  - Tests: `ListValueTests` (`Indexing_ListTarget_SelectsElement`, `Indexing_ListTarget_AgreesWithSequenceTarget`, `Indexing_NestedListElement_StaysExactList`, `Indexing_ChainedListSelection_SelectsOneLevelAtATime`, `Indexing_SequenceElementInsideList_SelectsOneValueLikeSequenceTarget`, `BracketAfterExpression_IsRejected_NeverIndexing`), `EvaluatorIndexingTests`, `SelectionValueBoundaryTests`. Spec cases `list-index-selects-element`, `list-index-nested-element-stays-exact`, `list-index-out-of-range`, `list-index-builtin-results` (`LanguageSpecCorpus.cs:3722-3790`), plus `negative-index-literal-rejected` (:3319).
  - tutorial.md "### Working with Lists" (line 966: `Primes:0`, `Grid:1:0`).
- **Probe:** `[1, 2, 3]:0` -> 1; `[7]:0` -> 7; `[[1, 2], [3, 4]]:0` -> `L[1, 2]`; `[(1, 2), (3, 4)]:0` -> `S[1, 2]` n=1; `Rows = [[1, 2], [3, 4]]` / `Rows:0:1` -> 2; `[]:0`, `[1, 2]:2`, `[1, 2]:(0 - 1)`, `[1, 2]:0.5` -> err BadIndex (sequence twins `(1, 2):2`, `(1, 2):0.5` -> err BadIndex); `[1, 2]:'a'` and `(1, 2):'a'` -> err TypeMismatch; `[1, 2]:[0]`, `[1, 2]:(0, 1)`, `[1, 2]:()` and their sequence twins -> err ArityMismatch; `[1,2]:-1` and `(1, 2):-1` -> parse failure UnexpectedToken; `take([1, 2, 3], 1):0` -> 1; `[3, 1, 2].order:0` -> 1; `A = [10, 20, 30]` / `A.take(2):1` -> 20; `Rows.take(1):0:1` -> 2; `[[1, 2]]:0 == [1, 2]` -> true; `[(1, 2)]:0 == (1, 2)` -> true; `[[1, 2]]:0 == (1, 2)` -> false; `7:0` -> 7, `7:1` -> err BadIndex, `'abc':0` -> `'abc'` (scalar/string projection unchanged: a scalar is its own position 0); `A = [1, 2]` / `A*:0` -> parse failure MisplacedSpread (#140); `A = [[1, 2]]`, `Cnt(*xs) = xs.count`: `Cnt(A:0)` -> 1, `Cnt(A:0*)` -> 2 (selected list is one value; only spread opens it).
- **Topics:** SEQ, VAL, SYN, COLL, FORMAL

### #138 — Make all rest bindings collect exact immutable lists
- **Dates:** created 2026-07-18 · closed 2026-07-18 (fixed by ab7d2f5; strengthened next day by fa381ae "Strengthen core arity algebra for exact-list rest binding")
- **Problem / question:** Rest bindings (deconstruction rest, user variadic parameters, movable prefix/middle/suffix rest) materialized their assigned items through canonical sequence capture, which erases singleton and empty boundaries: `first, rest... = [[1, 2], [3, 4]]` gave `rest = [3, 4]` with `rest.count` 2 (columns, not remaining rows); `head, rest... = [1]` gave `()`. With exact immutable lists now in the language (#134), what should a rest binding hold?
- **Decision / intended invariant:** Three distinct item-supply operations: `capture : Supply → Value` (canonical, normalizing; ordinary assignment and property/function results), `collect : Supply → ListValue` (every rest binding), `open : Value → Supply` (postfix spread). EVERY rest binding — deconstruction, single variadic parameter, mixed prefix/rest/suffix, callback, optimized paths — materializes exactly its assigned items as ONE exact list: 0 items `[]`, 1 item `[item]` (never erased), many `[a, b, …]`; result kind never depends on cardinality. Consequences stated in the issue: (a) `F(A)` and `F(A...)` are intentionally different (`[[1, 2]]` vs `[1, 2]`) — the old rest-only coincidence is abandoned; (b) round trip `open(collect(xs)) = xs`, so forwarding is ordinary spread (`Forward(items...) = Target(items...)`) and hidden raw-item/provenance metadata should be removed; (c) calls never implicitly open a lone list/sequence argument because the callee has a rest; (d) dotted receiver is one ordinary argument (`A.Inspect` = `Inspect(A)` = `[[1, 2]]`); (e) deconstruction keeps its receiver-specific lone-sequence/list opening before matching; (f) single-name capture and function/property results stay canonical (`x = [1, 2, 3]...` is `(1, 2, 3)`); (g) lone-rest assignment `items... = value` remains forbidden; (h) rest lists obey the same immutability contract as every `ListValue`; (i) one shared prefix/rest/suffix binder for all binders; (j) formal core must model `collect` separately and replace coincidence theorems with exactness laws (length, order, kind, singleton preservation, provenance independence, round trip).
- **Rationale:** A rest variable represents "the exact collection of items assigned to the rest pattern"; canonical capture cannot faithfully represent a singleton structured remainder or distinguish one empty item from zero items. Aligns rest results with collection-producing builtins (#135): `first, rest... = Rows` should agree with `skip(Rows, 1)` = `[[3, 4]]`.
- **Examples:**
  ```katlang
  first, rest... = [[1, 2], [3, 4]]   // rest = [[3, 4]], rest.count = 1
  Inspect(items...) = items
  Inspect([1, 2])      // [[1, 2]]
  Inspect([1, 2]...)   // [1, 2]
  F(first, middle..., last) = middle
  F([1, 2], [3, 4])    // []
  ```
  current equivalent: `first, *rest = [[1, 2], [3, 4]]`; `Inspect(*items) = items`; `Inspect([1, 2]*)`; `F(first, *middle, last) = middle`. Equality results written `1`/`0` in the issue are now `true`/`false`.
- **Lineage:**
  - supersedes the rest-result part of #126 (movable-rest deconstruction: "rest binding captures its assigned items as one grouped sequence value", issue lines 254-288) — replaces capture with collect.
  - reverses #111 (count-driven variadic opening so `Qmean(Vector)` works without spread): #138 makes `F(A)` ≠ `F(A...)` deliberately.
  - generalizes #134 (exact list values) and #135 (collection builtins return exact lists) to rest bindings.
  - partially reversed by the #139 commit eab2468 (2026-07-24): lone rest assignment `...all = 1, 2, 3` became VALID (`[1, 2, 3]`), contradicting #138's "Lone-rest assignment remains forbidden" (pre-#139 tutorial line 1409/3005 at eab2468^ still said it was a parse error).
  - replaces syntax of: #139 (prefix `...name` for rest), 09382b3 (back to postfix `name...` + `spread(x)`), then #140 / 73648e9 (prefix `*name` collect, postfix `x*` spread); terminology renamed rest → collecting binding by 5377b9c (2026-07-27), "variadic parameter" → "collecting parameter" by #140.
  - narrowed (temporarily) by #144 / f12af0f (2026-08-11): a WRITTEN group dot receiver was a "segment" whose raw rows a flat collector consumed (`(1, 2).Collect` → `[1, 2]`), contradicting #138's "no implicit receiver spreading"; and by #167 / dada1b6 (2026-09-21) "collector supply-boundary law" (a lone written sequence opened one level at any collector, `Coll((1, 2))` → `[1, 2]`).
  - reaffirmed by #167 / 68b3607 ("Make dot-call pass values without implicit spreading") and 702e7d7 (2026-09-23, "values stay values" / C-full), which deleted receiver segments, `SupplyOrigin`, `collectorSupply`, and restored exact collection of every non-spread argument — i.e. #138's original rule. Also the flat-callback row convention for rest callbacks (added in #138's same-day correction pass per memory note rest-collects-exact-lists) was deleted by 702e7d7 (callback element = one ordinary argument), bringing callbacks back to #138's "no separate rest-result rule for callback binding".
  - boolean-valued equality examples: superseded in form by #165 (first-class Booleans).
- **Classification:** PARTIALLY CURRENT
- **Surviving part / superseded by:** SURVIVES (all verified): the capture/collect/spread triple; every collecting binding collects exactly one exact list with emitted count 1 (`[]`/`[x]`/`[…]`, never erased); `F(A)` ≠ `F(A*)` for structured arguments; forwarding round trip `spread(collect(S)) = S` with no hidden raw-supply metadata (`variadicSupplyEnv`/`VariadicStreamEnv` deleted and forbidden); no implicit opening at calls or dot receivers; deconstruction's receiver-specific lone-structure opening; canonical single-name capture; one shared binder; immutable list snapshot. SUPERSEDED/REVERSED: (1) syntax `items...` / `A...` → `*items` / `A*` (#139 → #140); (2) "lone-rest assignment remains forbidden" → reversed by eab2468 (#139 commit); `*items = RHS` is now valid (EBNF `DeconstructionDefinition = CollectingBinding "=" OutputBundle`); (3) terminology "rest binding / variadic parameter" → "collecting binding / collecting parameter"; (4) `==` results `1/0` → `true/false` (#165). No disagreement with AGENTS.md found (its "Collecting binding COLLECTS one list" and "VALUES STAY VALUES" bullets restate #138's rule).
- **Current evidence:**
  - Lean: `collectSegment` (`lean/KatLang.lean:2889`, `= Result.listValue items`); laws in `lean/KatLangArityLaws.lean`: `collectSegment_eq_listValue` :171, `collectSegment_length` :175, `collectSegment_empty` :180, `collectSegment_singleton` :194, `collectSegment_singleton_ne_item` :214, `spreadItems_collectSegment` :223, `collector_lone_sequence_is_one_item` :592, `collector_lone_list_is_one_item` :604, `collector_lone_empty_values_are_one_item` :616, `collector_collects_spread_items_exactly` :644, `forwarding_resupplies_the_collected_items` :658, `selection_origin_does_not_change_collector_binding` :672, `dot_call_uses_same_collector_binding_as_plain_call` :684, `collector_fixed_parameter_binds_value_unchanged` :899. Paper algebra `lean/CoreArityAlgebra.lean`: `collect` :233 (`Val.list xs`), `openLoneStructure` :257, `bindArgs` :326, `bindCallback` :340, `bindDeconstruct` :358; proofs `items_collect` (`CoreArityAlgebraProofs.lean:457`), `variadic_collect_distinguishes_spread_seq/_list` :1058/:1073, `receivers_never_same_on_lone_structure` :1276, `collector_lone_argument_is_one_item` :1006, `forwarding_resupplies_the_collected_supply` :1019.
  - C#: `Evaluator.CollectSegment` (`src/KatLang/Evaluator.ParameterBinding.cs:561`, builds `Result.ListValue.TakeOwnership(capturedValues.ToArray())` — exclusive fresh buffer), `CreateCollectingCapture` :591 (emitted count 1), loop state path `Evaluator.Loops.cs:287`.
  - Docs: `docs/design/language-rules/sequences-lists-and-calls.md` § Collecting parameters (line 29ff, full `Coll(*xs)` table) and § Collecting parameter lists, deconstruction, and callbacks (line 35ff); `syntax.md` § Star roles (single-target `*items = RHS` valid).
  - Tests: `CollectingBindingTests` (e.g. `DeconstructionCollectingBinding_PreservesStructuredSingletonRow`, `CollectingCapture_EmptyStructureArgumentsAreOneItem`, `VariadicForwarding_SpreadRoundTripsCollectedItems`, `VariadicForwarding_UnspreadCollectedListIsOneArgument`), `ExplicitValueOpeningTests`, `DotCallCollectingReceiverTests`, `ListValueImmutabilityTests`, `DeconstructionBindingTests`.
  - Spec cases (`LanguageSpecCorpus.cs`): `collecting-binding-exact-list`, `decon-collecting-tail/head/middle`, `decon-lone-collecting`, `list-lone-collecting-assignment`, `variadic-capture-collects-list`, `variadic-forwarding-list-spread`, `variadic-receiver-distinction`, `variadic-grouped-vs-spread`, `values-stay-values`.
- **Probe:** (translated to current star syntax)
  - `p138a.kat`: `Rows = [[1, 2], [3, 4]]`, `first, *rest = Rows`, `Inspect(*items) = items`, `CountArgs(*items) = items.count`, `Mid(first, *middle, last) = middle`, `A = [1, 2]`, rows `rest`, `rest.count`, `rest == skip(Rows, 1)`, `Inspect()`, `Inspect(7)`, `Inspect([1, 2])`, `Inspect([1, 2]*)`, `Inspect((1, 2))`, `Inspect((1, 2)*)`, `CountArgs((10, 20))`, `CountArgs((10, 20)*)`, `Mid([1, 2], [3, 4])`, `A.Inspect`, `Inspect(1, 2) == (1, 2)`, `Inspect(1, 2) == [1, 2]` → `[[3, 4]]`, `1`, `true`, `[]`, `[7]`, `[[1, 2]]`, `[1, 2]`, `[(1, 2)]`, `[1, 2]`, `1`, `2`, `[]`, `[[1, 2]]`, `false`, `true` — every #138 expectation holds.
  - `p138b.kat`: `h1, *r1 = [1]` → `[]`; `h2, *r2 = [1, 2]` → `[2]`; `f3, *m3, l3 = [1, 2]` → `[]`; `a4, *r4 = 1, [2, 3]` → `[[2, 3]]`; `a5, *r5 = 1, (2, 3)` → `[(2, 3)]`; `a6, *r6 = 1, []` → `[[]]`; `a7, *r7 = 1, ()` → `[()]`; `*all = 1, 2, 3` → `[1, 2, 3]` (lone collecting assignment VALID — reversal); `x = [1, 2, 3]*` → `(1, 2, 3)`; `Forward()` → `[]`; `Forward((1, 2))` → `[(1, 2)]`; `Forward((1, 2)*)` → `[1, 2]`; `ForwardAsOne(1, 2)` (= `Target(items)`) → `[[1, 2]]`.
  - `Inspect(*items) = items` / `(1, 2).Inspect` → `[(1, 2)]`; `(1, 2)*.Inspect` → `[1, 2]`; `[7].map(Inspect)` → `[[7]]`; `map([(1, 2)], Inspect)` → `[[(1, 2)]]` (dot receiver and callback element are one item, as #138 required).
- **Topics:** VAR, SUP, SEQ, VAL, CALL, DOT, FWD, HO, FORMAL

### #139 — Distinguish rest bindings from spread expressions with prefix and postfix ellipsis
- **Dates:** created 2026-07-24 · closed 2026-07-24 (fixed by eab2468)
- **Problem / question:** Postfix ellipsis was used both for rest bindings (`F(items...) = …`, collect Supply → List) and for spread expressions (`F(values...)`, open Value → Supply) — identical spelling for opposite operations (`Forward(items...) = Target(items...)`).
- **Decision / intended invariant:** Distinguish the two operations structurally by ORIENTATION: prefix `...name` = rest/collect binding (parameter lists, nested patterns, deconstruction), postfix `expr...` = spread expression; parser decides structurally, not from context; only one rest binding per pattern; diagnostics for missing name / multiple rest / spread without expression; a temporary deprecation period for postfix rest (`items...` warns, code-fix, later removal) with postfix spread unchanged. Semantics unchanged (collect exact list per #138; spread opens one boundary).
- **Rationale:** Make the data-flow direction visible — "`...items` collects supplied items into a binding; `items...` opens a value into supplied items" — especially for movable rest `F(first, ...middle, last)`; explicitly contrasted with JavaScript, which uses prefix `...` for both and disambiguates only by grammatical context.
- **Examples:**
  ```katlang
  Forward(...items) = Target(items...)
  F(first, ...middle, last) = middle
  first, ...middle, last = values...
  ```
  current equivalent: `Forward(*items) = Target(items*)`; `F(first, *middle, last) = middle`; `first, *middle, last = values*`.
- **Lineage:**
  - refines #138 (same day family): gives the collect/open split of #138 a distinct surface.
  - its commit eab2468 also made the single-target form `...items = RHS` valid, reversing #138's / #126's "lone rest assignment remains invalid" (not requested in the issue body).
  - narrowed/reversed its own migration plan in 41c0bb6 (2026-07-25, "reject postfix rest binding syntax"): the deprecation period was dropped one day later — postfix rest became a hard error.
  - terminology refined by 5377b9c (2026-07-27): "rest binding" → "collecting binding", postfix `x...` standardized as "spread expression".
  - reversed by 09382b3 (2026-07-28, first #140 commit): collecting binding moved BACK to postfix `name...` (EBNF `CollectingBinding = BindingIdentifier "..."`) and spread became `spread(x)` / `x.spread`.
  - superseded by #140 / 73648e9 (2026-07-29): star syntax — prefix `*name` collect marker, postfix `x*` spread marker, infix `*` multiplication; the ellipsis token was removed entirely (`...` lexes as three dots; no aliases or migration diagnostics). The final star syntax restores #139's orientation (prefix = collect, postfix = spread) with a different glyph.
  - further refined by #161 (layout-independent star disambiguation, directly-attached marker law).
- **Classification:** PARTIALLY CURRENT *(revised in lineage review; ledger batch said SUPERSEDED)*
- **Surviving part / superseded by:** Superseded by #140 (commits 09382b3, 73648e9) and refined by #161. The concrete syntax `...name` / `value...` and the deprecation-period plan are gone (the `...` spellings are now ordinary parse errors). What survives in the successor: the design principle that collecting and spreading use one marker in opposite orientations — PREFIX marker in binding positions collects, POSTFIX marker on a completed expression spreads — decided structurally by the parser; at most one collecting binding per pattern level (targeted diagnostics); and the single-target collecting assignment its commit introduced (`*items = RHS`).
- **Current evidence:** `docs/design/language-rules/syntax.md` § Star roles (line 29: "`name...`, `...name`, `spread(expr)`, and `expr.spread` are NOT KatLang syntax: there is no ellipsis token") and § The spread marker (SYN-07B); `KatLang.ebnf` lines 97-100 (`DeconstructionDefinition = CollectingBinding "=" OutputBundle | …`, `CollectingBinding = "*" BindingIdentifier`); `src/KatLang/Parser.cs:2252` ("A deconstruction binding pattern may contain at most one collecting binding (`*name`).") and :3006 ("Only one collecting binding is allowed per pattern level."); `Ast.HasMultipleCollectingCapturesAtAnyLevel` (`src/KatLang/Ast.cs:510`); tests `CollectingBindingSyntaxTests.OldEllipsisSpellings_FailThroughOrdinaryParsing_NoCollectingBinding`, `PrefixCollectingBinding_ParsesCanonicalOrientationWithExactSpans`, `TwoCollectingBindings_PerPatternLevel_AreRejected`, `TwoCollectingTargets_InDeconstruction_AreRejected`, `PostfixStar_InBindingPattern_ReportsSpreadMarkerDiagnostic`, `PrefixStar_InExpressionPosition_ReportsCollectMarkerDiagnostic`; `StarSyntaxTests`, `MarkerAttachmentTests`.
- **Probe:** `F(...items) = items` / `F(1, 2)` → parseFailure `UnexpectedToken, UndeclaredIdentifier`; `F(items...) = items` / `F(1, 2)` → parseFailure `UnexpectedToken`; `F(*items) = items` / `A = [1, 2]` / `F(A...)` → parseFailure `UnexpectedToken` ×3; `F(*a, *b) = a` / `F(1, 2)` → parseFailure `InvalidCollectingBinding`; `Forward(*items) = Target(items*)` / `Target(*items) = items` / `Forward(1, (2, 3))` → `[1, (2, 3)]`. (All five paths agree.)
- **Topics:** SYN, VAR, SUP
- **Lineage review (phase 2) corrections/addenda:**
  - [supply-spread] SUPERSEDED → PARTIALLY CURRENT. Evidence: #139's decision was to distinguish collect from spread structurally by orientation: prefix collects, postfix spreads, decided by the parser, with one collecting binding per level. It also added the single-target collecting assignment. All of this survives verbatim in #140 with only the glyph changed. Evidence: syntax.md:29 ('prefix COLLECT MARKER in binding patterns, postfix SPREAD MARKER ... collect : Supply -> ListValue and spread : Value -> Supply'); #140 body §1 restates #139's data-flow rationale; `*items = RHS` is valid (KatLang.ebnf DeconstructionDefinition = CollectingBinding '=' ...). Only the `...` glyph and the deprecation plan are superseded. The ledger's own 'what survives' text lists this, and #124 (glyph change only) is labelled PARTIALLY CURRENT under the same standard.

### #140 — Adopt prefix collect and postfix spread star syntax
- **Current Q-65 note, 2026-10-14:** Marker roles, collect/spread VALUE semantics, closed spread, chained composition and fluent lowering survive. Physical line-final star always announces multiplication, including EOF or a later declaration/closer; spread requires explicit same-line closure. *(Issue #183, 2026-10-14: refined — attachment classifies a line-final star: attached spreads and completes, detached multiplies)* The dated #161/Q-33 disambiguation discussion below is history wherever it conflicts with current SYN-11.
- **Current-rule note (Q-81, 2026-10-12):** `A*:0` no longer exists; `A*[0]` is the multiplication `A * [0]` (SYN-11), `(A*)[0]` captures and then selects, `A[0]*` selects and then spreads, and a spread is a legal selector slot, `A[B*]` (SUP-05, SEQ-05).
- **Dates:** created 2026-07-28 · closed 2026-07-29
- **Problem / question:** KatLang needed one compact, symmetric spelling for its two complementary arity operations. The predecessors were `...name` / `name...` ellipsis forms (#139) and then, for one day, a named intrinsic (`spread(x)` / `x.spread`, commit 09382b3, 2026-07-28, which also kept postfix `x...` for collecting bindings).
- **Decision / intended invariant:** Prefix `*name` is the collect marker. It is valid only in binding positions: parameter lists, nested patterns and deconstruction. Postfix `expr*` is the spread marker (`spread : Value -> Supply`). Infix `*` multiplies. The syntax changes spelling, not meaning:
  - `capture : Supply -> Value`, `collect : Supply -> ListValue`, `spread : Value -> Supply`.
  - Collecting always yields an exact list, and a singleton never collapses.
  - At most one collector per pattern level, in any position.
  - Spread opens one boundary and evaluates its operand once. Spread-produced items are not reopened.
  - `spread(collect(xs)) = xs`, which gives the forwarding rule `Forward(*items) = Target(items*)`.
  - `A*.F ≡ F(A*)` holds uniformly, including for implicit callable-parameter inference (a typo `A*.Targe` infers `Targe` exactly like `Targe(A*)`).
  - `(A*).F` differs because the parentheses capture the supply into one value.
  - `spread` is an ordinary identifier.
  - The comment of 2026-07-30 fixes chained spread as `value** ≡ (value*)*` (spread, then capture, then spread), not recursive flattening. It also adds the Value/Supply table: `A*:0` is invalid; `(A:0)*` differs from `(A*):0`.
  - As originally written, disambiguation depended on attachment plus a same-line right operand: `a*` at line end was a spread, and `a *` newline `b` multiplied.
- **Rationale:** The marker sits on the construct that performs the operation. Collect is binding syntax; spread is expression syntax. The notation is concise for a math DSL and avoids reserving `spread`. It also keeps the single dotted-call law `a.F ≡ F(a)`.
- **Examples:** `Collect(*items) = items`; `Collect((1, 2))` gives `[(1, 2)]`; `Collect((1, 2)*)` gives `[1, 2]`; `Forward(*items) = items*.Target`; `A = 1, 2` with `F = a + b`: `A*.F` gives 3, while `(A*).F` is an arity error; `[[7]]**` supplies 7.
- **Lineage:**
  - replaces syntax of #139 (prefix/postfix ellipsis, eab2468) and of the interim `spread(x)`/`x.spread` (09382b3), all as #140.
  - continues #138 (collectors build exact lists) and #103/#119 (earlier spread spellings).
  - refined by 7c1da97 / c087356 (repeated-spread capture law and Lean fixed-point guards).
  - **narrowed/superseded in its disambiguation part by #161 (SYN-07B, cb6cfda, 2026-09-11).** Star reading became layout-independent: the next significant token decides, so `A*` newline `B` now MULTIPLIES. A spread-classified star must be attached, and a detached `A *` in spread position is `InvalidSpreadMarker`.
  - related #160 (SYN-07A: comma is the only same-line separator).
  - #144 briefly reversed the exact-collection examples for written group receivers. dada1b6 (2026-09-21, collector supply-boundary law) briefly reversed them for all calls: at dada1b6, `Collect((1, 2))` became `[1, 2]`.
  - reaffirmed by #167 / 702e7d7 (C-full "values stay values", 2026-09-23): `Collect((1, 2))` is `[(1, 2)]` again.
  - #168 (50c74c1) makes `(A)*` literally `A*`, consistent with #140's `(A)*.count ≡ A*.count`.
- **Classification:** PARTIALLY CURRENT
- **Surviving part / superseded by:** All of these are current:
  - the marker roles and terminology;
  - exact collection, including `Collect(1)` = `[1]`;
  - one collector per level and collector minimum arity;
  - one-boundary spread and the forwarding round-trip;
  - `A*.F ≡ F(A*)`, including inference;
  - capture receiver `(A*).F ≡ F((A*))`;
  - `value** ≡ (value*)*`;
  - `A*:0` rejection;
  - `spread` as an ordinary name.

  HISTORICAL #161/SYN-07B supersession: Original #140 star-disambiguation rules were superseded, including same-line-only right-operand multiplication and attached line-final star as spread. Q-65 (2026-10-14) further supersedes the conflicting EOF/later-line fallback: an attached or detached physical line-final star is now incomplete multiplication; *(Issue #183, 2026-10-14: refined the same day — an attached line-final star is a completed spread again, only a detached one is incomplete multiplication)* a detached marker in an explicitly closed spread slot remains InvalidSpreadMarker. Chained spread composition and marker roles survive unchanged.
- **Current evidence:**
  - Docs: `docs/design/language-rules/syntax.md` § Star roles and § The spread marker (SYN-07B) and the marker attachment law; `sequences-lists-and-calls.md` § Spread semantics and § Collecting parameters.
  - Lean: `lean/KatLang.lean:888` `Expr.sequenceSpread` (comment at 870–887 on `A**`), `:1273` `Result.spreadItems`, `:2889` `collectSegment`.
  - Proofs: `lean/CoreArityAlgebraProofs.lean:1763–1854` `repeated_spread_cardinality` / `_zero` / `_singleton` / `_fixed_point_of_multi`; `lean/KatLangArityLaws.lean:658` `forwarding_resupplies_the_collected_items`.
  - C# tests: `StarSyntaxTests` (e.g. `LineEndingStar_BeforeAnOperandRow_IsMultiplication_NeverASpreadRow`, `LineEndingStar_BeforeADeclarationHead_ReportsMissingMultiplicationOperand`), `MarkerAttachmentTests`, `SequenceSpreadTests`.
  - Spec cases: `repeated-spread-fixed-point`, `repeated-spread-singleton-opens`, `scalar-spread-neutral`, `select-spread-vs-capture-select`, `spread-capture-count`, `collecting-minimum-arity`, `variadic-forwarding-list-spread`, `star-before-operand-row-is-multiplication`, `star-before-declaration-or-boundary-is-spread`, `spread-marker-must-be-attached`, `collect-marker-must-be-attached`, `decon-two-collecting-rejected`.
  - Tutorial "Values and Items at a Glance" table (`tutorial.md:1431ff`).
  - Minor stale wording: the Lean comment at `KatLang.lean:875–877` still says "a star with a same-line right operand is MULTIPLICATION". That is true but incomplete after SYN-07B, where a later-line operand also multiplies.
- **Probe:**
  - `Collect(*items) = items` then `Collect()`, `Collect(1)`, `Collect((1, 2))`, `Collect((1, 2)*)`, `Collect(())`, `Collect(()*)`, `Collect([])`, `Collect([]*)`, `Collect([[1, 2]]*)`, `Collect(5*)` -> `L[], L[1], L[S[1, 2]], L[1, 2], L[S[]], L[], L[L[]], L[], L[L[1, 2]], L[5]` (matches #140 exactly).
  - `A = [[1, 2], [3, 4]]`: `Collect([[7]]*)`, `Collect([[7]]**)`, `Collect(A*)`, `Collect(A**)`, `Collect((A:0)*)`, `(A*):0`, `Collect([[1, 2], 3]**)` -> `L[L[7]], L[7], L[L[1,2],L[3,4]], L[L[1,2],L[3,4]], L[1,2], L[1,2], L[L[1,2],3]`.
  - `A = 1, 2` / `F = a + b` / `A*.F` -> `3`; `(A*).F` -> ArityMismatch.
  - `A = [1,2,3]`: `(A*).count` -> `3`; `A*.count` -> ArityMismatch "count(collection) expects 1 argument, … 3".
  - `A*:0` -> parse `MisplacedSpread`.
  - `A = 2` / `B = 3` / `A*` newline `B` -> **`6`** (the #140 reading would give `2, 3`; changed by #161). `A*,` newline `B` -> `S[2, 3]`.
  - `F(A *)` -> `InvalidSpreadMarker`; `F(* items) = items` -> `InvalidCollectMarker`.
  - `spread(x) = x + 1` / `spread(4)` -> `5`.
  - `F(first, *middle, last) = middle`: `F(1, 2)`, `F(1, 2, 3)` -> `L[], L[2]`; `F(1)` -> ArityMismatch "expects at least 2 items".
  - Forwarding: `Target(*xs) = xs`, `F1(*items) = Target(items*)`, `F2(*items) = items*.Target` agree on `()` and `((1, 2), [3], ())` -> `L[S[1,2], L[3], S[]]`.
  - `3.Calc*.Target` with `Calc(v) = v, v + 1` -> `L[3, 4]`.
  - `A = 1, 2` / `Use = A*.Targe` / `Use` -> ArityMismatch "implicit parameter 'Targe' was inferred", the same inference as `Targe(A*)`.
- **Topics:** SYN, SUP, VAR, FWD, DOT, SEQ

### #141 — Equality crashes with an uncatchable StackOverflowException on deeply nested values
- **Dates:** created 2026-07-31 · closed 2026-07-31
- **Problem / question:** `==` between two in-budget values nested about 10,000 levels deep crashed the host process with an uncatchable `StackOverflowException`. Value nesting depth is unbounded; limits bound only breadth.
- **Decision / intended invariant:** Every whole-value `Result` traversal is iterative with an explicit stack. This covers equality/hash (`==`, `!=`, `contains`, `distinct`, repeated-name checks), `Normalize`, atom views, host flattening, diagnostic formatting, and `ResultToExpr`. Evaluation of a legal program therefore returns its value or a structured error and never kills the host. Equality stays total structural equality, with results, order, hash inputs and diagnostic text unchanged.
- **Rationale:** An ordinary loop builds a depth-n value in n steps. A recursive walk overflowed at about 3,700 levels on a 1 MiB stack. Lean models an unbounded evaluator, so this is host robustness, not a Lean-visible semantic change.
- **Examples:** `Wrap = [x]` / `A = Wrap.repeat(10000, 0)` / `B = Wrap.repeat(10000, 0)` / `A == B`. This is still valid current syntax: the dot-call is `repeat(Wrap, 10000, 0)`.
- **Lineage:**
  - regression-class sibling of d53eec8 ("Make combine evaluation stack-safe") and f700066 (AST stack hardening).
  - fixed by cf6a650 (iterative walks) + da96a0f (#141: also breadth-safe indexed frames).
  - generalized by the later August follow-ups documented in SEMANTIC-ALIGNMENT.md: DAG-bounded reference-identity memos for equality, hash, `Normalize` and `ResultToExpr` (`SharedValueGraphComplexityTests`, `NormalizeSharedValueGraphTests`).
  - related e29d823 (stack backstops for structural evaluation).
- **Classification:** BUG FIX / REAFFIRMED EXISTING RULE
- **Surviving part / superseded by:** The whole rule survives: iterative, O(depth) auxiliary traversal plus DAG memoization. The repository itself files it as "implementation robustness only" with no Lean update (`src/KatLang/SEMANTIC-ALIGNMENT.md:342`). The constitutional content is the RUN guarantee (no host crash) and the reaffirmed total structural equality.
- **Current evidence:**
  - `src/KatLang/SEMANTIC-ALIGNMENT.md:342` (iterative whole-value traversals) and `:344`/`:346` (DAG-bounded follow-ups).
  - `src/KatLang/Result.cs:88` `ValueComparer`; `:899` `ValueSemanticComparer`, whose explicit-stack equality is at `:990` and hash at `:1100`; `:304` iterative `Normalize`.
  - `tests/KatLang.Tests/DeepValueRobustnessTests.cs` (`DeepListEqualityIsTrue`, `DeepListEqualityIsFalseAtTheLeaf`, `DeepListInequalityOperator`, `ValueComparerHandlesDeepListChains`, `NormalizeHandlesDeepValues`, …) and `WideValueRobustnessTests.cs`.
- **Probe:**
  - The original program -> `true`.
  - With `B = Wrap.repeat(10000, 1)`: `A == B, A != B` -> `S[false, true]`.
- **Topics:** RUN, CMP, VAL

### #142 — Replace `//` line comments with `#`
- **Dates:** created 2026-08-03 · closed 2026-08-03
- **Problem / question:** Choose the line-comment marker.
- **Decision / intended invariant:**
  - `#` outside a string starts a comment to the end of the physical line, and support for `//` is removed completely.
  - The terminating newline keeps its normal row/continuation semantics, so comments never change parse decisions.
  - `#` inside a string literal is ordinary text.
- **Rationale:** A single character, familiar from scripting languages, previously unused, friendlier to calculator-style editing. There was no compatibility obligation.
- **Examples:** `# Full-line comment` / `value = 7 # Trailing comment`; `text = "# is not a comment here"`. Current equivalent: string literals are single-quoted, `t = '# not a comment'`. A double-quoted string is an `UnexpectedCharacter` error. *(Q-80, 2026-10-11: since STR-02 a double-quoted string is a decoded string literal or an interpolated string, so `text = "# is not a comment here"` is valid and its `#` is text — SYN-03, SYN-15.)* *(Constitution catch-up, 2026-11-15: since STR-03 (owner decision 2026-11-11, `65885c4f`) a double-quoted string is the front-end error `UnsupportedDoubleQuotedString` again; the single-quoted equivalent stands — SYN-15.)*
- **Lineage:**
  - replaces syntax of the original `//` comments (no predecessor issue).
  - refined later by the line-ending work (a lone `\r` ends a comment but is not a line break; `.gitattributes` eol fix, see KatLang.ebnf `Comment`).
  - related the open issue #36 (strings).
- **Classification:** CURRENT
- **Surviving part / superseded by:** Entire decision current. Lean has no lexer, so this is C#-surface-only syntax.
- **Current evidence:**
  - Grammar: `KatLang.ebnf:757` `Comment = /#[^\r\n]*/` with its commentary; `src/KatLang/Lexer.cs:201–205` (`if (c == '#')`).
  - `tests/KatLang.Tests/CommentSyntaxTests.cs`: `DoubleSlash_LexesAsTwoDivisionTokens_NeverAsAComment`, `FormerDoubleSlashComment_IsAParseErrorNotTrivia`, `HashInsideStringLiteral_IsOrdinaryContent`, `CommentRemoval_PreservesTheRowSeparatingNewline`, `DefinitionBody_StillEndsAtTheNewlineAfterATrailingComment`, `EndOfFileComment_WithoutFinalNewline_TerminatesAtEndOfSource`.
  - Spec case `comment-does-not-change-parse`; `tutorial.md:82` "### Comments"; generator agent line comments `# like this`.
  - Commit f4c1b1b.
- **Probe:**
  - `# Full-line comment` / `value = 7 # Trailing comment` / `value` -> `7`.
  - `value = 7 // Trailing comment` -> parse failure `UnexpectedToken '/'` + `UnseparatedSameLineItem`.
  - `t = '# not a comment'` / `t` -> `'# not a comment'`.
  - `t = "# x"` -> `UnexpectedCharacter '"'`.
- **Topics:** SYN
- **Lineage review (phase 2) corrections/addenda:**
  - [output-syntax-layout] lineage: lone CR 'refined later by the line-ending work' → original lexer behavior, documented and pinned later. Evidence: Classification unchanged. The v0.7.3 Lexer.cs (25a8558) increments the line only on '\n' (`if (c == '\n') { line++; col = 1; }`), so a lone CR was never a line break. The September work (LexerTests.Tokenize_LoneCarriageReturn_IsWhitespaceThatBreaksNoLine, the EBNF Comment commentary) documented and pinned it; it did not change it.

### #143 — Simplify Algorithm abstraction: make parentheses a value-capture boundary, not an Algorithm
- **Dates:** created 2026-08-10 · closed 2026-08-10. The fix commit 7075071 is dated 2026-08-09, so the issue records an already-landed design.
- **Problem / question:** `Algorithm` was overloaded. It served as the real scoped computation (`{…}`, root, properties), as parenthesized groups, as call-argument containers, and as internal wrappers. A front-end `IsParametrized` mode bit distinguished "real" scopes from transparent bundles.
- **Decision / intended invariant:**
  - The AST separates `Algorithm` (intensional: scope, parameters, properties, `open`, identity) from an injection node, `AlgorithmExpr(Algorithm)`.
  - `OutputBundle` holds ordered written slots with no ownership. `Capture(OutputBundle)` is a surviving `(…)` value boundary. `ListLiteral(OutputBundle)` is `[…]`. `Call(fn, OutputBundle)` and `DotCall(…, OutputBundle?)` carry arguments. `Algorithm.Output` is an `OutputBundle`.
  - Every brace block has algorithm identity regardless of parameter count (`{42}` is an Algorithm).
  - A capture never exposes enclosed algorithm identity: not to higher-order slots, not as an `open` target, and not for structural members.
  - `IsParametrized` is deleted. Free names in captures, lists and arguments belong to the enclosing algorithm.
  - `Result` stays value-only, with the algorithm and value channels kept separate. Higher-order probing is non-forcing, and each written argument is evaluated at most once.
  - The issue additionally proposed that `(Name)` and `((1, 2))` MAY keep Capture nodes. It gave `Apply((Increment))`, `open (M)` and `(Obj).V` as examples that must NOT recover identity or structural members through the capture.
- **Rationale:** "Algorithm is intensional; Sequence is extensional." `(…)` is structurally a sibling of `[…]`, not of `{…}`. Node type, not a mode bit, should answer "is this a scope?".
- **Examples:** `{1, 2}` -> `AlgorithmExpr`; `(1, 2)` -> `Capture(OutputBundle[1, 2])`; `F((1, 2))` -> one written slot holding a Capture; `Apply((Increment))` (proposed: identity suppressed); `open (M)` (proposed: rejected).
- **Lineage:**
  - refines the Aug 8 two-kind investigation (memory `algorithm-two-kind-model.md`) and the parenthesized-declaration rejection (delimiter model).
  - implemented as the Aug 9 OutputBundle Tracks A–D (memory `outputbundle-tracks-2026-08.md`; Track D "open(Capture) rejected").
  - **partially reversed by #168 (50c74c1, 2026-09-22, "parentheses group syntax").** Every one-slot non-spread group is now erased by `Parser.IsRedundantGrouping`, whatever the inner kind. So `Apply((Increment))` ≡ `Apply(Increment)` forwards identity, `open (M)` ≡ `open M`, `(Obj).V` ≡ `Obj.V`, and `((1, 2))` is the pair (no nested capture).
  - later extended by the API-cleanup "variant-owned Algorithm payload" (roots are `Algorithm.User`).
- **Classification:** PARTIALLY CURRENT
- **Surviving part / superseded by:**
  - Current:
    - the AST split (`Expr.AlgorithmExpr` / `Expr.Capture` / `OutputBundle` / `ListLiteral`; `Call.Args` and `DotCall.Args?` as bundles);
    - deletion of `IsParametrized`;
    - every `AlgorithmExpr` provides identity whatever its parameter count (`Call0({42})`);
    - a GENUINE capture (several slots, or a lone spread `(A*)`) suppresses identity, has no structural members, and is not an open target;
    - value-only `Result` with dual channels;
    - exactly-once argument evaluation;
    - free names bubbling to the nearest owner;
    - `()` → empty sequence, `(1)` → `1`, `({…})` → the same `AlgorithmExpr`.
  - Superseded by #168: the proposal that parentheses around a single name or a single nested group (`(Increment)`, `(M)`, `(Obj)`, `((1, 2))`) stay a Capture that blocks identity or structural lookup.
- **Current evidence:**
  - Docs: `docs/design/language-rules/sequences-lists-and-calls.md` § Output bundles, capture, and algorithm identity; `syntax.md` § Parentheses group syntax.
  - C#: `src/KatLang/Ast.cs:145` `OutputBundle`, `:911` `Expr.AlgorithmExpr`, `:927` `Expr.Capture`; `src/KatLang/Parser.cs:4743` `IsRedundantGrouping`, `:1180` `ParseScopedAlgorithm`, `:1219` `ParseParenthesizedBodyParts`.
  - Result variants in `src/KatLang/Result.cs:105–208`: Atom/Str/Bool/SequenceValue/ListValue, with no algorithm variant.
  - Lean: `lean/KatLang.lean:905` `.algorithmExpr`, `:925` `.capture : List Expr -> Expr`, `:1142` `inductive Result`; `lean/CoreTests/OutputBundle.lean`.
  - Tests: `OutputBundleSplitTests` (`SurvivingParens_ProduceCapture_WithoutAnyAlgorithm`, `RedundantParens_AreErasedWhateverTheInnerKind`, `CallArgs_AreOutputBundles`, `FreeNamesInsideCapture_BelongToTheNearestScopeOwner`), `OutputBundleOwnershipTests`, `RedundantParenthesesTransparencyTests`.
  - Spec cases (`LanguageSpecCorpus.cs:2232/2250/2266/1314`): `capture-suppresses-higher-order-identity`, now `Apply((Increment, Increment))` err, with `Apply((Increment))` ok 10 as a probe; `capture-suppresses-structural-members` (`(Obj).V` → 7, `(Obj*).V` → lexical fallback); `open-capture-target-rejected` (now `open (M, M)`, with `open (M)` ok); `parentheses-group-syntax`.
  - `IsParametrized` survives only as a historical mention in `SEMANTIC-ALIGNMENT.md`.
  - The #168 diff (50c74c1) changed exactly these spec cases from `Apply((Increment))` err / `open (M)` rejected to the current forms.
- **Probe:**
  - `Apply(f) = f(9)`, `Increment(x) = x + 1`, `Call0(g) = g()`: `Apply(Increment)`, `Apply((Increment))`, `Apply{x + 1}`, `Call0({42})` -> `S[10, 10, 10, 42]`.
  - `Apply((Increment, Increment))` -> ArityMismatch ("Increment expects 1 parameter, but was called with 0").
  - `open (M)` (first row) with `M = { public X = 5 }` then `X` -> `5`; `open (M, N)` -> parse `BadOpenForm` ("a parenthesized group is a captured value, not an algorithm").
  - `F(x) = x.count`: `F((1, 2))`, `F(((1, 2)))`, `((1, 2)) == (1, 2)` -> `S[2, 2, true]`.
- **Topics:** ALG, SEQ, VAL, CALL, MOD, DOT, RES, SYN, FORMAL
- **Lineage review (phase 2) corrections/addenda:**
  - [calls-arguments] Surviving part lists 'exactly-once argument evaluation' as current (issue decision: 'each written argument is evaluated at most once') → Exactly once for SUCCESSFUL slots only; a failing slot with an algorithm channel bound to a FIXED parameter is re-derived on each value demand (classification stays PARTIALLY CURRENT). Evidence: Probe Bad = trace(1) / 0; F(v) = v; F(Bad) -> host=[trace(1),trace(1)] on engine and generic paths; OutputLessArgumentBlameTests.FixedParameterDemand_ReDerivesTheArgument_AsBefore (tests/KatLang.Tests/OutputLessArgumentBlameTests.cs:434) pins effects ["1","1"] as a deliberate pre-existing characterization; Lean bindFlatFixedUserCall drops error? and evalCounted .param re-demands the algorithm (analysis C6/C7a); F5 memory note says this was pre-existing and deliberately unchanged.
  - [sequences-lists-values] Lineage: 'The issue additionally proposed that (Name) and ((1, 2)) MAY keep Capture nodes' → These kept layers were INHERITED: (Name) kept its block layer since #128 (73cdba2, replacing the `(empty)`-only rule) and paren-in-paren preservation since #58 (c9a43fa ShouldUnwrapParenthesizedPrimary); #143 converted them into Capture layers. Classification stays PARTIALLY CURRENT.. Evidence: git show 73cdba2 -- src/KatLang/Parser.cs adds `Expr.Resolve => false` with comment 'A parenthesized reference keeps its block layer so sequence dot-call receiver normalization can observe (items).builtin'; git show c9a43fa:src/KatLang/Parser.cs lines 1172-1182; git log -S"ShouldUnwrapParenthesizedPrimary" shows introduction in c9a43fa and removal in 50c74c1.

### #144 — Fix collecting-parameter binding for lexical dot-call receivers
- **Dates:** created 2026-08-11 · closed 2026-08-11
- **Problem / question:**
  - `Mean(*Vector) = Vector.sum / Vector.count`: `Mean(1, 2, 2.718)` gave 1.906.
  - `(1, 2, 2.718).Mean` failed, because the collector received the receiver as ONE sequence element (`Vector = [(1, 2, 2.718)]`).
- **Decision / intended invariant (at the time):**
  - A lexical dot-call receiver is one leading argument SEGMENT for arity and for fixed prefix/suffix allocation. Its count never satisfies arity, and a fixed or patterned parameter binds the value view.
  - A flat top-level collecting parameter allocated that segment consumes the segment's evaluated top-level SUPPLY, one level and lists opaque. So a written group receiver feeds its raw rows (`(1, 2, 3).Mean` averages; `().Collect` supplies zero items), while direct calls are unchanged (`Mean((1, 2, 3))` collects one item).
  - This was to be implemented once in the shared C#/Lean binder, with no dot-only binder.
- **Rationale:** Make the extension form of a variadic "work like" the direct call, without receiver-shape special cases outside the shared binder.
- **Examples:** `Mean(*Vector) = Vector.sum / Vector.count` / `(1, 2, 2.718).Mean  # 1.906`. Current equivalent: `(1, 2, 2.718)*.Mean` gives 1.906, and the unspread form is an error.
- **Lineage:**
  - continues the long receiver-binding series #89, #105 and #112 (variadic dot-call receiver drift).
  - **reversed by #167:** 68b3607 (2026-09-21, "Make dot-call pass values without implicit spreading") deleted receiver segments, `CollectingSegmentEmittedCount` / `collectingSegmentCount?` and `CallArgumentAssembly`.
  - averaging was briefly re-obtained through dada1b6 (2026-09-21 collector supply-boundary law: a lone written sequence opened at a collector, and `(1, 2, 2.718).Mean` returned 1.906 again).
  - finally removed by 702e7d7 (2026-09-23, C-full "values stay values"), whose spec probe is `(1, 2, 2.718).Mean` → err arity.
  - later reaffirmed as a cache/value-demand-transparent ordinary call by #170 (ebf623e).
- **Classification:** SUPERSEDED
- **Surviving part / superseded by:**
  - Superseded by #167 (commits 68b3607 + dada1b6 + 702e7d7, to be read together per the #167 closing comment); the current rule is "DOT-CALL PASSES A VALUE": `R.F(args) ≡ F(R, args)`, `R*.F(args) ≡ F(R*, args)`.
  - Surviving fragments that pre-date or survive #144:
    - the receiver's count never satisfies arity;
    - a fixed parameter binds the receiver whole;
    - explicit spread expands before allocation;
    - binding goes through ONE shared funnel with no dot-only binder.
  - Removed: the receiver "segment supply" read by collectors. `docs/design/language-rules/sequences-lists-and-calls.md` § The dot-call receiver says this "replaces the former 'receiver segment' rule" and lists the deleted machinery as never to be reintroduced.
- **Current evidence:**
  - Doc: `sequences-lists-and-calls.md` § The dot-call receiver: "`(1, 2, 3).Mean` and `[1, 2, 3].Mean` hand `sum` one non-numeric element".
  - Lean: `lean/KatLangArityLaws.lean:485` `dot_receiver_is_ordinary_leading_argument`, `:496` `spread_dot_receiver_is_ordinary_spread_argument`, `:509` `dot_receiver_is_one_collected_item`, `:684` `dot_call_uses_same_collector_binding_as_plain_call`; `lean/CoreTests/DotReceiverSegments.lean`, which keeps the old file name but now pins "dot-call passes a value".
  - C#: `BuildLexicalReceiverCallArgs` → `EvalResolvedCallCounted`. Tests `DotCallCollectingReceiverTests` (`GroupReceivers_AreOneValue_NeverTheirRows`, `SequenceReceiver_IsOneItem_AloneOrBesideAnother`, `EmptySequenceReceiver_IsOneVisibleItem_AndOnlyItsSpreadSuppliesNothing`) and `DotCallValueBoundaryTests`.
  - Spec case `dot-receiver-passes-a-value` (`LanguageSpecCorpus.cs:1220`, probe `(1, 2, 2.718).Mean` → "err arity"). The #144-era spec case `dot-receiver-segment-supply` no longer exists (0 occurrences).
- **Probe:**
  - `Mean(*Vector) = Vector.sum / Vector.count` / `Mean(1, 2, 3)` / `(1, 2, 3)*.Mean` -> `S[2, 2]`.
  - `(1, 2, 3).Mean` -> ArityMismatch: "while evaluating dotCall .Mean of (1, 2, 3): … sum expects each collection element to be a single numeric value; item 0 was sequence value: Bad arity".
- **Topics:** DOT, VAR, CALL, SUP, FWD

### #145 — Accessibility: Monaco IntelliSense moves NVDA focus away from the editor while typing
- **Classification:** HOST/API ONLY. katlang.org web editor (katlangweb) Monaco configuration (`suggest: {selectionMode: "never"}`), fixed and published outside this repository; no language, library or tooling change here.
- **Topics:** TOOL

### #146 — Pieejamība: uzlabot virsrakstu struktūru KatLang darbnīcā (Accessibility: improve heading structure in the KatLang workshop)
- **Classification:** HOST/API ONLY. katlang.org web UI heading hierarchy (visually hidden H2/H3 for screen readers), closed in the katlangweb repository; no change to this repository.
- **Topics:** TOOL

### #147 — Dot-call lexical fallback should reuse ordinary callable resolution
- **Dates:** created 2026-08-14 · closed 2026-08-16
- **Problem / question:** `K(a, t) = t(a)` worked with `K(7, {a+1})` (8) but the dotted spelling `K(a, t) = a.t` failed ("Property 't' was not found on `a`, and no visible algorithm ... named 't'"): the lexical dot fallback could not see an algorithm-valued PARAMETER, while ordinary call resolution could. The body also asked to verify the implicit form `K = a~.t`.
- **Decision / intended invariant:** after structural member lookup fails, `R.F(A...) ≡ F(R, A...)`, and the fallback callee is resolved by the SAME canonical callable resolution as a plain call (parameters, lexical declarations, opens, shadowing) — explicitly not by a DotCall-specific `AlgEnv` check. Structural-member precedence and existing lexical dot (`3.Add(4)`) preserved.
- **Rationale:** one callable-resolution primitive; dot syntax must not be a weaker second resolver.
- **Examples:** `K(a, t) = a.t` / `K(7, {a+1})` → 8; `3.Add(4)`. Implicit form (as finally implemented): `K = a~.t` / `K({a+1}, 7)` → 8.
- **Lineage:** the first fix 6c63486 (2026-08-14) introduced an "EXTENSION DOT" mode (`recv~.Name` / `recv.~Name` skipping structural lookup; KatLang.ebnf text in that commit); the reopening comment called it "the wrong abstraction" and asked that `a~.t` lower to the ordinary call with Grace deciding order `(a, t)`. The final commit d21b163 (2026-08-15) **removes** the extension-dot mode (memory `extension-lowering-correction.md`, `dotcall-fallback-implicit-inference.md`) and makes `~` ordering-only on the SAME structural-first DotCall; base order `a.t` → `(a, t)`, graced `a~.t` / `a.~t` → `(t, a)` (AGENTS.md bullets added in d21b163). Documented in 600fedd (SEMANTIC-ALIGNMENT Grace+DotCall laws). Later: **#152** (proposed dotless `a~t`, reverted); **#162** / 6ef913c **generalizes** structural-first to every chain level; "DOT-CALL PASSES A VALUE" (68b3607, #167 era) **reaffirms and strengthens** `R.F(args)` ≡ `F(R, args)` through the ONE call funnel (receiver-segment machinery deleted); G-24 **extends** fallback to missing members on statically known receivers; F10 (GraceEffectivenessTests) **narrows** Grace to effective occurrences (so `K(a, t) = a~.t` is now `InvalidGraceMarker`).
- **Classification:** PARTIALLY CURRENT
- **Surviving part / superseded by:** SURVIVES: the runtime law "structural first, else `F(R, args)` with ordinary callable resolution" (parameters included). SUPERSEDED/REMOVED: the extension-dot resolution mode of 6c63486 (removed in d21b163), and the reopening comment's claim that `K1 = a~.t` equals `K2(a, t) = t(a)` (parameter order `(a, t)`, lowered to a call) — current law: `a~.t` is the ordinary structural-first DotCall with inferred order `(t, a)` (d21b163; GraceDotCompositionTests), so `K = a~.t; K(7, {a+1})` now fails.
- **Current evidence:** Lean `callLexicalWithReceiverCounted` (lean/KatLang.lean:6359, fallback callee through canonical `resolveAlg`) + `prepareLexicalDotCallArgs` (4337) + `resolveDotReceiver` (4724); C# `Evaluator.DotCalls.cs:51` `BuildLexicalReceiverCallArgs`, `CallLexicalWithReceiverCounted` (DotCalls.cs:485/547) and async twin (Evaluator.Async.cs:3315); docs `ownership-and-lookup.md` § Dot-call resolution and missing members (G-24), § Grace (F10); `sequences-lists-and-calls.md` § The dot-call receiver. Tests: `DotCallHigherOrderParameterTests`, `GraceDotCompositionTests.Law_GraceCounterpart_UsesOrdinaryWeightOnTheSameBody` / `Law_EquivalenceMatrix_ImplicitAndExplicitAgree`, `DotCallFallbackInvariantTests`, `DotCallFallbackExposureTests`. Spec cases `dot-member-higher-order-parameter`, `dot-member-fallback-implicit-signature`, `grace-dot-higher-order-implicit`, `grace-dot-keeps-structural-precedence`.
- **Probe:** `K(a, t) = t(a)\nK(7, {a+1})` → 8 AGREE; `K(a, t) = a.t\nK(7, {a+1})` → 8 AGREE; `K = a~.t\nK({a+1}, 7)` → 8 AGREE; `K = a~.t\nK(7, {a+1})` (comment's order) → err NotAnAlgorithm AGREE; `3.Add(4)\nAdd(x, y) = x + y` → 7 AGREE.
- **Topics:** DOT, RES, CALL, PAR, HO, SYN, FORMAL
- **Lineage review (phase 2) corrections/addenda:**
  - [dot-call] PARTIALLY CURRENT (lineage: 6c63486 -> d21b163) → PARTIALLY CURRENT (lineage: uncommitted runtime gate -> 6c63486 -> dangling 7496f5b Call lowering with (a,t) -> d21b163 amend). Evidence: git shows 7496f5b 'Correct extension-dot semantics to use Grace lowering (fixes #147)', with parent 6c63486 and the same author timestamp as d21b163. It is not reachable from any branch; d21b163's committer date is 2026-08-16. 7496f5b's AGENTS diff describes lowering a~.t to t(a) (the reopening comment's design). The runtime gate DotCallMemberUsesParameterChannel has no pickaxe hit (never committed). An uncommitted (t,a) inference order is recorded in memory dotcall-fallback-implicit-inference.
  - [parameter-inference-grace] PARTIALLY CURRENT (lineage: 6c63486 extension mode -> d21b163 final) → PARTIALLY CURRENT (lineage adds the uncommitted package versions 0.8.160 and 0.8.161 between them). Evidence: The SEMANTIC-ALIGNMENT text added in d21b163 names 'Package 0.8.159 exposed a provisional runtime-extension model ... Package 0.8.161 removes those members' and says 0.8.160 'routed them to a lexical call'. The csproj reads 0.8.159 at 6c63486 and 0.8.162 at d21b163, and no commit carries 0.8.160 or 0.8.161. The reopening comment's lowering model with order (a, t) was actually implemented as 0.8.160 before d21b163 replaced it (memory extension-lowering-correction). Only the lineage changes, not the classification; whether 0.8.160 reached NuGet is UNCERTAIN.

### #148 — Uncharged `AlgEnv` re-entry causes exponential evaluation
- **Dates:** created 2026-08-17 · closed 2026-08-17
- **Problem / question:** `F(v) = v; x = F(x); x` ran effectively forever (exponential, ~1.6x per unit of `MaxDepth`) because the two zero-parameter `AlgEnv` parameter-thunk paths re-entered `EvalAlgOutput` without charging evaluator depth; `MaxSteps` bounded it, `MaxMaterializedItems` did not. Follow-up comment: the ordinary-dot `.string` receiver path (`F(v) = v.string`) had the same gap.
- **Decision / intended invariant:** every evaluator entry that can recursively re-enter an algorithm body is depth-charged (`TryEnterArgumentEvaluation`), in plain AND counted paths; the reproducer must fail predictably with `EvaluationDepthExceeded` with work linear in `MaxDepth`; existing dual-channel fallback and unused-argument laziness unchanged.
- **Rationale:** restores the documented depth invariant (SEMANTIC-ALIGNMENT "Depth counts simultaneously active evaluator entries that can recursively re-enter an algorithm body").
- **Examples:** `F(v) = v\nx = F(x)\nx` → `EvaluationDepthExceeded`; control `F(v) = 0\nx = F(x)\nx` → 0; `F(v) = v.string\nx = F(x)\nx` → depth error.
- **Lineage:** **reaffirms** the pre-existing depth-accounting rule; fixed by PR #149 / 72414cc; later **refined** by the sticky resource-limit retention (a retained depth failure short-circuits the dual-channel retry — comments in `EvaluationLimitsTests`), "budget cross-talk"/"budget conservation" work (memory `budget-crosstalk-always-active.md`, `budget-conservation-scoped-counters.md`), and the scoped `BudgetLevel` protocol (AGENTS "Runtime evaluator budgets are OPERATION-LOCAL").
- **Classification:** BUG FIX / REAFFIRMED EXISTING RULE
- **Surviving part / superseded by:** fully in force: bounded, linear-work failure for self-referential parameter thunks, including the `.string` receiver.
- **Current evidence:** SEMANTIC-ALIGNMENT.md:411 (Depth definition); `evaluator-and-hosting.md` § Budgets and cancellation (rejected enter mutates no counter; resource-limit failure retained on the algorithm binding); `Evaluator.BudgetScopes.cs:60` (`TryEnterArgumentEvaluation` protocol); tests `EvaluationLimitsTests.AlgEnvThunkRecursion_IsDepthBoundedAndConsumesLinearWork`, `UnusedAlgEnvThunkArgument_RemainsLazyAndCheap`, `DotStringAlgEnvRecursion_IsDepthBoundedAndConsumesLinearWork`, `EvaluationLimitsProcessTests` (:198-199), `BudgetConservationTests` (:457).
- **Probe:** `F(v) = v\nx = F(x)\nx` → engine/generic/optimized `EvaluationDepthExceeded`, engineAsync/twin `EvaluationStackExhausted` (DISAGREE between two structured resource-limit kinds; this is the documented, deliberate twin-path backstop — `docs/design/async-evaluation-2026-08.md` "a run taking the twin path may report `EvaluationStackExhausted` at a shallower recursion depth", pinned by `AsyncStackDepthTests`). Same split for `F(v) = v.string\n...`. `F(v) = 0\nx = F(x)\nx` → 0 AGREE.
- **Topics:** RUN, PROP, CALL
- **Lineage review (phase 2) corrections/addenda:**
  - [property-caching] BUG FIX / REAFFIRMED EXISTING RULE; 'fully in force … including the .string receiver' → BUG FIX / REAFFIRMED EXISTING RULE; the depth-bounded outcome survives, but the .string half of the mechanism was superseded by ebf623e: a parameter's v.string now reads the bound value instead of re-running the argument's algorithm-channel binding. Evidence: SEMANTIC-ALIGNMENT.md:595 ('so F(v) = v.string re-ran a forwarded argument … a parameter through the ordinary value-position read'); probe B = tick(), F(v) = v.string, v.string, F(B) -> S['1','1'] with one tick; the reproducer still gives EvaluationDepthExceeded (StackExhausted on the twin paths).

### #150 — Add cooperative CancellationToken support to KatLang evaluation
- **Dates:** created 2026-08-19 · closed 2026-08-19
- **Problem / question:** hosts could not cancel a running evaluation (only source processing had a token).
- **Decision / intended invariant:** `RunOptions.EvaluationCancellationToken` (separate from `SourceProcessingCancellationToken`), token held in per-run evaluation state (not `EvaluationLimits`), observed at existing budget chokepoints and at entry; cancellation THROWS `OperationCanceledException` and is NEVER an `EvalError` (unlike resource-limit errors, which may be retained on bindings while evaluation continues); works whether or not limits are enabled.
- **Rationale:** cancellation must unwind the whole run immediately, not become a retainable in-language failure.
- **Examples:** `new RunOptions { SourceProcessingCancellationToken = token, EvaluationCancellationToken = token }`.
- **Lineage:** builds on 3331581 (host-aware cancellation for module loading); precondition for **#151**; **refined** later: token lives ON the run-scoped `EvaluationBudget`, observed BEFORE any counter mutation, optimized loop observes per iteration (AGENTS budgets bullet); "CancellationToken last" parameter-order rule (`CancellationTokenParameterOrderTests`, memory `cancellationtoken-last-parameter.md`); async path delivers OCE through the returned task.
- **Classification:** HOST/API ONLY
- **Surviving part / superseded by:** fully current as a host/runtime contract; not a language-level law.
- **Current evidence:** `src/KatLang/RunOptions.cs:130` (`EvaluationCancellationToken`); `src/KatLang/Evaluation/EvaluationBudget.cs:138` (`ObserveCancellation`); `evaluator-and-hosting.md` § Budgets and cancellation; tests `EvaluationCancellationTests` (e.g. `AlreadyCancelledToken_PreventsEvaluation_AtTheEvaluatorEntryPoints`, `SourceProcessingAndEvaluationTokens_RemainIndependent`, `CancellationDeepInRecursion_UnderDefaultLimits_EscapesAndConserves`), `AsyncEvaluation/AsyncCancellationTests`.
- **Topics:** RUN, API

### #151 — Add asynchronous execution support to the KatLang evaluator
- **Dates:** created 2026-08-19 · closed 2026-08-19
- **Problem / question:** make the evaluator able to await genuinely asynchronous host operations without browser-specific scheduling, while preserving all evaluator invariants; parser stays synchronous.
- **Decision / intended invariant:** an async evaluation surface (`Evaluator.RunAsync`/`RunFlatAsync`, `KatLangEngine.RunAsync`) that preserves semantics exactly: plain/counted equivalence, budgets, cancellation, stack guarantees; no `Task.Yield`, no background offloading; host decides scheduling.
- **Rationale:** genuine suspension at arbitrary depth requires awaitable frames; semantics must not depend on the execution path.
- **Examples:** (API) `await KatLangEngine.RunAsync(source, options)`.
- **Lineage:** follows **#150**; implemented as the "sync-delegating async twin spine" (12ea745; memory `async-evaluation-twin-spine.md`); **extended** by async-only source loading (2fa449b, same day) and public `HostOperations` (async host ops route to the twin); Runtime-Async V2 investigated Sep 16–17 2026 and NOT adopted (memory `runtime-async-v2-investigation-2026-09.md`).
- **Classification:** HOST/API ONLY
- **Surviving part / superseded by:** current. Runtime contract that survives: the SYNC evaluator is the semantic oracle; a run with a sync-only cache and host-operation set executes the sync pipeline inline; otherwise `// MIRROR OF` twins run with outcome + counter equality to the generic sync strategies; the one tolerated difference is the twin-only stack backstop (`EvaluationStackExhausted` may fire earlier — both structured resource-limit errors). No Lean counterpart.
- **Current evidence:** `src/KatLang/Evaluator.Async.cs` (RunAsync :89-144, `ThrowIfAsyncStrategyPinningViolated` :1843), `src/KatLang/KatLangEngine.cs:518`; `evaluator-and-hosting.md` § Async evaluation and host operations; `docs/design/async-evaluation-2026-08.md`; tests `AsyncEvaluation/AsyncTwinDifferentialTests`, `AsyncStackDepthTests`, `AsyncSuspensionTests`, `AsyncExpressionDispatchTests`.
- **Probe:** every probe in this batch runs `engineAsync` and `twin`; all AGREE except the documented stack-backstop split noted under #148.
- **Topics:** RUN, API

### #152 — Allow a~t as shorthand for a~.t / a.~t
- **Dates:** created 2026-08-20 · closed 2026-08-20
- **Problem / question:** since `a~.t` and `a.~t` mean the same, allow the dotless `a~t` as a shorthand; issue claimed `K=a~t ≡ K(t,a)=t(a)`.
- **Decision / intended invariant:** implemented (e82c301, v0.8.171) and then REVERTED the same day (b28567f). Closing comment: rarely used, adds grammar complexity; "removing it for now".
- **Rationale:** language-surface cost not justified. (The implementation review also found the issue's equivalence claim false: `a~t` is the structural-first dot edge, not universally `t(a)` — memory `omitted-dot-grace-syntax.md`, `OmittedDot_IsNotTheDirectCall_StructuralCollisionSplitsThem`.)
- **Examples:** proposed `K = a~t` ≡ `K = a~.t` ≡ `K = a.~t`. Current valid equivalents: `K = a~.t` or `K = a.~t` (both infer `(t, a)`).
- **Lineage:** **refines** the Grace-dot composition of **#147** (d21b163); **removed** by its own revert b28567f; the implementation had repurposed the old `A~B` two-slot adjacency, which the revert restored; **#160** (SYN-07A, 2b03c0b) later made any bare same-line `A~B` an `UnseparatedSameLineItem` error.
- **Classification:** REMOVED
- **Surviving part / superseded by:** nothing survives; `a~t` is today a parse error under the #160 comma rule.
- **Current evidence:** revert b28567f (removed Parser.cs trigger, spec case `grace-dot-omitted-dot`, tests); KatLang.ebnf:486-514 documents only `a~.t` / `a.~t`; no test pins the `a~t` rejection specifically (no `a~t` occurrence in tests besides `a~.t`) — it follows from `SameLineSeparatorTests`' generic rule.
- **Probe:** `K = a~t\nK({x+1}, 7)` → parseFailure `UnseparatedSameLineItem` at 1:7 (the `t`), AGREE; `K = a.~t\nK({x+1}, 7)` → 8 AGREE.
- **Topics:** SYN, DOT, PAR

### #153 — Use Decimal128 as KatLang's core numeric type
- **Dates:** created 2026-08-20 · closed 2026-08-20
- **Problem / question:** `System.Decimal` + `double`-based transcendental functions gave ~28 digits for arithmetic but ~15–16 for `sin`/`cos`/`log`…, forcing display trimming of fake precision.
- **Decision / intended invariant:** the C# runtime numeric type becomes IEEE 754 `System.Numerics.Decimal128` end-to-end: literals parse directly into it, every Math function computes natively in it (no `double`/`decimal` stage), constants from Decimal128, the double-residue output trimming removed; no compatibility mode. IEEE values (NaN, ±Infinity, −0) to be explicitly decided, preferring IEEE behavior unless a KatLang reason says otherwise.
- **Rationale:** consistent ~34-digit precision across a calculation; no precision cliff at transcendental calls.
- **Examples:** `sin(1)`, `exp(1)`, `sqrt(2)` at 34 digits.
- **Lineage:** **supersedes** #11's double-residue normalization (10fbd40) and the Decimal-era overflow handling (#8/#13, 12e278a); **refined** by e90826f (Decimal128 semantic boundary documented/pinned: Lean `Int` vs C# Decimal128 two-tier routing), 869c1bc (zero-base negative powers → domain error; formatting), bbca492 (exact `div`), dbeb93b (KatLang-owned fixed-point number text), 9bef9cc (range canonicalization), f9e4825 (asin/acos near ±1), 7c66530 (numeric audit #6: exact-mean `avg`, near-one log/power), 38b5918 (signed-zero `min`/`max`). **#155** follows directly (Exp).
- **Classification:** CURRENT
- **Surviving part / superseded by:** core decision in force. The open IEEE question was settled as: specials (NaN, ±Infinity, −0) are ordinary values and overflow gives signed infinity, BUT division/modulo by an evaluated zero stays the Lean-modeled `divByZero` error and `0 ^ negative` is a domain error; structural equality uses `Decimal128.Equals` (NaN == NaN is true) while ordering is IEEE; quantum visible for ordinary arithmetic, transcendental results quantum-canonicalized. The `SinPi`/`CosPi` suggestion was not adopted (no use in src).
- **Current evidence:** `evaluator-and-hosting.md` § Numerics; SEMANTIC-ALIGNMENT "Core numeric semantics" row; `src/KatLang/Decimal128Numerics.cs`; `Evaluator.Expressions.cs:835` (Math natives on Decimal128); Lean core stays `Int` (lean/KatLang.lean header comments, e.g. :30); tests `Decimal128NumericsTests`, `Decimal128NearOneLogarithmTests`, `Decimal128InverseTrigTests`, `Decimal128IntegerPowerReviewTests`, `NumericSemanticLawReviewTests`, `LexerNumericLiteralConversionTests`; spec case `decimal-fraction-arithmetic`.
- **Probe:** `sin(1)` → 0.841470984807896506652502321630299; `exp(1)` → 2.718281828459045235360287471352662; `1 / 0` → err DivisionByZero; `1 mod 0` → DivisionByZero; `0 ^ -1` → IllegalInEval (zero to negative exponent); `sqrt(-1)` → NaN; `sqrt(-1) == sqrt(-1)` → true; `10 ^ 6144 * 10 ^ 6144` → Infinity; `0.5 + 0.5` → 1.0; `-0` → -0; `Math.Sin(Math.Pi)` → -1.158…e-34 (no residue trimming). All AGREE.
- **Topics:** OP, VAL, FORMAL, RUN

### #154 — Add predefined lower-camel-case aliases for all Math members
- **Dates:** created 2026-08-24 · closed 2026-08-24
- **Problem / question:** `Math.Cos(…)` / `open Math` noise in ordinary formulas; an implicit `open Math` would weaken the explicit open model.
- **Decision / intended invariant:** every canonical `Math.X` member gets ONE explicit, reviewed lower-camel-case prelude alias (`cos` for `Math.Cos`, …), an ordinary prelude binding (not new syntax, not parser sugar, not implicit open, not duplicate implementations): shadowable by local properties and parameters, prelude precedes opens (an opened provider cannot override the alias), no longer an implicit parameter when unbound, dot fallback applies (`x.cos`), usable higher-order, reserved against host-operation registration; `Math.X` stays canonical PascalCase; tooling shows aliases as built-ins, not source declarations.
- **Rationale:** concise calculation language with a uniform name-resolution model; context-independent meaning (not call-position-only).
- **Examples:** `radius = 4\narea = pi * radius ^ 2\nresult = round(sqrt(area), 4)`; `cos(0.123) ≡ Math.Cos(0.123)`; `open Math\nCos(1)`.
- **Lineage:** **reverses** #48 (2026-04-12: Math only via `Math.` prefix or `open Math`); builds on #114 (builtin aliases propagate implicit parameters); inventory **amended** by **#155** the same day (`e`/`Math.E` removed, `exp`/`Math.Exp` added); **refined** by audit #8 (name-resolution, Sep 23 2026): alias and canonical member are DISTINCT property bindings sharing ONE algorithm object (own cache entries; `P(pi, Pi)` rejects under `open Math`), Math value-demand contract follows identity; G-24 changed the missing-member outcome of `Math.cos(1)`.
- **Classification:** PARTIALLY CURRENT
- **Surviving part / superseded by:** SURVIVES: the whole alias law (one explicit alias per member, ordinary prelude binding, shadowing, prelude-before-open, dot fallback, higher-order use, host-op reservation). NOT surviving: the `Math.E`/`e` row (removed by #155); the claim "`Math.cos(1)` → unknown property" (now, per G-24, a missing member on the known receiver `Math` falls back lexically to the prelude alias: `cos(Math, 1)` → ArityMismatch); "≡" holds for value/semantics/signature but not for binding identity (distinct bindings, audit #8). Lean does not model Math (C#-only surface, SEMANTIC-ALIGNMENT.md:318 known gap).
- **Current evidence:** `src/KatLang/BuiltinRegistry.cs:353-373` (`MathMemberDescriptors` with explicit `PreludeAlias`, 21 members, `Exp` present, no `E`); `ownership-and-lookup.md` § The resolution model in one place (rule 1 prelude outermost property level; rule 2 opens after the walk), § Math members, host operations, and the prelude in every layer; tests `MathAliasRegistryTests`, `MathAliasResolutionTests`, `MathAliasEvaluationTests`, `MathAliasSemanticModelTests`, `NameResolutionAuditTests`; spec case `ownership-parameter-beats-prelude-alias`.
- **Probe:** `Math.Cos(0.123) == cos(0.123)` → true; `open Math\nCos(0)` → 1; `cos = 5\ncos` → 5; `open M\nM = {\n  public cos(x) = 99\n}\ncos(0)` → 1 (prelude alias beats open); `F(cos) = cos(2)\nF({x * 10})` → 20; `[-1, 2].map(abs)` → L[1, 2]; `0.5.cos` → 0.8775825618903727161162815826038297; `Math.cos(1)` → err ArityMismatch ("Callable `cos(radians)` expects 1 argument, but was called with 2"); `P(f, f) = f\nP(pi, pi)` → π; `open Math\nP(f, f) = f\nP(pi, Pi)` → TypeMismatch (same callable identity required). All AGREE.
- **Topics:** RES, MOD, OP, HO, DOT, TOOL
- **Lineage review (phase 2) corrections/addenda:**
  - [dot-call] PARTIALLY CURRENT (lineage: 'G-24 changed the missing-member outcome of Math.cos(1)') → PARTIALLY CURRENT (lineage: Math.cos(1) -> cos(Math,1) ArityMismatch since b3738b9; G-24 diagnostics-only). Evidence: #154's own commit b3738b9 (2026-08-24) added MathAliasResolutionTests.MathLowercaseMember_StaysInvalid, asserting Math.cos(1) -> ArityMismatch (Expected 1, Actual 2). G-24 ef0f1cf was diagnostics-only (memory g24: 'semantics untouched'). The issue's 'unknown property' was never implemented. Only the property-style Math.cos error kind changed later: UnknownName at b3738b9, MissingOutput now (pickaxe points to 04b5fc8 or 8d2fc53).
  - [builtin-surface] PARTIALLY CURRENT; lineage lacks #156 effect → PARTIALLY CURRENT; lineage adds 04b5fc8 (#156): aliases and qualified Math.X functions became direct callbacks. Evidence: Memory note math-lowercase-aliases (08-24) records Apply(Math.Cos, 0) erroring; probe today Apply(f, x) = f(x); Apply(Math.Cos, 0) -> 1 and map([-1, 2], Math.Abs) -> L[1, 2]; AGENTS 'Qualified canonical Math function references' bullet was added by 04b5fc8, which also removed the AGENTS text 'map(Abs) -> Unknown name: x — wrap in a user property'.

### #155 — Replace Math.E with Math.Exp and the exp prelude alias
- **Dates:** created 2026-08-24 · closed 2026-08-25
- **Problem / question:** Euler's number existed (`Math.E`/`e`) but no exponential function; competing `e ^ x` vs `exp(x)` styles; no exact equality guaranteed between `Decimal128.E` and `Decimal128.Exp(1)`.
- **Decision / intended invariant:** add canonical `Math.Exp(x)` (via `Decimal128.Exp`, no narrower stage) with prelude alias `exp`; remove `Math.E` and `e`; no `Exp(1) == E` contract; `exp` is an ordinary lowest-priority prelude alias (shadowable); nothing else in Math renamed/removed.
- **Rationale:** one preferred form per common calculation (`exp(x)`, `ln(x)`); KatLang had no users, so removal was safe; a constant can be added later.
- **Examples:** `exp(x)`, `exp(1)`, `Math.Exp(0)` → 1.
- **Lineage:** **amends** #154's inventory; depends on **#153** (Decimal128.Exp); dda6ba7 exposed canonical alias metadata.
- **Classification:** CURRENT
- **Surviving part / superseded by:** fully current. Nuance from audit #8: "same identity" means same algorithm object/semantics/diagnostics; `exp` and `Math.Exp` remain distinct property bindings.
- **Current evidence:** `BuiltinRegistry.cs:354` (`new("Exp", MathMemberKind.UnaryFunction, "exp")`), `Evaluator.Expressions.cs:835` (`case "Exp": … Decimal128.Exp(args[0])`); tests `MathAliasEvaluationTests` (:140-156, `Math.E` / `e` are implicit parameters now), `MathAliasResolutionTests` (:214-215), `MathAliasSemanticModelTests` (:66, no `e` in `PreludeCatalog`).
- **Probe:** `exp(1)` → 2.718281828459045235360287471352662; `Math.Exp(0)` → 1; `Math.E` → err UnresolvedImplicitParams (dot fallback promotes `E`); `e` → err UnresolvedImplicitParams. All AGREE.
- **Topics:** OP, RES

### #156 — Fix native callback argument lookup using ambient values
- **Dates:** created 2026-08-29 · closed 2026-08-29
- **Problem / question:** native-call wrappers (Math members) and host operations read their parameters from `valEnv` only, while flat callback execution (`map(abs)`) binds callback arguments in `CountedParamEnv`; so `F(x) = [1, -2].map(abs); F(5)` returned `[5, 5]` (ambient `x` captured) or `Unknown name`; host operations could receive an ambient value.
- **Decision / intended invariant:** a native wrapper's argument is its OWN bound parameter, read exactly as an `Expr.Param` read (counted callback binding first, then value environment, then algorithm binding); never a same-named ambient caller value.
- **Rationale:** a bound parameter owns its name; natives must bind like any other callable.
- **Examples:** `F(x) = [1, -2].map(abs)\nF(5)` → `[1, 2]` (was `[5, 5]`).
- **Lineage:** 04b5fc8 (2026-08-29) introduced `LookupNativeArgument` (counted-first, then value); **generalized** by f321843 (2026-09-08 "Enforce parameter shadowing across binding channels") — AGENTS "A BOUND PARAMETER OWNS ITS NAME ON EVERY CHANNEL" (`ShadowInheritedParameterEnvironments`, Lean `EvalCtx.bindParameters`) — after which `LookupNativeArgument` became exactly `ProjectCountedValue(EvalParamCounted(...))` including the algorithm tier. NOTE: commit e4d19cc (2026-09-20, first-class Booleans) says "fixes #156" in its subject; that is a mis-numbered reference (the Booleans issue is #165), not part of this issue's lineage.
- **Classification:** BUG FIX / REAFFIRMED EXISTING RULE
- **Surviving part / superseded by:** fully in force, now subsumed by the channel-shadowing law.
- **Current evidence:** `src/KatLang/Evaluator.cs:242` `LookupNativeArgument` (doc comment :225-241); AGENTS async/host bullet ("Native wrappers read arguments through `LookupNativeArgument` — the `Expr.Param` value read"); `ownership-and-lookup.md` § Parameter channels and shadowing; spec case `native-flat-callback-binding` (LanguageSpecCorpus.cs:4194, C#-only: Lean does not model `Expr.NativeCall`); `EvaluatorTests`, `Hosting/HostOperationApiTests`, `Hosting/AsyncHostOperationTests`, `MathAliasResolutionTests`.
- **Probe:** `F(x) = [1, -2].map(abs)\nF(5)` → L[1, 2] AGREE; host op `F(x) = [1, -2].map(trace)\nF(5)` → L[1, -2], host log `trace(1), trace(-2)` AGREE; async host op `traceA` same, AGREE.
- **Topics:** RES, HO, CALL, RUN

### #158 — Preserve nearer explicit-parameter ownership in nested bodies
- **Dates:** created 2026-09-09 · closed 2026-09-09
- **Problem / question:** a farther root property overrode a nearer enclosing parameter in a nested body: `v = 99; Outer(v) = { Inner = v + 1; Inner }; Outer(7)` gave 100 (CLI 0.8.179), required 8.
- **Decision / intended invariant:** parameter ownership follows the algorithm's COMPLETED signature (inferred and lifted parameters included) throughout its lexical scope; lookup walks outward by owning scope, parameters before owned properties per level, first owned binding wins; `open`/prelude precedence preserved. After signatures are complete, a property whose name matches a parameter of the same or an enclosing algorithm is a declaration error (`ParameterPropertyCollision`); a farther ancestor property vs a nested parameter, and nested vs enclosing parameter, are allowed (nearer parameter wins).
- **Rationale:** completed signatures establish an algorithm's inputs; properties must not silently repurpose or be hidden by them.
- **Examples:** above → 8; `Outer(v) = { Mid = { v = 5\n Inner = v + 1\n Inner }\n Mid }\nOuter(7)` → `ParameterPropertyCollision`.
- **Lineage:** 3f57517 implements it (SYN-03 owner walk, memory `syn03-owner-walk-ownership.md`, replacing `HasVisibleNonPreludePropertyName`); **refined** by e6390ed (static open-target ownership SYN-03/F2, `OpenTargetIsParameter`), `ParameterDetector.CompleteOwnership`, the root exception (never-called root's completed signature checked only against the root's OWN declarations), and audit #8's six-rule model (ad6d6bf). Related open issue #169 (scope lookup balance).
- **Classification:** CURRENT
- **Surviving part / superseded by:** fully current; exception for the root's phantom signature added later.
- **Current evidence:** Lean `selectOwnedDeclaration` (lean/KatLang.lean:7105), `elaborateOpenHead` (:7139), `CoreTests/NameOwnership.lean`; C# `ElaboratedScopeLookup.SelectOwnedDeclaration` (ElaboratedScopeLookup.cs:534), `ParameterPropertyCollisionValidator` (ParameterPropertyCollisionValidator.cs:24), `DiagnosticCode.ParameterPropertyCollision = 39`; `ownership-and-lookup.md` § The owner walk, § The resolution model in one place; tests `ParameterOwnershipTests`, `LookupCoherenceTests`, `OwnershipConformanceTests`, `LiftedParameterOwnershipTests`; spec cases `ownership-captured-parameter-beats-outer-property` (8), `ownership-nearer-property-beats-outer-parameter` (ParseError ParameterPropertyCollision), `ownership-same-owner-*`, `ownership-nearest-enclosing-parameter-wins`, `ownership-parameter-beats-prelude-alias`, `ownership-parameter-beats-opened-name`.
- **Probe:** issue program 1 → 8 AGREE; issue program 2 → parseFailure `ParameterPropertyCollision` at 3:9 ("…The parameter is declared at line 1, column 7."); `v = 1\nOuter(v) = v * 10\nOuter(3)` (farther property vs nested parameter, allowed) → 30 AGREE.
- **Topics:** RES, PAR, PROP, FORMAL
- **Lineage review (phase 2) corrections/addenda:**
  - [open-ownership-modules] CURRENT (lineage: replacing HasVisibleNonPreludePropertyName) → CURRENT (lineage origin 58c227b). Evidence: The defective rule dates from 58c227b (2026-04-15): `capturedParamNames.Contains(name) && !visibleNames.Contains(name)`. It was narrowed by 3bc2a29 (#73, builtins exempt, HasVisibleNonBuiltinPropertyName) and b3738b9 (#154, prelude exempt) before 3f57517 replaced it with the owner walk. It was not a regression introduced by #154.

### #159 — Resolve if by callable identity, not spelling or arity
- **Dates:** created 2026-09-09 · closed 2026-09-09
- **Problem / question:** the parser gave `if` spelling-based treatment (arity check on raw `if`) before name resolution, so direct calls, dot-calls, spread calls, higher-order use and user shadowing disagreed (e.g. user `if(x)` worked via `7.if` but not `if(7)`; a PARAMETER named `if` was intercepted).
- **Decision / intended invariant:** builtin callables are ordinary prelude bindings: resolution selects ONE identity without considering arity (no overloading by arity), then that callable's signature binds and its semantics apply. `if` is not reserved; a nearer property/parameter shadows it completely (no arity fallback to the builtin); builtin `if`'s laziness belongs only to the resolved builtin identity; spread keeps value-to-supply semantics (values built before spreading into `if` are not made lazy). Grammar keywords may still be reserved as a separate decision.
- **Rationale:** uniform lexical name resolution; Lean already modeled `if` as an ordinary `publicProp` in `preludeAlg`.
- **Examples (original):** `if(1, 10, 20)` → 10; `1.if(10, 20)`; `args = (1, 10, 20)\nif(args*)`; `Apply3(if, 1, 10, 20)`; `if(x) = x + 1\nif(7)` → 8; `if(x) = x + 1\nif(1, 2, 3)` → arity error vs user `if(x)`; `if(a, b, c) = a + b + c\nApply3(if, 1, 10, 20)` → 31. **Current equivalent** for builtin cases: Boolean conditions — `if(true, 10, 20)`, `true.if(10, 20)`, `args = (true, 10, 20)`, `Apply3(if, true, 10, 20)`.
- **Lineage:** predecessors #15 / #49 (93a036d: builtin `if` standardized to arity 3), #131 (7e1085e deferred `if` arity check for spread args), 57e9ed0/f42195d (earlier if-arity diagnostics) — this issue **removes** the parse-time spelling/arity gate (0243678, 2026-09-10, commit subject "fixes 159" without `#`; SYN-05: deletion of `Parser.ValidateIfArity`, memory `syn05-builtin-identity-not-spelling.md`; a reserved-`if` design was abandoned). **Generalized** to all builtins and the zero-argument value-demand law (AGENTS "BUILTIN CALLABLES ARE ORDINARY PRELUDE BINDINGS (SYN-05)"). Example syntax **superseded** by #165 (first-class Booleans, e4d19cc): numeric conditions are now `TypeMismatch`.
- **Classification:** CURRENT
- **Surviving part / superseded by:** identity law fully current; only the numeric-truthiness example values are obsolete (#165). Documented exception: `load` alone is still recognized by spelling (deliberate, AGENTS).
- **Current evidence:** Lean `preludeAlg` (lean/KatLang.lean:7375, `publicProp "if" (Algorithm.builtin .ifBuiltin)`), `CoreTests/NameOwnership.lean`, `CoreTests/ValueDemand.lean`; `ownership-and-lookup.md` § Builtin identity and the zero-argument value demand (SYN-05); `Evaluator.BuiltinDisplayName` / `ResolvesToBuiltinAlgorithm` (optimizer key); tests `BuiltinCallableIdentityTests` (`UserIf_ShadowsTheBuiltin_OnEverySpelling`, `UserIf_WrongArityCall_DoesNotFallBackToTheBuiltin`, `UserIf_DemandsWhatItsBodyReads_BecauseSelectionBelongsToTheBuiltinIdentity` (formerly `UserIf_IsNotLazy_BecauseLazinessBelongsToTheBuiltinIdentity`, renamed 2026-10-09), `AParameter_ShadowsThePreludeBinding`), `LazySlotZeroArgumentDemandTests`, `DiagnosticCodeTests.NoFrontEndPath_ProducesTheParseTimeArityCode`; spec cases `builtin-callable-is-an-ordinary-prelude-binding`, `if-composition-forms-agree`, `if-arity-is-uniform-across-spellings`, `if-laziness-follows-the-resolved-identity`, `if-spread-builds-values-before-branch-selection`.
- **Probe:** `if(true, 10, 20)` → 10; `true.if(10, 20)` → 10; `args = (true, 10, 20)\nif(args*)` → 10; `Apply3(f, a, b, c) = f(a, b, c)\nApply3(if, true, 10, 20)` → 10; `if(x) = x + 1` with `if(7)` / `7.if` / `if((7)*)` → 8 each; `if(x) = x + 1\nif(1, 2, 3)` → ArityMismatch "Callable `if(x)` expects 1 argument, but was called with 3"; `Apply(if, x) = if(x)\nInc(x) = x + 1\nApply(Inc, 7)` → 8; user `if(a, b, c)` via `Apply3(if, 1, 10, 20)` → 31; `if(true, 2)` / `if(true, 2, 3, 4)` → ArityMismatch against `if(condition, whenTrue, whenFalse)`; `Boom = 1 / 0\nif(true, 5, Boom)` → 5 (unselected slot not demanded); original `if(1, 10, 20)` → TypeMismatch (Boolean required). All AGREE.
- **Topics:** RES, CALL, BOOL, HO, DOT, SUP, FORMAL
- **Lineage review (phase 2) corrections/addenda:**
  - [open-ownership-modules] CURRENT → CURRENT (one issue sentence never became law). Evidence: The issue's 'Parameters and properties participate in the same lexical shadowing model: the nearest applicable binding wins' does not hold for a property against an enclosing parameter. #158 (3f57517, landed before 0243678) makes that a ParameterPropertyCollision declaration error; memory syn05-builtin-identity-not-spelling.md records the contradiction as reported and not changed.

### #160 — Require commas between same-line slots
- **Current-rule note (Q-81, 2026-10-12):** `A[1]` (and `A [1]`) is a postfix selection now, not an unseparated item; the comma rule is otherwise unchanged (SYN-07).
- **Dates:** created 2026-09-11 · closed 2026-09-12
- **Problem / question:** bare same-line adjacency created separate slots, so likely mistakes were valid programs: `2(3)` (two outputs), `A[1]` (A and `[1]`), `2m` (2 and m); and `F(1 -2)` shows whitespace can't separate slots (it is `1 - 2`).
- **Decision / intended invariant:** comma separates same-line slots; newline separates output rows where the grammar permits multiple rows; bare same-line adjacency is an error; whitespace inside expressions never creates arity structure.
- **Rationale:** prevent missing operators/separators from silently becoming valid programs while keeping the concise multi-row report style.
- **Examples:** valid multi-row report (`'time…'` newline `t_highest` newline `v(t_highest)`); invalid `2(3)`, `A[1]`, `2m`; `F(1 -2)` is one argument, write `F(1, -2)`.
- **Lineage:** **reverses** the same-line half of #125 (2026-06-18 "unify comma/adjacency": same-line adjacency as implicit expression-list separator; newline half survives) and eadf87f's adjacency docs; also ends the `A~B` two-slot reading (see #152). Implemented as SYN-07A (2b03c0b; memory `syn07a-same-line-separator.md`, retiring spec case `adjacency-is-comma`), paired with #161 / SYN-07B (layout-independent `*`); refined by 89e5c86 (parameter-pattern missing-comma diagnostics) and parser-recovery audit #9.
- **Classification:** CURRENT
- **Surviving part / superseded by:** fully current.
- **Current evidence:** `syntax.md` § Comma and same-line items (SYN-07A); `Parser.StartsNextExpressionListSlot` / `ReportUnseparatedSameLineItem` (Parser.cs:54, :896, :1413), `Parser.StartsUnseparatedPatternItem`; `DiagnosticCode.UnseparatedSameLineItem`; KatLang.ebnf (~:189-217); tests `SameLineSeparatorTests`; spec cases `same-line-slots-need-comma`, `same-line-call-arguments-need-comma`, `same-line-declaration-begins-a-line`, `same-line-slot-before-spread-needs-comma`, `same-line-parameter-patterns-need-comma`.
- **Probe:** `2(3)` → parseFailure UnseparatedSameLineItem @1:2; `A = [10, 20]\nA[1]` → UnseparatedSameLineItem @2:2; `m = 5\n2m` → UnseparatedSameLineItem @2:2; `1 2 3` → two UnseparatedSameLineItem diagnostics; `F(a, b) = a + b\nF(1 -2)` → ArityMismatch (one argument); `F(1, -2)` → -1; `1\n2\n3` → S[1, 2, 3] n=3; the issue's report program (shortened) → S['time', 3.0612…, 0.0000…] n=3. All AGREE.
- **Topics:** SYN, SEQ

### #161 — Make `*` disambiguation layout-independent and require attached marker syntax
- **Current Q-65 caveat, 2026-10-14:** Conflicting line-final/EOF/declaration-closure subrules are superseded. Current SYN-11 gives every physical line-final star multiplication priority; spread requires explicit same-line closure. *(Issue #183, 2026-10-14: refined — only a detached line-final star has multiplication priority; an attached one is a completed spread)* Attachment-after-classification, collect, Grace, precedence and spread VALUE semantics survive. Original decision and probes below remain dated history.
- **Dates:** created 2026-09-11 · closed 2026-09-11. Fix commit cb6cfda (2026-09-11 23:41 +0300). The body was edited 2026-09-11 20:08 UTC to add the marker-attachment section; the fix covers both halves.
- **Problem / question:** Postfix spread and infix multiplication share `*`. Under the previous rule, whitespace before a line-final star changed the operation:
  - `A*` newline `B` was a spread row followed by a row (`2`, `3`).
  - `A *` newline `B` was multiplication (`6`).
  - So formatting silently changed the calculation.
- **Historical decision / intended invariant (2026-09-11; conflicting line-final subrule superseded 2026-10-14):** Syntactic context decides the star's role, never whitespace or a physical newline.
  - **Multiplication:** if a valid multiplication right operand follows, on the same line or a later one, the star multiplies. Declaration heads are never operands.
  - **Spread:** if the surrounding syntax closes the expression (`)`, `]`, `}`, `,`, a declaration boundary, end of context), the star is the postfix spread marker.
  - **Attachment, checked separately:** a star classified as spread must be DIRECTLY attached (`A*`). A detached spread (`F(A *)`, `{ A * }`, a final `A *`) is a targeted syntax error.
  - The same attachment law covers the other markers: `*x` collect, `~x`/`x~` Grace.
  - Invariant: "Whitespace never changes one valid operation into another valid operation." *(Issue #183, 2026-10-14: narrowed by owner decision to one physical line — at the end of a line a star's attachment selects spread or multiplication)*
  - Spread semantics (value → supply) are explicitly unchanged, and parsing never depends on value or type.
- **Rationale:** Formatting must not silently change a calculation. Multiplication stays spacing-independent. Markers must be visibly attached so that `A *` can never be read two ways.
- **Examples:**
  ```
  A*
  B          # 24 with A = 4, B = 6 (multiplication across the newline)
  A*,
  B          # spread row, then row B
  F(A*, B)   # spread A, then next argument slot
  F(A *)     # error: detached spread marker
  Step(*x) = { x.skip(1)* }   # a spread-ending body followed by more rows must be closed
  ```
- **Lineage:**
  - **Predecessors:**
    - #124 (postfix-only unary sequence supply): #161 keeps its postfix spread and changes only the layout reading.
    - #139 (prefix/postfix ellipsis), replaced in syntax by #140.
    - #140 (prefix collect and postfix spread star syntax): #161 **reverses** #140's "Newline rule". Under #140, an attached line-final star was spread and an unattached one was multiplication. #161 **reaffirms** #140's glyph roles.
  - **Siblings:**
    - #160 (require commas between same-line slots, SYN-07A, 2b03c0b, closed 2026-09-12): #161 makes the `A*,` + newline + `B` comma idiom necessary.
    - #152 (`a~t` shorthand, withdrawn 2026-08-20): context for the Grace side of the attachment law. The memory note records that `a ~ .t` was newly rejected.
  - **Successors:**
    - #165/#166 (e4d19cc): these **refine** the classification by making a star followed by `not` a spread marker.
    - Parser recovery audit #9 (2a140c9): **refines** the rule by making the ONE declaration-starter relation `Parser.StartsDeclarationAt` shared.
    - Q-33 (2026-10-09, owner decision P0): **confirms** the line-final consequence as law in every context, definition bodies included, with no lint, warning or error; the closing forms are `A*,` for a row and `(A*)` / `{ A* }` for a definition body.
- **Classification:** CURRENT (conflicting line-final/EOF subrule superseded by Q-65, 2026-10-14; marker roles and attachment/value laws retained)
- **Surviving part / superseded by:** Marker roles, attachment after classification, collect and Grace attachment, multiplication precedence and spread VALUE semantics survive. A physical line-final star is multiplication even at EOF or before a later declaration/closer; spread requires explicit same-line closure (SYN-11). *(Issue #183, 2026-10-14: refined — only a detached line-final star; an attached one is a completed spread)* The old broader closure fallback is historical.
- **Current evidence:**
  - `docs/design/language-rules/syntax.md` § The spread marker (SYN-07B) and the marker attachment law, and § Star roles.
  - `src/KatLang/Parser.cs:4418` `IsPostfixSpreadMarkerStar` (the decision; no attachment consulted) and `Parser.cs:4479` `ParseSpreadMarkerContinuation` (the attachment check). `Parser.IsDirectlyAttached` is the shared attachment helper.
  - `KatLang.ebnf` lines ~230–255 and ~378–383.
  - Error codes: `DiagnosticCode.InvalidSpreadMarker` / `KatLangErrorCode.InvalidSpreadMarker`.
  - Tests: `StarSyntaxTests` (layout-independence and detached sections, `NotAfterAStar_IsNeverAMultiplicationOperand`) and `MarkerAttachmentTests`.
  - Spec cases: `star-before-operand-row-is-multiplication`, `star-before-declaration-or-boundary-is-spread`, `spread-marker-must-be-attached`, `grace-marker-must-be-attached`, `collect-marker-must-be-attached`.
  - Lean is untouched: it is surface syntax only, and Lean sees the derived AST.
- **Historical probes (before Q-65 revision 2026-10-14; EOF/declaration closure outcomes superseded):**
  - `A = 2\nB = 3\nA*\nB` → `6`, and `A *\nB` → `6`.
  - `A*,\nB` → `S[2, 3]`.
  - `A = 2\nA*\nB = 5` → `2` (spread before a declaration head).
  - `F(A *)` → parseFailure InvalidSpreadMarker.
  - `A = (1, 2)\nA *` → InvalidSpreadMarker.
  - `F(* xs) = xs` → InvalidCollectMarker.
  - `K = ~ a + b` → InvalidGraceMarker.
  - `Coll(A*, 3)` with `A = (1, 2)` → `L[1, 2, 3]`.
  - `Step(*x) = { x.skip(1)* }\nrepeat(Step, 1, 7, 8)` → `8`.
  - `4 *6` → `24`.
- **Topics:** SYN, SUP, VAR

### #162 — Dot access should prefer structural property over extension fallback
- **Dates:** created 2026-09-12 · closed 2026-09-12 (fix commit 6ef913c, same day; follow-up c621e81 "Preserve chained dot error spans").
- **Problem / question:** `Lib.Sub.Q` returned `99` from a visible extension `Q(x) = 99`, even though `Lib.Sub` declares `Q = 1`. The outer dot edge never saw the members of an intermediate dot result. Both Lean `resolveAlg` and C# `ResolveAlg` lifted every dot edge to a memberless wrapper, and the front end agreed because `DotCall` was classified `DefinitelyAbsent` (memory `chained-dot-property-first.md`).
- **Decision / intended invariant:** For `receiver.Q`:
  1. If the receiver has the structural property `Q`, use it.
  2. Otherwise resolve `Q` lexically and apply it as `Q(receiver)`.

  This applies at every level of a chain, including nested structures and loaded modules. Extension chaining on values is unchanged: `3.A.B` = `B(A(3))`.
- **Rationale:** A structural member must never be pre-empted by a same-named extension just because the receiver is itself a dot expression. Chain level 2 must behave like level 1.
- **Examples:**
  ```
  Lib = { public Sub = { public Q = 1 } }
  Q(x) = 99
  Lib.Sub.Q        # 1
  3.A.B            # = B(A(3)) = B(3.A)
  ```
- **Lineage:**
  - **Predecessors:**
    - #14 (dot-call on constants).
    - #147 (dot-call lexical fallback reuses ordinary callable resolution): #162 **refines** it by fixing the precedence at chain depth > 1.
  - **Successors:**
    - G-24 (ef0f1cf, 2026-09-13) **refines** the rule: a missing member on a statically known receiver falls back lexically like any receiver, and receiver knowledge serves diagnostics only.
    - K1-08 (7300596, 2026-09-14) **refines** accessibility at every level (declaration and activation).
    - #167 (68b3607) **refines** the fallback arm: the receiver is an ordinary leading argument and is never opened.
    - #168 (50c74c1) **generalizes** the navigation to grouped receivers: `(Lib.Sub).Q` ≡ `Lib.Sub.Q` and `(Obj).V` ≡ `Obj.V`. At #162 time, `(Obj).V` was still a capture receiver.
- **Classification:** CURRENT
- **Surviving part / superseded by:** The rule survives, with one narrowing of the issue's wording. "Otherwise fall back" applies when the receiver has NO declared member `Q`, or when the receiver is a value (argument-bearing edge `Lib.Sub()`, `.string`, a number).
  - A member that is declared but inaccessible from the site (local-only outside its owner's activation) is a `LocalOnlyProperty` error, never a fallback.
  - A member defined only in conditional branches is likewise a `LocalOnlyProperty` error.
  - Private (non-`public`) members stay reachable structurally.
- **Current evidence:**
  - `docs/design/language-rules/ownership-and-lookup.md` § Dot-call resolution and missing members (G-24).
  - Lean `resolveDotReceiver` (`lean/KatLang.lean:4724`).
  - C# `Evaluator.ResolveDotReceiver` (`src/KatLang/Evaluator.DotCalls.cs:368`), shared by the sync, async (`Evaluator.Async.cs:3218`) and optimizer paths.
  - Static twin `AstHelpers.ResolveStaticStructuralMemberProvider`.
  - Tests: `ChainedDotStructuralPrecedenceTests`, `ChainedDotExecutionPathTests`, `ReceiverAwareMissingMemberDiagnosticsTests`, CoreTests `DotCallSemantics.lean` `chained*`.
  - Spec cases: `dot-chain-structural-member-beats-extension`, `dot-chain-extension-fallback-composes`, `dot-chain-nested-structural-members`, `dot-chain-local-only-member-is-not-a-fallback`, `dot-chain-continuation`.
  - `tutorial.md` § Dot Calls / "Chains Read Left to Right".
- **Probe:**
  - The issue program → `1`.
  - `3.A.B, B(A(3)), B(3.A)` with `A = x + 7`, `B = x * 5` → `S[50, 50, 50]`.
  - The same `Lib` with non-`public` `Sub`/`Q` → `1` (private members navigate).
- **Topics:** DOT, RES, MOD

### #165 — Add first-class Boolean values and remove numeric truthiness
- **Dates:** created 2026-09-19 · closed 2026-09-20. The fix commit is e4d19cc (2026-09-20), whose subject mis-cites "#156" (D-2); the issue comment links e4d19cc.
- **Problem / question:** Logical and predicate results were encoded as numeric `0`/`1`, and conditions used numeric truthiness (0 false, nonzero true). The issue replaces this before the first public release, with no backward compatibility.
- **Decision / intended invariant:**
  - `true`/`false` are a distinct value kind. There is no conversion in either direction.
  - They are reserved literals: they cannot be declared or shadowed.
  - Comparisons, `and`/`or`/`xor`/`not` and `contains` produce Booleans.
  - `if`, `filter`, conditional/branch predicates and the loop continuation require a Boolean.
  - Numeric truthiness is removed, and arithmetic rejects Booleans.
  - `==`/`!=` stay TOTAL across kinds: `true == 1` is `false`.
  - Booleans are unordered: `true < false` and `true > 0` are errors.
  - Display is lowercase.
  - There is no Boolean-specific sequence normalization.
  - Lean and C# must both model Boolean as a genuine value category.
- **Rationale:** Clean long-term semantics before release. Coercions hide errors (`filter{x}` over numbers). A Boolean must not be an alias for 1/0.
- **Examples:**
  ```
  1 < 2                        # true
  true == 1                    # false
  if(1, 10, 20)                # error (was 10)
  range(-5, 5).filter{x}       # error: predicate returns a number
  ```
- **Lineage:**
  - **Predecessors:**
    - #41 (2026-04-08, "Predicate returning value should be single atomic value 0 or 1"): #165 **supersedes** that numeric predicate convention.
    - #135 (collection builtins) said "Do not add truthiness for lists…continue following KatLang's existing truth-value rules". #165 **removes** those truth-value rules entirely: the `truthValue?`/`singleAtomicTruthValue?`/`Result.atoms` truth views were deleted.
  - **Successors:**
    - #166 **builds on** it: Booleans exposed the accidental left-associative comparison results.
    - e4d19cc itself also moved prefix `not` below the comparisons (the `NotPrecedence` tier). The issue body does not state this, and #166 restates it.
    - Open #33 (guard expressions) would be a future Boolean consumer.
- **Classification:** CURRENT
- **Surviving part / superseded by:** Everything survives.
- **Current evidence:**
  - `docs/design/language-rules/evaluator-and-hosting.md` § Boolean values.
  - Lean `Expr.boolLiteral` (`lean/KatLang.lean:829`), `Result.bool` (:1152), `Result.asBool?` (:1223), `requireBooleanOperand` (:2417), `booleanRequiredMessage` (:2428).
  - C# `Result.AsBool` (`src/KatLang/Result.cs:721`), `Evaluator.RequireBooleanOperand` (`Evaluator.cs:1800`), `BooleanRequiredMessage` (`Evaluator.cs:1818`), `Pattern.LitBool`.
  - `KatLangArityLaws.lean` `asBool_*` (:2232–2253).
  - Tests: `BooleanValueTests`, `BooleanAdversarialReviewTests`, CoreTests `Numerics`/`Conditionals`/`ListValues`.
  - Spec cases: `boolean-values-and-equality`, `boolean-predicates-and-patterns`, `boolean-loop-state-transition`, `boolean-predicate-rejects-visible-empty`, `atoms-no-truthiness`.
  - `tutorial.md` § Booleans and Decisions (line 442).
- **Probe:**
  - `1 < 2, 2 >= 3, true and false, true or false, true xor false, not true` → `S[true, false, false, true, true, false]`.
  - These each give TypeMismatch: `not 1`, `1 and 2`, `true + 1`, `false * 10`, `if(1, 10, 20)`, `true < false`, `true > 0`, `range(-5, 5).filter{x}`.
  - `true == 1, false == 0, true != 1, true == true` → `S[false, false, true, true]`.
  - `contains((1, 2, 3), 2)` → `true`.
  - `true = 3` → parseFailure UnexpectedToken.
  - `F(true) = 10\nF(false) = 20\nF(1) = 30\nF(1 < 2), F(2 < 1), F(1)` → `S[10, 20, 30]`.
  - `Step(x) = x - 1\nwhile(Step, 3)` → TypeMismatch "while continuation flag … must be a Boolean value".
- **Topics:** BOOL, CMP, OP, SYN, PAT, HO, LOOP, FORMAL

### #166 — Add first-class comparison chaining with unified comparison precedence
- **Dates:** created 2026-09-20 · closed 2026-09-20. Fix commit a085f35. Later hardening: 762cb03 "Strengthen comparison-chain semantic validation" (2026-09-27), and the ExprNameRenderer receiver fix 3a649c5.
- **Problem / question:** Comparisons were ordinary left-associative binary operators, and `==`/`!=` were on a separate tier from the ordering operators. With Booleans this gave accidental results:
  - `1 == 1 == 1` was `false`.
  - `1 != 1 != 1` was `true`.
  - `1 < 2 < 3` was a type error.
- **Decision / intended invariant:**
  - **One tier:** all six comparison operators share one precedence tier. Precedence order: arithmetic/unary/power/postfix > comparisons > `not` > `and` > `xor` > `or`.
  - **Chains:** consecutive unparenthesized comparisons at one level form ONE chain. A chain has adjacent-pair semantics and is `true` iff every link holds.
  - **`!=`** compares adjacent pairs only.
  - **Parentheses** break the chain: `(a < b) == true`, `a < (b == c)`.
  - **Evaluation** is left to right and incremental, and each operand is evaluated EXACTLY ONCE. The parser must never lower a chain to `and`.
  - **Eager after `false`:** `3 < 2 < true` still reports `2 < true`.
  - **Errors stop the chain,** and later operands are not evaluated.
  - **Representation:** a dedicated chain AST node, not nested binaries, modeled in both Lean and C#.
- **Rationale:** Accidental parser behavior should not freeze into a compatibility contract before release. Exactly-once evaluation forbids naive lowering to `and`. Eagerness matches KatLang's non-short-circuit Boolean composition. *(2026-11-26: `and` and `or` short-circuit since #202 (`65b1b136`); a comparison chain stays eager, CMP-02.)* The design motto is "False does not stop a comparison chain. Errors do."
- **Examples:**
  ```
  1 < 2 < 3            # true
  1 != 2 != 1          # true (adjacent only)
  a < b <= c == d != e # four adjacent links
  3 < 2 < true         # type error on `2 < true`
  ```
- **Lineage:**
  - **Predecessors:**
    - #165 (e4d19cc) motivated the issue. That commit also introduced `not` below the comparisons; #166 **reaffirms** that `not` placement.
    - Memory `power-unary-precedence.md` (2026-08-28): `^` binds tighter than prefix `-`/`not`. #166 **refines** this further by splitting `not` out of the prefix-unary tier.
  - **Successors:** none that change the law. 762cb03 hardened validation (differential oracle, mutation-verified), and 3a649c5 made diagnostic rendering precedence-faithful.
- **Classification:** CURRENT
- **Surviving part / superseded by:** Everything survives. The AST shape is `Expr.Comparison(First, Links)` with `ComparisonLink(Op, Operand)` and `ComparisonOp` disjoint from `BinaryOp`, rather than the issue's conceptual operands/operators arrays. That is within the "exact shape may differ" allowance. Misplaced `not` (`1 + not x`, `a == not b`) is a targeted `UnexpectedToken` diagnostic, an addition consistent with the tier.
- **Current evidence:**
  - `docs/design/language-rules/syntax.md` § Operator precedence, comparison chains, and prefix `not`.
  - Lean `inductive ComparisonOp` (`lean/KatLang.lean:431`), `Expr.comparison` (:850), `applyComparison` (:3510), `evalComparisonCounted` (:6776).
  - C# `Expr.Comparison` (`src/KatLang/Ast.cs:674`), `Parser.ExtendComparisonChain` (`Parser.cs:4049`), `Evaluator.ApplyComparison` (`Evaluator.Loops.cs:507`), `EvalExpressionSpineCounted` (Comparison case), `LoopOptimizer.EvalLoopComparisonPlan`.
  - `KatLang.ebnf` `ComparisonExpr` / `NotExpr` (:398–406).
  - Tests: `ComparisonChainParserTests`, `ComparisonChainEvaluationTests`, `ComparisonChainAuditTests`, `ComparisonChainDifferentialOracleTests`, `ComparisonChainHostileReviewTests`, CoreTests `ComparisonChains.lean`.
  - Spec cases: `comparison-chains-compare-adjacent-pairs`, `comparison-chain-is-eager-after-false`, `comparison-chain-boolean-and-arithmetic-operands`, `not-binds-below-comparisons`.
  - `tutorial.md` § Chained Comparisons (line 465).
- **Probe:**
  - `1 == 1 == 1, 1 != 1 != 1, 1 < 2 < 3, 1 != 2 != 1` → `S[true, false, true, true]`.
  - `3 < 2 < true` → TypeMismatch "while evaluating `2 < true`".
  - `(1 < 2) == true, not 1 > 3` → `S[true, true]`.
  - `1 < (2 == 3)` → TypeMismatch.
  - `1 < 2 == true` → `false`.
  - `tick() < tick() < tick()` → `true` with host=[tick#1,tick#2,tick#3] (exactly once).
  - `trace(3) < trace(2) < trace(true)` → TypeMismatch after all three traces (eager past false).
  - `trace(1) < trace(true) < trace(3)` → TypeMismatch with only `trace(1),trace(true)` (an error stops the chain).
  - Aside: bare `tick < tick < tick` → `false` with one tick, because a bare zero-argument name is a cached property read (#170). It is not a chain defect.
- **Topics:** CMP, BOOL, SYN, OP, FORMAL

### #167 — Define collector supply boundaries for sequences, selection, and dot-call
- **Dates:** created 2026-09-20 · closed 2026-09-23.
  - Commits: 874625a (selection/first/last/callback value boundaries), 68b3607 (dot-call passes values) and dada1b6 (collector supply-boundary law), all 2026-09-21. Then 5d6d60b (callback binding/forwarding/repeated names) and 702e7d7 ("Replace implicit value opening with explicit supply semantics"), both 2026-09-23.
  - The closing comment says the four linked fixes "should be viewed together as design evolved between each of these 4 fixes".
- **Problem / question:** Several mechanisms must compose: selection, call supply, dot-call receiver injection, collecting parameters, sequences vs lists, spread, callbacks, reducer/loop forwarding and structural patterns. Before the issue, a lone non-spread sequence allocated to a collector lost one boundary implicitly (`Coll((1, 2))` → `[1, 2]` but `Coll([1, 2])` → `[[1, 2]]`). Collector behavior therefore depended on value kind and duplicated spread.
- **Decision / intended invariant:** This is the FINAL body, edited 2026-09-23; see the reconstructed evolution below. "Value boundaries remain boundaries unless visible syntax or an explicitly structural consumer opens them."
  1. Selection chooses a value: `first(A) ≡ A:0` and `last(A) ≡ A:(A.count-1)`, with no hidden count/provenance.
  2. A non-spread argument contributes exactly ONE value.
  3. Dot-call is ordinary receiver injection: `R.F(args) ≡ F(R, args)` and `R*.F(args) ≡ F(R*, args)`.
  4. Explicit `*` opens one boundary.
  5. Fixed parameters keep their allocated values.
  6. Collectors collect exactly their allocated items: `Coll(())` → `[()]`, `Coll((1, 2))` → `[(1, 2)]`, `Coll([1, 2])` → `[[1, 2]]`.
  7. A collecting parameter counts supplied arguments: `Cnt((10, 7))` → 1.
  8. A callback element is ONE ordinary argument: `map([(1, 2)], Add)` is an arity error, and `AddPair((x, y))` opens explicitly.
  9. Reducer and loop forwarding never open implicitly.
  10. Structural patterns are the explicit openers.

  Collection builtins may inspect their collection argument as part of their declared operation.
- **Rationale:** Remove kind-dependent and provenance-dependent collector behavior, and make `*` the single value→supply operation. Governing principle: "If one value becomes multiple supplied items, visible spread syntax or an explicitly structural consumer must explain why." The motto is "selection chooses a value, dot-call passes a value, spread opens a value".
- **Examples:**
  ```
  Coll(*xs) = xs
  Coll((1, 2))     # [(1, 2)]      Coll((1, 2)*)  # [1, 2]
  (1, 2).Coll      # [(1, 2)]
  Mean((1, 2, 3))  # one argument  Mean((1, 2, 3)*)  # 2
  map([(1, 2)], Add)      # arity error
  map([(1, 2)], AddPair)  # [3]  with AddPair((x, y)) = x + y
  ```
- **Design evolution inside the issue** (from the GitHub edit history):
  - **v-original (2026-09-20 21:35 UTC), "Selection is a value boundary":** included `A = ((), 1)` with `A:0.Coll` → `[]`, meaning a selected `()` re-counts to zero items at the collector. **Superseded:** a selected `()` passed unspread is now one argument, so `A:0.Coll` → `[()]`. Only `(A:0)*.Coll` → `[]` survives.
  - **v (2026-09-21 11:23):** added "dot-call passes a value" (`(1, 2).Coll` → `[(1, 2)]`).
  - **v (2026-09-21 18:44 through 2026-09-22):** the "collector supply-boundary law" (dada1b6). "A collector collects an allocated supply exactly, except that one lone non-spread sequence value fuses with the collector's supply boundary exactly one level" (`Coll((1, 2))` → `[1, 2]`, `Coll(())` → `[]`), implemented via slot provenance `SupplyOrigin`/`collectorSupply`. **Superseded** on 2026-09-23 by 702e7d7, the "C-full" / "values stay values" candidate (memory `values-stay-values-c-full-2026-09.md`, `collector-supply-boundary-law-2026-09.md`). `SupplyOrigin`, `collectorSupply`/`CollectorSupply`, the flat-callback row convention and reducer accumulator-slot opening were deleted. `grep` finds none of these in `src/KatLang/*.cs` or `lean/KatLang.lean`.
  - **Final (2026-09-23 09:31):** the text above. It matches current behavior.
- **Lineage:**
  - **Predecessors, dot-call receiver family:** #74, #89, #105, #112 and #144, the older receiver-segment designs.
    - #167 **reverses** #144 (2026-08-11). #144 required `(1, 2, 2.718).Mean` with `Mean(*Vector)` to average the three items through a receiver segment. Now `(1, 2, 3).Mean` hands `sum` one non-numeric element, and only `(1, 2, 3)*.Mean` averages. This was probed.
    - #74, #89, #105 and #112 are presumed superseded by the same deletion of receiver segments (`CallArgumentAssembly`, `collectingSegmentCount?`). They were NOT individually re-verified; that needs reading those issues against the `dot-receiver-passes-a-value` spec case.
  - **Predecessors, collector family:**
    - #126 (movable rest / singleton-boundary item-stream binding) and #138 (rest bindings collect exact lists): #167 **narrows**/**supersedes** their implicit singleton-boundary opening at a collector.
    - #132 (property/call boundaries return one sequence value): #167 **generalizes** that boundary to selection.
    - #134/#137 (lists, `:` indexing): #167 **reaffirms** sequence/list symmetry for call binding.
  - **Successors:**
    - #168 (50c74c1, 2026-09-22) **complements** it: parentheses do not create a boundary, and the pattern written-slot view `explicitItems?` was deleted.
    - S3 callback nested patterns and D1 pattern failure order (2026-09-22) **refine** the callback binder.
    - "Flat fixed arity errors report complete inputs" (AGENTS § Arity error payloads) **closes** the Lean/C# payload asymmetry that the C-full memory recorded.
- **Classification:** CURRENT. This is the final C-full form of the issue body; the issue's own intermediate versions are SUPERSEDED inside the issue.
- **Surviving part / superseded by:** Everything in the final body survives. The surviving law is "Values stay values — the exact collector law" plus "Selection is a value boundary", "Dot-call passes a value" and "The callback law". The v-original `selection-of-() → []` rule and the dada1b6 lone-sequence fusion law are superseded by 702e7d7.
- **Current evidence:**
  - `docs/design/language-rules/sequences-lists-and-calls.md` § Value boundaries, § Collecting parameters, § Collecting parameter lists, deconstruction, and callbacks, and § The dot-call receiver.
  - Lean `Result.spreadItems` (`lean/KatLang.lean:1273`), `sequenceValuePatternItems` (:1304), `valueCount` (:1316), `select?` (:1344), `collectSegment` (:2889), `reCountValueBoundary` (:2910), `bindCountedParameterPatternList` (:2994), `prepareLexicalDotCallArgs` (:4337), `bindParameterPatternList` (:4933), `evalUserCallbackCallCounted` (:5459).
  - Laws:
    - `KatLangArityLaws.lean`: `dot_receiver_is_ordinary_leading_argument` (:485), `collector_lone_sequence_is_one_item` (:592), `selection_origin_does_not_change_collector_binding` (:672), `first_is_select_zero` (:1158).
    - `CoreArityAlgebraProofs.lean`: `collector_lone_sequence_is_one_item` (:565), `callback_is_the_ordinary_call` (:1031).
  - C# `Evaluator.BuildLexicalReceiverCallArgs` (`Evaluator.DotCalls.cs:51`), `CollectSegment` (`Evaluator.ParameterBinding.cs:561`), `EvalResolvedCallbackCallCountedCore` (`Evaluator.PatternMatching.cs:530`).
  - Tests: `ExplicitValueOpeningTests`, `SelectionValueBoundaryTests`, `DotCallValueBoundaryTests`, `DotCallCollectingReceiverTests`, `CallbackNestedPatternBindingTests`, CoreTests `ExplicitValueOpening.lean` / `SelectionValueBoundary.lean` / `DotReceiverSegments.lean`.
  - Spec cases: `values-stay-values`, `callback-element-is-one-argument`, `dot-receiver-passes-a-value`, `selection-forms-agree`.
  - `tutorial.md` § Callbacks Receive One Element and § Collecting Parameters.
- **Probe:**
  - `Coll(), Coll(1), Coll(1, 2), Coll(()), Coll((1, 2)), Coll([]), Coll([1, 2]), Coll((1, 2)*), Coll([1, 2]*)` → `S[L[], L[1], L[1, 2], L[S[]], L[S[1, 2]], L[L[]], L[L[1, 2]], L[1, 2], L[1, 2]]`.
  - `Cnt(), Cnt((10, 7)), Cnt([10, 7]), Cnt((10, 7)*), Cnt([10, 7]*), CntV((10, 7)), CntV([10, 7])` → `S[0, 1, 1, 2, 2, 2, 2]`.
  - `Apply(Cnt, [(10, 7), 20]), Apply(Cnt, [[10, 7], 20])` → `S[L[1, 1], L[1, 1]]`.
  - `map([(1, 2)], Add)` → ArityMismatch (expected 2, got 1).
  - `map([(1, 2)], AddPair), map([[1, 2]], AddPair), AddPair((1, 2)), AddPair([1, 2])` → `S[L[3], L[3], 3, 3]`.
  - `Add((1, 2)*), Add([1, 2]*), Id((1, 2)), Id([1, 2])` → `S[3, 3, S[1, 2], L[1, 2]]`.
  - `Add((1, 2))` → ArityMismatch.
  - With `A = ((1, 2), 3)`, `B = ((), 1)`, `C = ([], 1)`: `A:0.Coll, first(A).Coll, (A:0)*.Coll, B:0.Coll, first(B).Coll, (first(B))*.Coll, C:0.Coll, (C:0)*.Coll, (1, 2).Coll, (1, 2)*.Coll, ().Coll` → `S[L[S[1, 2]], L[S[1, 2]], L[1, 2], L[S[]], L[S[]], L[], L[L[]], L[], L[S[1, 2]], L[1, 2], L[S[]]]`.
  - `Mean(1, 2, 3), Mean((1, 2, 3)*), Mean([1, 2, 3]*)` → `S[2, 2, 2]`.
  - `Mean((1, 2, 3))` → ArityMismatch ("sum expects each collection element to be a single numeric value").
  - `repeat(Step, 1, (1, 2))` with `Step(*xs) = xs.count` → `1`.
  - `reduce([1, 2], Acc, 0)` with `Acc(x, *acc) = acc` → `L[L[0]]`.
  - `(1, 2, 3).Mean` → ArityMismatch, and `(1, 2, 3)*.Mean` → `2`.
- **Topics:** VAL, SEQ, SUP, CALL, VAR, DOT, HO, FWD, LOOP, PAT, FORMAL
- **Lineage review (phase 2) corrections/addenda:**
  - [sequences-lists-values] Problem field: 'Before the issue, a lone non-spread sequence allocated to a collector lost one boundary implicitly (Coll((1, 2)) -> [1, 2])' → The final body's 'previous design' is the INTERIM dada1b6 state (2026-09-21..23) created inside this issue; before the issue plain-call collectors already collected a lone sequence as ONE item, and only dot-call receivers opened it (via #144's receiver segment collectingSegmentCount?). Classification stays CURRENT.. Evidence: At a085f35 (parent of the #167 commits) LanguageSpecCorpus.cs:1107-1109 pins G(*x) = x.sum / G(A) -> err arity, G((1, 2, 3, 4, 5)) -> err arity, G(*x) = x.count / G(A) -> 1; at dada1b6 the same probes (:1110-1112) became 15, 15, 5 ('the collector supply-boundary law'); Lean VariadicItem.collectingSegmentCount? at a085f35 is documented as an injected dot-call receiver segment view only.

### #168 — Make redundant expression parentheses semantically transparent
- **Dates:** created 2026-09-22 · closed 2026-09-22 (fix commit 50c74c1; the issue body was never edited).
- **Problem / question:** Whether a redundant parenthesized group survived as a semantic layer depended on the AST kind inside it. The parser's kind list `ShouldUnwrapParenthesizedPrimary` kept a capture around names, Grace, nested captures and spreads, but unwrapped list literals, calls and so on. As a result, `P((B))` and `P(([1, 2]))` could bind differently for `P((*xs))` even though `(B) == ([1, 2])`. The pattern binder also had a separate written-slot view of arguments (`explicitItems?` / `ExplicitSequenceValueItems`).
- **Decision / intended invariant:** "Parentheses group syntax; they do not introduce a semantic boundary."
  - For an ordinary expression, `E ≡ (E) ≡ ((E))` holds for value, emitted count, normalization, argument and patterned binding, selection, dot-call, caching, evaluation count, and every execution strategy.
  - Pattern parentheses are call-shape syntax for matching, never a runtime wrapper.
  - Normalization continues through parentheses.
- **Rationale:** Behavior must follow one language rule and not parser representation. The issue fits the boundary model "parentheses = group syntax, selection = choose a value, dot-call = pass a value, spread = open a value".
- **Examples:**
  ```
  P((*xs)) = xs
  B = [1, 2]
  P((B))  P(([1, 2]))   # must agree
  (1) ≡ ((1)) ≡ 1;  Obj.X ≡ (Obj.X);  A:0 ≡ (A:0)
  ```
- **Lineage:**
  - **Predecessors:**
    - #143 (2026-08-10, "make parentheses a value-capture boundary, not an Algorithm"; `Capture(OutputBundle)` "created by surviving parentheses"). #168 **narrows** #143: only groups whose parentheses DO something survive as `Expr.Capture`, meaning several slots or a lone spread slot `(A*)`. A one-slot non-spread group is erased whatever its kind, so `(Obj).V` (a capture receiver under #143/#162) is now `Obj.V`, and `Apply((Increment))` is `Apply(Increment)`.
    - #127/#128/#130 (sequence normalization and wrapping): #168 **reaffirms** that grouping never suspends normalization.
  - **Sibling:** #167 (same week); together they state the four-part boundary motto.
  - **Successors:**
    - F6 grouping-extent spans (`Parser.WithGroupExtent`) **refine** spans only.
    - #170 **supersedes** the caching consequence stated at #168 time. At that time `(A).count` / `count((A))` were "direct demands" of the property algorithm with no cache read (memory `parentheses-group-syntax-2026-09.md`). Since ebf623e they read the ordinary property cache. The equivalence `(A).count ≡ A.count` still holds, because both now read the cache. See D-1.
- **Classification:** CURRENT
- **Surviving part / superseded by:** The rule survives in full, including the deletion of the written-slot pattern view. Only the parenthetical caching explanation attached to it in `syntax.md` ("never a cached value-position read") is stale since #170, not the equivalence itself (D-1).
- **Current evidence:**
  - `docs/design/language-rules/syntax.md` § Parentheses group syntax (line 7).
  - C# `Parser.IsRedundantGrouping` (`src/KatLang/Parser.cs:4743`, used at :4855), and `Parser.WithGroupExtent`.
  - Lean `bindParameterPattern` opens the value via `Result.structureItems?`. `explicitItems?` is absent from `lean/KatLang.lean` and `ExplicitSequenceValueItems` is absent from `src/KatLang` (`grep`; the similarly named `EvalExplicitSequenceValueItems` is the unrelated written-row evaluator).
  - Tests: `RedundantParenthesesTransparencyTests` (the `E ≡ (E) ≡ ((E))` observer matrix; its cache rows were updated in ebf623e), `OutputBundleSplitTests`, `GroupedExpressionSpanTests`, CoreTests `CollectingParameters`/`DotCallSemantics`/`OutputBundle`, `SemanticExplorerTests.DerivedLeanPrograms_MirrorParserParenthesisNormalization`.
  - Spec cases: `parentheses-group-syntax`, `redundant-call-parens-canonical`, `list-redundant-parens-canonicalize`, `singleton-paren`, `singleton-paren-deep`.
  - Lean cannot see the parser, so correspondence is through the derived-AST corpora.
- **Probe:**
  - `P((*xs)) = xs; B = [1, 2]`: `P(B), P((B)), P(([1, 2])), P((([1, 2]))), (B) == ([1, 2])` → `S[L[1, 2], L[1, 2], L[1, 2], L[1, 2], true]`.
  - `(Obj).V, ((Obj)).V, Apply((Inc), 1), (Inc)(1), (1), ((1, 2)), (())` with `Obj = { V = 5 }`, `V(x) = 99` → `S[5, 5, 2, 2, 1, S[1, 2], S[]]`.
  - `Apply((Inc, Dec), 1)` → ArityMismatch (a capture has no algorithm identity).
  - `(A*).count, (A*).Coll, A*.Coll, (A)*.Coll` with `A = (1, 2, 3)` → `S[3, L[S[1, 2, 3]], L[1, 2, 3], L[1, 2, 3]]`.
  - `IdSeq((x)) = x`:
    - `IdSeq([5]), IdSeq(7), IdSeq(((7)))` → `S[5, 7, 7]`.
    - `IdSeq((1, 2))` and `IdSeq(((1, 2)))` both → ArityMismatch "expects 1 value, but received 2 values" (same verdict).
  - `A = tick(), tick()`: `(A), A.sum, sum((A)), (A).count, A` → `S[S[1, 2], 3, 3, 2, S[1, 2]]` with host=[tick#1,tick#2]. That is only two ticks, so the grouped builtin consumers read the cache (D-1).
- **Topics:** SYN, VAL, SEQ, PAT, CALL, DOT, PROP
- **Lineage review (phase 2) corrections/addenda:**
  - [sequences-lists-values] CURRENT (no note on caching consequence staleness in current-evidence) → CURRENT, with note: the #168-era stated consequence '(A).count / count((A)) / if(true, (A), 0) / (A).string are direct demands, never a cached value-position read' is superseded by #170 (ebf623e); the equivalence (A).count ≡ A.count survives because both now read the cache; docs/design/language-rules/syntax.md § Parentheses group syntax still carries the stale sentence.. Evidence: ebf623e --stat does not touch syntax.md; current syntax.md line 7 still says 'never a cached value-position read'; probe `A = tick()` / `(A).count, count((A)), A.count, if(true, (A), 0), A, A()` -> S[1,1,1,1,1,2] host=[tick#1,tick#2] on all five paths.

### #170 — Define zero-parameter property caching by semantic binding identity
- **Dates:** created 2026-09-27 · closed 2026-09-27 (fix commit ebf623e). The body was edited 3 times on 2026-09-27 with no change of substance: the original version already had all the final rules.
- **Problem / question:** Per-run memoization of zero-parameter properties is semantics, not an optimization. Builtin consumers (`Data.sum`, `Data.max`, `if(c, A, B)`, `.string`) bypassed the cache and re-ran the property body. So `Data`, `Data.sum`, `Data.max` and `Stats(Data)` could observe different random draws.
- **Decision / intended invariant:**
  - A zero-parameter property is evaluated once per run for each RESOLVED property binding, and repeated value access reuses it.
  - A shadowing property is a different binding with its own entry.
  - Cache identity follows semantic binding identity, not spelling or access path. Lexical, structural and opened reads of one binding share an entry.
  - How the value is consumed never affects caching. This covers builtins, user algorithms, dot calls, callbacks, collection operations, selection, loops and forwarding.
  - `A()` is an explicit fresh evaluation that neither reads, populates nor replaces the entry.
  - The rule holds in sync and async evaluation.
- **Rationale:** A zero-parameter property denotes one value during a run. A builtin must not have different property-evaluation semantics from a user algorithm. A compound result (`Stats(Data)`) must describe one consistent `Data`.
- **Examples:**
  ```
  Data = randomInt(1, 10), randomInt(1, 10), randomInt(1, 10)
  Stats(xs) = xs.sum, xs.max
  Data
  Data.sum        # consistent with Data
  Stats(Data)
  A
  A()             # fresh; A's entry untouched
  A
  ```
- **Lineage:**
  - **Predecessors:**
    - #42 (2026-04-10, per-run memoization as an optimization; reopened 2026-04-22 when memoization was removed in 4a77f87 for a cleanup, later reintroduced): #170 **generalizes** it and turns it into semantic law.
    - #110 (2026-05/06, `Math.Rand` cached vs `Math.Rand()` not): #170 **reaffirms** the `A` vs `A()` distinction.
    - #86 (loop frames: "local property cache must not leak across iterations"): this is related context for the local-only per-iteration keys.
    - 31f7c76 (2026-09-12, "Fix zero-arg property caching and exposure semantics", F3 cache-scope law) is a predecessor on binding identity.
    - Memory `zero-arg-cache-builtin-arg-gap.md` (2026-08-08) recorded the builtin-slot bypass as an open design question. The docs now say that question is closed.
  - **Supersedes:**
    - The former builtin-slot bypass ("before September 27 2026 a builtin VALUE slot and the `.string` receiver demanded the named property's algorithm directly": `evaluator-and-hosting.md` § Zero-argument property cache).
    - #168's "(A).count is a direct demand, no cache read" consequence (D-1).
- **Classification:** CURRENT
- **Surviving part / superseded by:** Everything survives, as of the latest commit.
- **Current evidence:**
  - `docs/design/language-rules/evaluator-and-hosting.md` § Zero-argument property cache (line 94).
  - Lean `structure ResolvedArgumentAlgorithm` (`lean/KatLang.lean:3116`), `resolveArgAlgExpr` (:4769), `evalZeroArgPropertyAccessCounted` (:5404), `evalDotStringReceiverValue` (:6404).
  - C# `Evaluator.ResolveArgAlgsWithSequenceSpread` (`src/KatLang/Evaluator.Calls.cs:64`), `ResolvedArgumentAlgorithm.InvokedAlgorithm`, `EvalDotStringReceiverAlgOutput` (`Evaluator.Builtins.cs:2022`), `Caching/ZeroArgPropertyResultCache.cs`.
  - Tests: `PropertyCacheConsumerTransparencyTests`, `PropertyCacheBindingIdentityReviewTests`, `ZeroArgPropertyCacheScopeTests`, `ZeroArgPropertyResultCacheTests`, CoreTests `PropertyCacheConsumers.lean` (new in ebf623e).
  - There is no `LanguageSpecCorpus` case: random/host observers are C#-only, and the cache is pinned in Lean CoreTests.
  - `tutorial.md` was updated in ebf623e.
- **Probe:**
  - `Data`/`Stats` with `--seed 7` → `S[S[1, 7, 8], 16, 8, S[16, 8]]`, consistent on all paths.
  - `A = tick()`:
    - `A, A, A(), A` → `S[1, 1, 2, 1]` (two ticks).
    - `A(), A, A` → `S[1, 2, 2]`.
  - Shadowing: `Inner = { A = tick()\n A, A }` → `A, Inner, A` = `S[1, S[2, 2], 1]`.
  - `A = tick(), tick()` consumed by `A.sum, count(A), if(true, A, 0), take(A, 1), map(A, Id), reduce(A, {x + y}, 0), Id(A), Twice(K), A:0, first(A)` with `S = tick()` and `S.string, S.string` → only 3 ticks total.
  - `open Lib` with `Lib = { public A = tick() }`: `Lib.A, A, Lib.A` → `S[1, 1, 1]` with one tick (structural and opened spellings share one entry).
- **Topics:** PROP, RES, VAL, HO, COLL, LOOP, RAND, RUN, FORMAL
- **Lineage review (phase 2) corrections/addenda:**
  - [property-caching] CURRENT; 'Everything survives' → CURRENT as normative law, with two unreconciled implemented exceptions: (a) a failed named argument bound to a FIXED parameter is re-derived uncached on every read; (b) a dotted member in callee position ((Box.V)(), Call0(Box.V)) reads the cache while Box.V() is fresh. Evidence: OutputLessArgumentBlameTests.FixedParameterDemand_ReDerivesTheArgument_AsBefore (:434) and Lean bindFlatFixedUserCall; probe p3 (B = if(tick() < 2, 1/0, 7), Fixed(x) = x, x) -> S[7, 7] with 3 ticks; probe p5 Box.V, Box.V(), (Box.V)(), Call0(Box.V) -> S[1, 2, 1, 1]; analysis C6 § ALG/DOT and § CALL/PROP.


## Model-C Phase A3 independent-review evidence corrections — 2026-10-10

Evidence: `../constitution-model-c-a3-independent-review/constitution-review.md`, `raw/witnesses-independent.json` and six-route observations. No language decision or NEED law changes; Q-45, Q-25 and X-18 remain open, Q-37 unchanged. FORMAL-07 and the final Constitution-wide audit remain separate.

Corrected current draft boundaries/caveats: VAL-10 terminal cell completion, PAR-04 newline in its example, FWD-01 one-cell `sum(values*)` cardinality, PAR-07 identity-keyed Math alias reference. Prior wording is retained verbatim in decision-lineages.md and constitution-review-log.md. Rule IDs, statuses and inventory are unchanged.


## Model-C Phase A3 independent-review dependent alias residue — 2026-10-10

RES-06 and its topic pointer retain the pre-X-47 observation as history; FWD-02's adopted identity-keyed binding indirection is unchanged. Evidence: `../constitution-model-c-a3-independent-review/forwarding-and-lifting-review.md`, original 144-witness fresh rerun, and `raw/constitution-corrections.json`. Status cells and open owner questions are unchanged.

The exact old/new pairs are retained in decision-lineages.md and constitution-review-log.md. No rule title, ID, status or NEED law changed.


## Final Constitution-wide semantic audit — 2026-10-10

Evidence: `../constitution-final-wide-audit/` (final-report.md, complete-rule-matrix.md/json, semantic-findings.md, rule-before-after.md, cross-rule-consistency.md, appendix-a-review.md, owner-decisions.md). No owner decision and no NEED law change; no C# or Lean behavior change (comments, documentation, three test renames, one LanguageSpec explanation and one new test class only). Rule IDs, statuses and the status tally (46 / 1 / 113 / 15) are unchanged. Q-45, Q-25 and X-18 remain open; Q-37 is unchanged. FORMAL-07 remains a separate audit.

277 confirmed defects, all repaired (texts, citations, examples, comments, test names and documentation; no production behavior defect):

| Finding | Severity | Rules / file | Defect |
|---|---|---|---|
| D1-F07 | EVIDENCE_GAP | SYN-11 | SYN-11's Q-33 decision and evidence-correction artifacts are absent from this checkout |
| D2-F11 | EVIDENCE_GAP | RUN-03 | RUN-03 boundary observations of twin headroom are unverified since a2700f4 but stated in present tense |
| D3-F06 | EVIDENCE_GAP | RUN-06 | RunResult.WithHostDisplayDecimals (3fe6fd7e) re-applies the host filter post-run but is untested and undocumented |
| A1-F02 | P2 | CALL-05 | CALL-05 says a family's value demand is 'dispatching against the empty supply' and that explicit Fam() reaches NoMatchingBranch; Model C makes Fam() an ArityMismatch |
| A2-F01 | P2 | PAR-05 | PAR-05 Known tension and Docs evidence state resolved X-04 / X-41 conditions as current behavior |
| A2-F02 | P2 | PAR-04 | Binding docs/manifest still state the deleted Q-15 closed-list strict-value diagnostic as current behavior |
| A4-F01 | P2 | SUP-07 | SUP-07 failure table states Apply((Inc, Inc)) is ArityMismatch; current law gives UnresolvedImplicitParams at the root and NotAnAlgorithm (no evaluation) under a closed list |
| A5-F01 | P2 | DOT-03 | Historical Ready-binder theorems presented as binder proofs for the current dot receiver |
| A5-F02 | P2 | DOT-09 | DOT-09 cites two non-existent tests with superseded outcomes and a stale 'Not pinned by any test' list |
| A6-F01 | P2 | RES-02 | RES-02 says an opened name never overrides a parameter 'lifted into the owner's completed signature' — superseded pre-Q-04 law |
| A6-F02 | P2 | RES-04 | RES-04 examples assert superseded outcomes: ambiguous X as runtime ArityMismatch, and a closed-list lone bare row as runtime ArityMismatch 'not a front-end error' |
| A6-F03 | P2 | RES-09 | RES-09 Boundary states the pre-Q-18 dotted-wrapper exception in present tense and calls DOT-09 its owner; Known tension still says Q-19 open |
| A7-F01 | P2 | PROP-04 | PROP-04 rule text says no call result is memoized, contradicting Model-C per-slot cell memoization |
| B1-F01 | P2 | SEQ-03, SEQ-01 | SEQ topic intro states superseded kind-blind opener law with a clause-family-only exception |
| B1-F04 | P2 | HO-02 | HO-02 normal example and family caveat state the superseded kind-blind sequence-pattern behavior |
| B2-F01 | P2 | COLL-02, COLL-01 | The COLL topic's Open questions still present two resolved questions as open, one with superseded current-tense behavior |
| B2-F02 | P2 | COLL-04 | COLL-04 and the COLL open question call the closure of deferral points open, but RUN-08 (Current) already closes it |
| B3-F01 | P2 | LOOP-07 | Iteration-versus-nesting law is self-overlapping and false for a one-row list-valued step |
| B4-F01 | P2 | PAT-01 | PAT-01 table states clause families are rejected as repeat/while steps (superseded by Q-23) |
| B4-F03 | P2 | PAT-02 | PAT-02 caveat states eager pre-Model-C law: arguments fully evaluated before NoMatchingBranch |
| B5-F01 | P2 | PAT-11, CALL-05 | PAT-11 claims count(Fam), if(true, Fam, 0), Fam.string and Coll(Fam*) give NoMatchingBranch; at an inferring root they are lifted (UnresolvedImplicitParams) or UnliftableClauseFamily |
| B5-F02 | P2 | PAT-11 | PAT-11 states in present tense that a single-clause Swap((a, b)) accepts a list element [1, 2] — superseded by the structural-pattern kind law |
| B6-F01 | P2 | VAR-02 | VAR-02 'three positions only' omits nested list-value patterns |
| B6-F03 | P2 | VAR-05 | VAR-05 names deleted/historical binders as the current deconstruction path and presents historical-binder theorems as current formal evidence |
| B6-F06 | P2 | VAR-06 | VAR-06 says right-hand-side effects happen once per activation; an exported source runs once per run |
| C1-F01 | P2 | VAL-02 | VAL-02 states the superseded ArityMismatch for a string inside sum |
| C1-F05 | P2 | VAL-11 | VAL-11 presents a HistoricalReadyBinding theorem as formal evidence for the current Model-C repeated-name binder |
| C2-F05 | P2 | RAND-03 | RAND-03 rule overstates the `random` result as a draw on the exact 10^-34 lattice in [start, end) |
| C3-F01 | P2 | OP-05, OP-08, OP-09 | OP-05 states that every arithmetic result is rounded once half-even, contradicting OP-08's toward-zero rule for div beyond 34 digits and the non-constitutional accuracy of fractional powers |
| C3-F02 | P2 | OP-04, OP-01, OP-02, OP-03 | Appendix A row B05 still states that unary minus on a non-scalar is ArityMismatch (superseded by Q-27) |
| C4-F01 | P2 | MOD-04 | MOD-04 eligibility omits callable aliases, which are refused as open providers |
| C4-F02 | P2 | MOD-03 | MOD-03 says a LIFTED parameter owns an open head; Q-04 says a forwarded parameter never does |
| C4-F03 | P2 | MOD-06 | MOD-06 caveat and Known tension state superseded pre-Q-18 law: Box.G in algorithm position is a 'zero-parameter dot wrapper' (ArityMismatch) |
| C4-F05 | P2 | MOD-07 | MOD-07 title still says the module is spliced 'as an ordinary brace block' — superseded by Q-31/Q-32 |
| C4-F06 | P2 | MOD-10 | MOD-10 exception 'single-clause definitions load eagerly' is false for a single clause that elaborates to a one-branch family |
| D1-F01 | P2 | SYN-06 | SYN-06 states the superseded error kind ArityMismatch for invoking a capture (Apply((Inc, Dec))); current law is NotAnAlgorithm |
| D1-F02 | P2 | SYN-13, SYN-01 | The parser reads the callee spelling `load` in its open-form check, contradicting SYN-13 ('no parse decision looks at a callee's spelling'; load is 'not a parse decision') and SYN-01 ('never from the lexer or the parser') |
| D2-F02 | P2 | RUN-01, RUN-03 | Appendix A row J01 states the superseded limit-driven strategy switch in current tense |
| D3-F01 | P2 | ALG-07 | ALG-07 states a callable alias B = A is a distinct identity; FWD-02 binding indirection makes it the target's callable |
| D3-F02 | P2 | ALG-07 | ALG-07 caveat and Known tension state pre-NEED-04 family behavior (values only, 'accepts it by value') |
| D3-F04 | P2 | RUN-07 | RUN-07 (e) static-error enumeration is incomplete and 'All other kinds are dynamic' is false (AmbiguousOpen et al.) |
| D3-F09 | P2 | ALG-05 | ALG-05 examples f03/f09 and the call-gate caveat state pre-Q-18 behavior contradicting the rule |
| D4-F01 | P2 | FORMAL-07 | FORMAL-07 presents historical Ready-binder theorems/guards as proofs and checks of the real (Model-C) model |
| D4-F02 | P2 | FORMAL-02 | FORMAL-02's statement of the Lean model domain predates callable aliases and Model C |
| DOC1-F02 | P2 | docs/design/language-rules/sequences-lists-and-calls.md | § Lists presents historical Ready-binder theorems as proving list-side receiver behavior 'over the real model' |
| DOC1-F03 | P2 | docs/design/language-rules/sequences-lists-and-calls.md | § Arity error payloads says a theorem over the deleted `bindParams` proves the current full-length rejection |
| DOC1-F06 | P2 | docs/design/language-rules/syntax.md | Clause-head confinement treats `[` in a pattern, and `F([a, b]) = a + b`, as malformed recovery |
| DOC2-F02 | P2 | docs/design/language-rules/ownership-and-lookup.md | Builtin VALUE-slot demand is described with pre-Model-C 'call-item assembly' timing ('before later argument effects', 'before the next argument is evaluated') |
| DOC3-F01 | P2 | .github/agents/katlang-generator.agent.md | Both generator files say a bare callable in an `if` branch or builtin value slot is always an arity error when selected; this predates the unified formula-lifting law |
| DOC3-F02 | P2 | experimental/prompts/katlang-generator.txt | The prompt lists `[x, *rest]` as a supported pattern in conditional algorithms, but collecting bindings are rejected in family heads |
| X1-F01 | P2 | PROP-04, FWD-02, PAR-07 | PROP-04 says a zero-accepting callable's bare name is never rewritten into a call 'in every position'; FWD-02 completes a lone row naming it into the explicit call |
| X1-F02 | P2 | CALL-01, DOT-09, SYN-09 | CALL-01 Boundary states the pre-Q-18 rule that `(a.b)(1)` calls the dot RESULT |
| X2-F01 | P2 | HO-04, LOOP-01 | HO-04 lists a loop's initial state among the builtin VALUE slots that are 'demanded once', contradicting LOOP-01 (the loop never demands its initial slots) |
| X3-F01 | P2 | RES-04, PAR-03 | RES-04 (and ownership-and-lookup.md rule 3) say a promoted name lives in the INNERMOST list-less algorithm; PAR-03 and the implementation claim it top-down by the OUTERMOST inferring level whose own rows use it |
| X3-F02 | P2 | PAR-07, FWD-02 | PAR-07 says a lone row naming a ZERO-parameter callable is a callable alias or bare forwarding; FWD-02 makes it an ordinary property (no alias), with observably different evaluation counts |
| X4-F01 | P2 | OP-09, OP-03, COLL-09, OP-11 | OP-09 claims `^`, `pow` and `Math.Pow` can never disagree, but OP-03 and COLL-09 give them different operand demand orders and different error kinds |
| X4-F02 | P2 | VAL-11, PAT-09, PAT-10, NEED-04 | VAL-11's Permutation caveat still states, in the present tense, that permutation preserves the error kind, contrary to the Q-28 owner follow-up |
| X5-F01 | P2 | HO-04, LOOP-01 | HO-04 says a loop's initial state is a value slot the builtin demands once; LOOP-01 and Model C say the loop never demands it |
| X6-F01 | P2 | RES-07, PAR-03, MOD-06 | RES-07(a) and PAR-03 say every brace block captures through the owner walk; an inline open target (MOD-06) does not, and RES-07's 'inline-open' caveat never says so |
| X8-F01 | P2 | FORMAL-05, VAL-08 | FORMAL-05 and VAL-08(c) define 'emitted count' as the items an expression contributes where written, contradicting VAL-04/VAL-07 for () |
| A1-F01 | P3 | CALL-06 | Test name ResourceLimitFailureOfASlot_IsTerminalAtAssembly misstates Model-C first-demand terminality |
| A1-F03 | P3 | CALL-05 | CALL-05 examples predate the unified formula-lifting law and Model-C blame: root `if(true, Inc, 0)`, `count(Fam)`, `if(true, Fam, 0)`, `Fam.string` are UnresolvedImplicitParams, not the claimed kinds |
| A1-F04 | P3 | CALL-01 | CALL-01 evidence loci stale; NoMatchingBranch raise site and callee resolver misattributed |
| A1-F05 | P3 | CALL-03 | CALL-03 evidence cites deleted EvalInitialLoopStateSlots / evalInitialLoopStateSlots as current, and stale line loci |
| A1-F06 | P3 | CALL-05 | CALL-05 evidence line loci stale throughout |
| A1-F07 | P3 | CALL-03, CALL-06 | Current examples use the removed CLI flag `--seed N` |
| A1-F08 | P3 | CALL-06 | CALL-06 cites a tutorial section title that no longer exists |
| A1-F09 | P3 | CALL-04 | CALL-04 ArityDifferential Lean-anchor locus stale |
| A1-F10 | P3 | CALL-02 | Cited CallArgumentSingleForcingTests class header still describes pre-Model-C forcing at preparation/binding and 'AlgEnv probing' |
| A2-F03 | P3 | PAR-04 | Test class ClosedListStrictValueDiagnosticTests is named after the deleted diagnostic |
| A2-F04 | P3 | PAR-01 | PAR-01 'ALL inherited tiers' enumeration omits the Model-C need (cell) tier |
| A2-F05 | P3 | PAR-01 | PAR-01 Lean evidence loci are stale |
| A2-F06 | P3 | PAR-03 | PAR-03 C# and Lean evidence loci are stale |
| A2-F07 | P3 | PAR-05 | PAR-05 evidence loci stale and the quoted Lean comment no longer exists |
| A2-F08 | P3 | PAR-06 | PAR-06 tutorial-contract test loci stale |
| A3-F01 | P3 | PAR-07 | PAR-07 example prints a non-executable CLI option `--seed 7` |
| A3-F02 | P3 | PAR-07 | PAR-07 evidence names a renamed symbol, a stale locus and a non-existent docs heading as current |
| A3-F03 | P3 | PAR-07 | PAR-07 misdescribes CoreTests/RepeatedNameConstraints §15-17 as evaluating the superseded `Some(x) = P(x, x)` tree |
| A3-F04 | P3 | PAR-07 | PAR-07 summary states superseded `.string` behavior in present tense and narrows the still-neutral position list |
| A3-F05 | P3 | FWD-02 | FWD-02 Docs evidence cites a non-existent ownership-and-lookup.md heading |
| A4-F02 | P3 | SUP-03 | SUP-03's exclusive list of deeper openers omits two SEQ-03 openers (the `:` target view and a collection builtin's collection view) |
| A4-F03 | P3 | SUP-02 | SUP-02 evidence/tension claims are stale: the nested reclassification IS pinned (six routes), and CALL's note no longer says 'either way' |
| A4-F04 | P3 | SUP-01 | SUP-01 cites stale/out-of-range file:line loci as current evidence |
| A4-F05 | P3 | SUP-02 | SUP-02 cites stale/out-of-range loci (Evaluator.Async.cs lines beyond EOF; Lean lines off by 300-700) |
| A4-F06 | P3 | SUP-03 | SUP-03 presents the historical Ready-binder theorem collector_collects_spread_items_exactly as Lean evidence without qualification |
| A4-F07 | P3 | SUP-04 | SUP-04 cites stale loci (Async twin beyond EOF; Lean spread loop off by ~600 lines) |
| A4-F08 | P3 | SUP-05 | SUP-05 cites drifted Parser/Lean loci |
| A4-F09 | P3 | SUP-06 | SUP-06 cites stale/out-of-range loci for the capture path |
| A4-F10 | P3 | SUP-07 | SUP-07 cites a renamed test and stale loci |
| A4-F11 | P3 | FWD-01 | FWD-01 cites drifted test/guard/tutorial loci |
| A5-F03 | P3 | DOT-09 | DOT-09 still quotes superseded comments and docs in present tense |
| A5-F04 | P3 | DOT-09 | LanguageSpec case repeated-forwarded-dot-wrapper-keeps-identity explains with the retired wrapper identity |
| A5-F05 | P3 | DOT-02 | DOT-02 Known tension reports a docstring defect that no longer exists |
| A5-F06 | P3 | DOT-05, DOT-07 | The inferred-parameter order of the fluent receiver a*.t is unstated (PV-37) |
| A5-F07 | P3 | DOT-06 | The `Obj~.V` boundary example is labelled '(structural member)' but fails on the receiver |
| A5-F08 | P3 | DOT-01, DOT-02 | The `Mk(3).V` example omits Mk's definition and fails with the obvious one |
| A5-F09 | P3 | DOT-08 | Lean inline comment on the `.string` arm still describes pre-Model-C eager assembly |
| A5-F10 | P3 | DOT-09 | Appendix A row A19 still calls a call on an argument-bearing dot result DOT-09's wrapper call |
| A5-F11 | P3 | DOT-01 | DOT-01 stale file:line loci presented as current evidence |
| A5-F12 | P3 | DOT-02 | DOT-02 stale loci |
| A5-F13 | P3 | DOT-03 | DOT-03 stale loci |
| A5-F14 | P3 | DOT-04 | DOT-04 stale loci |
| A5-F15 | P3 | DOT-05 | DOT-05 stale loci |
| A5-F16 | P3 | DOT-06 | DOT-06 stale locus |
| A5-F17 | P3 | DOT-07 | DOT-07 stale loci |
| A5-F18 | P3 | DOT-08 | DOT-08 stale loci (residue item 1) |
| A5-F19 | P3 | DOT-09 | DOT-09 stale loci |
| A6-F04 | P3 | RES-03 | RES-03 cites Lean guards that no longer exist and quotes the pre-Q-29 run-time message for r03e |
| A6-F05 | P3 | RES-08 | RES-08 cites deleted PropertyExposureResolver.ProcessUserAlgorithm and a renamed Lean guard; r08g quoted as run-time error |
| A6-F06 | P3 | RES-07 | RES-07 Boundary heading 'Direct calls only' restates the pre-Q-18 restriction |
| A6-F07 | P3 | RES-10 | RES-10 rule text points to a resolved MOD-01 open question (PV-25) |
| A6-F08 | P3 | RES-01 | RES-01 look-alike attributes `Outer(v) = Inner` to 'CALL: implicit argument lifting' instead of FWD-02 bare forwarding |
| A6-F09 | P3 | RES-01, RES-02, RES-03, RES-04, RES-05, RES-06, RES-07, RES-08, RES-09, RES-10 | Stale file:line loci presented as current evidence across RES-01..RES-10 |
| A7-F02 | P3 | PROP-09 | PROP-09 cites a Lean guard for no-rollback that no longer exercises any failure; Q-37 not named |
| A7-F03 | P3 | PROP-06, PROP-05 | PROP-06 pinning claim stale after Q-18; misused spec ID; stale pre-Model-C Lean comment |
| A7-F04 | P3 | PROP-07 | PROP-07 says module-splice identity is unpinned and leads with superseded tension (a) |
| A7-F05 | P3 | PROP-05 | PROP-05 docs pointer and PROP topic note call syntax.md stale after it was fixed |
| A7-F06 | P3 | PROP-08 | PROP-08 Boundary list is malformed: the dead-reference paragraph lost its bullet marker |
| A7-F07 | P3 | PROP-06 | PROP-06 presents the deconstruction-target a() behavior as settled without citing open Q-38 |
| A7-F08 | P3 | PROP-01 | PROP-01 cites stale file:line loci as current evidence |
| A7-F09 | P3 | PROP-02 | PROP-02 cites stale file:line loci as current evidence |
| A7-F10 | P3 | PROP-04 | PROP-04 cites stale loci and a stale test count |
| A7-F11 | P3 | PROP-05 | PROP-05 cites stale test and doc loci |
| A7-F12 | P3 | PROP-06 | PROP-06 cites stale loci |
| A7-F13 | P3 | PROP-07 | PROP-07 cites stale loci |
| A7-F14 | P3 | PROP-08 | PROP-08 cites stale loci |
| A7-F15 | P3 | PROP-09 | PROP-09 cites stale loci |
| B1-F02 | P3 | SEQ-03 | SEQ open question lists the deleted sequenceValuePatternItems as one of the identical one-level views |
| B1-F03 | P3 | SEQ-03 | SEQ-03 cites deleted C# symbols as current evidence |
| B1-F05 | P3 | HO-02 | HO-02 evidence and ALGHO notes cite deleted/renamed symbols, an unqualified historical guard, a moot open question and stale wording |
| B1-F06 | P3 | HO-05 | HO-05 Known tension presents host-stack depth disparity as live although Q-09a resolved it |
| B1-F07 | P3 | HO-04 | HO-04 enumerates the value slots but omits repeat's count |
| B1-F08 | P3 | SEQ-01, SEQ-02, SEQ-04, SEQ-05, HO-01, HO-02, HO-03, HO-05 | Unstamped file:line loci are stale across the batch |
| B2-F03 | P3 | COLL-06 | COLL-06 calls the sort relation 'the Decimal128 total order', which suggests IEEE 754 totalOrder, a different relation |
| B2-F04 | P3 | COLL-05, COLL-07, COLL-03, COLL-06 | Stale documentation that the COLL section records is still present at HEAD, and its recorded loci have drifted |
| B2-F05 | P3 | COLL-06, COLL-09 | The rules-only edition keeps 'below' references to topic lists that it does not contain |
| B2-F06 | P3 | COLL-01, COLL-02, COLL-03, COLL-04, COLL-05, COLL-06, COLL-07, COLL-08, COLL-09, COLL-10 | Evidence loci in every COLL rule are stale and are presented as current evidence (not stamped 'verified at') |
| B2-F07 | P3 | COLL-10, COLL-04 | The atoms result-kind laws are proved over a law-local mirror, not over the production `.atomsBuiltin` arm |
| B3-F02 | P3 | LOOP-02 | LOOP-02 Rule cites retired ALG-08 as the owner of lexical closure |
| B3-F03 | P3 | LOOP-02 | Stale current-tense 'Value-tier shadowing' tension about deleted Lean runStepSlots |
| B3-F04 | P3 | LOOP-05 | 'The count is demanded BEFORE the initial state' omits the spread-first exception |
| B3-F05 | P3 | LOOP-05 | LOOP-05 C#/Lean evidence describes a relocated, pre-Model-C count path and understates test coverage |
| B3-F06 | P3 | LOOP-06 | LOOP-06 evidence names a nonexistent async twin and out-of-range loci as the current while implementation |
| B3-F07 | P3 | LOOP-01 | LOOP-01 evidence loci presented as current are stale |
| B3-F08 | P3 | LOOP-01, LOOP-06, LOOP-08 | LOOP topic notes state superseded arity wording and a stale implementation map |
| B3-F09 | P3 | LOOP-01, LOOP-02, LOOP-03, LOOP-05, LOOP-06, LOOP-07, LOOP-08 | Appendix A row I03 cites nonexistent WhileLoopCounted / RepeatLoopCounted |
| B4-F02 | P3 | PAT-01 | PAT-01 Known tension lists the callable channel and strictness as still differing between ordinary and family |
| B4-F04 | P3 | PAT-02 | PAT-02 evidence labels EvalConditionalCallCountedCore as deleted; it exists as a delegating wrapper |
| B4-F05 | P3 | PAT-03 | PAT-03 evidence cites a nonexistent C# MatchCallPattern and the off-path Lean matchCallPattern as current |
| B4-F06 | P3 | PAT-04 | PAT-04 'No hidden argument' example gives the wrong outcome for the lone row `F(0) = A` |
| B4-F07 | P3 | PAT-04 | PAT-04 evidence cites a renamed C# diagnostic factory and an outdated docs claim |
| B4-F08 | P3 | PAT-06 | PAT-06 evidence cites deleted C# symbols and off-path Lean matchers as the current kind-law implementation |
| B4-F09 | P3 | PAT-06 | PAT-06 lists four HistoricalReadyBinding theorems as current laws of the kind rule |
| B4-F10 | P3 | PAT-06, PAT-04 | PAT-06 states collector forms valid for 'both pattern languages' though family heads reject every collector |
| B4-F11 | P3 | PAT-01, PAT-02, PAT-03, PAT-04, PAT-05, PAT-06 | Unstamped stale file:line loci across PAT-01..PAT-06 Evidence sections |
| B5-F03 | P3 | PAT-11 | PAT-11 'One value' example uses a single-clause Pair, which is an ordinary algorithm, not a clause family |
| B5-F04 | P3 | PAT-11 | PAT-11 Evidence cites deleted C# symbols and stale Lean/C# line numbers as current evidence |
| B5-F05 | P3 | PAT-09 | PAT-09 summary Rule has a normative clause (c) 'Forwarded occurrences' that the draft states only as a Boundary caveat |
| B5-F06 | P3 | PAT-09 | PAT-09 Known tension 1 opens with superseded law in present tense, and the Decision record still says Q-05 is 'not yet committed' |
| B5-F07 | P3 | PAT-09 | PAT-09 cites a test and spec cases whose names/explanation describe dot 'wrapper identities' superseded by Q-18 C-B3 |
| B5-F08 | P3 | PAT-08 | PAT-08 Evidence calls MatchPattern 'the clause matcher'; since Model C it only compares literal patterns |
| B5-F09 | P3 | PAT-07 | PAT-07 Lean evidence cites testValueBinderShadowsCallerAlgorithm at :2018; it is at :2065 |
| B6-F02 | P3 | VAR-02 | VAR-02 cites a non-existent loop 'twin binder' and claims lifted signatures are unpinned |
| B6-F04 | P3 | VAR-01 | VAR-01 lists a historical Lean binder as a current definition and historical-binder laws without qualification |
| B6-F05 | P3 | VAR-03 | VAR-03 cites HO-01 for the callback law and a non-existent test class |
| B6-F07 | P3 | VAR-04 | VAR-04 current-evidence loci for EvalExplicitSequenceValueItems are stale, and a CollectSegment remark is false |
| B6-F08 | P3 | VAR-06 | VAR-06 C# implementation loci are stale |
| C1-F02 | P3 | VAL-04 | Two VAL-04 'zero count' examples fail for a binder reason, and one loop example has a pre-Q-26 emitted count |
| C1-F03 | P3 | VAL-05 | VAL-05 describes pre-X-07 behaviour in the present tense ('The record as found ... They are rejected by the evaluator's pre-evaluation gate') |
| C1-F04 | P3 | VAL-09 | VAL-09 cites the deleted C# ParameterPatternInput and a historical-fixture Lean structure as current 'no provenance' evidence |
| C1-F06 | P3 | VAL-01 | VAL-01 Evidence loci are stale (Lean, spec corpus, tutorial) |
| C1-F07 | P3 | VAL-02 | VAL-02 Evidence loci are stale (one out of range) |
| C1-F08 | P3 | VAL-03 | VAL-03 Evidence loci are stale (CombineOutputSlots out of range; Lean theorems shifted) |
| C1-F09 | P3 | VAL-04 | VAL-04 Evidence loci are stale (EvalOutputRowsPreparedCore out of range) |
| C1-F10 | P3 | VAL-05 | VAL-05 Evidence loci are stale (MissingOutput site out of range; engine, Ast, Lean shifted) |
| C1-F11 | P3 | VAL-06 | VAL-06 re-count sites are stale, and the user-call sites moved from Calls.cs to Evaluator.Needs.cs under Model C |
| C1-F12 | P3 | VAL-07 | VAL-07 Evidence loci are stale (two out of range) |
| C1-F13 | P3 | VAL-08 | VAL-08 Evidence loci are stale (BuiltinCollectionItems out of range) |
| C1-F14 | P3 | VAL-09 | VAL-09 Evidence theorem/guard/Result loci are stale (besides the deleted symbol in C1-F04) |
| C1-F15 | P3 | VAL-10 | VAL-10 Evidence loci are stale; the evalAttempt use list is incomplete; line 901 still calls inferred-parameter ExplicitParametersRequireOutput a pre-evaluation check |
| C1-F16 | P3 | VAL-11 | VAL-11 has no Appendix A coverage row (pre-recorded A3 carry-forward); exact row proposed |
| C2-F01 | P3 | BOOL-01, BOOL-02, BOOL-03, BOOL-04, BOOL-05, CMP-01, CMP-02, CMP-03, CMP-04, CMP-05, RAND-01, RAND-02, RAND-03 | Evidence file:line loci across the batch are stale and presented as current evidence |
| C2-F02 | P3 | BOOL-01 | Generator guidance still says `contains` on an empty collection returns `0` |
| C2-F03 | P3 | BOOL-03 | BOOL-03 caveat quotes a message for `-true` that the runtime does not print |
| C2-F04 | P3 | RAND-01, RAND-02, RAND-03 | Randomness examples name a CLI option `--seed` that does not exist |
| C2-F07 | P3 | CMP-02 | CMP-02 evidence says every path applies links through `Evaluator.ApplyComparison`, but planned numeric ordering links do not |
| C3-F03 | P3 | OP-11 | OP-11 evidence cites the deleted Evaluator.TryResolveQualifiedMathNativeReference as current implementation |
| C3-F04 | P3 | OP-14 | OP-14 rationale overclaims .string as THE representation observer, cites VAL-09 instead of VAL-11, and keeps a stale DOT-08 description and a non-repo locus |
| C3-F05 | P3 | OP-07 | OP-07 caveat cites VAL-09 for the representative kept by ==-merges, and its list of where the two zeros differ is incomplete |
| C3-F06 | P3 | OP-04 | OP-04 evidence pairs unary minus with ExpectInt and understates the post-Q-27 pinning |
| C3-F07 | P3 | OP-01 | OP-01 claims no test pins prefix minus over a spread; StarSyntaxTests pins `-values*` |
| C4-F04 | P3 | MOD-06 | MOD-06 example `F(p) = { open { public Y = p } ⏎ Y }` / `F(3)` claims ArityMismatch; FWD-02 bare forwarding gives 3 |
| C4-F07 | P3 | MOD-02, MOD-03, MOD-04, MOD-05, MOD-06, MOD-07, MOD-10, MOD-11 | Stale file:line evidence loci presented as current across MOD rules |
| D1-F03 | P3 | SYN-09 | SYN-09 evidence quotes the pre-Q-18 call gate, its Lean bullet states the superseded dot-wrapper in present tense, its status names no open-question ID, and Appendix A19 states superseded law |
| D1-F04 | P3 | SYN-04, SYN-06 | Retired rule IDs cited as current owners (ALG-09 in SYN-04, ALG-03 in SYN-06) |
| D1-F05 | P3 | SYN-06, SYN-11, SYN-01, SYN-07, SYN-09, SYN-12 | SYN topic 'Stale surfaces to fix' list and F13b sub-bullets are out of date: one item is repaired but still listed, the others remain unrepaired, and new stale doc text exists |
| D1-F06 | P3 | SYN-01, SYN-02, SYN-03, SYN-04, SYN-05, SYN-06, SYN-07, SYN-08, SYN-09, SYN-10, SYN-11, SYN-12, SYN-13, SYN-14 | Unstamped file:line loci in every SYN rule's Evidence are stale at fb7b5646 (Parser.cs, Lean, EBNF, tutorial, spec-corpus lines; one renamed test) |
| D2-F01 | P3 | RUN-03 | RUN-03 says cancellation is 'never retained on a binding', contradicting NEED-02/NEED-09 sticky cancelled completion |
| D2-F03 | P3 | RUN-01 | RUN-01 evidence claims the ResourceLimitTerminalityTests route matrix requires the same resource-limit kind on all six routes |
| D2-F04 | P3 | RUN-01 | RUN-01 evidence: stale line loci and one misqualified symbol |
| D2-F05 | P3 | RUN-02 | RUN-02 'never between limit configurations' is literally unattainable given its own JIT-state clause |
| D2-F06 | P3 | RUN-02 | RUN-02 caveat omits cross-run deferred-region state (materialization memo and per-parse acquisition budget) |
| D2-F07 | P3 | RUN-02 | RUN-02 evidence: stale line loci |
| D2-F08 | P3 | RUN-03 | RUN-03 evidence: stale line loci |
| D2-F09 | P3 | RUN-03 | Production comments in RUN-03's owning code still carry pre-Q-02 / pre-Model-C rationale |
| D2-F10 | P3 | RUN-04 | RUN-04 evidence: stale line loci |
| D3-F03 | P3 | ALG-07 | ALG-07 evidence cites the deleted RepeatedNameAggregate, a removed doc sentence, misleadingly named spec cases, and stale loci |
| D3-F05 | P3 | RUN-05 | RUN-05 Known tension is presented as current although Q-09a/X-34 resolved it and the manifest row now carries the caveat |
| D3-F07 | P3 | RUN-08 | RUN-08 cites an absent document (analysis/L3.md) and stale Lean/C# loci as current evidence |
| D3-F08 | P3 | ALG-02 | ALG-02 example a02c (Apply([Inc]) → ArityMismatch) is stale; Known tension still worded as current |
| D3-F10 | P3 | ALG-01 | ALG-01 caveat examples a01g/a01d omit their Apply definition (rule's own Apply gives 14, not 11); a01e quotes stale wording; no alias pointer |
| D3-F11 | P3 | RUN-07 | RUN-07 Lean/C# evidence loci stale, two of them out of file range |
| D4-F03 | P3 | FORMAL-07 | FORMAL-07 printed theorem/guard/partial-def counts are stale and internally inconsistent |
| D4-F04 | P3 | FORMAL-07 | FORMAL-07 draft and summary are not normatively equivalent on the alias/forwarding law inventory |
| D4-F05 | P3 | FORMAL-06 | FORMAL-06 cites a historical-fixture theorem as the Lean pin of the current flat-arity payload; stale C# loci |
| D4-F06 | P3 | FORMAL-03 | FORMAL-03 exclusion counts stale and Known tension superseded by Q-09a |
| D4-F07 | P3 | FORMAL-08 | FORMAL-08 evidence quotes the pre-Q-18 call gate, cites a deleted test that contradicts clause (e), and understates its checkers |
| D4-F08 | P3 | FORMAL-01 | FORMAL-01 evidence: stale library count, guard counts and guard locus; HistoricalReadyBinding not classified |
| D4-F09 | P3 | FORMAL-02 | FORMAL-02 evidence loci and ratchet figures stale |
| D4-F10 | P3 | FORMAL-04 | FORMAL-04 Lean loci stale; ':3510 applyComparison' now points at an unrelated historical helper |
| D4-F11 | P3 | FORMAL-05 | FORMAL-05 C#/Lean loci stale |
| D4-F12 | P3 | FORMAL-07 | Lean comments still describe the historical Ready binders in current tense as 'the real binder' and name deleted C# twins |
| DOC1-F04 | P3 | AGENTS.md | Dot-receiver and exact-collector law lists cite historical Ready-binder theorems as pins for current behavior without qualification |
| DOC1-F07 | P3 | docs/design/language-rules/syntax.md | Collecting-binding and pattern-list enumerations name only nested sequence patterns and omit list patterns |
| DOC1-F08 | P3 | docs/design/language-rules/syntax.md | Pre-Q-18 'dot RESULT' wording for `(a.b)(1)`, and `(x)~` misclassified as the attachment error |
| DOC1-F09 | P3 | docs/design/language-rules/syntax.md | `F(a` newline `b) = a + b` is claimed to be one diagnostic, but it reports two |
| DOC1-F10 | P3 | docs/design/language-rules/syntax.md | Comparison-chain rendering pin cites a renamed test and a superseded missing-output outcome for `(-2).f` |
| DOC1-F11 | P3 | src/KatLang/SEMANTIC-ALIGNMENT.md | Normative Grace+DotCall §7 structural-collision example presents `Obj~.t` and `Obj.~t` as valid when the receiver owns the member |
| DOC1-F12 | P3 | AGENTS.md | Traversal-exhaustiveness bullet names the deleted C# matcher `MatchCountedPattern` as a current dispatch |
| DOC1-F13 | P3 | AGENTS.md | Parameter-channel bullet says 'all three inherited tiers' and omits the Model-C need-cell tier |
| DOC1-F14 | P3 | src/KatLang/SEMANTIC-ALIGNMENT.md | Known gaps mixes present-tense statements of since-superseded law with no reading note; module-splice rationale predates Q-31/Q-32 |
| DOC2-F01 | P3 | docs/design/language-rules/ownership-and-lookup.md | The Math-members section still states the deleted Q-15 closed-list strict-value diagnostic as current behavior |
| DOC2-F04 | P3 | docs/design/language-rules/evaluator-and-hosting.md | The display-decimals section misdescribes the composition carrier and omits RunResult.WithHostDisplayDecimals |
| DOC2-F05 | P3 | docs/design/language-rules/ownership-and-lookup.md | The open-provider eligibility list in § Open, exposure, and accessibility omits callable aliases |
| DOC2-F06 | P3 | docs/design/language-rules/editor-semantics.md | Shared open-provider member indexes are still described as a pending follow-up |
| DOC2-F07 | P3 | docs/design/language-rules/evaluator-and-hosting.md | The error-taxonomy table gives bare `Apply((Inc, Dec))` as a NotAnAlgorithm example, but as a root program it is UnresolvedImplicitParams |
| DOC2-F08 | P3 | docs/design/language-rules/ownership-and-lookup.md | 'shadow all three inherited tiers' omits the Model-C need (cell) tier |
| DOC3-F04 | P3 | .github/agents/katlang-generator.agent.md | A variadic loop step is said to need as many state slots as it has parameters; the minimum is its fixed parameters only |
| DOC3-F05 | P3 | .github/agents/katlang-generator.agent.md | Clause-matching guidance still describes eager evaluation of all arguments and misclassifies a wrong-count call as 'no branch matches' |
| DOC3-F06 | P3 | .github/agents/katlang-generator.agent.md | `not ()` is described as failing 'numeric conversion'; it fails because `not` requires a Boolean (both are TypeMismatch) |
| DOC3-F07 | P3 | KatLang.ebnf | The EBNF says same-line `2 (3)` is the expression list `2, 3`; it is the UnseparatedSameLineItem error |
| DOC3-F08 | P3 | tutorial.md | The tutorial says every line of a program is an output row |
| DOC3-F09 | P3 | README.md | The README's --random-seed paragraph lists 'left-to-right arguments' among the rules that decide which random calls draw (pre-Model-C) |
| DV1-N01 | P3 |  | evaluator-and-hosting.md § Traversal exhaustiveness names the deleted C# matcher `MatchCountedPattern` as current |
| DV1-N02 | P3 |  | C# and Lean doc comments of the parameter-shadowing helper omit the need-cell tier they filter |
| DV2-N01 | P3 |  | AGENTS.md Q-10 bullet names a stale composition locus and omits RunResult.WithHostDisplayDecimals |
| NF-V03-1 | P3 | SYN-06 | SYN-06 Evidence cites the pre-Q-18 name of a renamed RedundantParenthesesTransparencyTests test |
| NF-V03-2 | P3 | DOT-01, DOT-02, DOT-03, DOT-04, DOT-05, DOT-06, DOT-07, DOT-08, DOT-09 | DOT topic note lists an Evaluator.DotCalls.cs 'never the property cache' comment that no longer exists |
| V02-N01 | P3 | PAR-07 | PAR-07 summary ROLE bullet omits the runtime-decided dot receiver from the CALLABLE keepers |
| V07-N01 | P3 | VAR-01, VAR-04 | SEMANTIC-ALIGNMENT.md names the deleted CollectSegment as the current checked helper for collected lists |
| X1-F03 | P3 | PROP-05, PAR-07 | PROP-05 enumerates the lifting positions with the pre-unified-law list, including the deleted 'registry-strict Math' notion |
| X1-F04 | P3 | PAR-01, RES-07 | PAR-01 says names the callee does not bind 'stay visible to it', which read after the inherited-tier sentence states dynamic scoping, contrary to RES-07 |
| X2-F02 | P3 | LOOP-07, HO-03 | LOOP-07 says a loop result 'as a callback body' is one item like any non-spread row, but a zero-slot loop result `()` there is HO-03's ArityMismatch |
| X2-F03 | P3 | VAR-03, LOOP-02, LOOP-03, VAR-02, VAR-05, PAT-08 | VAR-03's lazy cell-transfer law is stated without its scope: it holds for top-level collecting parameters in a call's supply, not for nested or deconstruction collectors, nor for an output row `name*` (including a loop step's next-state rows) |
| X2-F04 | P3 | LOOP-02, PAT-06, PAT-09, NEED-04 | LOOP-02's user-step binding list omits list patterns, reduces repeated names to 'equality constraints', and names the internal kind BadArity among public codes |
| X2-F05 | P3 | FWD-02, PAR-07, PAT-06, VAL-03 | FWD-02's forwarding by shape is said to forward the stream 'as that group's own kind', but for a sequence group a one-item stream is that item (C(7) TypeMismatch; Use((7, 8)) == Use(7, 8)), an undocumented consequence |
| X2-F06 | P3 | PAT-09, VAR-02 | PAT-09's '(or one nested group level, the collector included)' reads as allowing a collector to be a repeated occurrence, which VAR-02 forbids (InvalidCollectingBinding) |
| X3-F03 | P3 | PAR-04, NEED-07, BOOL-05, RUN-08 | PAR-04 says a blocked closed-list reference is never run by an unselected branch or unused argument; written as a spread operand it is evaluated at supply formation |
| X3-F04 | P3 | RUN-07, RUN-04, MOD-10, MOD-11 | RUN-07 (e) says static errors reject the program regardless of demand and are reported as ParseFailure, omitting RUN-04's deferred-unit exception (judged only when the branch is selected, as EvalFailure) |
| X4-F03 | P3 | VAL-11, OP-13, COLL-06, COLL-07 | VAL-11 says every collapsing operation states its representative, but OP-13 leaves the same-signed quantum tie of min/max explicitly unspecified |
| X4-F04 | P3 | VAL-11, OP-14, DOT-08, OP-07 | VAL-11 names `.string` as THE in-language representation observer, but the zero sign is also observable through sign-sensitive Math (DOT-08) |
| X4-F05 | P3 | COLL-08, OP-07, COLL-09, SEQ-05 | COLL-08 does not say that NaN and ±Infinity counts are not whole numbers, although its saturation table plus OP-07 invite reading `take(xs, Infinity)` as saturating |
| X4-F06 | P3 | VAL-03 | VAL-03 Rule example mixes metavariables: the capture `([x]*)` is said to equal `v` |
| X5-F02 | P3 | PROP-09, RUN-08, RUN-07 | PROP-09's rule says a later read after a failed property evaluation 'evaluates again, and may succeed'; RUN-08 says no such read occurs in the run |
| X6-F02 | P3 | RES-01, RES-02, RES-03, MOD-06 | RES-01's consequence 'a reference in a body and one in a nested body select the same binding' is false under nested opens and for prelude-rooted units |
| X6-F03 | P3 | ALG-01, MOD-05, RES-02 | ALG-01(3) says no lookup outside a block selects its declarations, but `open` of the block does |
| X6-F04 | P3 | PAR-01, RES-07 | PAR-01 'Names the callee does not bind stay visible to it' reads as dynamic scoping, against RES-07 |
| X6-F05 | P3 | PAR-04, FWD-02, FWD-01 | PAR-04 restates bare forwarding's source as a top-level parameter 'with the same pattern', but a collecting capture forwards into a fixed one and the reverse |
| X6-F06 | P3 | MOD-03, RES-01 | MOD-03's root-phantom carve-out for open heads is missing from the summary, and the draft attributes it to RES's root exemption, which governs only collisions |
| X7-F01 | P3 | SYN-08, SYN-11, OP-01, PAR-06 | SYN-08 says an operator-led line 'never continues the previous line' and a marker-led line 'is a new row' without the qualification its own caveats and SYN-11/Q-33 require |
| X7-F02 | P3 | SYN-08, SYN-11, SUP-05, DOT-07 | SYN-08 caveat says a trailing `*` 'continues like any trailing operator', but SYN-11 makes it a spread that ends the line whenever the next line cannot begin an operand |
| X7-F03 | P3 | SYN-11, SYN-07, SYN-10 | SYN-11 offers `A*,` as a way to end a BODY in a spread; Q-33's own decision reserves `A*,` for rows, since a trailing comma continues a body or is a parse error before a declaration |
| X8-F02 | P3 | SUP-06, FORMAL-07, VAL-03 | SUP-06 cites capture laws over the law-local mirror captureForArityLaw (normalize of a sequence), not over the production .capture arm (combineOutputSlots) |
| X8-F03 | P3 | SEQ-03, CALL-04, FORMAL-07 | SEQ-03 and CALL-04 still present HistoricalReadyBinding theorems as current Lean laws without the FORMAL-07 qualifier |
| X8-F04 | P3 | FORMAL-07, FORMAL-02, FWD-02, PAR-07 | FORMAL-07 counts theorems over Lean specifications of C#-only front-end passes, and over the production-unused collectSegment, as proofs over 'the real model' |
| X8-F05 | P3 | FORMAL-08, SYN-09, DOT-09 | FORMAL-08 clause (i) states the pre-Q-18 callee shape: a source Call's DotCall callee is always argumentless |
| XV4-N01 | P3 |  | evaluator-and-hosting.md calls `.string` THE in-language representation observer (same overclaim as X4-F04) |


## Final Constitution-wide independent review evidence corrections (2026-10-10)

IR-F01..07 are recorded in constitution-final-wide-independent-review. Current-law text corrections affect VAL-04/VAL-08/LOOP-07/FORMAL-05 (callback row count and nonempty-value gate), RES-01 (owner declarations versus level-specific opens), and SUP-06 (production shallow capture versus recursive proof mirror). No implementation defect or new design choice was introduced. Original 279 actionable finding records include two duplicate repair groups; the independent accounting records 277 groups under the explicit repair-set convention. Appendix A has 36 total additions (D15 plus 35 later additions).

## Q-25 — owner decision and implementation — 2026-10-10

No issue classification changes. The ledger's statements that #37's single-value callback result, #135's strict single-value map/reduce callback contract and the callback-binding lineage's "must emit exactly one non-() value" survive are superseded by Q-25 (Option B, owner decision): a `map` transform or `reduce` step returns the ordinary result of calling its callback. Dated pointers were added at the head of the ledger, in #37 and #135, and in the "Callback binding for map/filter/reduce" lineage; the original statements remain verbatim. Evidence: `../q25-callback-result-investigation/implementation/`.

## Q-25 independent review - unfolding qualification (2026-10-10)

*2026-11-26 review note. The result boundary decided here still applies. The demand order and effect examples below describe October. For the superseding #203 and #204 decisions, see HO-02 and HO-03 in the current Constitution.*

Owner follow-up: "Qualify the unfolding equation; preserve existing demand rules." Q-25 Option B remains fully adopted and resolved. Each callback returns its complete ordinary call result. Operationally, reduce processes collection elements from left to right, invokes each step with the current accumulator, and preserves the complete ordinary call result as the next accumulator.

The map/reduce unfolding equations express result-value equivalence for pure, deterministic, total computations. They do not guarantee identical effect ordering, argument demand, random draws, resource consumption or error timing. Model-C demand and established evaluation order are unchanged: reduce demands its initial once and finishes each earlier step; map demands its collection; expanded ordinary calls can skip unused arguments and inner calls.

Permanent six-route counterexamples: with R(x, acc) = tick() * x + acc, reduce([1, 2], R, 0) returns 5 and R(2, R(1, 0)) returns 4, with tick starting at one. With L = [tick(), tick()] and F(x) = tick(), map(L, F) returns [3, 4] and [F(L:0), F(L:1)] returns [1, 2]. A failing unused initial or collection similarly distinguishes the builtin from expanded calls. Pins: CallbackResultBoundaryTests.Independent_Reduce* and Independent_Map*; four derived-AST canonical cases in LanguageSpecCorpus (reduce-demands-initial-before-iteration, nested-reducer-calls-may-skip-unused-initial, map-demands-collection-before-transforms, expanded-map-calls-may-skip-indexed-arguments).

Evidence correction: reduce's result count is observed directly by internal counted evaluator entry points, and also by production planned-loop handover diagnostics when reduce is a nested step output. Ordinary source value receivers normalize that count. Independent_EmptyReduceResult_PreservesPlannedLoopHandover pins the optimized hit, exact handover reason, one materialization, and generic/async value and budget agreement.

Affected current text: HO-03 unfolding premise, the Q-25 resolution banners/register, and Appendix A P34 evidence scope. HO-04 and Model-C remain authoritative. No rule ID, classification, status, rule count or unrelated owner decision changed (175 active / eight retired; status tally 46 / 1 / 115 / 13). All prior replaced lines are preserved verbatim in decision-lineages.md. The six-record pre/post manifests and byte-exact restore-verified external archives are recorded in ../q25-callback-result-investigation/independent-codex-review/constitution-archives.json. Local archives establish local recoverability; no off-device durability is claimed.

## Q-45 — owner decision — 2026-10-10

No issue classification changes. The ".string intrinsic" lineage's surviving-semantics statement that `R.string(args)` evaluates and rejects the arguments without evaluating the receiver describes the pre-Model-C order; Q-45 (owner decision) keeps the current Model-C order — formation with explicit spreads executed, cardinality before any demand, the receiver demanded only for a supply of zero items — as the law. Dated pointers were added at the head of the ledger and in that lineage; the original statements remain verbatim. #32's row ("rejects arguments") stays accurate. Evidence: `../q45-string-args-resolution/`.

## X-18 — owner decision — 2026-10-10

No issue classification changes. The "Callee identity and the builtin argument adapter" lineage's surviving-semantics statements that user callables share one eager left-to-right assembly and that builtins use their own adapter describe the pre-Model-C regimes; X-18 is RESOLVED — existing Model-C semantics confirmed by owner (2026-10-10) — every callee forms its supply alike, cardinality precedes every ordinary VALUE demand, and each callee demands in its own order. Dated pointers were added at the head of the ledger and in that lineage; the original statements remain verbatim. The rows of #49, #131 and #159 stay accurate. Evidence: `../constitution-x18-closeout/`.

## Q-37 — owner decision and implementation — 2026-10-11

No issue classification changes. The "Cache key / binding identity" lineage's surviving-semantics statement that "the first successful entry wins" and the "Failures, re-entrancy, re-derivation" lineage's statements that the first completed success is the entry and that a self-recursive property can return two different values for two reads describe the first-successful-completion rule of 31f7c76; Q-37 (owner decision) makes the outermost successful property-style evaluation of a key the owner of its entry, so probe p4 gives (2, 2). Dated pointers were added at the head of the ledger and in those lineages; the original statements remain verbatim. #42, #110 and #170 keep their classifications. Evidence: `../q37-outermost-property-cache/`.

## FORMAL-07 — research and binder formalization — 2026-10-11

No issue classification changes. New research findings are recorded in `artifacts/validation/formal07-research/semantic-gap-analysis.md` § 6: F7-D1 (C#, a host-built clause head with two collecting binders made `Evaluator.Run` throw `ArgumentOutOfRangeException` or silently misbind) and F7-D4 (a single collecting clause binder lost its kind in C#'s single-clause flattening and disagreed with zero-argument acceptance) are FIXED in the same candidate (any collecting clause binder is now `IllegalInEval` before evaluation); F7-D2 (third X-02 rule not gated in either engine), F7-D3 (empty family `arityMismatch 0 0`), F7-D5 (`LeanAstEncoder` drops `ParameterKind`) and F7-D6 (loop-plan helper fails open) are open, host-built or hygiene only.

## FORMAL-07 independent Codex review — 2026-10-11

The 25 production-binder theorems remain accepted at their stated scope: cardinality-before-binder-effects, guarded allocation/conservation, minimum agreement, non-repeated all-plain heads, and allocation-only algebra correspondence. They do not establish full evaluator or binder-result refinement. Independent old/new probes now exercise successful CALLABLE projection, same/different declarations and activations, inherited VALUE/count/CALLABLE/need contexts, failures after inspection/allocation and family dispatch; see `../formal07-codex-independent-review/` for raw probes and final validation.

The preexisting third X-02 host-signature omission (F7-D2) and fail-loud encoder omission (F7-D5) were repaired without changing valid written-program semantics. CoreTests now has 2,022 guard lines; ModelC has 45; the canonical corpus has 414 source cases and 334 Lean guard lines. Q-66 retains full binding-result/formation/demand refinement as open; Q-69 retains the paper tag and owner-less caching questions. Earlier dated decisions and supersession quotations are preserved. All six records were archived and restored byte-for-byte before editing; the independent review records the verified post-change archive and exact replacements.

## Q-80 — owner decision (task STR-02) — 2026-10-11

No issue classification changes. Q-80 (string interpolation and double-quoted strings) is a new owner decision, not an issue resolution: #36 (string operations) stays open for ordering and the other operations, and #142's example `text = "# is not a comment here"` is valid since STR-02 (annotated in place). The head pointer above records the current rules (SYN-15, VAL-12); `decision-lineages.md` § Q-80 quotes every replaced constitution line.

## Independent STR-02 Codex review corrections — 2026-10-12

The independent review demonstrated actual downloader invocations for lexer-rejected string targets, including `open "https://katlang.org/{x` and `open "https://katlang.org/a\q"`. The same unterminated single-quoted behavior predated STR-02; that does not make its observable acquisition harmless. SYN-15 and MOD-07 now state explicitly that recovery text cannot authorize acquisition, under RUN-04's existing recovery boundary. No owner decision or question was reopened; valid import scheduling, URL admission, single-quoted value semantics and VAL-12 are unchanged.

Implementation: the parser records every lexical error's provenance on `Expr.StringLiteral.IsRecoveryLiteral`, using the existing equality-transparent `RuntimeStateSlot`; `open` sugar uses the same literal constructor. `ModuleLoader.ExtractLoadUrl` refuses those literals before target admission and downloader invocation, preserving the rejected directive and its original diagnostic for provisional analysis. The flag survives record copies and works when diagnostic reports were omitted by the list cap.

The review also corrected unbounded preparatory comparison-link reads in interpolation diagnostic rendering and two blocking async regression tests that emitted xUnit1031 warnings on recompilation. These are implementation/evidence corrections, with no language-rule change. Evidence and final validation: `../str02-codex-review/review-report.md` and `regression-evidence/`.

Preservation: all six files were inventoried; the STR-02 pre/post archives were restored and hash-verified; a fresh external pre-review archive was byte-restored before these edits. Separate post-review backup and hash evidence are in `../str02-codex-review/constitution-backups/`. Earlier records and decision lineages are retained verbatim.

## Q-81 — owner decision (variadic postfix selection) — 2026-10-12

No issue classification changes. Q-81 replaces `:` indexing with variadic postfix selection and retires the colon; it is an owner decision, not an issue resolution. The head pointer above records the current rules (SEQ-04, SEQ-05); dated notes at #137, #140 and #160 and in the selection and layout lineages state which of their spellings and rejections describe their dates; `decision-lineages.md` § Q-81 quotes every replaced constitution line.

## F7-D6 — loop optimizer fail-closed hardening — 2026-10-12

No issue classification changes. F7-D6, which the FORMAL-07 section above lists as open, is FIXED in the candidate. The loop-plan helper failed open. `IsOptimizedLoopShapeEligible` now treats a user step whose binding plan cannot be built as ineligible, so the loop runs the generic route and records "loop step binding plan unavailable". Non-user steps, every eligible shape and the generic route are unchanged.

Reach correction: an invalid step stored in a host-built scope that parents an `open { … }` block reaches the refusal without any host mutation, because the pre-evaluation walker never visits such scopes. This supersedes two statements:
- that a refused pattern level is "reachable only by mutating a host-owned pattern list" (`src/KatLang/SEMANTIC-ALIGNMENT.md` § C# evaluator cleanup);
- that F7-D6 had no validated-tree trigger (`../formal07-research/semantic-gap-analysis.md`, the F7-D6 row and its review addendum).

The validation gap itself is pre-existing and left open. No language rule, rule status or owner decision changed. Evidence: `../f7-d6-loop-optimizer-hardening/`.

## Host-built parent-scope validation — 2026-10-12

Owner decision, 2026-10-12: the pre-evaluation gate validates host-built parent scopes. No issue classification changes. The gap that the F7-D6 section above recorded as open is CLOSED in the candidate.

A host-built `ScopeCtx` can parent an algorithm (Lean `Algorithm.mk` / `.conditional` / `.alias`, C# `User` / `Conditional` / `Alias`). Both engines' pre-evaluation validation now walks such a scope (Lean `validateScopeTree`, C# `PreEvaluationValidationWalker.VisitParentScopes`):
- what it walks: the scope's `open` targets and property algorithms, then its own parent;
- when: after the carrying algorithm's own content;
- against what: the scope chain in which the members resolve names.

A member there is held to every pre-evaluation rule, with the same error as an ordinary property. This holds wherever the scope sits and whether or not anything reads it. Lean's static alias chase also counts parent-scope aliases as fuel (`Algorithm.aliasCount`).

Consequences for the records above:
- The F7-D6 reach correction's host-scope route is now refused before evaluation. The two statements it superseded hold again:
  - a refused pattern level is reachable only by mutating a host-owned pattern list (`src/KatLang/SEMANTIC-ALIGNMENT.md` § C# evaluator cleanup);
  - F7-D6 has no validated-tree trigger.
- The X-02 statements in `AGENTS.md` and `docs/design/language-rules/ownership-and-lookup.md` now say that the gate covers parent scopes.

The change is observable only for host-built ASTs: these are L10's host-only shapes, whose handling is totality under FORMAL-08. No source program changes, and no language rule, rule status or count changed. Evidence: `../parent-scope-validation-gap/`.

## Four-fix independent review: deferred host parents — 2026-10-12

The parent-scope owner decision remains unchanged. The independent review found one C# host-boundary gap: the deferred-placeholder early return also skipped a complete host-built parent attached to that placeholder. An undemanded branch could therefore hide an invalid two-collector signature or static alias cycle and the run would succeed. The corrected walker validates the parent while preserving the provisional body's materialization boundary. Alias reachability and target-head metadata follow that same boundary. Lean has no deferred-module placeholder representation, so this repair needs no Lean semantic change.

Permanent evidence is `FourFixInteractionReviewTests` (invalid parent refusal with zero downloads and zero steps, scope cycles, declaring-scope alias lookup, and parent-resolved planned steps combining shadowed captures, head mutation and generic handover). `CoreTests/ParentScopeValidation.lean` adds the matching valid shadowed ancestor alias-chain guard. The original parent-scope, fail-closed and admitted-head rules are preserved. The old parent-scope closure remains correct for ordinary algorithms and now also covers this placeholder attachment. No normative rule, identity, status, count, owner decision or dated historical passage is replaced.

Combined review and new validation evidence: `../f7d6-combined-codex-review/`. Earlier task reports and backup archives are retained. All six live records were inventoried and archived to new complete external pre/post backups, independently restored and verified byte for byte; encoding and line-ending conventions are preserved.

## Four-fix independent review: shared-parent error order — 2026-10-12

The review also confirmed a C# first-violation ordering gap on a shared acyclic host-scope graph. An inner scope's earlier property algorithm and the inner scope itself referenced the same outer scope. C# marked the entire pending outer chain visited before entering its members, so the property's earlier edge skipped an unvalidated outer violation and reported a later inner violation. Lean's existing depth-first traversal reported the outer violation first.

C# now marks a scope only when entering that scope's content, preserving the established traversal order while retaining identity memoization. Matching C#/Lean guards pin both edge orders; two new C# scale checks pin linear scope/link visitation when an ancestor chain is also reachable through property parents. A separate process probe validates 140 such levels on a 1 MiB thread. Lean semantics, normative rules, identities, statuses, counts and historical decisions are unchanged.

The first combined V3 attempt passed 35,247 of 35,248 core tests and all 342 CLI and 133 public API tests, with one existing independent-run stress-test deadline failure and zero build warnings/errors. The unchanged failed check passed alone in approximately one second. Its whole-workload deadline and worker cleanup were hardened separately; the smaller cell-level guards remain unchanged. That failed run is not final acceptance evidence. Fresh combined validation and preservation evidence are recorded in `../f7d6-combined-codex-review/validation.md`.

All six records were inventoried and backed up again before this addendum, independently restored byte for byte, and archived separately afterward. Earlier F7-D6, parent-scope and independent-review archives and records are preserved.

## R8 / X-13 formal proof evidence correction — 2026-10-12

X-13 (AGENTS cites restatements as binding laws) is resolved by evidence bookkeeping over `main` @ `8070b033`; no behavioural divergence existed and no language semantics changed. In `lean/KatLangArityLaws.lean` the duplicate bundle equation `dot_call_uses_same_collector_binding_as_plain_call`, the congruence `selection_origin_does_not_change_collector_binding`, three `dot_receiver_*` historical-binder instances and three duplicates (`capture_eq_normalize_sequenceValue`, `variadic_single_collecting_binds_collect`, `a_number_is_one_position`) were removed, and two point cases merged into `build_empty_sequence_value_is_empty_sequence`; `dot_receiver_count_never_satisfies_arity` was replaced by the production `one_cell_supply_fails_two_fixed_patterns_before_any_effect`; `select_is_a_value_boundary` was strengthened over the production selection core; 62 theorems were renamed (the historical Ready-binder laws to `historical_*`), plus two in `CoreArityAlgebraProofs.lean` (and one algebra instance removed); and production counterparts of the historical collector and dot-receiver laws, general bare-forwarding laws and the value-level view identity `spread_view_is_the_positional_view` were added. Final counts: 376 + 30 theorems and 22 examples in `KatLangArityLaws.lean` (375 + 30 and 15 at `8070b033`), 174 + 9 in `CoreArityAlgebraProofs.lean` (175 + 9). `#print axioms` over all 558 public theorems shows only `propext`, `Quot.sound` and `Classical.choice`. Q-66 stays open with an itemized status; the register X tally is now 41 resolved, 1 superseded, 7 open. Records: both Constitution editions (active evidence passages), `open-questions.md` (banner, totals, X-13 resolution, Q-66 row), `decision-lineages.md` (every replaced line verbatim) and the review log. Evidence: `../r8-x13-proof-evidence-cleanup/`.

## Historical Ready-binder retirement — 2026-10-12

Owner decision, evidence bookkeeping over `main` @ `6bf2f624` with the uncommitted R8/X-13 change; no behavioural divergence existed and no language semantics changed. `lean/HistoricalReadyBinding.lean` and its `lean_lib` target were deleted, with every declaration of `lean/KatLangArityLaws.lean` whose statement reaches it (found by a dependency analysis of the built environment: 47 public `historical_*` / `bindParameterPatternList_*` theorems, 7 private helpers, the private `repeatedMergeStep`; no retained theorem's proof reached the fixture), the four laws over the laws-only splitter `bindCallableArguments`, and eight helpers left without a user. `lean/KatLang.lean` lost six definitions with no production caller (`bindCallableArguments`, `CallableArgumentBindings`, `Algorithm.isFunctionShaped`, `ParameterPattern.repeatsAtLevel`, `bindsName`, `anyBindsName`); no definition the evaluator reaches changed. Final counts: 325 + 19 theorems and 22 examples in `KatLangArityLaws.lean` (376 + 30 after R8/X-13), 174 + 9 in `CoreArityAlgebraProofs.lean` (unchanged; the Constitution's "184" was an R8 miss, recounted as 183). CoreTests: the `bindParams` guard was retired; `callbackShapeMatrixAgreesWithTheDirectCall`, `repeatedCountedBindingChecksTheCompletePair`, RepeatedNameConstraints § 14, the ValueDemand zero-supply guard and the CollectingParameters zero-argument guards now run the production evaluator, `bindNeedPatterns` or `acceptsZeroSuppliedArguments`; 2,184 `#guard` lines. Q-66 stays OPEN (items unchanged), X-13 stays RESOLVED; no Q, PV or X status changed. An independent read-only adversarial review led to the follow-ups recorded in the lineage. Records: both Constitution editions (active evidence passages, FORMAL-01 annotated, Appendix A rows and tally), `open-questions.md` (banner, Q-66 row note, PV-04/PV-13/X-13 appended clauses), `decision-lineages.md` (every replaced line verbatim) and the review log. Evidence: `../formal08-retire-historical-proofs/`.

## F7-D3 — empty clause-family diagnostic — 2026-10-12

No issue classification changes, no rule text change and no code change. F7-D3, which the FORMAL-07 section above lists as open, is CLOSED as FORMAL-08 totality: the current behaviour follows the existing contract. Evidence: `../f7-d3-empty-family-diagnostic/`.

- **Reach: host-built only.** Source never forms an empty family: a clause group is created together with its first clause (`Parser.cs:1436-1455`), and every front-end rewrite and loader walk maps branches one to one. A host can build one with `new Algorithm.Conditional(…, Branches: [])` or with the public `Algorithm.ElaborateClauseGroup([])`.
- **Behaviour** (re-run 2026-10-12 at `e5009f5c`; four C# routes and Lean agree). An explicit call supplying n arguments is `ArityMismatch` with payload `(0, n)` for every n, before any argument is demanded, on every invoking route: direct call, `map`/`reduce` callback, user higher-order parameter, `repeat`/`while` step, dot fallback, host-built parent scope. A bare zero-argument value demand is `NoMatchingBranch` (the split PAT-11 records for every family). An unused empty family evaluates, as `ConditionalBranchArityValidationTests.SingleBranchAndEmptyConditionals_PassValidation` pins.
- **Category: determined by existing rules.** A family with no clause head accepts no count, and "a count no clause head accepts is rejected … as the call's cardinality `ArityMismatch`" (PAT-02; PAT-03(b), NEED-05 and FORMAL-07's text agree). The production theorem `family_dispatch_rejects_unaccepted_supply_before_any_effect` covers the empty case, because its hypothesis holds vacuously, and states the payload. `NoMatchingBranch` on a call would contradict all of them.
- **Payload: presentation.** The `0` is the dispatchers' documented fallback ("0 when there is no clause"). It is misleading, because an empty family accepts no count, zero included. But arity payload numbers are presentation (FORMAL-06: payloads are compared on one side only; the consolidated non-constitutional list), and no rule states a payload for a family without clauses.
- **Refusal before evaluation: permitted, not required.** Appendix A L10 makes the choice of refused host-only shapes totality. No front-end rule refuses the shape, since source cannot write it. Refusing an unused empty family would flip the pinned test above and the outcome of the public `ElaborateClauseGroup([])` tree. If wanted, it is an owner-level host-AST policy decision, like the parent-scope one. The recommended form is then an `IllegalInEval` pre-evaluation refusal in both engines, leaving the dispatchers and the theorem unchanged.
- **Separate finding, not F7-D3 and not changed here.** A host-built program ROOT that is a clause family with no zero-arity clause, empty or not, evaluates to `UnresolvedImplicitParams([])` in both engines. C# `KatLangError.FromEvalError` then throws `ArgumentOutOfRangeException`, because `FormatUnresolvedImplicitParams` reads `ParamNames[^1]` on an empty list. This is recorded as its own follow-up.

## KatLangError facade totality: host-built nameless roots — 2026-10-12

No issue classification changes, no rule text change and no language semantics change. The separate finding that the F7-D3 section above records as a follow-up is FIXED in the candidate, in C# presentation only (the manifest row "Diagnostic wording only"). Evidence: `../katlangerror-family-root-totality/`.

- **Defect.** A host-built program root, or a written block demanded as a value, can require a supplied argument while binding no name for it: a clause family without a zero-arity clause (empty or not), or a nameless `()` / `[]` pattern. It evaluates to `UnresolvedImplicitParams` with an EMPTY name list. The public `KatLangError.FromEvalError` then threw `ArgumentOutOfRangeException`, because `FormatUnresolvedImplicitParams` read the last name of the empty list. This was reproduced on the sync route and the async twin, through six host-built routes.
- **Repair.** The empty list now gets its own sentence: "The algorithm being evaluated requires supplied arguments, but it names no implicit parameter for them. No arguments were provided, so the program cannot be executed." A host-supplied nonzero count reads "Only N arguments were provided". Every report with one or more names is unchanged.
- **Unchanged.** The structured error, its context and its code are untouched. They equal Lean's verdict for the same trees: `runResultM` and the written-block arm of `zeroArgumentDemandError?` give `unresolvedImplicitParams []`. A root keeps CALL's root rule ("A root that still requires a supplied argument is an evaluation error (`UnresolvedImplicitParams`)"). A family BLOCK demanded as a value keeps the family arm of the zero-argument value-demand law (`NoMatchingBranch`). Source never produces these trees: a parsed root is an `Algorithm.User` whose inferred parameters are names (FORMAL-08).
- **Totality.** A matrix over every public error and context variant, with degenerate payloads (empty lists and strings, zero, negative and extreme counts), bare and nested, found no other throwing shape. `KatLangErrorTotalityTests` pins it, with the six routes on both evaluation paths.

## P3 maintenance cleanup — 2026-10-13

No issue classification changes, no rule text change and no language semantics change. Dead evaluator infrastructure was removed: Lean `matchCallPattern`, `matchCallBranches` and the counted matchers `matchCountedPatternInto` / `matchCountedStructureInto` / `matchCountedPattern` / `matchCountedCallPattern` / `matchCountedCallBranches` (their last call sites were replaced by Model C's need-supply family dispatch in `8f0ceb85`); the legacy algorithm-tier failure channel — Lean `AlgBinding.valueFailure?` with `parameterValueFailure?`, `argumentParameterValueFailure?` and `AlgEnv.lookupBinding`, C# the `AlgEnv` `ValueError` element with `ParameterValueFailure`, `ParameterHasValueOutcome` and `LookupAlgBinding` (folded into `LookupAlg`); the unused private simp lemma `parameter_kind_collecting_beq_normal`; and the dead C# 2-argument `MatchPattern` overload. Evidence: `../p3-maintenance-cleanup/`.

- **Why it was dead.** The matchers lost their last call sites to Model C's need-supply family dispatch (`8f0ceb85`), which also deleted their C# twins. The failure channel had no production writer after Model C, and in both engines no production binding site adds an algorithm-tier entry at all; every removed read returned none and only read state. A dependency analysis of the built Lean environment and a C# reference audit, each followed by an adversarial refutation, found no live use.
- **Unchanged.** Values, error categories, payloads, context frames, spans, evaluation order, budget charges and sync/async outcomes. A Lean declaration inventory shows only the deletions, the four evaluator bodies that called a removed reader, `AlgBinding`'s generated declarations and test fixtures; no user theorem changed; every theorem uses standard axioms only. The public API baseline and both generated corpora are unchanged.
- **This ledger's loci.** The `path:line` loci in this ledger's "Surviving semantics" and "Current evidence" fields are snapshot locators of the 2026-09-27 archaeology at `a2700f4` (see the status banner), and were deliberately not re-anchored: the maintained current evidence is `constitution.md`'s rule Evidence sections and Appendix A, whose loci are now symbol-based.
- **Found, not changed (follow-ups).** (1) Pre-existing Lean/C# difference in context frames: for `Show(v) = v.string` / `Show(Inc)` with `Inc(z) = z + 1`, both engines report `ArityMismatch(1, 0)`, but C# adds a "while evaluating property Inc" frame that Lean does not (C# demands a need-backed parameter receiver's cell before the zero-argument law; Lean applies the law first). (2) The algorithm-channel and counted parameter tiers themselves have no production writer in either engine; retiring them is a larger restructuring left to a separate decision.

## `.string` receiver alignment — 2026-10-13

No issue classification changes and no rule text change. Closes follow-up (1) of the P3 section above. Evidence: `../string-receiver-frames/`.

- **Decision.** By the rules, without an owner question: CALL-06 lists the `.string` receiver among a slot's VALUE demands and states that a callable read as a value reports what the written argument raises; AGENTS.md's at-most-once rule names the `.string` receiver among the reads that reuse the slot's outcome; and Lean's own `evalDotStringReceiverValue` docstring promised "the failure its argument slot established". C#'s cell-first order is the intended one.
- **Change.** Lean only: the `string` arm of `evalDotCallCounted` skips the zero-argument law for a parameter bound to a supplied cell (`hasSuppliedParameterCell`) and reads the cell. C#: comments only.
- **Scope of the old divergence** (a 50-program probe matrix through both engines over the same elaborated programs): wider than the frame P3 noted. Besides the missing property frame (`Show(Inc)`, a callable alias, a forwarded parameter, a minimum supply, a loop step), `Show({x + 1})` was `ArityMismatch(1, 0)` in Lean and `UnresolvedImplicitParams` in C# (an error-category divergence), a clause family's `NoMatchingBranch` named the parameter instead of the family, an inline alias `{ Inc }` lost its target's report (FA-OQ-1), and a member path lost its `dotCall .F` frame. Values never differed.
- **Still differing, presentation (documented):** a parameter receiver's description in a dot-call frame (`(param)` in Lean, the name in C#), Lean's builtin-arity frame (C# keeps it on the leaf), and C#'s implicit-parameter frame.
- **Found, not changed:** `openExprName`'s `(param)` also reaches a payload: `Apply(f, x) = f(x)` / `Apply(F, 5)` with a clause family `F` is `noMatchingBranch "(param)"` in Lean and `NoMatchingBranch("f")` in C# (the category agrees).

## Parameter-tier retirement — 2026-10-13

No issue classification changes, no rule text change and no observable behaviour change. Closes follow-up (2) of the P3 section above. Evidence: `../retire-algenv-counted-tiers/`.

- **Retired.** The algorithm-channel tier and the counted callback-parameter tier, in both engines: Lean `AlgBinding`, `AlgEnv`, `CountedParamEnv`, the `EvalCtx` fields and their `with…` helpers, the `ParameterActivation` fields and the two cache-key fields; C# the two aliases, the `EvalCtx` members, the shadow and lookup helpers, the activation and cache-key identities of both tiers, and the loop planner's `CountedParamSlot` plan with its reads.
- **Why it was dead.** A built-environment analysis listed every `EvalCtx.mk` / `ParameterActivation.mk` argument in the project: in production every tier value was `[]`, a copy, a filter of a copy, or `[] ++` a shadowed copy (the only adder, `bindParameters`, was called with `[] []`; `withAlgEnv` / `withCountedParamEnv` had no caller); only three CoreTests guards wrote entries. In C# the root and `EvalCtx.Empty` start both tiers as the shared empty array and every path only carried, shadowed or filtered them; a probe over 4,334 corpus programs (both strategies) found all 4,479 cache executions (239 local-only) keyed by the shared empty instance, so dropping the two key components merges no entry.
- **Unchanged.** Values, error categories, payloads, context frames, spans, cache hits, budgets and sync/async outcomes. The only reachable difference is on hand-built contexts: a parameter found only on the algorithm channel (formerly `badArity` / `BadArity`) cannot exist any more; a parameter with no binding reads as `unknownName` / `UnknownName`, as before.

## Parameter callee names — 2026-10-13

No issue classification changes and no rule text change. Closes the `.string` receiver section's "Found, not changed" bullet and the dot-call-frame item of its "Still differing, presentation" bullet. Evidence: `../param-callee-name/`.

- **Decision.** By the rules, without an owner question: a report names the written reference (FWD-02: a call through an alias "names the written callee once"; FA-OQ-1: a family's `NoMatchingBranch` is "named by the reference"). A parameter is a reference, which C# and Lean's own `exprDiagnosticName` already wrote as its name.
- **Change.** Lean only: `openExprName` gains a parameter arm. A parameter callee or receiver is now named as written in call and dot-call frames, in a clause family's `noMatchingBranch`, in a parameter receiver's `localOnlyProperty` object, and, on host-built trees, in the `badOpenForm` message of a parameter open target and the alias-target message. C#: tests only.
- **Scope of the old divergence** (11 programs through both engines over the same ASTs): 6 differed in a structured payload and 8 in frame text; the error category never differed. After the change all 11 agree in every frame and payload.
- **Still differing, presentation (documented):** Lean's `openExprName` still writes every other non-reference kind as `(kind)` (for example `(num)`), where C# writes the full spelling.

## `resolveArgAlgsWithSequenceSpread` retirement — 2026-10-13

No issue classification changes, no rule text change and no observable behaviour change. Evidence: `../resolve-arg-algs-dead-code/`.

- **Retired.** Lean `resolveArgAlgsWithSequenceSpread`, a total `def` that mapped a call's written arguments to need-backed `ResolvedArgumentAlgorithm`s. The C# method `ResolveArgAlgsWithSequenceSpread` (capital R) is a different, live function and is unchanged.
- **Why it was dead.** Model C (`8f0ceb85`) replaced its last caller, the builtin arm of `evalResolvedCallCounted`, with `formNeedSupply` and a cell wrapper, and no later commit called it. A dependency analysis of the built environment (every project, test, proof, demo and generated-case module; `partial` bodies through their `._unsafe_rec` constants) found no referencer, and the forward closure of the evaluator entry points and of every client declaration never reaches it.
- **Unchanged.** Values, error categories, payloads, context frames, spans, cache hits, budgets and sync/async outcomes. The kernel declaration inventory differs by the one deletion; every theorem's statement, proof and axioms are unchanged.
- **Evidence corrected.** PROP-05's and HO-04's Lean evidence and Appendix A row H02 cited it as live; they now cite `formNeedSupply`.
- **Found, not changed (follow-ups).** (1) Lean `applyBuiltinResolved` has no caller either. (2) Every argument that reaches a Lean builtin is cell-backed, so `ResolvedArgumentAlgorithm.source?` and `.callable?` are set to `some` nowhere and the non-cell branches serve only CoreTests fixtures; C# never sets `SpreadsSequence = true` or `ResolvedArgumentAlgorithm.Callable` either. (3) For `reduce([1, 2], Add, Inc)`, Lean reports `withContext "while evaluating property Inc" (arityMismatch 1 0)` and never its own `reduceInitialAccumulatorRequiresValueError`; C# reports `ReduceInitialAccumulatorContext` over `BadArity`. The public category `ArityMismatch` agrees. (4) BOOL-05's evidence says `expandSequenceSpreadBuiltinArguments` forms the need supply (it is `formNeedSupply`), and CALL-06's evidence still describes a binding found only on the retired algorithm-channel tier.

## `reduce` initial-accumulator report alignment — 2026-10-13

No issue classification changes and no rule text change. Closes follow-up (3) of the `resolveArgAlgsWithSequenceSpread` retirement section above, and amends its follow-up (2): the builtin arm records `ResolvedArgumentAlgorithm.source?` again. Evidence: `../reduce-initial-report-alignment/`.

- **Decision.** By the rules, without an owner question: PV-05 (resolved 2026-09-29, Lean and C# together) keeps reduce's dedicated accumulator hint as the `initial` slot's rejection report, decided from the named callable's signature; `ownership-and-lookup.md` § Builtin identity states it as the rule, and Lean's own `reduceInitialRejection` documents it. Model C kept it in C# and lost it in Lean, where the same commit rewrote the guard `reduceInitialSlotRejectsFromSignature` to pin the property frame under a comment that still promised the hint.
- **Change.** Lean only, mirroring C#: `formNeedSupplySourced` (the one formation, now pairing each cell with its written source; `formNeedSupply` is its projection), the builtin arm of `evalResolvedCallCounted` (passes the sources on), and `demandSequenceBuiltinCallItemValue` (a failed VALUE demand records the cell's CALLABLE projection unless the written slot is a parameter). C#: tests only.
- **Scope of the divergence** (288 programs through both engines over the same elaborated programs): 45 differed, and the change moved exactly those 45. 33 were `reduce`'s initial in the written, dotted and empty-collection forms naming a property, an ignored parameter, a written block, an inline or callable alias, a navigated or nested member, a member alias, a minimum or a structural signature; 4 were transports of a collector cell; 8 were navigated members in `count`, `.count`, `take` and `contains`, now the law's bare `arityMismatch 1 0`. For a written block initial the error CATEGORY changed in Lean (`unresolvedImplicitParams` to the dedicated `badArity`). Values never differed.
- **Unchanged.** A written parameter's established failure (CALL-06), a clause family's `noMatchingBranch`, the non-collection builtins' value slots, and every value.

## Builtin-argument dead-infrastructure retirement — 2026-10-13

No issue classification changes, no rule text change and no observable behaviour change. Closes follow-ups (1), (2) and (4) of the `resolveArgAlgsWithSequenceSpread` retirement section above (with the `reduce` section, all four are closed). Evidence: `../retire-builtin-argument-dead-infrastructure/`.

- **Why dead.** Since Model C every argument a builtin receives is a supplied need cell: the builtin arm of `evalResolvedCallCounted` passes the call's supply (`formNeedSupplySourced`; C# `ResolveNeedSupply`), a builtin loop step its state cells and a builtin callback its element cells. A compiled-environment audit of the starting tree (every project, test, proof, demo and generated-case module; `partial` bodies through `._unsafe_rec`) classified every constructor application: production code writes `ResolvedArgumentAlgorithm.spreadsSequence = false` and `.callable? = none` everywhere (the one exception copies a callback argument's callable, itself `none`), only two `CoreTests/ParityGuards.lean` fixtures wrote `spreadsSequence = true`, `CallableCallItem.skipMissingValue` is written only `false` and read only by `requireCallableValues`, and `applyBuiltinResolved` and `requireCallableValues` have no referencer.
- **Retired (Lean).** `applyBuiltinResolved`, `requireCallableValues`, `expandSequenceSpreadBuiltinArguments` (the identity on every production supply), `ResolvedArgumentAlgorithm.spreadsSequence` / `.callable?` / `.invoked`, `CallableCallItem.skipMissingValue`, and the `callable?` of `PreparedSequenceBuiltinSuffixArg.algorithm`. `collectSequenceCallableCallItems` evaluates nothing, so it moved out of the `partial` block as a total definition (law `call_item_assembly_evaluates_nothing`); the spread arm of `formNeedSupplySourced` finds a known collector slice without allocating a cell (`spreadCollectorSlice?`). The `if(X*)` guards of `CoreTests/ParityGuards.lean` (issue #131) now run the written call through the whole evaluator instead of a spread-marked fixture.
- **Retired (C#).** `ExpandSequenceSpreadBuiltinArguments` and its async twin, `BuildCallableCallItemsAsync` (assembly evaluates nothing, so both engines share `BuildCallableCallItems`), `ResolvedArgumentAlgorithm.SpreadsSequence` / `Callable` / `InvokedAlgorithm` / `PreparedValue`, the write-only `VariadicCallItem.PreparedValue`, and `AlgorithmArg.Callable` / `InvokedAlgorithm`; `FormSpreadSupplySlot` finds a known collector slice without constructing a cell.
- **Unchanged.** Values, error categories, payloads, context frames, spans, evaluation order, cache hits, budget charges and sync/async outcomes: the 288-program cross-engine probe of the `reduce` section gives byte-identical observation matrices in both engines before and after.
- **Evidence corrected.** CALL-03 (C# and Lean supply formation; the call-item assembly), PROP-06 (the invoking slot), BOOL-05 (C# and Lean), HO-04 (Lean), LOOP-01 (Lean), and CALL-06 (a parameter read without a supplied cell reads its value binding, and with neither is `unknownName`; the bullet still described the algorithm-channel tier retired earlier the same day). After an independent review: PROP-05, HO-04 and Appendix A row H02 name `formNeedSupplySourced` for the builtin arm; BOOL-05's Lean demand is `demandNeed` through `evalArgumentValueCounted` (the `if` arm never calls `argumentNeed`); CALL-03's and LOOP-01's C# loop evidence says `EvalNeedLoop` demands its initial state itself only as a zero-iteration `repeat`'s final state (it demands the final state cells); and the claims that no argument was spread-marked are scoped to evaluator-built arguments.

## P3 reification and Constitution closeout — 2026-10-13

No issue classification changes and no rule text change; no Q, PV or X status changed (relabels are recommended to the owner only). Evidence: `../p3-reification-constitution-closeout/`.

- **Dead C# instrumentation retired.** `EvaluationObservations.RecordCountedArgumentReification` and its counter `CountedArgumentReificationCount` (internal; test-only readers) had no caller since Model C: `8f0ceb85` deleted `CountedArgAlgorithm`, the recorder's only caller, when an evaluated value became a Ready cell with no CALLABLE identity (NEED-06, Q-06). A compiled-IL scan of every current build (the library in each configuration, the CLI, DemoApp, the benchmarks, the parser fuzzer and the three test assemblies) found no caller, no reflection and no use by name; the 21 `Reifications == 0` assertions were vacuous. Removed with the test plumbing; the one theory whose only assertions read the counter became a dotted-equals-written charge-parity theory with optimizations off and on (every row runs the generic strategy), and a new theory, `OptimizedDotCalls_ChargeExactlyTheirWrittenCall`, covers the fused filter→count and planned-loop strategies, asserting which one ran and exact expression-work checkpoint parity with the generic run (Q-09b); `MaintainedDocumentationConsistencyTests.StaleShapes` rejects both names. Lean never had a counterpart.
- **CoreTests inventory recounted.** 2,230 `#guard` commands in the 45 modules `lean/CoreTests.lean` imports at `2581ab63` (2,172 and 2,195 were uncommitted intermediate states of `feb983a4`, which has 2,210): +15 parameter callee names, +20 `reduce` initial-accumulator report. The same FORMAL-07 list's other living counts were stale too and were recounted (112 `partial def`s; 344 = 326 + 18 laws; LanguageSpecCases 352 + 1 of 441 cases; SemanticExplorerCases 2,644 + 2), as were CALL-05's and HO-01's per-module counts; Appendix A rows P15, P18 and P33 and the § P header were corrected, and row P37 (`ParentScopeValidation.lean`) added. The counting scripts reproduce each earlier total that was recorded at a commit (1,953 at `fb7b5646`, 2,184 at `e5009f5c`); 406 = 376 + 30 theorem declarations and 2,172 and 2,195 `#guard`s were uncommitted intermediate states, and the former "108 `partial def`s", recorded beside three theorems, matches no commit of its time: none from 2026-09-04 to `2581ab63` has 108, and of all 210 commits that touched `lean/KatLang.lean` only two of 2026-05-04, with no theorems, do (`../p3-reification-constitution-closeout/logs/partial-defs-per-commit.txt`, `partial-defs-all-history.txt`).
- **Open items reconciled.** See the dated section at the end of `open-questions.md`: 32 documentation-fix items closed, 29 narrowed, 14 added; PV-35, X-43 and X-38 relabels recommended to the owner.
- **Follow-ups observed, not acted on.** (1) `Evaluator.ResultToExpr` and Lean `resultToExpr` have no evaluator caller since Model C (tests and a CoreTests fixture only), so `ResultToExprStructureExpansionCount` is recorded only by direct test calls; the dead `sharedMemo` branch and an orphaned duplicate summary in `Evaluator.Results.cs` go with them — a retirement candidate like this one. (2) Lean `lookupPropDefExportedAny?` has no caller (a leftover of exposure-based selection before K1-08). (3) Many evidence folders the six records cite are not on this machine (`artifacts/` is git-ignored, so no checkout carries them): 50 of the 87 distinct backticked `../` folders in the pre-edit records are absent, among them `q33-parser-boundary-investigation/` (33 citations) and `pre-release-question-rebaseline/` (22); so is `post-lifting-rebaseline/`, cited 73 times without the `../` prefix. (4) HO-01's rule sentence "Binding a callable demands nothing" lacks the plain-binder qualifier that CALL-06 and HO-04 carry (an inspecting pattern demands VALUE, NEED-04): a rule-text precision point for the owner. *(ResultToExpr retirement, 2026-10-13: (1) and (2) are done — the next section.)*

## ResultToExpr retirement — 2026-10-13

No issue classification changes and no rule text change; no Q, PV or X status changed. Evidence: `../retire-result-to-expr/`.

- **Retired (C#).** `Evaluator.ResultToExpr` (the internal entry and its private core, whose `sharedMemo` was always `null`), `ResultToExprLeaf`, `ResultToExprFrame`, `IsEmptySequenceChain`, the orphaned duplicate summary in `Evaluator.Results.cs`, and the internal test counter `EvaluationObservations.ResultToExprStructureExpansionCount` with its recorder. `8f0ceb85` (Model C) deleted `CountedArgAlgorithm`, the only production caller: an evaluated value is a Ready cell with no CALLABLE identity (NEED-06), never a rebuilt expression (Q-06). A compiled-IL scan of 42 assemblies (the library in Debug and Release and its copies beside the CLI, DemoApp, the benchmarks, the parser fuzzer and the test projects, and those assemblies themselves) found the cluster referenced only by itself and by `KatLang.Tests`.
- **Retired (Lean).** `resultToExpr` (its only user was the `CoreTests/SelectionValueBoundary.lean` fixture `filterCallbackUsesTheOrdinaryValueBoundary`, which now compares with the written list literal around the selected expression and checks that it denotes the expected value), `isEmptySequenceChain` (used by `resultToExpr` alone), and both `lookupPropDefExportedAny?` definitions: `6d7617e` added the list helper for exposure-filtered selection, and `b7e6ba1a` (2026-06-10) deleted its last callers, `lookupPropExportedAny` and `hasPropExportedAny`. The note on runtime "Algorithm adapters" no longer names the deleted `countedArgAlgorithm`.
- **Tests.** The direct-call tests of the conversion went with it; its four evaluations of a shared reified fragment moved to `SharedExprOccurrenceSemanticsTests` over a hand-built literal DAG; the source-level tests are `SharedValueGraphTransportTests`, without the counter's vacuous assertions.
- **Unchanged.** Every evaluation: the removed code ran in none. Lean kernel inventory 11,749 → 11,736 constants (exactly the retired definitions, their generated auxiliaries and one unshared matcher); the 602 audited theorems keep identical axiom sets; `#guard` lines 5,229 and `theorem` lines 537 before and after; both generated differential corpora untouched.
- **Records.** The two documentation-fix items of `open-questions.md` carry DONE records; dated notes on the draft's VAL depth note, RUN-01 and Coverage-table row Q39, on the follow-up list of the previous section, and on the two `6d7617e` steps of `decision-lineages.md`.

## Four owner decisions applied, 2026-10-13

Authority: the owner's explicit approval of 2026-10-13. This is Constitution-only implementation of established Model-C decisions; no Lean, C#, parser, public API, generator or language behavior changes.

- **PV-35 — RESOLVED BY DECISION (Model C).** Model C was adopted and implemented on 2026-10-02 (`8f0ceb85`); the owner-approved classification is recorded on 2026-10-13. The former eager VALUE read during callable transport disappeared: NEED-01/03/06/08 and RAND-01 govern plain binding, independent CALLABLE projection and first-demand effects. The original issue, lens verdict and historical evidence remain auditable.
- **X-43 — SUPERSEDED (Model C).** The algorithm-channel arity-payload carve-out disappeared with Model C on 2026-10-02 (`8f0ceb85`); classified 2026-10-13. Every supplied slot is one need cell and cardinality checks the complete supply before ordinary VALUE demand: `Inc(x) = x + 1` / `F(x, y) = x(y)` / `F(Inc)` reports `ArityMismatch(2, 1)`. The differential-observation question remains **Q-67 — OPEN**; its separately tracked documentation overclaims remain open.
- **X-38 — RESOLVED, effective 2026-10-02.** Q-15 option (c) and the Model-C implementation (`8f0ceb85`) established runtime rejection when the consumer demands the value; the canonical explanation and both generated blocks were corrected. The owner status classification is recorded on 2026-10-13. The separate documentation item that describes an explicit `A()` call as forwarding remains open under FWD-02; it is not part of X-38's original strict-value contradiction.
- **HO-01 — precision correction only.** Its plain-binding qualification and explicit inspecting-pattern reference agree with NEED-01, NEED-04, NEED-06, NEED-08, CALL-06 and HO-04. VALUE-demand behavior and demand order are unchanged.

Mechanically reconciled totals: PV 50 = 21 resolved violations + 21 resolved by decision + 6 intentional exceptions + 2 refuted (formerly 21/20/7/2); X 49 = 42 resolved + 2 superseded + 5 open (formerly 41/1/7). Q totals and all rule IDs, classes and statuses are unchanged. Q-66 and Q-67 remain OPEN. The five owner-gated documentation items (Q-65 lexical facts, Q-34 Math scope, Q-38 deconstruction `a()`, Q-63/Q-35 Lean load model, Q-14's optional hint) are unchanged.

The earlier P3 closeout recommendation and its unchanged-status statements are historical snapshots; this dated owner record supersedes only the three classifications and HO-01 precision point. Evidence, V0 checks, independent review and verified six-file pre/post backups: `artifacts/validation/constitution-four-owner-decisions/`.

The original GitHub issue classifications in this ledger remain unchanged; these are PV/X register classifications and a current-rule pointer correction.

## Five owner decisions implemented — 2026-10-13

Authority: explicit owner approval of 2026-10-13, plus the owner's subsequent choice to enforce the complete-line rule rather than retain the definition-body leading-comma exception.

- **Q-65 current rule (revised 2026-10-14):** Names remain exact case-sensitive ordinal strings; LF alone defines physical line breaks (CR is whitespace, so CRLF works); backslash is not continuation. Q-65 now adopts grammar-role-first newline priority: independent expressions/declarations win, otherwise ordinary syntactic continuation crosses LF. Leading comma continues its expression-list grammar, including definition/clause/deconstruction bodies. Unary minus and negative literal pattern signs require exact direct attachment; -2 is independent while - 2 can continue binary subtraction. Leading star can continue multiplication; a physical line-final star always announces multiplication, including EOF/declaration/later closer. Spread requires explicit same-line closure. Precedence and spread VALUE semantics are unchanged. The 2026-10-13 strict choice, initial restricted stage, star amendment, unary amendment and explicit pattern clarification remain auditable in decision-lineages.md. Evidence: artifacts/validation/q65-restricted-leading-continuation/. *(Issue #183, 2026-10-14: refined by owner decision, katlangorg/katlangnet#183 — a line-final star is classified by attachment: an attached `A*` is a spread that completes the expression, a detached `A *` is multiplication, EOF/declaration/later closer included; spread is closed by explicit same-line syntax or by the end of its line after an attached star. The sentence on line-final multiplication above records the superseded subrule)*
- **Q-34 — RESOLVED BY OWNER DECISION:** The C# native Math surface, its Expr.NativeCall bodies, random natives and lowercase aliases are C#-only by design, outside the current executable Lean model. Shared exact-integer operators and core builtins, values, binding and demand remain subject to Lean correspondence and FORMAL-04's common tier. Future native Math formalization requires a separate research decision; no exclusion or core test is weakened.
- **Q-38 — RESOLVED BY OWNER DECISION:** An explicit deconstruction-target call `a()` freshly invokes the target projection wrapper and bypasses a's own property-cache entry; the wrapper reads the separately cached shared RHS. It does not request fresh RHS evaluation. A first target call can cause the RHS's first demand. Successful source caching remains per run for exported sources and per owner activation for local-only sources, with Q-37 publication unchanged. C# may reuse its shared binding; Lean may rebind the same cached source.
- **Q-63 — RESOLVED BY OWNER DECISION:** Loading is implemented by C# frontend/hosting infrastructure. Lean retains concise descriptive prose and executable structural postElabInvariant predicates, without a complete executable load elaborator or a proof of C# loading. LoadError, LoadCtx and LoadPosition and their exclusively generated auxiliaries are retired after compiled dependency inspection. Definition/open entry contexts pass through transparent carriers; runtime positions refuse loading. Deferred and refused regions keep their separate C# rules. Q-35's load-prose subpart is settled as descriptive; its other front-end-sketch questions remain OPEN.
- **Q-14 optional hint — NOT_PLANNED for November 2026:** Q-14's semantic decision of 2026-10-01 remains RESOLVED. Its optional forwarding editor hint is NOT_PLANNED for the November 2026 release. This is a release feature disposition, not a permanent prohibition; future usability research may propose a separate feature. No diagnostics or editor behavior are added, and DiagnosticSeverity.Hint remains supported.

Current totals: 81 Q IDs: 52 resolved, 1 superseded, 2 partially resolved (Q-35, Q-44), 26 fully open (28 with an open part; 0 before release). PV: 50 total, 21 resolved violations, 21 resolved by decision, 6 intentional exceptions, 2 refuted. X: 49 total, 42 resolved, 2 superseded, 5 open. Former Q totals were 48 resolved, 1 superseded, 1 partial, 31 fully open (32 with an open part); only Q-34/Q-38/Q-63/Q-65 close and Q-35 becomes partial. Q-66/Q-67 remain OPEN, and all other questions and the previous four owner decisions are unchanged. The five P3 documentation dependencies are discharged by the approved dispositions; historical P3 and four-decision snapshots remain intact.

Validation level V3: final frozen serial .NET then all seven Lean targets, plus focused parser/deconstruction checks, isolated wrong-RHS mutation and compiled declaration/theorem/axiom inventories. Full results, independent review and verified six-file pre/post external backups are in `artifacts/validation/five-owner-decisions-closeout/`. No staging, commit or publishing is authorized.

Historical GitHub-issue classifications remain unchanged; this record supersedes only the current owner questions and matching documentation dependencies.

## Q-65 owner revision — 2026-10-14 (Europe/Riga)

Names remain exact case-sensitive ordinal strings; LF alone defines physical line breaks (CR is whitespace, so CRLF works); backslash is not continuation. Q-65 now adopts grammar-role-first newline priority: independent expressions/declarations win, otherwise ordinary syntactic continuation crosses LF. Leading comma continues its expression-list grammar, including definition/clause/deconstruction bodies. Unary minus and negative literal pattern signs require exact direct attachment; -2 is independent while - 2 can continue binary subtraction. Leading star can continue multiplication; a physical line-final star always announces multiplication, including EOF/declaration/later closer. Spread requires explicit same-line closure. Precedence and spread VALUE semantics are unchanged. The 2026-10-13 strict choice, initial restricted stage, star amendment, unary amendment and explicit pattern clarification remain auditable in decision-lineages.md. Evidence: artifacts/validation/q65-restricted-leading-continuation/.

Q-34, Q-38, Q-63 and Q-14 keep their 2026-10-13 dispositions. Q-66/Q-67 remain OPEN; earlier PV-35/X-43/X-38/HO-01 decisions remain intact. Totals remain Q81 = 52 resolved + 1 superseded + 2 partial + 26 fully open (28 open parts, zero before release); PV50 = 21 resolved violations + 21 resolved by decision + 6 intentional + 2 refuted; X49 = 42 resolved + 2 superseded + 5 open. No rule ID is added or retired. Previous dated records are retained as history, with conflicting current subrules superseded by this entry.

## Independent combined R3′ / internal-join review — 2026-10-14 (Europe/Riga)

Reviewed range: `18a81a1568da342b681826178e6454f1da1774b9 .. 37fdf5916a11199a7a859e87ca1800fa81918e41` (R3′ `a366f888304f1522f2ee6632740401555c6698e4` and the following internal-join fix). No production or proof correction. Evidence-quality repair: replaying a join spread leaf twice survived the original C# containment/async-dispatch tests and Lean guards. `SequenceConstructSpreadReviewTests` now uses fresh explicit host calls, a deterministic async suspension gate and twice-written controls; `CoreTests.RepeatedSpread.joinSpreadLeafEvaluatesItsOperandOnce` counts fresh call binding contexts with a twice-written control. These kill duplicate evaluation in Lean, sync C# and async C#. Independent one-to-three-layer shapes, positioned output-less property failures after suspension, and exact join reservation/work-checkpoint parity are also pinned. CoreTests now has **2,238** `#guard` lines in the same 46 imported modules (formerly 2,237); generated corpora and theorem counts are unchanged. Earlier dated evidence and counts remain historical snapshots.

**Q-66 remains OPEN.** Item 4 has algebra-level and real-`Result` total-value-operation proofs; arbitrary evaluator equivalence, including errors/resources, is still unproved. The join consumes the spread's represented supply without applying another reopening layer. The existing join-fixture documentation item remains open for `reduceStructuralAppendAlg242` and `boundaryAtomsArg`; their values are unaffected, and this review does not replace those fixtures. Q/PV/X totals remain 81 (52 resolved, 1 superseded, 2 partial, 26 fully open), 50 (21 resolved violations, 21 resolved by decision, 6 intentional exceptions, 2 refuted), and 49 (42 resolved, 2 superseded, 5 open). No rule ID, normative rule, owner decision or status changes. Evidence and fresh validation: `../independent-r3-sc-review/`.

## Q-65 owner refinement: line-final star attachment (issue #183) — 2026-10-14 (Europe/Riga)

Owner decision: GitHub issue katlangorg/katlangnet#183 ("Follow-up design decision: newline continuation and attachment-sensitive `*`"), approved 2026-10-14. Canonical newline rule: "Newlines separate complete expressions by default. An incomplete expression continues when valid syntax permits it, without consuming a new declaration. Otherwise, an independent expression or declaration begins a new construct. Syntax that cannot stand alone but can legally continue the preceding expression attaches backward. All decisions are syntactic, never based on evaluated values." Star refinement: when `*` follows a completed expression and is the final significant token on its physical line — EOF included, across trailing comments and blank lines — attachment determines its role: an attached `expr*` is postfix spreading and completes the expression; a detached `expr *` is binary multiplication, leaves the expression incomplete and requires a right operand. With a same-line operand, multiplication stays whitespace-insensitive; explicitly closed spreads are unchanged; `F(A *)` stays InvalidSpreadMarker. Consequences: `A = 1, 2, 3` newline `A*` emits three rows; `A*` newline `B` is two rows and `A *` newline `B` multiplies; `A*` newline `B = 5` is a spread then a declaration, while `A *` newline `B = 5` is a missing operand with the declaration preserved; `A*` newline `-2` is two rows and `A *` newline `-2` is `A * -2`; `A**` at EOF is two spread layers; `7*` at EOF spreads the scalar 7; `X = A*` newline `X` is the spread definition and the row `X`; `A*` newline `.F` is the fluent `F(A*)` and `A*` newline `+ B` is MisplacedSpread. The classification is exclusively syntactic (exact source adjacency, `Parser.IsDirectlyAttached`); the owner explicitly rejected evaluating multiplication and falling back to spread.

Superseded current subrules (retained as dated history — annotated in place, except SYN-11, whose rewritten text is retained verbatim in decision-lineages.md under this heading): the Q-65 subrule of 2026-10-14 "a physical line-final star always announces multiplication, including EOF/declaration/later closer. Spread requires explicit same-line closure."; SYN-11's "EOF is not a spread boundary" and "Root-final bare `Values*` is intentionally no longer valid"; SYN-12's "Attachment is checked after classification. It never influences SYN-11's decision." (now limited to stars with a same-line follower); A22's "Whitespace never turns one valid operation into another." (now limited to one physical line). This adopts, by owner decision, the attached/detached newline rule of #140 (reversed by #161, rejected as Q-33's P4A). Q-33, Q-65 and #161 remain resolved/current in their surviving parts, and no new numbered question is created.

Implementation: C#-only surface syntax. The one classifier `Parser.IsPostfixSpreadMarkerStar` returns `IsDirectlyAttached(Previous, star)` for a line-final star and is now a non-inlined leaf; the detached spread-marker recovery run stays on one physical line; the line-final continuation diagnostic, the missing-operand message after `*` and the `InvalidSpreadMarker` wording name the attachment repair. No Lean production rule, theorem or guard changes; `lean/LanguageSpecCases.lean` and the generated generator-prompt blocks are regenerated from the canonical corpus (new case `line-final-star-attached-at-eof-is-spread`; `star-before-operand-row-is-multiplication`, `line-final-star-in-definition-continues` and `line-final-star-at-eof-is-incomplete` now spell their detached star explicitly). Pins: `LineFinalStarAttachmentTests` plus the migrated `LineFinalStarLawTests`, `LineFinalStarPriorityTests`, `StarSyntaxTests`, `MarkerAttachmentTests`, `DeclarationHeadLineRuleTests` and neighbors; `MaintainedDocumentationConsistencyTests` pins the canonical rule in AGENTS.md, `syntax.md` and `tutorial.md`.

Totals remain Q81 = 52 resolved + 1 superseded + 2 partial + 26 fully open (28 open parts, zero before release); PV50 = 21 resolved violations + 21 resolved by decision + 6 intentional + 2 refuted; X49 = 42 resolved + 2 superseded + 5 open. No rule ID is added or retired. Evidence: `artifacts/validation/line-final-star-attachment/`.


## Q-67 completed — 2026-10-15

Authority: the approved Q-67 implementation task explicitly preserves FORMAL-06 and authorizes testing/documentation repairs and Constitution reconciliation. No new language rule or error-message contract is adopted. No Lean/C# evaluator semantic change was needed; the historical X-43 complete-supply error remains ArityMismatch(2,1).

Disposition: items 1, 2, 3, 5 and 6 are **Completed**; item 4 is **Completed by existing evidence**. The complete six-item table is in the resolved Q-67 entry of open-questions.md and `q67-differential-observations/07-documentation-and-constitution.md`.

Verification: final frozen `pwsh -NoProfile -File ./scripts/validate-all.ps1 -Phase All` exits 0; build zero warnings/errors; core 36,368, CLI 342, public API 133, zero failures/skips; all seven Lean targets pass and both phases preserve repository state. Eighteen completed behavioral mutants killed (16 C#, 2 Lean); one aborted broad order attempt is explicitly excluded, with a completed finite replacement. The first V3 attempt's new-test provenance violation was repaired using SourceProvenance.ParseValid and the focused guard passed before the successful final retry. Logs and exact restoration evidence are in `artifacts/validation/q67-differential-observations/`.

Scope: selected expected/actual counts, names, exposure kind and fieldless tags are supplementary differential evidence. Messages, spans, context arrays, diagnostic codes, rendered object/provider/branch descriptions, display and C# host budgets remain outside Lean's required neutral observation. Projection goldens are not evaluator executions; one-sided heap/host-effect tests are not a shared trace proof. R3–R7 and Q-66 are unchanged.

Current Q totals: 81 = 53 resolved + 1 superseded + 2 partial + 25 fully open (27 open parts, zero before release). PV 50 = 21 resolved violations + 21 resolved by decision + 6 intentional exceptions + 2 refuted. X 49 = 42 resolved + 2 superseded + 5 open. All rule IDs and unrelated decisions/classifications are preserved. Pre/post six-record external ZIP backups are independently restored and SHA256-verified; encoding, BOM and line endings are preserved.

## R3 binder demand-order proofs — 2026-10-15 (Europe/Riga)

Authority: the approved R3 implementation task (Option B′: a generic-monad production binder with explicit effect capabilities). Formal-evidence strengthening only: no owner decision, no rule text, ID, class or status change, no Q/PV/X status change, no observable behaviour change, no C# change.

Change: `lean/KatLang.lean`'s binder and dispatcher are one generic core (`NeedBinder` over `NeedCapabilities`); the production names are its `EvalM` specializations (definitional, § The generic binder core of `KatLangArityLaws.lean`). Preservation: kernel proofs that a verbatim copy of the HEAD 091ddca4 binder block equals the new production binder and dispatcher for every input (complete `EvalM` computations), and a 22,464-run executable old/new comparison (21,312 binder and 1,152 dispatcher runs) with zero mismatches (evidence only). Proofs: `KatLangArityLaws/BinderTrace.lean` (68 theorems), `KatLangArityLaws/FamilyDispatch.lean` (25 theorems) and `KatLangArityLaws/BinderCorrespondence.lean` (63 theorems), built by the `KatLangArityLaws` target — trace erasure for every lifted capability record, state and prefix; the syntax-indexed event schedule; ordering, silence of plain non-repeated bindings, repeated-name order and verdict, first-failure and production-allocation laws; family search precedence, exhaustive outcomes, arbitrary-context activation and the end-to-end dispatcher; channel substitution per channel and its static form (invocations only on cells at inspecting positions or on cells the run allocated; its production use needs the source fact that `demandNeed`'s heap never reuses a supplied cell) and the family/ordinary mode correspondence for every head (the modes differ only where the ordinary binding raises an incompatibility error; a literal-free head's ordinary binding is never a non-match; errors are classified by value, so "non-match iff incompatibility" holds in that one direction) — the FORMAL-07 roadmap's R3 obligations (b) and (c) in these precise forms; two counterexamples show the protection hypothesis is necessary. 48 executable guards. Every new or adapted theorem's `#print axioms` lists only propext, Quot.sound and Classical.choice.

Naming: "R3" is the FORMAL-07 roadmap's demand-order item (`formal07-research/formalization-roadmap.md`). The roadmap's own "R3′" (binder-helper totalization) remains open; the 2026-10-14 "R3′" in these records is the repeated-spread work, which reused the label.

Not proved: Q-28's permutation laws (R4), the opaque helpers' outcomes, `demandNeed`, supply formation, the `partial` callers, C#. FORMAL-06 unchanged; Q-66 stays OPEN with its six items unchanged.

Records changed: draft (banner, FORMAL-07 sentence and count, PAT-10 Lean evidence, Model-C annex note, Appendix A O07/O14 notes), summary (banner, FORMAL-07 sentence and count), open-questions (banner, Q-66 note), decision-lineages (retained prior text), issue-ledger and this log. Pre-change backups external to the repository, SHA-256-verified; LF line endings and the absent BOM preserved. Totals unchanged: Q81 = 53 resolved + 1 superseded + 2 partial + 25 fully open (27 open parts); PV50 = 21 + 21 + 6 + 2; X49 = 42 + 2 + 5.

## R5 total supply and collector-demand control — 2026-10-15

Evidence update for NEED-01, NEED-02, NEED-07, NEED-08, FWD-01 and FORMAL-07;
no frozen language rule or question status changes. This dated entry supersedes earlier
claims that *all* supply/materialization/completion control is only executable evidence.
The old statements remain historical evidence of the pre-R5 boundary.

The approved A2+B2 extraction is implemented in the authoritative `lean/KatLang.lean`:
`NeedSupply.slot`/`form` are one total EvalM supply core (only computed-spread evaluation
is injected), and `NeedDemand.materialize`/`suspendedValue`/`step` are total collector
sequencing and completion control. The total public `formNeedSupplySourced`,
`formNeedSupply` and `demandNeed` specialize those helpers by definition. Partial evaluator
call sites install the same formation core; the one recursive `demandNeedRecursive`
driver installs the same completion shell. That recursive connection is source/guard
evidence, not a kernel unfolding theorem about the partial driver.

`lean/KatLangArityLaws/NeedControl.lean` proves actual-helper address/source retention,
ordinary transport and fallback, exact known-slice reopening (including duplicates),
whole-written computed-spread Ready allocation, formation ordering and failure truncation,
the address projection, exact eager-list collector materialization, ordered VALUE demands,
first-error state retention, completed outcome reuse and qualified current-cell publication.
Publication preserves the latest CALLABLE cache; its address must still be present.
Local allocation freshness and backward-reference validity have explicit initial-validity
premises. Conditional whole-list heap-size laws retain their callback/slot nonshrinking
premises; heap size alone does not preserve suspension identity or ownership.

Kernel theorems, source-exact migration comparison and finite executable observations are
separate evidence in `artifacts/validation/r5-implementation/REPORT.md`, `THEOREMS.md` and
their reproducible logs. The maintained guards include malformed-state counterexamples.
R3's generic binder, trace erasure, substitution, mode correspondence and dispatcher proofs
are preserved. R5 does not prove C# behavior, host concurrency/cancellation, arbitrary
expression evaluation, whole-run heap refinement or acyclicity of expression dependencies.
FORMAL-06 remains unchanged. Q-66 remains OPEN; R6, R7, the whole-run heap bridge and
the other separate Q-66 obligations remain open. No R6 implementation is included.
