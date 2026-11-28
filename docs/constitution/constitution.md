# KatLang Semantic Constitution

**Status: draft for human review. This document is not authoritative in itself.**

> **Q-57, the position of `xor` on the precedence ladder — 2026-11-28 (ONE owner decision, made on 2026-11-27 and recorded from the brief of the task that records it; OP-01's *Open Q-57* note becomes a dated *Resolved* note, the rationale bullet and one qualification are added and one example is added, and its law-index marker keeps only *C#-only*, in step with `constitution-summary.md`; no law title changed, no law added, retired or renumbered; ONE registry status change, Q-57 RESOLVED BY DECISION; no change in the grammar, Lean or C#; no program was run; uncommitted over `main` @ `a11ad7fa`):** the owner confirmed the Boolean order `or` < `xor` < `and`, from loosest to tightest, and adopted its rationale. `xor` binds less tightly than `and` so each side of an exclusive choice can express a conjunction. It binds more tightly than `or` so the whole exclusive choice can serve as one alternative in a larger disjunction. The rationale dates from 2026-11-27; the original reason for the parser's ordering was undocumented. The decision concerns grouping only. Issue #202 and BOOL-04 govern evaluation separately: `and` and `or` short-circuit, and `xor` needs both Boolean operands. Each boundary is observable: `true or false xor true` is `true or (false xor true)`, and `true xor true and false` is `true xor (true and false)`; both are `true`, and each would be `false` under the other grouping. The grammar (`KatLang.ebnf`: `OrExpr`, `XorExpr`, `AndExpr`), the parser's table (`Parser.BinaryOperatorPrecedence`) and the parse-tree test `ComparisonChainParserTests.PairwisePrecedenceContract_EveryOperatorPairParsesAsTheLadderPrescribes` already state the confirmed order, so only the records change. The registry entry, its history and the recount are in `open-questions.md`; the lineage is `decision-lineages.md` § Q-57.

> **Q-51, a written spread right-hand side of assignment deconstruction — 2026-11-28 (ONE owner decision, recorded from the brief of the task that records it; VAR-05's *Open Q-51* note becomes a dated *Resolved* note, one bullet is restated and two examples are added, and its law-index marker is cleared in step with `constitution-summary.md`; no law added, retired or renumbered; ONE registry status change, Q-51 RESOLVED BY DECISION; no change in Lean or C#; uncommitted over `main` @ `1708b36f`):** the owner decided that the behavior Q-51 asked about is intended. Assignment deconstruction captures the right-hand side's output rows into one value by ordinary capture (SUP-06). A written spread contributes its immediate items to that capture, and when it contributes the only item, capture returns that item itself. Deconstruction then opens the captured value one level (VAR-05). With `Points = [(10, 20)]`, `x, y = Points*` binds `10` and `20`, as `Point = Points*` / `x, y = Point` does; `x, y = Points` is `ArityMismatch`, because the outer list holds one point for two targets; and with `Points = [(10, 20), (30, 40)]` each target binds a whole pair. Lean and C# already behave so, and existing pins cover it. SUP-03's qualification already stated this and is unchanged. VAR-05 keeps *Open Q-84*, the independent question about argument views. The registry entry, its history and the recount are in `open-questions.md`; the lineage is `decision-lineages.md` § Q-51.

> **Returned callables across detached reads (EXPORTED-DETACHED, formal ledger rows E-22 and R-1) — 2026-11-27 (ONE owner decision recorded from the brief of the task that implements it, Lean first: the expected outcome — a correctly classified returned callable keeps its value in both row orders — and the change of the detachment contract it needs; PROP-08's enforcement bullet, its retained-cell reuse bullet and its host contract restated, one sentence of a RES-08 bullet restated; no law added, retired or renumbered; no Q, PV or X status change, Q-59 stays OPEN; uncommitted over `main` @ `024da438`):** an exported evaluation is detached from its ENCLOSING CALLS — the activations of the levels that enclose the property being evaluated and exist when it starts — and no longer from every activation that exists then. With `Cap(meta r) = r`, `Build(z) = { G(x) = x + z ⏎ Cap(G(0)) }`, `B = Build(5).Algorithm` and `Observe = B(1) + 0`, with both readers classified exported by the front end, `B(2), Observe` is `(7, 6)` and `Observe, B(2)` is `(6, 7)`, at the root and inside a call; until this change the first order was `UnknownName(z)`, because the row had established `B` first and `Build`'s activation — the returned callable's own, enclosing no call around `Observe` — existed when `Observe` started. An enclosing call's input is still refused: a callable that also reads `F`'s `y`, forced exported, is `UnknownName(y)` in both orders, and a falsely exported member declared in `Build` and read through the callable is `UnknownName(z)`. A retained runtime-alias cell keeps every read of its computation and refuses its reuse exactly to a reader that detaches one of them. Demanding a lazy position in the returned callable uses the same ownership test (`evaluator-and-hosting.md` § Detached evaluation of exported properties, "Returned callables"; HP-23a…n, compared with Lean).

> **Demand-driven evaluation: short-circuit `and`/`or` (#202), lazy `reduce` accumulators (#203), lazy collections and pipelines (#204) — 2026-11-26 (reconciliation with language changes already landed on `main`; three owner decisions recorded from the record — issues #202, #203 and #204, closed on 2026-11-23 by `65b1b136`, `66ebae56` and `108268c7` — and none made here; five law titles changed (BOOL-04, OP-03, SEQ-02, VAR-03, COLL-04), no law added, retired or renumbered; ONE registry narrowing, Q-57, which keeps only its `xor`-tier part and stays OPEN; no Q, PV or X status change; uncommitted over `main` @ `c9116ed6`):** the Constitution still stated the evaluation order these three changes replaced. **(1) #202.** `and` and `or` evaluate their left operand once and require a Boolean before anything else, and evaluate the right operand only when the left one does not decide (`false and _`, `true or _`); a skipped operand has no effect, failure, value-kind check, charge or demand, and is still elaborated. `xor` stays eager, and comparison chains are unchanged. BOOL-04 is restated under a new title and loses its *Open Q-57* marker; BOOL-02, OP-03, COLL-09, NEED-03, VAL-10, RUN-08, RAND-01 and the BOOLCMP preamble are amended. **(2) #203.** `reduce` demands its collection whole and then only its last step; each accumulator is a deferred VALUE-only cell evaluated at most once, so `reduce([a, b], R, i)` is `R(b, R(a, i))` for VALUE demand of its accumulators, with the top-level elements evaluated first; an empty fold demands `initial` once. HO-02, HO-03, HO-04, CALL-03, CALL-06, COLL-02, PAR-01, VAR-03, VAL-10, RUN-03, RUN-08 and RAND-01 are amended. **(3) #204.** A list is a finite collection of positions: a list literal defers its ordinary elements, `map`, `filter` and `take` build stages over their source's positions, and each consumer reads only what it needs, while equality, `contains`, `distinct`, a repeated name, `atoms`, the run's output, the engine's named top-level reads and host-operation arguments read whole values, and a collecting binding's VALUE stays eager. SEQ-02 and COLL-04 are restated under new titles; the SEQ preamble, SEQ-03, SEQ-04, SEQ-05, SUP-01, SUP-02, SUP-06, VAL-07, VAL-10, NEED-03, NEED-04, NEED-06, NEED-07, NEED-08, VAR-03, VAR-05, CMP-03, PAT-07, PAT-08, CALL-03, COLL-02, COLL-03, COLL-07, COLL-08, COLL-10, HO-02, HO-03, HO-04, RUN-01, RUN-03, RUN-05, RUN-07 (new item (g)), RUN-08, RAND-01, FORMAL-02 and FORMAL-07 are amended, the last two with the revised premises of formal ledger row E-24. NEED-07's sentence "No shape-only count, lazy list node or lazy element rule exists" had also been stale since the selective observers of a retained collector (`772d936e`, 2026-11-07); the bullet now states them. Stale examples were replaced by pinned witnesses or recomputed against them. PROP-08's retained-cell law (formal ledger row R-1, QUALIFIED) already covered lazy positions and is unchanged. `constitution-summary.md` mirrors the five titles and the marker; `open-questions.md` (Q-57), `decision-lineages.md`, `issue-ledger.md` and `constitution-review-log.md` carry their own dated notes. Evidence: the issues and commits above; `docs/design/language-rules/evaluator-and-hosting.md` § Boolean values and § Limits observe a run; `sequences-lists-and-calls.md` § Collection builtins, § Callback results, § Lazy `reduce` accumulators and § Lazy collections and pipelines; `call-by-need.md` § NEED-04 and § NEED-07; `dotnet/src/KatLang/SEMANTIC-ALIGNMENT.md`; `docs/design/formal-correspondence-ledger.md` rows E-19 and E-24; `lean/KatLang.lean` (`BinaryOp.leftOperandDecides`, `EvalBody.evalBinaryCounted`, `EvalBody.evalReduceCounted`, § Lazy collections, `evalRunValue`); the conformance cases of `conformance/features/` named in the laws (`logical-*`, `hunt-logical-xor-operands-both-evaluated`, `reduce-*`, `lazy-*`, `map-reads-each-source-position-before-its-transform`, `hunt-builtin-map-callbacks-run-in-collection-order`, `selective-collector-*`); `ShortCircuitLogicalOperatorTests`, `LazyReduceAccumulatorTests`, `StreamedReduceFoldEquivalenceTests`, `CallbackResultBoundaryTests`, `LazyCollectionTests`, `OutputLessArgumentBlameTests` and `PropertyObservationPositionReadTests`; and the lineages [#202](decision-lineages.md#202--and-and-or-short-circuit-owner-decision-issue-202-november-2026--recorded-2026-11-26-by-the-demand-driven-evaluation-reconciliation), [#203](decision-lineages.md#203--reduce-evaluates-its-accumulators-on-demand-owner-decision-issue-203-november-2026--recorded-2026-11-26-by-the-demand-driven-evaluation-reconciliation) and [#204](decision-lineages.md#204--lists-and-their-pipelines-are-evaluated-on-demand-owner-decision-issue-204-november-2026--recorded-2026-11-26-by-the-demand-driven-evaluation-reconciliation).

> **Retained runtime-alias cells, the `open` route (formal ledger row R-1 QUALIFIED) — 2026-11-26 (narrowing of the qualification in the repair note below, from the brief of the task that implements it; PROP-08's retained-cell bullet and its host contract restated again; no owner decision is made here; no Q, PV or X status change, Q-59 stays OPEN; uncommitted over `main` @ `5777c440`):** the ADMITTED ACCESS OF A LOCAL-ONLY MEMBER THAT AN `open` PROVIDES is an input read of the retained cell whose computation makes it, like a dot access or a static alias path step: the access uses the owner's activation whether or not the member's body reads the owner's parameter. The lexical lookup is unchanged — the same selection, the same provider order, a state-free judgment that only reports the admission — and the evaluation that USES the selected member (a callee or a supplied name's projection, a value read, a receiver head, an alias's static step or route decision) records it, with the open route's own refusal. With `Cap(meta r) = r` and `F(y) = { open Box ⏎ Box = { public G(x) = if(true, x + 1, y + 0) } ⏎ A = Cap(G(0)).Algorithm ⏎ P = A(5) + 0 ⏎ A(5), P }`, `F(1)` is `(6, 6)` as classified in both row orders; with `P` alone declared exported it is `LocalOnlyProperty` for `A` when the row reads `A` first and `LocalOnlyProperty` for `G` of `Box` — at the row's `G`, as `P`'s own use of `G` is refused — when `P` reads it first (until this change neither order was refused). ROW R-1 STAYS QUALIFIED: the member steps of an `open` TARGET's path (`open Box.Sub`, or `open L` with `L = Box.Sub`) are checked when the level's opens are resolved, for every lookup that consults the level, and are not recorded, so a falsely exported property that reuses a cell whose computation selected a name through a local-only target step is not refused (no wrong value is known). Independent review found two C# paths that recorded an unused selection. Preparing an unused alias argument and planning a row skipped by a false `while` flag now leave the cell shareable in both row orders. The law identifiers and headings are unchanged, so `constitution-summary.md` and `open-questions.md` are unchanged. Evidence: `lean/KatLang.lean` (`ResolvedProperty.openRefusal`, `lookupOpenProperties`, `noteOpenAccess`, `lookupLexicalPropertyNoted`, `noteOpenAccess_unmarked`, `lookupLexicalPropertyNoted_unmarked`), `DetachedExportedEvaluationTests` § 5c (`R1_AnOpenProvidedLocalOnlyMember_IsRefusedInBothRowOrders` and its neighbours, on the optimized, generic, async and genuinely suspending routes; `R1_AnOpenTargetsLocalOnlyPathStep_IsNotRecorded_OpenTargetQualification`), HP-20a…i of `HostParentDifferentialCorpus` (compared with Lean), `docs/design/formal-correspondence-ledger.md` rows R-1 and E-22, `docs/design/language-rules/evaluator-and-hosting.md` § Detached evaluation of exported properties ("Retained runtime-alias cells"), and the [lineage of that date](decision-lineages.md#r-1--the-open-route-an-open-provided-members-access-is-recorded-where-its-selection-is-consumed-november-2026--recorded-2026-11-26-by-the-task-that-implements-it).

> **Retained runtime-alias cells, repair (formal ledger row R-1 QUALIFIED) — 2026-11-24 (correction and qualification of the note below, from the independent review `050804fe` of that change and the owner's repair brief; PROP-08's bullets on retained cells and its host contract restated again, one sentence of a RES-08 bullet restated again; ONE owner decision recorded from the brief, none made here; no Q, PV or X status change, Q-59 stays OPEN; uncommitted over `main` @ `c1549957`):** four corrections to the note below. (1) THE REUSE IS JUDGED BEFORE THE CHANNEL RUNS: a reuse of a retained cell's value or callable by an evaluation that detaches an input the cell is KNOWN to have read is refused with `LocalOnlyProperty` naming the alias (the cell is a binding of an enclosing call), and nothing of the cell runs — no demand, no effect, no work; it is not judged after the channel answered and does not report the recorded read's own refusal. A read of an unavailable captured parameter made directly still reports `UnknownName`. (2) OWNER DECISION (2026-11-24, from the repair brief): THE DEMAND DECIDES — a detached reader may count a lazy list without restricting a later attached reader. An input read the cell's computation makes is refused at the read exactly when a detached evaluation that detaches the read's activation is being served and the read is an input of a cell that admitted such a reader; a read an attached reader demands afterwards uses its own inputs. With `F(y) = { Mk(v) = { Z(*xs) = [1, 2].map{ n + y } ⏎ Cap(Z()) } ⏎ A = Mk(5).Algorithm ⏎ P = A.count + 0 ⏎ A.count, P, A[1] }` and `P` alone declared exported, `F(1)` is `(2, 2, 3)`, and also with the rows `P, A.count, A[1]`; a detached `P` that itself demands an element whose calculation needs `y` is refused. (3) An ADMITTED ACCESS OF A LOCAL-ONLY MEMBER by a dot access or a static alias path step is an input read, whether or not the member's body reads its owner's parameter. (4) A read through an activation the cell's own computation recorded is the cell's own work and an input of no cell, so a correctly classified program keeps its freshly owned inputs. The review's witness `F(y) = { A = Sel(y).Algorithm ⏎ P = A(5) + 0 ⏎ A(5), P }` with `Cap(meta r) = r`, `Inc(n) = n + 1`, `Dbl(n) = n * 2` and `Sel(k) = if(k == 1, Cap(Inc(0)), Cap(Dbl(0)))` is `((6, 6), (10, 10))` as classified; with `P` alone declared exported it is `LocalOnlyProperty` for `A` when the row reads `A` first and `UnknownName(y)` when `P` reads it first. ROW R-1 IS QUALIFIED, NOT CLOSED: the admitted access of an `open`-provided local-only member is not recorded on the cell, so a falsely exported property that reuses a cell whose computation used such a member is not refused (no wrong value is known); and the repair awaits its own independent review. The law identifiers and headings are unchanged, so `constitution-summary.md` and `open-questions.md` are unchanged. Evidence: `lean/KatLang.lean` (`CellInputs`, `CellRecords`, `noteCellInput`, `noteMemberAccess`, `lateRefused`, `servingDetached`, `CellInputs.admit`, `judgeRetainedCellReuse`, `reuseRetainedCell`, `EvalCtx.reattach`), `lean/KatLangArityLaws/RetainedCellReuse.lean`, `DetachedExportedEvaluationTests` § 5c, HP-19a…z and HP-20a…b of `HostParentDifferentialCorpus` (compared with Lean), `docs/design/formal-correspondence-ledger.md` rows R-1 and E-22, `docs/design/language-rules/evaluator-and-hosting.md` § Detached evaluation of exported properties ("Retained runtime-alias cells"), and the [review findings and regression cases](decision-lineages.md#r-1-review-evidence). *(2026-11-26: the admitted access of an `open`-provided local-only member IS recorded now — where the selection is consumed — and row R-1 stays qualified for the path step of an `open` target; see the note of that date and PROP-08.)*

> **Retained runtime-alias cells (formal ledger row R-1 closed) — 2026-11-24 (reconciliation with the evaluator change of November 2026 that closes row R-1, from the brief of the task that implements it; PROP-08's bullet on retained cells and its host contract restated, one sentence of a RES-08 bullet restated; no Q, PV or X status change; no owner decision is made here; uncommitted over `main` @ `c1549957`):** a RETAINED runtime-alias binding cell — the cell of any non-parameter alias row — records the input reads of its computation through the activations that existed when it was established (its captured parameter operations, its admitted local-only property reads and the recorded reads of a cell it reuses), and a reuse of its value or callable by an evaluation in which one of those activations is detached is refused with that read's refusal, whichever read established the cell; any other reader shares the cell and is admitted, and a read the computation makes later (a lazy position, a captured call's argument) below an admitted reader's watermark is refused at that read. The review's witness `F(y) = { A = Sel(y).Algorithm ⏎ P = A(5) + 0 ⏎ A(5), P }` is `((6, 6), (10, 10))` as classified and `UnknownName(y)` in either row order when `P` alone is declared exported; independent and freshly owned cells are shared exactly as before. The law identifiers and headings are unchanged, so `constitution-summary.md` and `open-questions.md` are unchanged. Evidence: `lean/KatLang.lean` (`CellInputs`, `noteCellInput`, `lateRefused`, `CellInputs.admit`, `judgeRetainedCellReuse`, `reuseRetainedCell`), `lean/KatLangArityLaws/RetainedCellReuse.lean`, `DetachedExportedEvaluationTests` § 5c, HP-19a…n of `HostParentDifferentialCorpus` (compared with Lean), `docs/design/formal-correspondence-ledger.md` rows R-1 and E-22, `docs/design/language-rules/evaluator-and-hosting.md` § Detached evaluation of exported properties ("Retained runtime-alias cells"), `artifacts/validation/r1-alias-dependence/`. *(2026-11-24, the same day, after the independent review `050804fe`: CORRECTED AND QUALIFIED by the note above — the reuse is judged before the channel runs and reports `LocalOnlyProperty` for the alias, the demand decides for the reads that follow, an admitted local-only member access is an input read, and row R-1 is qualified, not closed.)*

> **Inner-property lifetime (INNER-PROPERTY LIFETIME) — 2026-11-21 (owner decision recorded from the follow-up brief of EXPORTED-DETACHED, its second delta; PROP-04 and PROP-08 restated with their headings, the PROP family heading, one bullet of the deconstruction evaluation rule, one RES-08 cross-reference and PROP-08's R-1 bullet restated, three PROP-08 examples recomputed; no Q, PV or X status change, Q-59 stays OPEN; uncommitted over `main` @ `5ae82403`):** STORAGE FOLLOWS THE RESOLVED DECLARING BINDING AND ITS OWNING INVOCATION, never the exposure. Every actual call of an owner — a user call, a selected clause, a loop round, an explicit zero-supply `B()` — has fresh bindings for the properties and runtime aliases declared under it, whether or not their definitions use the call's arguments; reads inside one owning invocation share them, and no callback, helper, open or referring caller starts a new lifetime; the name `A` and the path `F.A` are one binding when they resolve to the same active one; outside every call of the owner bare `F.A` is the separate run-scoped binding, and `F.A()` there is fresh, may establish the empty outside entry and never reads or replaces an established one. Exposure still decides accessibility (RES-08) and detachment. Until this decision an exported property had one value per run, shared by every call of its owner. The headings of PROP-04, PROP-08 and the PROP family change, so `constitution-summary.md` changes with them; `open-questions.md` is unchanged. Evidence: `lean/KatLang.lean` (`EvalCtx.enteringInvocation`, `ParameterActivation.ownsInvocation`, `propertyOwnerInvocation`, `propertyKeyBindingContext`), `lean/KatLangArityLaws/InnerPropertyLifetime.lean`, `InnerPropertyLifetimeTests` (the acceptance witnesses on the optimized, generic and async routes), the `inner-property-lifetime-*` and `runtime-alias-cell-*` cases of `LanguageSpecCorpus` (compared with Lean), `RuntimeAliasCellLifetimeTests`, `docs/design/formal-correspondence-ledger.md` rows E-23, E-20 and R-1, `docs/design/language-rules/evaluator-and-hosting.md` § Zero-argument property cache, `tutorial.md` § Local Definitions, `artifacts/validation/exported-detached/followup/`.

> **Exposure enforcement, follow-up (EXPORTED-DETACHED) — 2026-11-21 (qualification and extension of the note below, from the independent review of that change and the owner's follow-up brief; the RES-08 bullet, the PROP-08 bullet and PROP-08's host contract restated again; no Q, PV or X status change, Q-59 stays OPEN; uncommitted over `main` @ `5ae82403`):** Two corrections to the note below. (1) A captured parameter whose lexical owner has no usable activation is UNAVAILABLE, and every EXECUTED operation on the written occurrence is refused with `UnknownName`: its value read, a call through it (formerly `NotAnAlgorithm`), and its direct transport as a supplied argument, which fails while the supply is formed even when the callee ignores the argument (formerly the callee's value). An absent lexical owner keeps the context lookup, and an available value-only parameter keeps the ordinary not-callable error. (2) The enforcement is NOT unconditional. The watermark blocks direct access to a pre-existing input on the paths the evaluators check — a captured parameter operation, a local-only member access, a local-only property read. The binding cell a LOCAL runtime-target alias retains is not checked: a falsely exported property that reads such an alias after another read of the same call established its cell reuses that call's value and publishes its own result for the run (`F(y) = { A = Sel(y).Algorithm ⏎ P = A(5) + 0 ⏎ A(5), P }` with `Cap(meta r) = r`, `Inc(n) = n + 1`, `Dbl(n) = n * 2` and `Sel(k) = if(k == 1, Cap(Inc(0)), Cap(Dbl(0)))`: `F(1), F(2)` is `((6, 6), (10, 10))` as classified, and `((6, 6), (10, 6))` when `P` alone is declared exported). The formal ledger records this as the open row R-1; a release that requires an unconditional guarantee against cross-activation reuse is blocked by it. The law identifiers and headings are unchanged, so `constitution-summary.md` and `open-questions.md` are unchanged. Evidence: `lean/KatLang.lean` (`capturedParameterActivation?`, `supplyNeed`, `projectParameterWith`, `shouldTreatAsImplicitParam`), `lean/KatLangArityLaws/DetachedEvaluation.lean` (`unavailable_transport_refused`, `unavailable_projection_refused`), `DetachedExportedEvaluationTests` (the callee and transport witnesses; `KnownResidual_R1_…`), `DetachedPlannedLoopModeTests`, `ExposureShapeDeferredRouteTests`, HP-18l…u of `HostParentDifferentialCorpus`, `docs/design/formal-correspondence-ledger.md` rows E-22 and R-1, `docs/design/language-rules/evaluator-and-hosting.md` § Detached evaluation of exported properties ("The guarantee is conditional"), `artifacts/validation/exported-detached/followup/`. *(2026-11-24: row R-1 is closed — retained runtime-alias cells are judged at every reuse; see the note of that date and PROP-08.)* *(2026-11-24, later: row R-1 is QUALIFIED, not closed — see the repair note of that date and PROP-08.)*

> **Exposure enforcement (EXPORTED-DETACHED) — 2026-11-21 (reconciliation with the evaluator change of November 2026, whose origin is the adversarial audit of 2026-11-14; one bullet of RES-08 and one of PROP-08 restated, PROP-08's host-contract qualification and item 4 of § Scope brought in step; no owner decision made here; no Q, PV or X status change, Q-59 stays OPEN; uncommitted over `main` @ `6e99edc9`):** RES-08 and PROP-08 said the evaluator TRUSTS the front end's exposure classification, and PROP-08's host contract said a host-built tree that declares a parameter-reading property exported gets a stale value by design. Both evaluators now ENFORCE the classification: an exported property is evaluated detached from the activations that exist when its evaluation starts, a captured parameter is read only through its lexical owner's activation, and a local-only member or property that needs a detached activation is refused. A classification that under-approximates a dependence is therefore a deterministic refusal (`UnknownName`, `LocalOnlyProperty`), observable only for misclassified and host-built trees; no value, key or charge of a correctly classified program changes. The law identifiers and headings are unchanged, so `constitution-summary.md` is unchanged; `open-questions.md` is unchanged (Q-59 asks whether Lean should state the classification, which it still takes as an input). Evidence: `lean/KatLang.lean` (`EvalCtx.detachedBefore`, `capturedParameter`, `localOnlyReadRefused`, `EvalBody.evalZeroArgPropertyAccessCounted`), `lean/KatLangArityLaws/DetachedEvaluation.lean`, `DetachedExportedEvaluationTests`, `AGENTS.md` (the parameter-channel and cache bullets), `docs/design/language-rules/evaluator-and-hosting.md` § Detached evaluation of exported properties, `artifacts/validation/exported-detached/`.

> **Constitution catch-up — 2026-11-15 (reconciliation with language changes already landed on `main` since 2026-11-10; rule text brought to the landed law; four owner decisions recorded from the record and none made here — STR-03 of 2026-11-11, the two decimal-places settings of 2026-11-12 that extend Q-10 D-F, declaration-level output spreading with D1 and D2 of 2026-11-14, and E-18 Q1 of 2026-11-14; ONE new law, SUP-08; VAL-12 retired to a stub; SYN-15 restated under its identifier; no open question closed; no Q, PV or X status change (`open-questions.md` registers two post-fix records, PV-53 and PV-54); over `main` @ `9ec6bf3b`):** Nine completed tasks left Constitution amendments as owner follow-ups; each was checked against `main` (source, `AGENTS.md`, `docs/design/language-rules/`, tests, and probe programs run on the built CLI) and only inaccurate or missing entries were changed. **(1) Strings** — task "Remove string interpolation and double-quoted strings" (`65885c4f`; `AGENTS.md` § ONE STRING LITERAL FORM; `syntax.md` § Strings; `evaluator-and-hosting.md` § String values; `UnsupportedDoubleQuotedStringTests`): VAL-02, OP-14, SYN-02 and SYN-15 are restated for the one raw single-quoted spelling and the lexical error `UnsupportedDoubleQuotedString`; VAL-12 is retired; every other interpolation or double-quote clause is removed or restated (VAL-01, VAL-09, VAL-11, SUP-05, SUP-06, PAR-03, PAR-07, NEED-03, NEED-06, CR-6, CR-12, FWD-03, MOD-02, MOD-07, PROP-05, BOOL-03, OP-03, OP-04, ALG-01, ALG-02, ALG-10, PAT-05, SYN-03, SYN-05, SYN-07, SYN-08, RUN-02, RUN-03, RUN-08, FORMAL-02, FORMAL-04); the error kinds of the removed forms (`InvalidStringEscape`, `UnmatchedBraceInString`, `UnterminatedInterpolationHole`, `InvalidInterpolationHole`, `InterpolationNotAllowedHere`) no longer exist and are named nowhere in the rules. **(2) Decimal places** — task "Replace DisplayDecimals with MinDecimalPlaces and MaxDecimalPlaces" (`1d3e1354`; `AGENTS.md` § DECIMAL PLACES; `evaluator-and-hosting.md` § Decimal places; the four `Hosting/DecimalPlaces*Tests` classes): RUN-06 is restated for the two independent settings, their per-name composition, the consistency error, the read order and the display rule, and the `DisplayDecimals` wording is replaced in the Scope note, VAL-11, RES-06, OP-14, SYN-01, SYN-13, RUN-01, RUN-02, RAND-01 and FORMAL-03. **(3) Output spreading** — tasks "Implement declaration-level output spreading (static form)" (`6c736e3f`), its certain-read follow-up (`899789d8`, `4562d74c`) and the two "Close E-18 F1" runs that carried the same D2 sentence (`sequences-lists-and-calls.md` § Declaration-level output spreading; `syntax.md` § The declaration-level output-spreading marker; `DeclarationOutputSpreadingTests`): the new law SUP-08 states the marker, the eligible positions, the explicit-`*` counterpart, D1, D2 with the final read sentence, and `OutputSpreadReferenceNeedsCall`; SYN-11, SYN-12 and SYN-13 gain the fourth star role and its attachment errors, and DOT-05 and PAR-07 one cross-reference each. **(4) Exposure** — "Close E-18 F1 against the route census" (`73d6256e`; `ownership-and-lookup.md` § Open, exposure, and accessibility; spec case `impossible-read-in-untaken-branch-charges-nothing`): RES-08 gains the Q1 sentence, a check that can never pass where it is made charges nothing. **Loop model classification:** LOOP-05 (task "Widen finite-loop correspondence (E-15)", `20742ba8`): its correct body note is preserved, but the index and summary now scope *C#-only* to non-integral count rejection. The repeat driver is Lean-modeled (`lean/KatLang.lean`, `.repeatBuiltin`; `lean/KatLangArityLaws/FiniteLoopCorrespondence.lean`, `repeatDriver_zero`, `repeatDriver_succ`, `repeat_trace_iff`); E-15 widens the conditional ordinary-call correspondence, and the formal ledger retains its premises. **Checked and left unchanged:** X-51 and X-52 (task "Prove the ordinary-call production bridge", `f4bc7ac1`, an ancestor of `main`) were already recorded RESOLVED on 2026-11-11 in `open-questions.md`. The two defects corrected by "Charge every intermediate dot-edge fallback" (`da209fa0`) change no rule text here: RES-08 already states the rule the code now meets. `open-questions.md` records them as the post-fix violations PV-53 and PV-54, as it records PV-51 and PV-52. `constitution-summary.md` mirrors the changed headings; `open-questions.md`, `decision-lineages.md`, `issue-ledger.md` and `constitution-review-log.md` carry their own dated notes. Evidence and the unified diff against the backed-up edition: `../constitution-catch-up-20261115/`.

> **Front-end decision differential — 2026-11-15 (formal-evidence strengthening; two FORMAL-02 qualifications and FORMAL-01's corpus sentence updated to the checked status, no change to what the law requires; no owner decision; no Q, PV or X status change; uncommitted over `main` @ `cdebe88d`):** FORMAL-02 said the derived corpora bypass Lean's partial front-end models and that conformance checks exist only for the owner walk and the signature selector. `lean/CoreTests/FrontEndDecisionCases.lean` (generated by `FrontEndDecisionLeanArtifactTests`, built by `lake build CoreTests`) now guards five of those specification functions against the C# front end's own decisions on the 3,098 parser-accepted programs of `SemanticExplorerCorpus` and `LanguageSpecCorpus` (42 parser-rejected programs skipped): `selectOwnedDeclaration` and `elaboratesToParameter` on 8,187 name occurrences, `elaborateOpenHead` on 83 open heads, `familyLiftingSignature?` on 58 clause families, and the whole `liftingSlotRole` table (260 roles). No disagreement was found, so nothing is recorded as drift. Implicit-parameter promotion (`shouldTreatAsImplicitParam`), clause grouping (`elaborateClauseGroup`), forwarding sources, alias formation and exposure classification remain unchecked, and Q-35 keeps its status. Evidence: `tests/KatLang.Tests/FrontEndDecisionCorpus.cs`, `tests/KatLang.Tests/FrontEndDecisionLeanArtifactTests.cs`, `docs/design/formal-correspondence-ledger.md` § Front-end decisions (FD-1..FD-6), and the mutation proof and build logs under `artifacts/validation/front-end-lean-oracle/`.

> **B16 cross-program cycles — 2026-11-11 (record correction and characterization; one clause of MOD-10's Reentrant selection bullet made exact, no change to the adopted host contract; no owner decision; no Q, PV or X status change; uncommitted over `main` @ `dbd2e8fd`):** The bullet's statement that the refusal reaches through nested loads of other programs this context started is now pinned by tests (two and three programs; blocking, `Task.Run` and asynchronous downloaders; the unit being loaded and another unit) and by mutations that remove the turn-frame chaining. Its list of cycles outside the guard named "another program's load that this context only joined". The uncaught class is every load this context did not start, whether its evaluation joins that load or queues for that program's loader turn, and the clause now says so, with a dated note of what the pins observe: no refusal and no timeout; cancelling the evaluations that started the loads need not end the cycle; a waiting evaluation's own bounded token ends it, and every unit stays loadable. Widening the refusal to such loads is an owner option and is not decided here. The summary mirrors headings only and is unchanged. Evidence: `../deferred-cross-tree-cycles/`, `tests/KatLang.Tests/DeferredMaterializationCancellationTests.cs` § 9c.

> **E-6 Tier 3 — 2026-11-11 (formal-evidence strengthening; FORMAL-07's evidence-class list updated to the proved status, no change to what the law requires; no owner decision; no Q, PV or X status change; uncommitted over `main` @ `1b4f5e84`):** FORMAL-07's Production Lean class no longer names the derived `Repr` printers as a parametric premise of the public-run results: the last 15 `partial` definitions of `lean/KatLang.lean` and the derived printers of the nested inductives are total (no KatLang constant on `runResultM`'s path is kernel-opaque; core's `Std.Format.pretty` stays opaque), and the admitted set of the validation is proved (`validate_ok_iff`). The law's identifier and heading are unchanged; `constitution-summary.md` carries no class text, so it is unchanged; the Q-82 row stays accurate and unchanged (the new outcome-form corollary presupposes no answer). Evidence: `lean/KatLangArityLaws/AdmittedSet.lean`, `lean/KatLangArityLaws/TotalLeaves.lean`, `artifacts/validation/e6-tier3/`.

> **Constitution marker check — 2026-11-10 (record correction; no rule text change; no owner decision; no Q, PV or X status change; over `main` @ `c48eb6f9`):** Three law-index *Open* markers no longer matched their entries and are cleared, in step with `constitution-summary.md`. DOT-09 (audit finding C-1) and MOD-03 (audit finding C-2) were fixed in `a4181877`, where C# follows Lean; their *Open* notes become dated *Resolved* notes citing the fix and its tests. VAR-03's note already read *Resolved* (audit finding A-2, implemented in `8a989f33` / `a6350e23`); only its index marker lagged.

> **SEM-2C transformation-member guards — 2026-11-10 (formal-evidence strengthening; no rule text change; no owner decision; no Q, PV or X status change; uncommitted over `main` @ `b8777840`):** FORMAL-01's `SemanticGeneratedCases` sentence now covers each valid SEM-2B case's `alpha-rename` and `declaration-reorder` members as well (264 cases plus 414 members; each member guard pins the base member's neutral text, mirroring the SEM-2B runner's SemanticEqual/Normalized member relation). FORMAL-07 and the summary are unchanged. Evidence: `tests/KatLang.Tests/SemanticTesting/SemanticGeneratedLeanArtifactTests.cs`, `lake build CoreTests` green.

> **SEM-2C Lean guards — 2026-11-09 (formal-evidence strengthening; no rule text change; no owner decision; no Q, PV or X status change; uncommitted over `main` @ `d8999d56`):** FORMAL-01's qualification on bounded corpora gains one sentence for the new generated corpus `lean/CoreTests/SemanticGeneratedCases.lean`: its guards check Lean on each valid SEM-2B case's identity-prelude member against the constructed expectation (230 of 239 cases; the 9 invalid front-end cases are excluded by kind). FORMAL-07's Executably checked class already covers such a corpus and is unchanged; the summary mirrors headings only and is unchanged. Evidence: `tests/KatLang.Tests/SemanticTesting/SemanticGeneratedLeanArtifactTests.cs`, `lake build CoreTests` green.

> **E-6 Tier 2 — 2026-11-08 (formal-evidence strengthening; FORMAL-07's evidence-class list updated to the proved status, no change to what the law requires; no owner decision; no Q, PV or X status change; uncommitted over `main` @ 4f3b2dbb):** FORMAL-07's evidence classes move the public-run bridge from Conditional to Production Lean: the validation prefix of `runResultM` is total (identification and wiring since FG-I1), its frame is proved (`validate_frame`, `validate_never_incomplete`), and the address invariant covers the public run (`public_inv`). What stays parametric is stated there (the derived `Repr` printers reached through `reprStr`; Q-82). The law's identifier and heading are unchanged; `constitution-summary.md` carries no class text, so it is unchanged. Evidence: `lean/KatLangArityLaws/ValidationFrame.lean`, `artifacts/validation/e6-tier2/`.

> **Q-66 dot funnel — 2026-11-08 (formal-evidence strengthening; DOT-03's *Open* marker removed because the Q-66 dot-funnel item that qualified it is proved; no rule text change; no owner decision; no Q, PV or X status change; uncommitted over `main` @ `b3cf5771`):** Independent review clarified the probe's entry and exit states and the loop corollaries' non-spread-slot and prelude-resolution premises; no theorem changed. DOT-03's *Open* line now states what Lean proves and under which premises (`lean/KatLangArityLaws/DotFunnel.lean`, `dot_funnel`, `dot_repeat_funnel`, `dot_while_funnel`), and its law-index marker is cleared, in step with `constitution-summary.md`. Q-66 itself stays OPEN for its other items (`open-questions.md`). Evidence: `artifacts/validation/dot-funnel/`.

It states KatLang's accepted language design in one place, as a set of numbered laws. It was restructured on 2026-11-06: rule identifiers are unchanged, and the laws were reconciled with the decisions accepted up to `main` @ `fe66a6bd`. The audit is `experimental/features/constitution-correspondence-audit.md`.

## Authority

Where this document and another source differ, this order decides, strongest first:

1. `lean/KatLang.lean`, for every construct it models (FORMAL-01, FORMAL-02).
2. Accepted owner decisions as recorded in `AGENTS.md` and `docs/design/language-rules/`, which are binding and tracked. A later decision supersedes an earlier one.
3. `dotnet/src/KatLang/SEMANTIC-ALIGNMENT.md` for change classification and decision records, and `docs/design/formal-correspondence-ledger.md` for the status of every proof claim.
4. This document.

Implementation behavior alone never settles intent, and neither does the oldest wording. Where intent cannot be established, a rule carries an *Open* marker naming its question in `open-questions.md`.

## How to read

- **Laws.** Each law has a stable identifier. A retired identifier stays as a one-line stub. Identifiers `NEED-nn` and `CR-n` are the laws formerly held in annexes.
- **Obligations.** The bullets directly under a heading are the law. **Qualifications** are necessary exceptions, boundaries and scope limits, and they are as binding as the bullets. Examples illustrate; where an example and a bullet seem to differ, the bullet governs.
- **Markers.** A law with no marker is Current. *C#-only by design* means it has no Lean counterpart (FORMAL-03). *Open* names a live question that qualifies it.
- **Examples.** A fenced program is followed by `⇒` and its outcome on the public engine: `S[…]` for a sequence or several root rows, `L[…]` for a list, `'text'` for a string, or an error kind. In running text, ` / ` separates the lines of a program. `trace(x)` and `tock()` are host operations configured for these examples: `trace` records and returns `x`, and `tock` counts. Random examples run with seed 42.
- **Error kinds** are the public `KatLangErrorCode` names, unless a law names a Lean constructor.
- **Provenance.** Dated decision history is not repeated here. It is in `decision-lineages.md`, `issue-ledger.md` and `constitution-review-log.md`. The registry of open questions and past violations is `open-questions.md`. The edition before the 2026-11-06 restructuring, with its per-rule Evidence sections and coverage table, is `../constitution-cleanup-20261106/backup/constitution-draft.md`.

## Scope

This document covers language semantics. The areas below are deliberately outside it. Each names its residue: what remains of it here.

1. **Presentation.** Message text, arity payload numbers, context frames, argument blame, synthetic-frame transparency, receiver-aware diagnostics, suggestions and provenance notes, rendered names, bounded diagnostic lists, spans and coordinate spaces, which diagnostic code a malformed form reports and how often, display text of rows and collections, the host decimal-places API, and output formatters. *Residue:* the error kind (RUN-07, FORMAL-06); presentation is not meaning (RUN-06); `.string` text, which is a value (OP-14, DOT-08); lowercase Boolean display (BOOL-01).
2. **Host policy and protection.** Limit values and their calibration, which resource verdict fires on which route, parser budgets, structural preflight, the stack backstop, traversal of deep or shared values, source-processing limits, module count and splice charging, cancellation observation points, and the mechanism that makes limits terminal. *Residue:* RUN-03 and RUN-01.
3. **Mechanisms whose only law is transparency.** Planned loops and their eligibility gates, pipeline fusion, async twins and routing, operational counters, planning memos, cache-key representation, front-end sharing structures, binder duplication, lookup twins, and the front end's pass staging. *Residue:* RUN-01, RES-09, FORMAL-05.
4. **Host-built shapes outside the source-reachable core.** `Expr.SequenceConstruct`, single-row and empty captures, a capture callee, a zero-link comparison chain, surviving Grace, a single-clause family with a binder head, the zero-arity family arm, runtime duplicate rechecks, the redundant-singleton clause of the truth view, host exposure metadata that contradicts a property's reads, `EmptySequence` depth, and the evaluator kinds `UnknownProperty` and `NotPublicProperty`. *Residue:* FORMAL-08.
5. **API, packaging, CLI and process.** The public API layering and baseline, closed hierarchies, `RunResult` projections, host-level immutability, host-atom projections, host-operation API details, the downloader contract, CLI flags, release and CI workflows, validation levels and regeneration flags.
6. **Library surface details.** The exact builtin and Math inventory and parameter names, transcendental accuracy, the near-one power band, quantum propagation of arithmetic, `round`'s digit rules, NaN placement in `order`, range-bound canonicalization, which equal `min`/`max` representative is returned, the PRNG algorithm and cross-version stream stability. *Residue:* OP-07, OP-11, COLL-01, RAND-01 to RAND-03.
7. **Editor and tooling.** Hover, references, completion ranking, classification, module provenance collection, recovery binders, and the representation of scope-visibility views. *Residue:* RES-09.
8. **Recovery.** Delimiter ownership, reported-character stand-ins, clause-head confinement, recovery of semicolons and collectors, refused loads kept as written, withheld provisional diagnostics. *Residue:* SYN-14, RUN-04, MOD-11.
9. **Evidence artefacts.** `CoreArityAlgebra` definitions, Lean law names, tutorial result claims, spec-link and generator-prompt checks, harness encoding conventions, Lean's own message strings. *Residue:* FORMAL-01, FORMAL-06, FORMAL-07.

Superseded spellings and laws (`;` joins, `...`, `spread(x)`, receiver segments, numeric truth, the colon selector, the retired loop interface, double-quoted strings and string interpolation, the single `DisplayDecimals` setting) are history, kept in the lineages. Current law is stated positively in the rules.

*Open:* the scope of rename invariance is unstated (Q-44). An unconditional rename law would be false: formula lifting and bare forwarding work by parameter name (PAR-07, FWD-02), a name that coincides with a prelude or host-operation name is captured (RES-04, RES-06, RUN-05), some names are selected by spelling (`load`, the root `MinDecimalPlaces` and `MaxDecimalPlaces`, the contextual `meta`, and the dot intrinsics `.string`, `.Invoke`, `.Arguments` and `.Algorithm`), and first occurrence orders inferred parameters (PAR-05).

## Law index


**VAL — Value model: kinds, canonical forms, value boundaries and counts**

| Law | Statement | Marker |
| --- | --- | --- |
| VAL-01 | Every value is exactly one of six kinds, and kinds never convert |  |
| VAL-02 | Strings are opaque scalar values with exact equality, produced only by literals, `.string` and the host |  |
| VAL-03 | Sequences are canonical: there is no one-item sequence | Open Q-50 |
| VAL-04 | `()` is a real value, never an absence and never an identity |  |
| VAL-05 | An output-less algorithm is a container, not a value: "no output" is never the empty value |  |
| VAL-06 | Every value boundary delivers exactly one value |  |
| VAL-07 | Output rows are an item supply, not a value boundary |  |
| VAL-08 | Element count, supplied items and emitted count are distinct measures |  |
| VAL-09 | Values carry no provenance |  |
| VAL-10 | A failure is not a value: a demanded failure ends the run, and nothing in the language can observe or recover from it |  |
| VAL-11 | A numeric datum carries value and representation: equality ignores representation, observers may not | C#-only |
| VAL-12 | (retired: string interpolation was removed, STR-03) |  |

**SEQ — Sequences, lists, and selection**

| Law | Statement | Marker |
| --- | --- | --- |
| SEQ-01 | A list is a second collection kind whose own boundary is never normalized |  |
| SEQ-02 | A list literal builds exactly one list from its written slots; each ordinary slot is a position evaluated at most once, when it is first read |  |
| SEQ-03 | Collections are opened only by explicit openers, one boundary at a time: the kind-blind openers open both kinds alike, and a structural pattern opens only its own kind |  |
| SEQ-04 | Selection chooses stored values and never opens them |  |
| SEQ-05 | Selection positions are the target's zero-based one-level positions, and a missing position is an error |  |

**SUP — Item supply: slots, spread, and capture**

| Law | Statement | Marker |
| --- | --- | --- |
| SUP-01 | A supply is built slot by slot: each non-spread slot supplies exactly one item, each spread slot supplies its spread items |  |
| SUP-02 | Spread opens exactly one boundary of its operand's value; any other value supplies itself |  |
| SUP-03 | Spread-produced items are established items: no receiver ever reopens them |  |
| SUP-04 | Stacked spread is composition through capture, never recursive flattening: `E**` means `(E*)*` |  |
| SUP-05 | A spread is a slot-level construct, not a value: legal only as a whole slot, as a spread operand, or as the fluent receiver | C#-only |
| SUP-06 | Capture turns a supply into one canonical value: `()` for no items, the item itself for one, one sequence for several |  |
| SUP-07 | A capture is a value, never an algorithm identity: no callable, no structural members, no open target |  |
| SUP-08 | A declaration's output-spreading marker changes no algorithm: every eligible call that resolves statically to a marked declaration is elaborated as its written-`*` counterpart | C#-only |

**CALL — Calls, argument binding, and parameters**

| Law | Statement | Marker |
| --- | --- | --- |
| CALL-01 | A call selects one callee identity first and binds against that callee's signature only |  |
| CALL-02 | A user call forms one argument supply before any binding decision: each non-spread slot supplies a suspended computation of the caller, evaluated only if its value is demanded |  |
| CALL-03 | A builtin callee forms its supply like every call; the builtin decides which non-spread slots it demands, and in what order |  |
| CALL-04 | Arity counts supplied items, and a fixed parameter binds its item unchanged in every call form |  |
| CALL-05 | A zero-argument value demand is accepted exactly when an ordinary zero-argument call can bind the callable | Open Q-46, Q-58, Q-42 |
| CALL-06 | A written argument slot is evaluated at most once, on its first value demand, and that outcome is final for the call; a slot whose value is never demanded is never evaluated |  |
| PAR-01 | A parameter binds on the value channel, the algorithm channel, or both, and owns its name on every channel |  |
| PAR-02 | (retired: merged into RES-07) | Open Q-42 |
| PAR-03 | A free name that nothing binds becomes an inferred parameter of the outermost inferring level whose own rows use it | Open Q-42 C#-only |
| PAR-04 | An explicit parameter list is closed for its own level: nothing is inferred there, and forwarding never adds a parameter to it | C#-only |
| PAR-05 | An inferred signature lists the level's own names by first semantic occurrence, followed by the names it forwards | C#-only |
| PAR-06 | Grace `~` moves the OWN inferred parameters of the owner whose rows contain it; saturation is never an error | C#-only |
| PAR-07 | In a formula, a value-role reference to a callable that requires supplied arguments becomes a call that forwards the parameter bindings its site already sees; automatic forwarding never changes what an existing name refers to | C#-only |
| PAR-08 | Inferred signatures are selected jointly before any rewrite: a recursive inference that settles completes, and only a group with no unique grounded settled answer is refused | C#-only |

**NEED — Call by need: supplied computations, demand and transport**

| Law | Statement | Marker |
| --- | --- | --- |
| NEED-01 | Supply computations in the caller environment |  |
| NEED-02 | One immutable completed VALUE outcome |  |
| NEED-03 | Executed demands determine effects |  |
| NEED-04 | Ordered pattern inspection and shared clause supply | Open |
| NEED-05 | Whole-source validation, then runtime demand phases |  |
| NEED-06 | CALLABLE projection and fresh invocation |  |
| NEED-07 | Lazy supply, eager collection VALUE |  |
| NEED-08 | Forwarding transfers supplies |  |
| NEED-09 | Single flight, cycles, cancellation and resources |  |
| NEED-10 | Retained ownership and separate property cache |  |

**REF — Call references: `meta`, `Invoke`, `Arguments`, `Algorithm`**

| Law | Statement | Marker |
| --- | --- | --- |
| CR-1 | META is a binder capability |  |
| CR-2 | Written-order, inert capture |  |
| CR-3 | Identity |  |
| CR-4 | The reference value |  |
| CR-5 | `R.Invoke()` |  |
| CR-6 | Run scope |  |
| CR-7 | Plan retention is decided once and is unobservable | C#-only |
| CR-8 | The view |  |
| CR-9 | The view's supply |  |
| CR-10 | Count and selection |  |
| CR-11 | The cell-preserving spread |  |
| CR-12 | Boundaries | Open Q-84 |
| CR-13 | The callee cell |  |
| CR-14 | The `.Algorithm` intrinsic |  |
| CR-15 | The link |  |
| CR-16 | What obtaining and using `R.Algorithm` does (qualified inertia) |  |
| CR-17 | A builtin may declare META parameters |  |

**VAR — Collecting bindings, deconstruction, and forwarding**

| Law | Statement | Marker |
| --- | --- | --- |
| VAR-01 | A collecting binding collects exactly its allocated items as one exact list |  |
| VAR-02 | One collector per pattern level; fixed positions bind from both ends first and the collector takes the exact middle | Open Q-47 |
| VAR-03 | A collecting binding preserves its cells for re-spread, selective reads demand only the needed cells, and a whole read demands every cell |  |
| VAR-04 | No binder carries supply provenance: binding sees only the supplied items |  |
| VAR-05 | Assignment deconstruction is the explicit unpacking receiver | Open Q-84 |
| VAR-06 | Deconstruction declares properties of the enclosing algorithm; its right-hand side is one row of that body, successfully evaluated at most once | Open Q-70 |
| FWD-01 | Forwarding collected arguments re-spreads the collector's own cells: spread(collect(S)) = S |  |
| FWD-02 | Bare forwarding reuses existing compatible bindings by name, and a written call means what it writes; every synthesized call forwards bindings unchanged and rebuilds each structural pattern as its own kind | C#-only Open Q-44 |
| FWD-03 | Whole-algorithm transport: an open body whose one row is a bare algorithm reference is a transparent reference when unbraced and a structural forwarding carrier when braced, and neither owns a zero-argument entry |  |
| FWD-04 | A runtime-target alias takes its callable from one binding cell per declaring activation: an identity of any arity is invoked freshly, absence leaves a value view, and a failure stays a failure |  |

**DOT — Dot syntax: member access, the `.string` intrinsic, and extension calls**

| Law | Statement | Marker |
| --- | --- | --- |
| DOT-01 | A declared structural member wins; the extension call happens only on a structural miss |  |
| DOT-02 | Structural-first holds at every level of a chain, and navigation evaluates nothing |  |
| DOT-03 | Extension fallback passes the receiver as the ordinary leading argument: `R.F(args)` ≡ `F(R, args)` |  |
| DOT-04 | The fallback callee is resolved by ordinary callable resolution; a missing member on a known receiver falls back like any other |  |
| DOT-05 | In parameter inference a dot edge contributes receiver, then member (only if the fallback may be selected), then arguments; a closed list checks a certain fallback name | C#-only |
| DOT-06 | Grace on a dot edge (`a~.t`, `a.~t`) only reorders inferred parameters; it never changes dispatch | C#-only |
| DOT-07 | A fluent receiver `R*.F(args)` is exactly the lexical call `F(R*, args)`; a grouped spread `(R*).F` is a capture receiver; a redundant group is erased |  |
| DOT-08 | `.string` is a dot-only, zero-parameter intrinsic, selected on a structural miss |  |
| DOT-09 | A dot expression carries one callable identity in every position: a structural path is its member, everything else is a value |  |

**RES — Name resolution and ownership**

| Law | Statement | Marker |
| --- | --- | --- |
| RES-01 | The owner walk: the nearest owning scope that declares a name decides | Open Q-44 |
| RES-02 | `open` is consulted only after the whole owner walk; an opened name never overrides anything owned |  |
| RES-03 | At the deciding open level one provider selects; two or more providers are an error, never a fall-through |  |
| RES-04 | A name becomes an implicit parameter only when nothing declares it and no open provides it |  |
| RES-05 | A property may not share a name with a parameter of its own or of any enclosing owner |  |
| RES-06 | Builtins are ordinary, shadowable prelude bindings: the resolved identity decides, never the spelling or the argument count | Open Q-62 |
| RES-07 | A name inside a declaration denotes what its declaration site sees (lexical scoping), never what the caller or opener sees |  |
| RES-08 | Visibility selects; accessibility is checked on the selected member afterwards (K1-08) | C#-only Open Q-59 |
| RES-09 | One resolution for every layer, position and execution path |  |
| RES-10 | Declaration order within a scope is not observable |  |

**MOD — The `open` declaration, `load`, and modules**

| Law | Statement | Marker |
| --- | --- | --- |
| MOD-01 | An algorithm has at most one `open` declaration, written before its properties and output rows, with one comma-separated target list | C#-only |
| MOD-02 | An open target names an algorithm, never a value: a name, an argumentless dotted path, a brace block, or a module | Open Q-58 |
| MOD-03 | Open targets resolve statically: the head through the owner walk and the direct chain, dotted steps through public members, and every written target must resolve |  |
| MOD-04 | An open provider must need no call, and opening it neither activates nor evaluates it | Open Q-58 |
| MOD-05 | `open` provides exactly the provider's own public members, and only to the opening body and its nested scopes |  |
| MOD-06 | Opened members keep their definition site; inline open targets and every loaded module are rooted at the prelude |  |
| MOD-07 | `load('url')` is a static source directive that splices a separately parsed module as the one prelude-rooted declaration of its canonical URL, and module elaboration transforms nothing else; `open 'url'` is `open load('url')` | C#-only Open Q-60 Open Q-62 |
| MOD-08 | A module has hygiene of its own: its free names resolve against the module itself and the prelude, never at the load site |  |
| MOD-09 | One module per canonical URL per compiled program: every load and every open of it is the same declaration | C#-only |
| MOD-10 | A clause branch that owns a load materializes its modules only when selected, and then means exactly what eager elaboration would have produced | C#-only |
| MOD-11 | A module that is not loaded never becomes a value, and a program with a missing module is never evaluated | C#-only |

**PROP — Properties: declarations, demand, and one value per binding per owning invocation**

| Law | Statement | Marker |
| --- | --- | --- |
| PROP-01 | Each name is bound once per algorithm; a property is never redefined or reassigned |  |
| PROP-02 | A declaration evaluates nothing: a property body runs only when demanded |  |
| PROP-03 | (retired: merged into RES-10) |  |
| PROP-04 | A zero-parameter property is evaluated at most once for each resolved binding in its owning invocation: once per actual call of the owner around it, once per run where no call owns it |  |
| PROP-05 | How a property's value is consumed never causes its body to run again |  |
| PROP-06 | Only property-style reads reuse the entry: an explicit call invokes afresh and never reads or replaces it, a zero-supply call may only establish an empty one, and freshness is local | Open Q-83 Open |
| PROP-07 | Cache identity is the resolved binding, never the spelling or the access path |  |
| PROP-08 | Storage follows the declaring binding and its owning invocation: every actual call of an owner has fresh inner bindings, reads in one call share them, and a binding no call owns is one value per run; exposure decides accessibility and detachment, never lifetime | Open Q-59 |
| PROP-09 | A binding's entry is created only by its outermost evaluation, and only if it succeeds; the entry is final for the run |  |

**BOOLCMP — Booleans, truth, comparison chains, and builtin `if`**

| Law | Statement | Marker |
| --- | --- | --- |
| BOOL-01 | `true`/`false` are a scalar kind of their own, written only as reserved literals, with no Boolean-specific structural rules |  |
| BOOL-02 | Only a Boolean has a truth value | Open Q-54 |
| BOOL-03 | A Boolean is never a number: no numeric projection, no implicit conversion |  |
| BOOL-04 | `and` and `or` evaluate their right operand only when their Boolean left operand does not decide; `xor` evaluates both operands, left to right, before validating either; `not` takes one Boolean |  |
| BOOL-05 | Builtin `if` demands its Boolean condition first, then exactly the selected branch; the unselected branch is never demanded |  |
| CMP-01 | The six comparison operators form one chain of adjacent links; a chain is one Boolean, `true` iff every link holds; parentheses end a chain |  |
| CMP-02 | A chain evaluates every operand exactly once, left to right and incrementally; a `false` link never stops it; the first error does |  |
| CMP-03 | `==` and `!=` are total, kind-exact structural equality over every value |  |
| CMP-04 | Ordering (`<`, `>`, `<=`, `>=`) is defined only between numeric scalars |  |
| CMP-05 | On the Decimal128 runtime tier, numeric equality is value equality — representation is not part of it — while ordering is IEEE | Open Q-56 C#-only |

**OP — Operators and numerics**

| Law | Statement | Marker |
| --- | --- | --- |
| OP-01 | Operators group by one fixed precedence ladder; `^` is right-associative and binds tighter than prefix minus | C#-only |
| OP-02 | Prefix `not` sits between the logical operators and the comparisons, and is never silently regrouped | C#-only |
| OP-03 | Arithmetic operators evaluate operands in source order before checking their kinds |  |
| OP-04 | Arithmetic operators and Math functions take numeric scalars only: no vectorization, no identity element, no concatenation, no coercion |  |
| OP-05 | A number is a 34-digit decimal floating-point value, and every arithmetic result is rounded once | C#-only |
| OP-06 | Division, `div` and `mod` by an evaluated zero-valued divisor is an error, never an IEEE infinity or NaN |  |
| OP-07 | A violation of a numeric domain yields an IEEE value, not an error; IEEE special values are ordinary numbers | C#-only |
| OP-08 | `div` truncates the exact quotient toward zero, and `mod` is the matching remainder |  |
| OP-09 | `^`, `pow` and `Math.Pow` are one operation; a zero base with any negative exponent is an error |  |
| OP-10 | A numeric literal denotes the nearest Decimal128 value with its written quantum; an out-of-range magnitude is a front-end error | Open Q-56 C#-only |
| OP-11 | Every spelling of a Math member is the same function; the spellings are nevertheless distinct bindings | C#-only |
| OP-12 | `avg` is the correctly rounded exact mean, independent of element order | C#-only |
| OP-13 | `min`/`max` are IEEE minimum/maximum: they return an input element, propagate NaN, and order the two zeros by sign | Open Q-56 C#-only |
| OP-14 | `.string` renders a number as its canonical positional text; quantum, sign and specials are part of that string value | C#-only |

**ALGHO — Algorithms and the higher-order channel**

| Law | Statement | Marker |
| --- | --- | --- |
| ALG-01 | A brace block is a scope-owning algorithm in every expression position |  |
| ALG-02 | Algorithms are not values: only naming forms reach the algorithm channel, and no value is ever callable |  |
| ALG-03 | (retired: merged into SUP-07) |  |
| ALG-04 | (retired: merged into SYN-06) | C#-only |
| ALG-05 | Trailing-brace call: `F{…}` is exactly `F({…})` | C#-only |
| ALG-06 | (retired: merged into DOT-09) |  |
| ALG-07 | Callable identity is the written declaration plus its captured activation |  |
| ALG-08 | (retired: merged into RES-07) |  |
| ALG-09 | (retired: merged into VAL-05) |  |
| ALG-10 | Consumer-directed observation: a name resolves to one binding, and its consumer decides what to observe |  |
| HO-01 | A callable passed by name is the same callable at the receiver |  |
| HO-02 | The callback law: each element is one ordinary argument, and each callback call is the ordinary call |  |
| HO-03 | A callback returns its ordinary call result: `map` stores it as one element, `reduce` passes it as the next accumulator; `filter` needs a Boolean |  |
| HO-04 | Forwarding preserves the algorithm channel: invoking slots call the named callable, value slots read its value |  |
| HO-05 | Recursion is by name, and every call is a fresh activation whose parameters shadow inherited bindings |  |

**COLL — Collection builtins: one collection argument, one-level view, exact-list results**

| Law | Statement | Marker |
| --- | --- | --- |
| COLL-01 | Each builtin has exactly one signature and one behavior contract; none is overloaded by the kind of its input |  |
| COLL-02 | A collection builtin binds exactly one `collection` argument plus fixed controls; argument boundaries are never altered before binding |  |
| COLL-03 | The bound collection is read through ONE post-binding level; `count` counts exactly those items |  |
| COLL-04 | Collection-producing builtins return one exact list. Each consumer determines which positions it needs |  |
| COLL-05 | Numeric collection builtins accept only single numbers; the empty-collection policy is fixed per builtin |  |
| COLL-06 | Aggregates and sorts are defined over the viewed numbers: `order` is a stable ascending sort in which equal numbers tie, and `orderDesc` is its exact reverse | Open Q-28 |
| COLL-07 | `distinct` and `contains` use the one structural equality of `==`, at the top level of the view |  |
| COLL-08 | `take`/`skip` split the view at a whole-number count and saturate at both ends |  |
| COLL-09 | `range(start, stop)` is the inclusive run of integers in either direction, as one exact list |  |
| COLL-10 | `atoms` is the only recursive flattener and always returns one exact list of numbers |  |

**PAT — Clause families and parameter patterns**

| Law | Statement | Marker |
| --- | --- | --- |
| PAT-01 | A same-name clause group is classified as a whole: one literal-free binder/group clause is an ordinary algorithm, anything else is a clause family | Open Q-46 |
| PAT-02 | A family call selects the first matching clause in written order; no match is NoMatchingBranch | Open Q-49 |
| PAT-03 | A family has one outer call interface: every clause takes the same number of argument slots and writes the same number of output rows | Open Q-48 |
| PAT-04 | A clause head is the complete input specification of its branch | Open Q-47 |
| PAT-05 | A literal pattern matches only an equal value of its own kind |  |
| PAT-06 | Structural pattern delimiters select the value kind they destructure: a parenthesized pattern matches sequence values only, a bracketed pattern list values only, and a one-item sequence pattern is invalid |  |
| PAT-07 | A clause family demands only what its patterns inspect, and its binders keep both channels of their cells |  |
| PAT-08 | An ordinary structural parameter pattern consumes one argument and opens that argument's value exactly one level, through its own kind |  |
| PAT-09 | A repeated name is a compatibility constraint over independently supplied arguments, never a merge or a rebinding | Open |
| PAT-10 | A pattern list is inspected in written order after its cardinality check, and the first failure or conflict that inspection meets is reported |  |
| PAT-11 | A clause family is an ordinary callable: it can be passed, called back and dot-called, its call result is one value, and a zero-argument value demand of it is NoMatchingBranch |  |

**LOOP — `repeat` and `while`: stepping an explicit multi-slot state**

| Law | Statement | Marker |
| --- | --- | --- |
| LOOP-01 | The initial state is one state slot per supplied argument of the captured step call |  |
| LOOP-02 | Each iteration invokes the step on the current state as the ordinary call |  |
| LOOP-03 | The step's emitted row supply becomes the next state; patterns bind, they never produce |  |
| LOOP-04 | (retired: merged into LOOP-03) | C#-only |
| LOOP-05 | `repeat` invokes the step exactly `count` times, and `count` is a non-negative whole number | C#-only: non-integral count rejection |
| LOOP-06 | `while` reads its continuation flag first: the last effective output item is a Boolean flag, and `false` returns the state that entered the round |  |
| LOOP-07 | The loop result is ONE value: the canonical capture of the final state's slots, one item at every receiver |  |
| LOOP-08 | A loop step is an ordinary callable invoked over the current state supply | Open Q-39 |

**SYN — Syntax and layout: vocabulary, rows, delimiters, separators, lines, and markers**

| Law | Statement | Marker |
| --- | --- | --- |
| SYN-01 | Exactly ten words are reserved; every other identifier-shaped word is an ordinary name, and names are exact | C#-only |
| SYN-02 | Literal forms: unsigned decimal numbers, raw single-quoted strings, and the two Boolean keywords | C#-only |
| SYN-03 | `#` comments are invisible to the grammar, and a physical line ends only at a line feed | C#-only |
| SYN-04 | An algorithm body is a set of declarations plus an ordered list of output rows; there is no output keyword |  |
| SYN-05 | Only a brace block (and the root) creates a scope; parentheses group and capture, brackets build lists, and indentation means nothing |  |
| SYN-06 | Parentheses group syntax: a one-slot, non-spread group IS its content, so `E ≡ (E) ≡ ((E))` everywhere | C#-only |
| SYN-07 | On one physical line only a comma separates slots; a newline separates slots only where a list is open across lines; `;` is not KatLang syntax | C#-only |
| SYN-08 | Grammar role has priority across physical newlines | C#-only |
| SYN-09 | A call is written only as a same-line `(` or `{` after a callable name or argumentless dot edge; juxtaposition never calls and never multiplies | C#-only Open Q-46 |
| SYN-10 | Declarations are line-anchored: each begins a line, its head never spans lines, and a head is never an operand | C#-only |
| SYN-11 | Star roles are syntactic; a line-final star is classified by attachment | C#-only |
| SYN-12 | Markers and special prefix roles require attachment; binary operators retain ordinary spacing | C#-only |
| SYN-13 | The grammar never consults meaning: no parse depends on arity, values, types, name resolution, or callee spelling, except MOD-07's `load(...)` open-target form check | C#-only |
| SYN-14 | Recovery is not grammar: recovery trees, stand-ins, delimiter repairs and clause-head confinement give malformed text no meaning | C#-only |
| SYN-15 | A string has one spelling, raw single-quoted text; a double quote is the targeted front-end error `UnsupportedDoubleQuotedString` | C#-only |

**RUN — Runtime transparency, evaluation outcome, host policy, and seeded randomness**

| Law | Statement | Marker |
| --- | --- | --- |
| RUN-01 | The meaning of a program is independent of the execution route | Open Q-41 C#-only |
| RUN-02 | The run is the unit of evaluation state |  |
| RUN-03 | Runtime protection is host policy: it may stop a run, never redefine it | Open Q-39 Open Q-40 Open Q-41 |
| RUN-04 | A source with any front-end error is never evaluated, and recovery gives malformed text no meaning | Open Q-41 C#-only |
| RUN-05 | Host operations are ordinary prelude members; each executed call invokes the host exactly once | C#-only |
| RUN-06 | Presentation is not meaning: display settings change only rendered text | C#-only |
| RUN-07 | A run yields its output or exactly one error: errors are not values, cannot be caught, and end the run; the outcome is the first RAISED failure in the evaluation order the rules fix | Open Q-42 |
| RUN-08 | Evaluation is strict except at a closed set of demand points, and "exactly once" has enumerated exceptions |  |
| RUN-09 | `tick()` counts actual executions: one counter per run, advanced only when the primitive executes |  |
| RAND-01 | One run-scoped random stream, consumed exactly where evaluation executes a random call | C#-only |
| RAND-02 | A seed is host configuration: it reproduces the stream, never memoizes, and has no source syntax | C#-only |
| RAND-03 | `random`/`randomInt` draw uniformly from a half-open interval, and validation precedes every draw | C#-only |

**FORMAL — Lean/C# correspondence: authority, model coverage, and what is proved**

| Law | Statement | Marker |
| --- | --- | --- |
| FORMAL-01 | `lean/KatLang.lean` is the normative semantics of every construct it models |  |
| FORMAL-02 | Lean models the elaborated core; surface syntax and front-end elaboration are C#-only, and both sides run the same elaborated program |  |
| FORMAL-03 | Everything outside the Lean model is C#-only by design and must extend the modeled core conservatively | C#-only |
| FORMAL-04 | Numerics are two-tier: Lean's `Int` laws bind C# on the common exact integer subdomain, and Decimal128-only behavior has no Lean witness |  |
| FORMAL-05 | Counted evaluation is the one meaning of an expression; plain evaluation is its value projection |  |
| FORMAL-06 | Lean/C# agreement is defined on the neutral observation: structure, emitted count, and innermost error kind |  |
| FORMAL-07 | Proofs cover total helpers and operation-level laws of the fuel-indexed evaluator core; whole-program evaluation is checked executably on bounded corpora |  |
| FORMAL-08 | The constitution is stated over the source-reachable elaborated core; host-built shapes outside it are not constitutional |  |

## VAL — Value model: kinds, canonical forms, value boundaries and counts

KatLang computes immutable values. Algorithms are not values, and neither are failures. Three terms recur throughout this document. A **value boundary** hands its consumer exactly one value (VAL-06). An **accumulating receiver** (output rows, a loop step's row supply) carries several items (VAL-07). **Emitted count** is the 0-or-1 count of a value at a boundary (VAL-08).

### VAL-01 — Every value is exactly one of six kinds, and kinds never convert

- Every evaluated value is exactly one of six kinds: a number, a string, a Boolean, a sequence, a list, or an opaque run-scoped call reference (REF). A reference is an invocation plan identity, never an algorithm. Its lazy argument view `R.Arguments` is a facet of the same kind: distinct from its reference, equal only to itself, never invocable.
- No value kind holds an algorithm; algorithms travel only on the algorithm channel (ALG-02).
- No operation implicitly converts a value from one kind to another. An operator or value view that receives the wrong kind rejects it with an error. Equality between values of different kinds is `false`, never an error and never a conversion (CMP). `.string` (DOT-08) is an explicit rendering of a number: it builds a new string and converts nothing.
- Values are immutable: no language operation changes a value once it has been produced.

**Qualifications**
- Kind is decided by the value, not the written form: `(7)` and `7` are the same value (VAL-03), while `[7]` and `7` are different kinds.
- Numbers are `Int` in Lean and IEEE `Decimal128` in C#. NaN, ±∞, −0 and decimal quantum exist only in C# (OP, FORMAL-04).

```katlang
true == 1, [1] == 1, [] == (), '1' == 1, (1, 2) == [1, 2], false == 0
```
⇒ `S[false, false, false, false, false, false]`

`true + 1`, `1 + '1'`, `true < false` and `if(1, 2, 3)` are `TypeMismatch`.

### VAL-02 — Strings are opaque scalar values with exact equality, produced only by literals, `.string` and the host

- A string, written `'…'` (SYN-02, SYN-15), produced by `.string` (DOT-08) or supplied by the host (a host operation's result, RUN-05, or a host-built literal), is a scalar. A collection view reads it as one element: `count('abc')` is 1 and `'abc'[0]` is `'abc'`.
- `==` and `!=` compare strings by exact, case-sensitive character equality. Ordering, arithmetic and unary minus reject a string with `TypeMismatch`.
- No operation converts a string to another kind or back. `.string` accepts only a numeric scalar. Nothing joins strings or builds text from values: there is no concatenation, no formatting builtin and no implicit conversion of a value to text (OP-04).
- A string contributes no numeric atoms.

**Qualifications**
- Display drops the quotes, so `'42'` and `42` display identically. Display is presentation only.
- A string literal has no escapes, and nothing is evaluated inside it (SYN-15). The only string operations are equality and literal pattern matching (PAT-05).
- A sequence or list that holds strings and numbers holds them as distinct values and is never a built string: a number beside a string is still a number, so the display settings reach it (RUN-06). Labelling a result is the host's presentation concern.
- A string element in a numeric collection builtin is `TypeMismatch` (`sum(('a', 'b'))`; COLL).

### VAL-03 — Sequences are canonical: there is no one-item sequence

*Open: Q-50, whether "no one-item sequence at any depth" is a law or an implementation invariant. The universal canonical-value invariant is asserted, not proved.*

- Every sequence produced by construction or capture is normalized. A sequence of exactly one item IS that item, recursively at every depth, and nested empty sequences collapse (`(())` is `()`). A sequence therefore has either zero elements or at least two.
- `(v)`, `((v))` and the capture of a one-item supply such as `([v]*)` all equal `v`.
- Normalization never removes a list boundary (SEQ-01). It does normalize sequence structure inside list elements: `[(5)] == [5]`.
- Nesting with more than one item is never flattened: `((1, 2), ())` keeps both boundaries.
- Normalization is deliberately not injective. A one-row table written as a sequence, `((10, 20))`, IS the row `(10, 20)`. A list is the way to keep a one-element collection.
- A one-item sequence pattern (`(x)`, `((x))`, `(([x]))`) describes a boundary no value has, so it is invalid source; the one-element collection pattern is `[x]` (PAT-06).

**Qualifications**
- This is the value-side law: it holds for values from every route, spread capture and host returns included. Parenthesis erasure (`(E)` ≡ `E`, SYN) is its parser-side face.
- Host-operation results are normalized at the host boundary. A host-constructed `SequenceValue` may be non-canonical outside evaluation.
- The internal `SequenceConstruct` join drops non-spread `()` leaves, and a spread leaf contributes exactly its spread items. The parser never produces it, so this is not surface semantics (FORMAL-08).
- Canonicity of evaluated results is pinned on bounded corpora only. No theorem states it for the evaluator. C#'s shallow spread capture and Lean's recursive normalization agree on canonical items by theorem over `Result` (`shallow_spread_agrees_on_canonical_operand`), which models the C# rule and is not a proof about C# code.

```katlang
Z = ((1, 2))
One = [7]
(7) == 7, Z == (1, 2), Z.count, (()) == (), (One*) == 7, [(5)] == [5], (5, ()*) == 5
```
⇒ `S[true, true, 2, true, true, true, true]`

### VAL-04 — `()` is a real value, never an absence and never an identity

- `()` is the empty sequence value. It has zero elements (`count(())` is 0), equals itself and `(())`, and is distinct from `[]`, `0`, `false` and every string.
- Written as a non-spread slot (a row, a sequence or list element, an argument) it is exactly ONE visible item, like any other value. Only an explicit spread of it (`()*`) supplies zero items.
- It is no operator's identity and has no truth value. Every scalar operator, unary and binary alike, and every condition rejects it with `TypeMismatch`.
- Its emitted count at a value boundary is 0 (VAL-06), yet every accumulating receiver still gives a non-spread `()` one slot (VAL-07). `E*` supplies nothing because spread opens the value (SUP-02), not because of the count.
- A `map` transform or `reduce` step may return `()`: it is one ordinary element or accumulator, never "skip this element" or "keep the previous accumulator" (HO-03).

**Qualifications**
- `{}` is not `()` (VAL-05). `[]` is the empty list: one value with emitted count 1, so the program `[], 1` has two rows and `([]*, 1)` is `1`.
- A root whose explicit spreads supply no rows exposes count 0 through FORMAL-06: the program `E = ()` / `E*` has no output rows, while the program `()` has one.

```katlang
E = ()
Coll(*xs) = xs
E, count(E), (E, 5), (E*, 5), E == [], Coll(E), Coll(E*), [E]
```
⇒ `S[S[], 0, S[S[], 5], 5, false, L[S[]], L[], L[S[]]]`

### VAL-05 — An output-less algorithm is a container, not a value: "no output" is never the empty value

- An algorithm whose body has no output rows, such as `{}` or `{ X = 1 }`, is a container. It has no value.
- Demanding its value anywhere fails with `MissingOutput`, and spreading it fails with `SpreadMissingOutput`. Demands include reading, comparing, counting, a builtin value slot, an inspecting pattern (a literal, a structural pattern or a repeated name, NEED-04), reading a collector that holds it, and calling it with no arguments (`A()`).
- Merely passing it to a parameter or collecting parameter demands nothing (CALL-02, VAR-03). A call that supplies arguments is first an arity verdict (NEED-05): `A(6)` is `ArityMismatch`.
- It is never silently treated as `()` or as an omitted argument. A program whose root has no output rows likewise has no result, and that is not an empty success.
- An algorithm with rows that supply zero items (`{ []* }`, or `F(*a) = a*` called as `F()`) DOES have output: the value `()`.
- An output-less algorithm is still an algorithm. It can be bound on the algorithm channel and passed, its members stay reachable (`A.X`), and it can be opened (MOD). An undemanded container argument is no error.
- An algorithm that declares parameters but has no output rows is rejected before any evaluation (`ExplicitParametersRequireOutput`): a container takes no parameters, and a function must produce something. Written and inferred parameters are both front-end errors (`ParseFailure`); the inferred case is judged once signatures are complete. The pre-evaluation gate rejects the same shape in a host-built tree.

**Qualifications**
- The split between `NoProgramOutput` and `MissingOutput` is host API. The law is only that no output is not a success.
- A clause family is outside the before-evaluation rejection. A branch whose body has no output parses, and selecting it is the run-time `MissingOutput`: `F(0) = { Q = 2 }` / `F(0)` is `MissingOutput`, while `F(x) = { Q = 2 }` / `5` is `ExplicitParametersRequireOutput`.
- A parameter rejects an output-less argument only when it demands it. `Coll(*xs) = 7` / `Coll({ X = 1 })` gives `7`, while `Coll(*xs) = xs` / `Coll({ X = 1 })` and `P((a, b)) = 7` / `P({ X = 1 })` are `MissingOutput`.

```katlang
open A
A = { public X = 1 }
Use(f) = f.X
Ignore(f) = 0
A.X, Use(A), Ignore(A), X
```
⇒ `S[1, 1, 0, 1]`

### VAL-06 — Every value boundary delivers exactly one value

- Each of these is a value boundary, and delivers ONE value to its consumer however many rows or items its body produced:
  - a property read, whether lexical, a structural member (`Obj.P`) or an opened name;
  - a user or clause-family call (`A()`, `F(x)`, `Obj.M(x)`), a `map`/`reduce` callback invocation included (HO-03);
  - a builtin call result, a completed `while`/`repeat` included (LOOP-07);
  - the selected branch of `if`;
  - a brace block or a surviving capture in value position.
- A multi-output body arrives as one sequence value. The value is delivered unchanged, with emitted count `valueCount`: 0 for `()`, and 1 for everything else, `[]` and every list included.
- No consumer re-opens it implicitly. Only an explicit spread at the consumer (SUP) turns it back into items. A spread inside a body is local to that body's output.
- Selection (`A[i, …]`, `first`, `last`; SEQ), callback elements and callback results (ALGHO) obey the same boundary.

**Qualifications**
- Root and body output accumulation (VAL-07) and a loop step's own row supply (LOOP-03) are NOT value boundaries. The completed `while`/`repeat` result is one.
- Collection-producing builtins return ONE exact list (COLL).

```katlang
Fib(a, b) = b, a + b
C(*xs) = xs.count
C(repeat(Fib(0, 1), 3)), repeat(Fib(0, 1), 3), 9
```
⇒ `S[1, S[2, 3], 9]`

### VAL-07 — Output rows are an item supply, not a value boundary

- The rows of an algorithm body, the program root included, are each evaluated exactly once, left to right. The exception is a step body activated by a `while` round, whose rows are formed at most once each, condition first (LOOP-06).
- A non-spread row contributes exactly one slot: its value, even `()`, whatever produced it, a completed `while`/`repeat` included (LOOP-07). A spread row contributes its supplied items, possibly none. A loop step's rows form its next state the same way (LOOP-03).
- In the root and in a brace body, comma and newline separate independent rows with the same output meaning. A token that takes a binary continuation role starts no row (SYN-08). A spread row is closed by explicit same-line syntax or by the end of its line after an attached star (SYN-11): `A*` newline `B` is two rows, while the detached `A *` newline `B` is the product `A * B`.
- A simple definition body ends before an independent next-line expression: `P = 1` newline `2` is the definition followed by the root row `2`. A leading comma or an eligible binary role continues the owning body.
- The collected slots form the body's output: one slot is that value itself, and several form one sequence value. A caller sees that output only through a value boundary (VAL-06). At the program root, the emitted items are the program's top-level results, one output row each.
- Grouping comes only from values (parentheses, lists, results), never from line layout.

**Qualifications**
- A capture group `(a, b)` uses the same row loop, but from outside it is a value boundary.
- The display format of rows is presentation only.
- Evaluating a row gives its value, and a list in that value can still hold positions that are evaluated only when read (SEQ-02). The run reads its assembled output whole afterwards (RUN-07 (g)): `L = [tick()]` / `L, tick()` is `S[L[2], 1]`.

```katlang
A = 1, 2
B = { A*, (), [3] }
A
A*
(), 9
B
B.count
```
⇒ `S[S[1, 2], 1, 2, S[], 9, S[1, 2, S[], L[3]], 4]`

### VAL-08 — Element count, supplied items and emitted count are distinct measures

- Three different numbers answer "how many", and no consumer derives one from another implicitly:
  - (a) A value's **element count**, which `count(v)` reports: the number of elements in v's one-level collection view. A scalar counts 1; `()` and `[]` count 0 (COLL).
  - (b) The number of **items a written slot supplies** to a receiver. A non-spread slot supplies exactly 1, whatever its value; a slot supplies the value's elements only when explicitly spread (SUP).
  - (c) An expression's **emitted count**: the count its counted evaluation yields beside its value (FORMAL-05). It is 0 or 1 at every value boundary (VAL-06), and 0 exactly when the value is `()`. It exceeds 1 only for a spread and for row accumulation (VAL-07). It is not the number of items a non-spread slot contributes (VAL-04).
- Argument arity is checked against (b), never against (a) (CALL). "Arity" is metalanguage only: KatLang has no `arity` construct, so `arity` is an ordinary name.

**Qualifications**
- A callee's WRITTEN output-row count is none of the three measures and is not a property of any value, because every call result is one value. Yet callables with equal call results but different written row counts differ in three places:
  - Clause-family branch validation (PAT-03): `G(0) = 1, 2` with `G(x) = x` is `BranchOutputArityMismatch`, while `G(0) = (1, 2)` with `G(x) = x` is accepted.
  - Loop steps (LOOP-03): with `F(a, b) = b, a + b` and `G(a, b) = (b, a + b)`, `F(0, 1) == G(0, 1)` is `true`, yet `repeat(F(0, 1), 2)` gives `(1, 2)` while `repeat(G(0, 1), 2)` is `ArityMismatch`.
  - The `while` flag, the last item of the step's row supply (LOOP-06): with `S(x) = x + 1, x < 3` and `T(x) = (x + 1, x < 3)`, `S(0) == T(0)` is `true` and `while(S(0))` gives `3`, while `while(T(0))` is `TypeMismatch`.
- Public error kinds use "arity" for supply and emitted-slot cardinality only (RUN-07). An element of the wrong kind is `TypeMismatch`.

```katlang
P = 10, 20
Add(x, y) = x + y
Cnt(*xs) = xs.count
P.count, Cnt(P), Cnt(P*), Add(P*)
```
⇒ `S[2, 1, 2, 30]`

With the same `P` and `Add`, `Add(P)` and `count(P*)` are `ArityMismatch`.

### VAL-09 — Values carry no provenance

- In every consumer, a value's behaviour depends only on the value itself and on whether it was explicitly spread at that consumer.
- It never depends on the route that produced it: a literal, a parenthesized group, a property or alias, a call result, `if`, a selection, `first`/`last`, a block, a capture or a dot receiver. Likewise a string records nothing of where its text came from: the literal `'12'` and `12.string` are one value.
- Ordinary calculation values carry no written-source provenance. A call reference explicitly denotes an original supplied invocation plan, and transporting it preserves that identity without adding provenance-sensitive views to ordinary values.
- For non-reference values, storing a value in a property (`X = A[0]`) and using it later is indistinguishable, in value terms, from using the producing expression directly wherever that expression delivers a value, a directly written `while`/`repeat` result included. A generative reference follows the ordinary property cache: `R = Capture(F(1))` gives `R == R` true but `R == R()` false.

**Qualifications**
- The law is about VALUES. Algorithm identity on the algorithm channel is separate: a name and a written expression can differ in callability (ALGHO, CALL). A `meta` parameter captures the supplied COMPUTATION, not its value: with `Start = Step(0)`, `Step(0).while` loops while `Start.while` is the ordinary META refusal (CR-2).
- Whether and when a producing expression runs is governed by PROP and RUN: a zero-argument property read is cached, while `A()` evaluates afresh.
- The binder-specific consequence, that no collector, forwarding or dot mechanism carries per-item provenance, is VAR-04. A supplied cell keeps its written source as the suspended computation itself and for blame. That is no provenance record on a value.
- **Representation is not provenance.** `1.50` and `1.5` (or `-0` and `0`) are one value with different representations (VAL-11). The representation is data the value carries, produced by the operation, never a record of the route.

```katlang
A = (1, 2), 3
V = 1, 2
X = A[0]
Id(v) = v
Coll(*xs) = xs
Coll(V), Coll(X), Coll(A[0]), Coll(Id(V)), Coll((1, 2)), Coll(first(A)), Coll(if(true, V, 0)), V.Coll
```
⇒ `S[L[S[1, 2]], L[S[1, 2]], L[S[1, 2]], L[S[1, 2]], L[S[1, 2]], L[S[1, 2]], L[S[1, 2]], L[S[1, 2]]]`

### VAL-10 — A failure is not a value: a demanded failure ends the run, and nothing in the language can observe or recover from it

- Evaluating a demanded expression yields either one value (with its emitted count) or one failure: a structured error of exactly one kind. Context frames attached while the failure travels outward are presentation (FORMAL-06 keeps the innermost kind).
- A failure is not a value kind. It cannot be bound, stored in a property, passed as an argument value, collected, compared, selected, spread or tested. A supplied computation is not its value: one that would fail can be passed, forwarded and collected unevaluated (NEED-01, NEED-07, NEED-08), and it fails only if demanded.
- No construct catches, inspects, replaces or defaults a failure. There is no try/catch, no default-on-error and no error sentinel value (OP-06).
- A failure propagates outward through every enclosing operator, comparison, call, callback, loop iteration and output row, and becomes the single outcome of the run. The run then has no output: earlier completed rows are discarded and later rows never run.
- The reported failure is the first one RAISED in evaluation order: for supplied arguments and list positions, the order of first demand (NEED-03, CALL-02, SEQ-02); otherwise the orders of OP-03, BOOL-04, CMP-02, PAT-10 and the consuming construct.
- A program avoids a failing computation only by never demanding its value. RUN-08 is the complete, closed list of demand points. The most common avoidances are an undemanded property body (PROP-02), the unselected branch of builtin `if` (BOOL-05), a supplied argument never demanded as a value (CALL-02, CALL-06; a CALLABLE use is no VALUE demand, NEED-06), the right operand of an `and` or `or` whose left operand decides (BOOL-04), a list position that no consumer reads (SEQ-02), a `reduce` step that no later step needs (HO-02), and an uninvoked callback or loop step.
- A resource-limit failure is not avoided by leaving a value undemanded: once any evaluation that actually occurs reaches a limit, the run ends (RUN-03). Only code that is never evaluated reaches no limit.
- Completed run state survives a failure: cache entries that the owning evaluations of other keys created are kept, while the failed evaluation's own key gets none, not even a result that a re-entrant read of it computed (PROP-09). Because a demanded failure always ends the run, no later read can observe them from source.

**Qualifications**
- Front-end errors never reach evaluation (RUN-04, SYN-14). A root with unresolved implicit parameters fails before any row runs: `trace(1), x + 1` is `UnresolvedImplicitParams` with no host event (PAR-03).
- Resource limits and cancellation are host policy (RUN-03). Cancellation is a host exception, not a KatLang failure. A resource-limit failure is terminal: the demanded cell retains that completion, and the run's terminal budget prevents restarting it or continuing evaluation (NEED-02, NEED-09).
- Translation is not recovery. A spread reports its operand's OWN `MissingOutput` as `SpreadMissingOutput` and keeps a nested one (SUP-02). Context decoration never changes the kind.
- Implementations capture errors internally, but never turn one into a value: only to decorate or translate an error, keep a demanded computation's completed failure for its later demands (NEED-02), choose which of two failures a consumer reports, or probe name resolution and the zero-argument demand. None of these is a source construct, and none lets a run continue after a demanded failure.
- A demanded failure is the parameter's completed value outcome and is never re-derived, so its host effects happen once: `A = trace(1), 1 / 0` / `B = A` / `F(x) = x` / `F(B), trace(3)` is `DivisionByZero` with host log `[trace(1)]` (CALL-06).
- Host effects executed before the failure have happened. "No partial output" concerns the result, not host side effects.
- The run-level error outcome is RUN-07 and its route invariance RUN-01. VAL-10 states only the value-model half.

```katlang
Bad = trace(1) / 0
Ignore(f) = 0
Unused = Bad + 1
Ignore(Bad), if(false, Bad, 2)
```
⇒ `S[0, 2]`, with an empty host log: nothing demands `Bad`.

`trace(1), 1 / 0, trace(2)` is `DivisionByZero` with host log `[trace(1)]`.

### VAL-11 — A numeric datum carries value and representation: equality ignores representation, observers may not

*C#-only in its representation clauses: on Lean's `Int` every value has one representation (FORMAL-04).*

- **One value relation.** Numeric equality (`==`) is the language's ONE value relation: `Decimal128.Equals` at numeric leaves (NaN equals NaN, `-0 == 0`, the quantum is ignored, so `1 == 1.0 == 1.00`) and recursive structural equality over sequences and lists, kinds kept (CMP-03, CMP-05). It is "the same value" for every consumer: `==`/`!=`, `contains`, the classes of `distinct`, numeric literal patterns (PAT-05), duplicate clause heads (PAT-02) and repeated-name compatibility (PAT-09, NEED-04). There is no second, representation-sensitive numeric equality.
- **Representation is data, not provenance.** A number carries its exact Decimal128 representation: quantum, zero sign, NaN sign. It is produced by the operation from its operands' representations, never a record of the route, the source spelling or the evaluation path (VAL-09). Two `==`-equal data may carry different representations, and no `==` class has a canonical representation: the computed `0.5 + 0.5` and the literal `1.0` are bit-identical.
- **Representation-preserving operations.** Every value-carrying operation (binding, storage, selection, passing, collecting, sorting) carries the representation unchanged. Only an operation whose own contract says so normalizes it (transcendental Math results, `range` bounds; OP).
- **Collapsing operations state their representative.** An operation that collapses several `==`-equal inputs into one result states which input's representation survives, or states explicitly that the choice is unspecified. A repeated name binds one complete original contribution, never a splice: its first callable-bearing contribution, otherwise its first value-only one (PAT-09, NEED-04). `distinct` keeps the first occurrence (COLL-07). `order` keeps every input in a stable arrangement and `orderDesc` is its exact reverse (COLL-06). `min`/`max` follow OP-13, which fixes the signed-zero tie and leaves explicitly unspecified which of several same-signed `==`-equal inputs is returned. There is no global normalization and no synthesized representative.
- **Observers.** `.string` (OP-14) is the in-language observer of the quantum and among the observers of the zero sign: `1.50.string == 1.5.string` is `false`. IEEE-sign-sensitive Math results also see the zero sign (`atan2(0 * -1, -1) == atan2(0, -1)` is `false`; DOT-08, OP-14). Display and the host API's Decimal128 values observe the representation outside the language.
- **Presentation never feeds back.** Presentation (the decimal-places settings, RUN-06) may round, trim and pad the displayed digits, but never changes a value, a representation, `.string`, or any comparison, pattern, collection or arithmetic result.

**Qualifications**
- `.string` cannot show everything: positional text shows neither a positive quantum exponent (`1e3.string == 1000.string`) nor a NaN sign. Only the host API's `Decimal128` values expose them.
- Permuting one repeated name's contributions is governed by PAT-09 and NEED-04: acceptance on the stable domain is permutation-invariant, while failure reporting follows ordinary binding order, so the error category may change. With `A = 1.0`, `B = 1.00` and `P(x, x, x) = x`, `P(A, B, 2)` is `TypeMismatch` while `P(A, 2, B)` is `ArityMismatch`. There is no exact-representative permutation invariance.

```katlang
P(x, x) = x.string
A = 1.50
1.50 == 1.5, 1.50.string == 1.5.string, 0 == -0, 0.string == (-0).string
P(1.5, 1.50), P(1.50, 1.5), P(0, -0), P(-0, 0), P(1.5, A), P(A, 1.5)
distinct((1.0, 1)), order((1.0, 1)), (0.5 + 0.5).string
```
⇒ `S[true, false, true, false, '1.5', '1.50', '0', '-0', '1.50', '1.50', L[1.0], L[1.0, 1], '1.0']`

### VAL-12 — (retired: string interpolation was removed, STR-03)

## SEQ — Sequences, lists, and selection

KatLang has two collection kinds. A **sequence value** is the canonical value that commas, several outputs and surviving parentheses produce; its redundant structure normalizes, so there is no one-element sequence (VAL-03). A **list value** `[…]` keeps its exact shape: its own boundary is never normalized and it never equals a sequence. A list's ordinary elements are **positions**, each evaluated at most once, when it is first read (SEQ-02), while a sequence value's elements are values from the moment it exists: `[10, 1 / 0][0]` is `10`, and `(10, 1 / 0)[0]` is `DivisionByZero`. Apart from normalization, identity and when their elements are evaluated, the kinds behave alike, and neither is opened implicitly. An **opener** is an explicit construct that turns a collection into items; each opens exactly one boundary (SEQ-03). **Selection** (`A[i, …]`, `first`, `last`) chooses stored elements of the receiver's one-level positions and never opens them (SEQ-04, SEQ-05).

### SEQ-01 — A list is a second collection kind whose own boundary is never normalized

- A list value and a sequence value are different kinds. Structural equality between them is `false` even when their elements are equal: `[1, 2] == (1, 2)` and `[] == ()` are both `false`.
- A list boundary is never erased, collapsed or created by normalization: `[x]` is never `x`, `[[x]]` never `[x]`, `[[]]` never `[]`, and `[()]` never `[]`. A list keeps its exact length and nesting through storage, argument passing, selection and return.
- A list, `[]` included, is always one visible value with value count 1. Only `()` has value count 0 (VAL-06).
- Each kind has its own structural pattern: `(…)` matches sequence values only and `[…]` list values only (PAT-06).
- Kinds never convert implicitly. A list boundary is created only by a list literal, a collecting binding (VAR), or a collection-producing builtin (COLL); a host operation may also return one (RUN-05). It is removed only by an explicit opener (SEQ-03).

**Qualifications**
- Sequence structure inside a list element still normalizes: `[(7)]` is `[7]` (VAL-03). Redundant parentheses around a list are only grouping: `([1, 2])` is `[1, 2]` (SYN).
- Sequence structure arises from capture and output (VAL, SUP-06). So `(L*)` captures a list's items and then normalizes: with `S = 1, 2`, `[S*]`, `Coll(S*)` (with `Coll(*xs) = xs`), `take(S, 2)`, `map(S, {x})` and `*all = S` are all `[1, 2]` and `x, *rest = S` gives `rest = [2]`, while `([1, 2]*)` is `(1, 2)`, `([7]*)` is `7` and `([]*)` is `()`.
- Equality itself is owned by CMP; this rule fixes only that the two kinds are distinct values.

```katlang
[7] == 7, [] == (), [1, 2] == (1, 2), [[7]] == [7], ([1, 2]) == [1, 2], [(7)] == [7]
[7], [[]], [()], ((7))
```
⇒ `S[false, false, false, false, true, true, L[7], L[L[]], L[S[]], 7]`

### SEQ-02 — A list literal builds exactly one list from its written slots; each ordinary slot is a position evaluated at most once, when it is first read

- `[e1, …, en]` yields exactly one list value (emitted count 1) and evaluates none of its ordinary slots (issue #204). Each non-spread slot becomes one **position**: a deferred VALUE computation captured in the literal's own environment. A slot that is a parameter transports its existing cell while the literal is formed. An unavailable binding is refused there. Otherwise the argument and the position share one completion (NEED-01, PROP-08). A number, string or Boolean literal and `()` are their values.
- A spread slot is formed while the literal is built, as in every supply: its operand is evaluated, the level it opens is read in order, and its items enter as values (SUP-02); `()*` and `[]*` contribute nothing. A declaration-level output spread is formed the same way (SUP-08). The literal's cardinality is therefore known when it is built, and counting it or checking a bound reads no position.
- A position is evaluated at most once per LIST INSTANCE, when it is first read, and keeps its value or its ordinary failure for every later reader of that instance. Each evaluation of a literal creates a fresh list instance. A parameter slot still refers to its original argument cell (NEED-01). Effects, draws and failures follow the order in which positions are read, not the written order, and a position that no consumer reads is never evaluated.
- A non-spread slot contributes exactly one element: its value whole, whatever it is, including `()`, `[]`, a multi-output property's sequence value, a selection, and a block's output value. The literal opens nothing by itself.
- An output-less slot still occupies a position. `[1, {}]` has two positions, and reading its second position raises `MissingOutput`, including during a whole read.
- Bracket content is a pure expression list: a declaration inside brackets is a parse error (`[X = 1]`), and whitespace never separates slots (`[1 2]` and `Data[0 1]` are `UnseparatedSameLineItem`, SYN-07). Inside an open `[`, a newline separates slots as it does inside `(`: `[1` / `2, 3` / `]` on three lines is `[1, 2, 3]`.
- A nested capture or zero-parameter block as an element gives the same value and the same error position as the general path.
- A `[` that begins an expression or a slot, or stands on a later physical line, begins a new list literal. A `[` on the same physical line as a completed receiver expression (spaces and tabs allowed) opens that receiver's selector list instead (SEQ-05): `A[1]` and `A [1]` select from `A`, while `A, [1]` and `A` newline `[1]` are two slots. `[` is never a call delimiter.
- A list can hold itself through a position: `L = [L]` builds `L` without reading it, and `L.count` is `1`. Reading such a value whole reaches a list it is already inside, which is `DemandCycle`, never an endless read; a position whose computation reads itself (`L = [L[0]]`) is its own cell's `DemandCycle` (NEED-09).

**Qualifications**
- How a consumer reads positions belongs to that consumer: selection (SEQ-05), the collection builtins and their stages (COLL-04), structural patterns and deconstruction (NEED-04, PAT-08, VAR-05), spread (SUP-02), equality (CMP-03), and the run's output and host-operation arguments, which are read whole (RUN-07, RUN-05). Reading a collecting binding as a value demands its slice one level deep (NEED-07).
- A position keeps the context of the literal that built it, a detached one included (NEED-10, PROP-08). An input read its computation makes under a detached evaluation is judged where the position is read (PROP-08; formal ledger row R-1, qualified).
- *C#-only:* a diagnostic names an unread position `<deferred>` and never reads it, and a list of known cardinality reserves its positions when it is built (RUN-03).

```katlang
A = 1, 2
[trace(1), A, A*, (), [], { 4, 5 }, trace(6)]
```
⇒ `L[1, S[1, 2], 1, 2, S[], L[], S[4, 5], 6]` with host log `[trace(1), trace(6)]`: `A*` is formed while the list is built, and the run reads the list whole afterwards, left to right.

`[trace(1), trace(2)].count` is `2` with an empty host log, `[trace(1), trace(2)][1]` is `2` after `[trace(2)]`, and `[trace(1), (trace(2), trace(3))*][0]` is `1` after `[trace(2), trace(3), trace(1)]`: the spread was formed with the list. `X = [trace(1)]` / `X[0], X[0]` traces once, and `F = [trace(1)]` / `F()[0], F()[0]` twice. With `L = [tick(), tick(), tick()]`, the rows `L[2, 0, 2], L[0], tick()` are `S[S[1, 2, 1], 2, 3]`. `F(a) = [a, a][1] + a` / `F(trace(3))` is `6` after one `trace(3)`. A nested list is a position like any other: `[[1 / 0], 2][1]` is `2`, and `[[1 / 0], 2][0].count` is `1`. `Coll(*xs) = xs` / `Coll([1, {}])` raises `MissingOutput` when the run materializes its nested list. Counting `[1, {}]` needs only its cardinality. `L = [L]` / `L` is `DemandCycle`.

### SEQ-03 — Collections are opened only by explicit openers, one boundary at a time: the kind-blind openers open both kinds alike, and a structural pattern opens only its own kind

- A list is one opaque value everywhere outside the explicit openers, exactly as a sequence value is (values stay values, SUP-03, VAR). A call argument, fixed parameter, collected item, dot receiver, callback element, stored property, root row, loop-state slot and selected element each keep a list whole.
- A list never coerces to a number (`[5] + 1` is `TypeMismatch`) and never has a truth value (BOOL).
- The in-language openers are exactly: the spread marker `v*` (SUP-02); assignment deconstruction's unpacking receiver (VAR-05); the selection receiver's position view, which only chooses positions (SEQ-05); the post-binding view of a collection builtin's bound `collection` argument (COLL); and structural parameter patterns (PAT-06, PAT-08). `atoms` (COLL) is a separate recursive numeric projection, not an opener.
- Each opener opens exactly one boundary. The first four are kind-blind: they share one one-level view in which a sequence value or a list offers its immediate elements and any other value is itself, one item. They expose the same one-level shape for a sequence and a list with the same elements. A list may still have deferred positions (SEQ-02).
- A structural pattern is kind-specific: a sequence pattern opens only a sequence value and a list pattern only a list, and neither treats a scalar as a one-item structure (PAT-06).
- An argument view `R.Arguments` is not read as one item: selection, `count`, `first` and `last` read its argument cells as positions (SEQ-05), a spread transports or refuses it (SUP-02), and every other collection builtin refuses it as its whole collection (`TypeMismatch`).

**Qualifications**
- Opening is never recursive: `count([1, [2], 3])` is `3`, and `Coll([[1, 2]]*)` supplies the one list `[1, 2]`.
- Deconstruction opens the one value its right-hand side captures. `x, *xs = [[1, 2]]` gives `xs = []`, while `x, *xs = (A*)` with `A = [[1, 2]]` gives `xs = [2]`. The difference comes from capture normalization of the spread supply (SUP-06), not from a kind asymmetry.
- The host numeric projection (`RunFlat`, `RunResult.Success.Atoms`) sees through both kinds recursively; it is outside the language and never feeds back into evaluation.

*Open: whether assignment deconstruction should treat an `R.Arguments` view as one opaque item (today) or refuse it like a value-position spread (Q-84).*

```katlang
S = 1, 2
L = [1, 2]
Coll(*xs) = xs
P((x, y)) = x + y
LP([x, y]) = x + y
count(S), count(L), Coll(S), Coll(L), P(S), LP(L), (L*), [S*]
```
⇒ `S[2, 2, L[S[1, 2]], L[L[1, 2]], 3, 3, S[1, 2], L[1, 2]]`

With `Add(x, y) = x + y`, `Add([1, 2])` is `ArityMismatch` while `Add([1, 2]*)` is `3`. `P(L)` and `LP(S)` are `TypeMismatch`, each naming the expected and the received kind.

### SEQ-04 — Selection chooses stored values and never opens them

- `A[i]`, `first(A)` and `last(A)` choose one element of the receiver's position view (SEQ-05) and return it exactly as stored; for a list position, that is the value its one demand produced (SEQ-02). `A[i1, …, in]` chooses one element per supplied index, in supplied order, a repeated index repeating the stored element. A chosen element is never rebuilt, normalized, projected or opened: a selected sequence stays one sequence value, a selected list one exact list, a selected `()` the value `()`.
- The result passes through the ordinary value boundary (VAL-06), so a selected `()` spreads to nothing and any other selected value is one value.
- Only the result grouping is normalized, by ordinary capture (SUP-06): zero selections give `()`, one gives the chosen element itself, several give one sequence of the chosen elements, each kept whole (a chosen `()` or `[]` stays an element). No selector count survives. A multi-selection is one sequence value, never an argument supply.
- The selection's origin is forgotten. Every later consumer sees exactly what it would see for the same value from any other source, including a stored `X = A[0]`: fixed parameter, collector, dot receiver, pattern, `count`, list slot, root row and loop-state slot alike.
- Only an explicit spread opens a selected value, and only by one boundary: `A[0]*` is `(A[0])*`. Chained selection peels one boundary per bracket (`A[0][1]`), while commas inside one bracket select siblings (`A[0, 1]`).
- For every value `v` in hand, `first(v)` and `v[0]`, and `last(v)` and `v[count(v) - 1]`, have the same outcome: the same value and count, or the same `BadIndex` when the value has no requested position. These are laws over a value in hand, not rewrites of effectful expressions: `last(BuildData())` invokes `BuildData` once, `BuildData()[count(BuildData()) - 1]` twice. Higher-order callback items are selected values under the same rule (HO-03).
- `first(())`, `first([])`, `last(())`, `last([])` and `().first` are `BadIndex`, exactly as `()[0]` and `[][0]` are.

**Qualifications**
- `first`/`last` read their bound collection through the builtin one-level view and selection reads its receiver through the position view; these are the same function, so they agree on every kind, scalars and strings included: `first(7)` is `7[0]` is `7`, and `first('abc')` is `'abc'[0]`.
- A selected `()` written as a non-spread root row or loop-state slot still occupies one visible slot, because those receivers count every non-spread row as one slot (VAL-07), not because of a selection-specific count. `count(A[0])` opens the selected value one level because `count` is an opener (COLL), not because selection opens.

```katlang
A = (1, 2), 3
B = (), 1
Coll(*xs) = xs
X = A[0]
A[0], Coll(A[0], 3), A[0].Coll, X.Coll, (A[0])*.Coll, first(A), last(A), B[0].Coll, (B[0])*.Coll
```
⇒ `S[S[1, 2], L[S[1, 2], 3], L[S[1, 2]], L[S[1, 2]], L[1, 2], S[1, 2], 3, L[S[]], L[]]`

With `Data = [10, 20, 30]`, `Data[2, 0, 2]` is `(30, 10, 30)` and `Data[]` is `()`. With `Nested = [(10, 20), [30, 40], (), []]`, `Nested[2, 3]` is `((), [])`. With `Data = [(10, 20), 30]`, `[Data[0]*]` is `[10, 20]`. With `Add(x, y) = x + y` and `Data = [10, 20]`, `Add(Data[0, 1])` is `ArityMismatch` and `Add(Data[0, 1]*)` is `30`.

### SEQ-05 — Selection positions are the target's zero-based one-level positions, and a missing position is an error

- **Evaluation order.** When `T[s1, …, sn]` is demanded: (1) the receiver `T` supplies its retained collector slice (NEED-07) or is demanded once through its ordinary value path (`Data` is the ordinary cached read; `Data()` is one fresh invocation that never reads or replaces the entry, though its owning success may establish an empty entry, PROP-05, PROP-06), and a receiver failure stops the selection before any selector runs, even for `T[]`; (2) the selector list forms its supply exactly like a call's argument list (CALL, NEED-07): explicit spread selectors run during formation in written order, ordinary selectors stay suspended; (3) the supplied indices are demanded, validated and selected left to right, and the first failure ends the selection; (4) the chosen elements are normalized (SEQ-04). Formation precedes validation.
- **Positions.** A sequence value or a list offers its immediate elements, in order. Any other value (number, string, Boolean) is one position, position 0: `7[0]` is `7`, `'ab'[0]` is `'ab'`, the empty string too (`''[0]` is `''`), and a string is never its characters. `()` and `[]` have no positions. An argument view `R.Arguments` offers the captured call's effective argument cells: each selector is validated before the view's supply is read, and only the selected cells are demanded (`R.Arguments[]` reads nothing).
- **List positions are read on demand.** Over a list, a selection reads only the positions it names, in written order, each through its one VALUE demand (SEQ-02). A selector's bound is checked first, against the known cardinality or by discovering positions up to the one it names (a `filter` stage, COLL-04), and a repeated selector reads the position's completed value: `[10, 1 / 0][0]` is `10`, `[1, 1 / 0][5]` is `BadIndex`, and `[trace(1), trace(2), trace(3)][2, 0]` is `S[3, 1]` after `[trace(3), trace(1)]`.
- `count`, `first`, `last` and selection read this one immediate positional view (COLL): `count('abc')` is `1` and `'abc'[1]` is `BadIndex`. The view is distinct from argument cardinality, emitted count and explicit-spread supply.
- Positions are zero-based and counted from the front only. A numeric selector that names no position is `BadIndex`, never a default or empty value; in C# this covers negative, fractional, non-finite and beyond-int-range selectors. A selector whose value is not numeric (string, Boolean, `()`, sequence, list) is `TypeMismatch`.
- A selector is a whole expression slot of the selector list: `A[i + 1]`, `A[B.I]` and `A[f(1)]` select the positions those expressions name, and `A[-1]` is `BadIndex`. There is no negative indexing, slicing, string-character indexing, mutation or user-defined indexing, and `[…]` never resolves a user-visible name.
- Grammar: the `[` stands on the receiver's physical line (spaces and tabs allowed); once open, the list may span lines like a list literal. Commas select siblings and chained brackets descend: `Grid[0, 1]` is two elements of `Grid`, `Grid[0][1]` one element of one. The colon form `A:i` is retired and is the parse error `RetiredColonSelection`.
- A spread is a legal whole selector slot (`Data[Indexes*]` supplies the items of `Indexes` as selectors); a collection-valued selector that is not spread is one supplied value (`Data[(0, 1)]` is `TypeMismatch`). A star before `[` is multiplication (SYN-11): `A*[0]` is `A * [0]`; capture-then-select is `(A*)[0]`, select-then-spread `A[0]*`.

**Qualifications**
- The error category of each bad selector is part of the contract (FORMAL-06): `TypeMismatch` for a non-number, `BadIndex` for a number naming no position. `first`/`last` of an empty collection use the same `BadIndex` rule (SEQ-04). Fractional and non-finite selectors exist only in C#; Lean selectors are `Int`.

```katlang
Nums = 10, 20, 30
Nums[0], Nums[2], [[1, 2], [3, 4]][1][0], 7[0], 'ab'[0], trace(Nums)[trace(1)]
```
⇒ `S[10, 30, 3, 7, 'ab', 20]` with host log `[trace(S[10, 20, 30]), trace(1)]`

`Nums[3]`, `Nums[1.5]` and `[][0]` are `BadIndex`; `A['x']`, `A[true]` and `A[()]` are `TypeMismatch`. `[10, 20][99, 1 / 0]` is `BadIndex` (`1 / 0` is never demanded) while `[10, 20][99, (1 / 0)*]` is `DivisionByZero`, because the spread runs during formation. `(1/0)[trace(0)]` is `DivisionByZero` and `trace(0)` never runs. With `Is = [2, 0]`, `Nums[Is*], Nums[1, Is*]` gives `S[30, 10]`, `S[20, 30, 10]`.

## SUP — Item supply: slots, spread, and capture

KatLang separates values from item supplies. A **supply** is the ordered list of items that written slots hand to a **receiver**, and the receiver decides what the items become: root and body output make rows, a capture makes one value, a list literal one list, a call argument slots, a collector one list. Three operations connect the two worlds: `spread : Value -> Supply` (the postfix marker `v*`), `capture : Supply -> Value` (a surviving parenthesized group, SUP-06) and `collect : Supply -> ListValue` (VAR). This section fixes how a supply is assembled, what spread opens and never opens, where a spread may be written, and what a capture is and is not.

### SUP-01 — A supply is built slot by slot: each non-spread slot supplies exactly one item, each spread slot supplies its spread items

- Every expression-list receiver assembles its supply from its written slots in written order. Receivers are root and body output rows, a surviving parenthesized group, list-literal elements, call and dot-call argument lists, a postfix selector list (SEQ-05), a definition body, and a loop step's output rows (which form the next state, LOOP-03).
- A slot without a spread marker contributes exactly one item: its value, whatever it is (number, string, Boolean, sequence, list, `()`, `[]`) and whatever produced it. No construct turns a non-spread slot into zero items or into several; a nested `while`/`repeat` result is one value (LOOP-07).
- A slot `E*` contributes the items of SUP-02.
- A spread creates no value of its own. The receiver decides: a capture yields one canonical value (SUP-06), a list literal one exact list (SEQ-02), a call binds argument slots (CALL), a collector one exact list (VAR), root and body output emit rows (VAL-07), a loop step's rows become the next state's slots (LOOP-03).
- Evaluation follows the receiver. Root and body output rows, a surviving parenthesized group, a definition body and a `repeat` step's rows evaluate each slot exactly once in written order (NEED-03). A list literal evaluates only its spread slots while it is built; each of its other slots is a position, evaluated at most once, when it is read (SEQ-02). A `while` receiver discovers its flag by forming rows right to left until one supplies an item, then forms the earlier rows left to right only after `true`; each row is formed at most once (LOOP-06). A call, dot-call or selector list evaluates only its arbitrary spread operands while the supply is formed, left to right among them (SUP-02, NEED-07); a spread whose last star opens an argument view transports that call's original computations unevaluated (CR-11). Each non-spread call slot is a supplied computation evaluated at most once, on its first value demand, or never (CALL-02, CALL-06). Re-spreading a known collector slice transfers its computations unevaluated (VAR-03).

**Qualifications**
- A same-line item after a spread needs a comma (`A*, B`); without it `A* B` is multiplication. An attached `A*` at the end of a line already ends its item (SYN-11).
- With `Fib(a, b) = b, a + b`, a non-spread `repeat(Fib(0, 1), 1)` slot is one item in every receiver, loop-step receiver included: `Nest(x) = repeat(Fib(0, 1), 1), x` / `repeat(Nest(5), 1)` is `((1, 1), 5)`, while `Nest(x) = { repeat(Fib(0, 1), 1)*, x }` supplies the items, `(1, 1, 5)`.

```katlang
A = [1, 2]
X = { A* }
Coll(*xs) = xs
Add(x, y) = x + y
X
[0, A*, ()]
Coll(A*, ())
Add(A*)
A*,
9
```
⇒ `S[S[1, 2], L[0, 1, 2, S[]], L[1, 2, S[]], 3, 1, 2, 9]`

The same `A*` becomes a captured sequence (the property body), list elements, collected items, two fixed arguments, and two root rows; the unspread `()` stays one visible item in both the list and the collector. A capture and the rows evaluate in written order (`(tick(), tick(), (), tock())` gives `(1, 2, (), 1)`, SUP-06), while a list row's remaining positions are read when the run materializes its assembled output: `[trace(1), [trace(2), trace(3)]], trace(4)` is `S[L[1, L[2, 3]], 4]` after `[trace(4), trace(1), trace(2), trace(3)]` (RUN-07). With `F(x, y) = y, x`, `F(trace(1), trace(2))` is `(2, 1)` after `trace(2), trace(1)` (the body's rows are in order, the argument computations run in demand order), and with `F(x, y) = x`, `F(1, trace(2))` never runs `trace(2)`. A known collector slice is transferred, an arbitrary spread is evaluated: with `F(a, b) = a` and `Fwd(*xs) = F(xs*)`, `Fwd(trace(1), trace(2))` logs only `trace(1)`, while `Mk(a, b) = [a, b]` / `F(Mk(trace(1), trace(2))*)` logs both. Spread formation precedes ordinary demand in every callable: `range(trace(1), trace(3)*)` and `F(trace(1), trace(3)*)` with `F(a, b) = a, b` both log `trace(3)` then `trace(1)`.

### SUP-02 — Spread opens exactly one boundary of its operand's value; any other value supplies itself

- `E*` evaluates `E` exactly once and supplies the items of its value `v`: a sequence value its immediate items, a list its immediate elements, every other value (number, string, Boolean, call reference) itself as one item. Only that one boundary is opened: nested sequences and lists stay intact as items. `()*` and `[]*` supply zero items, and inserting them anywhere in a supply changes nothing.
- Spread is total with one exception: an argument view `R.Arguments` is never opened into values. In an argument or selector supply a spread whose last star opens a view transports the captured call's original argument cells, undemanded (CALL-02); any other star that would open a view (`[R.Arguments*]`, an inner star of `F(R.Arguments**)`) is `TypeMismatch`.
- A missing output is never an empty supply. A failure that originates within the operand's dependencies or arguments is preserved with its category, cause and blame. Only the operand's own missing output becomes `SpreadMissingOutput`, at the operand's span, retaining the property, call and argument context. The own missing output is the output check of the computation the operand directly denotes or invokes: `{}*`, `G*`, `G()*`, and through a parameter or alias, which denote the supplied computation (`P(x) = x*` / `P({})`).
- A `MissingOutput` met inside the operand's evaluation is nested and keeps its kind, context frames, blame and location; the spread adds one frame, `while evaluating spread operand …`. Nested places include a dependency (`H = G + 1` / `H*`), an argument (`F({})*`), a written output row (`{ G }*`), a constructed value or operator operand (`(G, 1)*`, `[G]*`, `(G + 1)*`), a collector element, a builtin's argument or callback, an argument a pattern or clause inspects, and a dot intrinsic's receiver. Every other error, an inner spread's own `SpreadMissingOutput` included, passes through unchanged. This holds for every operand shape, and the failure's origin is part of the completed failure, so it survives memoization for every consumer.
- In a call (user callable, clause family or builtin alike) evaluating a spread operand is part of assembling the supply: if it fails, that failure is the call's failure, raised before the arity check, clause selection or binding, and before any later slot. A failed spread never supplies an item: `Bad = 1 / 0` / `take(Bad*)` is `DivisionByZero`, `count(1, {}*)` is `SpreadMissingOutput`, and `count(1, H*)` with `H = G + 1` is `G`'s `MissingOutput`.
- Spread is the only general value-to-supply operation; the explicit openers are listed in SEQ-03.

**Qualifications**
- `A[0]*` is `(A[0])*`, and a multi-selection spreads its chosen elements: `A[0, 1]*` (SEQ-04).
- Over a list, the spread reads the positions of the level it opens, in order, and supplies their values; deeper lists keep their own positions (SEQ-02): `F(*xs) = xs.count` / `F([1, 1 / 0]*)` is `DivisionByZero`, while `F([1, 1 / 0])` is `1`, and `[[trace(1)], trace(2)]*` is `S[L[1], 2]` after `[trace(2), trace(1)]`.
- An unspread output-less argument is `MissingOutput` blamed at the argument (`Coll({})`, CALL); once the call is a spread operand (`Coll({})*`) that blame is kept under the spread frame.
- Only the operand's own `MissingOutput` is rewritten: with `F(x, y) = x`, `F(1)*` is `ArityMismatch`, and `Coll((1 + 'a')*)` is `TypeMismatch`.
- A loop step's top-level spread output row supplies its items exactly as everywhere: `Step((a, b)) = { (b, a + b)* }` supplies two next-state slots, which its one-pattern head cannot rebind, so `Step((0, 1)).repeat(3)` is `ArityMismatch`; `Step((a, b)) = (b, a + b)` keeps one slot (`(2, 3)`); the flat two-row `Step((a, b)) = b, a + b` is the same `ArityMismatch`.

```katlang
Coll(*xs) = xs
Coll((1, (2, 3))*, [(4, 5), [6]]*, 'ab'*, true*, ()*, []*)
```
⇒ `L[1, S[2, 3], S[4, 5], L[6], 'ab', true]`

```katlang
E = {}
Coll(*xs) = xs
Coll(E*)
```
⇒ `SpreadMissingOutput`

`{A = 1}*` is `SpreadMissingOutput`. `Coll(tick()*, (tick(), tick())*)` gives `L[1, 2, 3]`: each operand is evaluated once. With `G = { public X = 1 }`, `Coll(*xs) = xs`, `F(x) = x` and `Cnt(*xs) = xs.count`:

| Program | Unspread | Spread |
|---|---|---|
| `H = G + 1`: `H` vs `H*` | `MissingOutput` at `G` | `MissingOutput` at `G`, under the spread frame |
| `(G + 1)*` | n/a | `MissingOutput` at `G` |
| `Coll({})` vs `Coll({})*` | `MissingOutput` blamed at the argument | same report and span, under the spread frame |
| `F({})` vs `F({})*` | `MissingOutput` at the parameter read `x` | same report and span, under the spread frame |
| `Cnt(F(G))` vs `Cnt(F(G)*)` | `MissingOutput` | `MissingOutput` at `G` |
| `G*`, `G()*`, `{}*`, `P(x) = x*` / `P({})` | n/a | `SpreadMissingOutput` (the operand's own) |

### SUP-03 — Spread-produced items are established items: no receiver ever reopens them

- An item that a spread supplied is, for every receiver, an ordinary one-item value: a fixed parameter binds it whole, a collector collects it as one element, a callback receives it as one argument, root output emits it as one row.
- No binder, collector, callback, dot-call or builtin adapter opens a spread-produced item again. One level deeper is reached only by writing another explicit opener (SEQ-03): another spread layer (SUP-04), a structural pattern (PAT), deconstruction (VAR), the selection receiver's position view (SEQ-05), or a collection builtin's view of its bound `collection` argument (COLL).
- So with `P = [(1, 2)]`, `count(P*)` is `2`: the one item `(1, 2)` binds whole as `collection` and the builtin's own one-level view counts its elements, while `Add(a, b) = a + b` / `P*.Add` is `ArityMismatch` (one argument).

**Qualifications**
- Assignment deconstruction first captures a written spread right-hand side and only then opens a lone structure, so it reaches one level beyond the bare right-hand side. With `V = [(1, 2)]`, `x, y = V*` and `x, y = (V*)` both bind `x + y` to `3`, while `x, y = V` is `ArityMismatch`. This is an explicit capture followed by the explicit deconstruction opener, not a receiver reopening an item (VAR).

```katlang
Coll(*xs) = xs
Id(x) = x
AddPair((x, y)) = x + y
P = [(1, 2)]
Coll(P*)
Id(P*)
AddPair(P*)
```
⇒ `S[L[S[1, 2]], S[1, 2], 3]`

With `Add(x, y) = x + y` and `P = [(1, 2)]`, `Add(P*)` is `ArityMismatch`: the one spread item `(1, 2)` is not reopened; only the explicit pattern `(x, y)` opens it.

### SUP-04 — Stacked spread is composition through capture, never recursive flattening: `E**` means `(E*)*`

- In every spread position of SYN-11, each additional written star re-captures the previous layer's supply as one value, by ordinary capture (SUP-06), and then spreads that value. So `E**` supplies the items of `capture(items(v))`. A multi-item supply is therefore a fixed point, a zero-item supply stays empty, and a further boundary is exposed only when the previous layer supplied exactly one structured item (singleton capture collapses to that item, and the next star opens it).
- `E**` is never "flatten all levels". The operand is evaluated exactly once, however many stars there are.

**Qualifications**
- Spread is not idempotent: `[[7]]*` is not `[[7]]**`. The intermediate capture turns a multi-element list into a sequence; that conversion is invisible because the items are re-spread.
- `value**next` is not exponentiation: it is a spread used as a multiplication operand and is rejected (`2**3` is `MisplacedSpread`, SUP-05).

```katlang
Coll(*xs) = xs
A = [[1, 2], [3, 4]]
Coll(A*)
Coll(A**)
Coll((A*)*)
Coll([[7]]*)
Coll([[7]]**)
Coll(([[7]]*)*)
Coll([[[7]]]***)
Coll([]**)
```
⇒ `S[L[L[1, 2], L[3, 4]], L[L[1, 2], L[3, 4]], L[L[1, 2], L[3, 4]], L[L[7]], L[7], L[7], L[7], L[]]`

Stacked spread inside a planned loop body agrees: `Step(i, s) = i + 1, s + count(([[i, i]]**, (i, 7)*, ()*))` / `Step(0, 0).repeat(4)` is `(4, 16)`.

### SUP-05 — A spread is a slot-level construct, not a value: legal only as a whole slot, as a spread operand, or as the fluent receiver

*C#-only by design: placement is parser territory.*

- A spread expression may appear only as a whole expression-list slot (a root or body row, a call argument, a group or list element, a definition-body slot, a selector slot such as `Data[Indexes*]`); as the operand of another spread (`E**`); or as the fluent receiver `E*.F(args)`, which lowers at parse time to the ordinary lexical call `F(E*, args)` with no structural member lookup (DOT).
- As a unary, binary or comparison operand, a spread is the parse error `MisplacedSpread`. A star before `[` is never a spread receiver: `A*[0]` is the multiplication `A * [0]` (SYN-11).
- Grouping changes the construct deliberately: `(E)*` is `E*` because a one-slot non-spread group is erased (SYN); `(E*)` is a capture (SUP-06), so `(A*).F` is `F((A*))`, one argument; `A[0]*` selects and then spreads; `(A*)[0]` captures and then selects.

**Qualifications**
- SYN-11 decides the syntactic role of a star (a line-final star is classified by attachment: attached spreads and completes, detached multiplies; a star with a same-line follower multiplies unless closed by a comma, closer or fluent dot). SUP governs the resulting supply.
- `A*.count` is `count(A*)`, an `ArityMismatch` for `count(collection)` when `A` has several items; `(A*).count` counts one captured value (`3` for `A = (1, 2, 3)`, `2` for `A = [[1, 2], [3, 4]]`).
- `open A*, A` is rejected by open-form validation (`BadOpenForm`, MOD).
- With `A = 2` and `B = 3`, `A *` newline `B*, 0` rejects the right-hand spread as a multiplication operand (`MisplacedSpread`), while `A*` newline `B*, 0` is two spread rows. `Coll(A *)` is `InvalidSpreadMarker`.

```katlang
A = [[1, 2], [3, 4]]
Coll(*xs) = xs
Coll(A*)
[0, A*]
A*.Coll
(A)*.Coll
A[0]*,
(A*)[0]
```
⇒ `S[L[L[1, 2], L[3, 4]], L[0, L[1, 2], L[3, 4]], L[L[1, 2], L[3, 4]], L[L[1, 2], L[3, 4]], 1, 2, L[1, 2]]`

With `A = [1, 2]`, each of `A* + 1`, `1 < A*, 0`, `-A*, 0` and `A* == A*, 0` is `MisplacedSpread`. With `A = [[1, 2], [3, 4]]` and `B = [1, 0]`, `A[B*]` is `S[L[3, 4], L[1, 2]]`.

### SUP-06 — Capture turns a supply into one canonical value: `()` for no items, the item itself for one, one sequence for several

- A parenthesized group survives as a capture exactly when its parentheses do something: it has two or more slots, or its single slot is a spread (`(A*)`). Every one-slot non-spread group is erased (SYN).
- A capture owns no scope (its free names belong to the enclosing algorithm, and declarations are not allowed inside it), evaluates its slots in the surrounding context in written order, each exactly once, and captures the supply into one value: zero items give `()`, one item gives that item unchanged, several give one sequence value of those items.
- No list survives a spread-then-capture: `([7]*)` is `7` and `([]*)` is `()`. In value position a capture is a value boundary, re-counted by value count (VAL).
- Capture and collect are different operations on the same supply. Capture normalizes to a sequence; `*xs` collects an exact list and never erases a singleton (VAR).
- Capture is the only way to build a sequence from several items and the only written way to concatenate sequences (`(A*, B*)`); nothing joins text (VAL-02).

**Qualifications**
- `()` is the empty-sequence node, not a capture; `((1, 2))` is the pair itself and `(())` is `()`. The rule deciding which groups survive is C#-only; Lean sees only the resulting `.capture`.
- A list literal is the other materialization. It is exact, and it evaluates its ordinary slots only when they are read, while a capture evaluates every slot when it is formed: `[10, 1 / 0][0]` is `10`, and `(10, 1 / 0)[0]` is `DivisionByZero` (SEQ-02).
- A capture element is a value role for implicit-parameter lifting (PAR-07): with `A = x + 1`, `F = (A + 1, 2)` / `F(3)` is `(5, 2)` and `F = (A, 2)` / `F(3)` is `(4, 2)`.

```katlang
A = [1, 2, 3]
B = 4, 5
Coll(*xs) = xs
(A*)
(B*, 6)
(A*, B*)
([7]*)
([]*)
(A, B)
Coll(A*)
```
⇒ `S[S[1, 2, 3], S[4, 5, 6], S[1, 2, 3, 4, 5], 7, S[], S[L[1, 2, 3], S[4, 5]], L[1, 2, 3]]`

The last two rows differ: `(A, B)` keeps both values whole, and the same spread becomes a sequence under capture (`(A*)`) but a list under collect (`Coll(A*)`). `(tick(), tick(), (), tock())` gives `(1, 2, (), 1)`: written order, the `()` slot visible, each slot evaluated once. With `A = x + 1`, `F = (x, 2)` / `F(5)` is `(5, 2)`: the capture's free `x` is `F`'s implicit parameter.

### SUP-07 — A capture is a value, never an algorithm identity: no callable, no structural members, no open target

- A surviving capture (SUP-06) never exposes the algorithm identity of anything written inside it.
- **Argument.** As a user-call argument it binds on the value channel only; calling the parameter is `NotAnAlgorithm`, and nothing inside the capture is evaluated to find that out (NEED-06). Evaluating the capture (a value demand) evaluates its elements, so an enclosed bare callable is demanded with zero arguments (CALL-05), unless the enclosing body infers its parameters, where a capture element's value role lifts a callable that requires arguments first (PAR-07).
- **Builtin slot.** In a builtin callback slot it has no callable identity, so the slot reports `NotAnAlgorithm` when the builtin needs to invoke it, exactly as a user parameter does. A loop's step is a `meta step` parameter (LOOP-01): a capture is no written invocation, so binding refuses it at once with `NotAnAlgorithm` ("meta: not a supplied call computation", CR-2), before `repeat`'s count.
- **Receiver.** As a dot receiver it has no structural members: `(Obj*).V` and `(Obj, Obj).V` fall back lexically, passing the captured value as the leading argument (DOT, RES).
- **Open target.** It is never an `open` target (`BadOpenForm`).
- Brace blocks `{...}` are the opposite construct: every `AlgorithmExpr` carries algorithm identity whatever its parameter or row count (ALG-01), including a multi-row block `{a, b}` whose value equals the capture `(a, b)`.

**Qualifications**
- With `Call0(g) = g()`, `(1, 2, 3) == {1, 2, 3}` is `true` and `Call0({1, 2, 3})` is `(1, 2, 3)`, while `Call0((1, 2, 3))` is `NotAnAlgorithm`. With `Const = 5`, `Call0((Const)), Call0(Const), Call0({Const, Const})` gives `5, 5, (5, 5)`: the redundant group is erased and the block carries identity. In a builtin value slot a zero-declaration block is one value exactly like a capture: `count({1, 2, 3})` is `3`. A block additionally owns a scope, which a capture never does.
- A capture in callee position is reachable only from a host-built AST (Lean `captureCalleeIsAValueThunk`); source `(F, F)(1)` is `UnseparatedSameLineItem`. This shape is outside the source-reachable core (FORMAL-08).

```katlang
Apply(f) = f(9)
Call0(g) = g()
Inc(x) = x + 1
V(x) = 99
Obj = {
  public V = 7
  0
}
Apply(Inc)
Apply((Inc))
Call0({1, 2})
Obj.V
(Obj).V
(Obj*).V
(Obj, Obj).V
```
⇒ `S[10, 10, S[1, 2], 7, 7, 99, 99]`

The redundant group `(Inc)` / `(Obj)` is erased, so identity and members pass through it; the genuine captures `(Obj*)` and `(Obj, Obj)` fall back to the lexical `V`. Failures:

| Program | Result |
|---|---|
| `Apply((Inc, Inc))` at the root | `UnresolvedImplicitParams`: a capture element is a value role, so `Inc` lifts and the never-called root needs `x` (PAR-07) |
| `Probe(u) = Apply((Inc, Inc))` / `Probe(0)` | `NotAnAlgorithm`: `f(9)` projects the capture, which has no callable identity |
| `Id(v) = v` / `Probe(u) = Id((Inc, Inc))` / `Probe(0)` | `ArityMismatch`: a value demand of the capture demands the bare `Inc` with zero arguments (PAR-04, CALL-05) |
| `Call0((1, 2))`; `A = 1, 2` / `Apply((A*))`; `map([1, 2], (5, 6))` | `NotAnAlgorithm` |
| `open (M, M)` and `open (M*)` | `BadOpenForm` |

### SUP-08 — A declaration's output-spreading marker changes no algorithm: every eligible call that resolves statically to a marked declaration is elaborated as its written-`*` counterpart

*C#-only by design: front-end elaboration, like Grace (PAR-06). Lean evaluates the inserted ordinary spreads and does not certify where they were inserted.*

- **The marker.** A declaration may carry one postfix `*` directly attached to its name or to its parameter list (`A* = x, y`, `A(x, y)* = x, y`; SYN-11, SYN-12), on every clause of a family or on none. The marker leaves the algorithm unchanged: its parameters, inference, body and result value stay the same.
- **Elaboration.** Every written, lifted or bare-forwarded call that the front end resolves statically, through transparent references, to that declaration is elaborated with the existing spread (SUP-02) wherever a written `*` supplies items: whole rows, argument slots of any callee and selector slots, list and multi-slot group elements, the operand of a written spread (`A(1, 2)*` is `A(1, 2)**`, SUP-04), and the receiver of an extension call. Every other value position keeps the call's one value: operator and comparison operands, selection receivers, receivers of intrinsic edges, and callees.
- **The counterpart.** A marked program IS the program with the markers removed and `*` written after each eligible call. That includes which references formula lifting turns into calls (PAR-07) and the order of inferred parameters (PAR-05); for a call that lifting creates, the counterpart writes `*` after the bare reference. Evaluation, call by need, caching and Lean's core are therefore unchanged.
- **What never spreads.** A read is not a call: a bare reference never spreads, and of a marked zero-parameter declaration only the explicit call `P()` does. Calls through a parameter, runtime-target aliases (FWD-04), `R.Algorithm(…)` and `R.Invoke()` routes, callbacks and loop iterations do not acquire the marker.
- **Aliases, carriers and wrappers.** A transparent alias inherits its target's marker. A transparent or runtime-target alias, an `.Algorithm` link that stays a calculation and a module holder cannot declare one (`OutputSpreadMarkerOnAlias`), and neither can a deconstruction target (`OutputSpreadMarkerOnDeconstructionTarget`). A structural forwarding carrier (`B* = { A }`, FWD-03) may carry its own marker. An explicit wrapper (`W(x, y) = A(x, y)`) and a bare-forwarding body are declarations of their own: calls to them spread only if they are marked.
- **D1: a marked extension edge is the lowered call.** `A(x, y).F(3)`, with `A` marked and `.F` an extension call, is `F(A(x, y)*, 3)` from parameter detection onward, exactly what the written `A(x, y)*.F(3)` is (DOT-07). So `H = A(x, y).F(3)` infers `H(F, x, y)`. Every other dot edge keeps its receiver-first order (DOT-05).
- **D2: a lifted marked call ends the known argument positions.** A marked call that formula lifting creates makes the later argument positions unknown to the lifting roles exactly as a written spread does (PAR-07). Roles and spread slots are decided together, left to right, before signature selection, from static facts: a final signature, or own parameters that require an argument, decide a lift.
  - A bare reference to a marked declaration is a read (no spread, no role change) when the declaration has no required parameter of its own and nothing its rows reach can lift one. A value-role reference can lift when its callee requires a supplied argument, or is an open declaration that has a required parameter of its own or whose own rows can lift, decided the same way; a link stays conservative. Declarations that read only each other cannot lift.
  - Every other case is a selection result. At a bare marked reference it is the front-end error `OutputSpreadReferenceNeedsCall`, only where that selection would change a later builtin slot's role and whether its reference lifts. Where only inference decides, the error names both spellings: `P(…)` calls it and spreads the result, `{ P }` reads it as one value.
  - A declaration whose marker is refused gets no such error at its uses, including a transparent alias whose target is validly marked.
- **Timing.** A marked call in an argument or selector slot runs while the supply is formed, as every explicit spread does (SUP-02, CALL-02): before the arity check, whether or not the callee uses it, META positions included.

**Qualifications**
- There is no opt-out syntax. Parentheses are transparent (`(A(1, 2))` spreads); a block `{ A(1, 2) }`, a list `[A(1, 2)]` or a stored property keeps one value.
- Item positions and value positions differ: with `A(x, y)* = x, y`, `A(1, 2)[0]` is `1`, while `first(A(1, 2))` and `count(A(1, 2))` are `ArityMismatch`.
- A marked algorithm cannot be a loop step or a `meta` argument directly: `Fib(0, 1).repeat(10)` is `repeat(Fib(0, 1)*, 10)`. A marked loop step uses an unmarked wrapper.
- The same algorithm behaves differently by route: a statically resolved call spreads, and the same algorithm called through a parameter does not. Marking a public declaration changes every caller, importing code included.
- The spelling errors of the marker are SYN-12's. A detached or repeated marker still stands, and a family whose clauses disagree (`MixedOutputSpreadMarkers`) recovers marked, so a report at their uses is genuine.

```katlang
A(x, y)* = x, y
Add(x, y) = x + y
Add(A(1, 2)), [A(3, 4)], A(1, 2)[0]
```
⇒ `S[3, L[3, 4], 1]`

The unmarked `A(x, y) = x, y` with `Add(A(1, 2)*), [A(3, 4)*], A(1, 2)[0]` is the same program.

```katlang
A(x, y)* = x, y
Add3(a, b, c) = a + b + c
H = A(x, y).F(3)
H(Add3, 1, 2)
```
⇒ `6`

- `P* = 1, 2` / `C(*xs) = xs.count` / `C(P), C(P()), C({ P() }), C([P()])` gives `S[1, 2, 1, 1]`: the read, the block and the list each keep one value.
- With `Add(a, b) = a + b` and `Inc(x) = x + 1`: `Q = [[1, 2], 3]` / `P* = Q[0]` / `H = reduce(P, Add, Inc)` / `H(-3)` is `1`, because `P` can never gain a parameter and the bare `P` is a read. With `Q(x) = [[x]]` the same `H` is `OutputSpreadReferenceNeedsCall`.
- With the `A` and `Add` above: `B = A` / `Add(B(1, 2))` is `3`, and so is `B* = { A }` / `Add(B(1, 2))`; `B* = A` is `OutputSpreadMarkerOnAlias`; `Apply(f) = Add(f(1, 2))` / `Apply(A)` is `ArityMismatch`; `W(x, y) = A(x, y)` / `C(*xs) = xs.count` / `C(W(1, 2)), C(A(1, 2))` gives `S[1, 2]`.
- `a*, b = 1, 2` is `OutputSpreadMarkerOnDeconstructionTarget`, and `F(0)* = 1` / `F(n) = n` is `MixedOutputSpreadMarkers`.
- `D(x, y)* = x / y, y` / `FirstOf(a, b, c) = a` / `FirstOf(5, D(1, 0))` is `DivisionByZero`: a marked argument call runs although `FirstOf` never uses it.
- `Fib(a, b)* = b, a + b` / `Fib(0, 1).repeat(10)` is `ArityMismatch`; with the wrapper `F(a, b) = Fib(a, b)`, `F(0, 1).repeat(10)` is `S[55, 89]`.

## CALL — Calls, argument binding, and parameters

A call runs in a fixed order: it selects one callee identity, forms the written arguments into one **supply** in the caller's context, checks the supply's cardinality against the selected signature, binds it, and runs the body. A non-spread slot supplies one **supplied computation** (a cell): a suspended evaluation of the slot's expression in the caller's environment, with a **VALUE channel** and, for a written reference, a **CALLABLE channel** (also called the algorithm channel). A **zero-argument value demand** asks a callable for its value with no argument supplied (CALL-05). An **inferring level** is a body with no written parameter list, whose parameters the front end infers (PAR-03 to PAR-08); a **closed level** is the own level of a written parameter list or a clause-branch body. A **formula** is a body that uses a reference inside an expression, unlike a body whose one written row is a bare reference, which is an alias or bare forwarding (FWD-02, FWD-03).

### CALL-01 — A call selects one callee identity first and binds against that callee's signature only

- For `f(args)`, the callee expression is resolved to exactly one algorithm identity before any argument slot is evaluated. The ordinary argument supply is then bound against that identity's own signature.
- Resolution never considers the number or shape of the arguments. KatLang has no overloading and no fallback to another callable of the same name.
- A supply that the selected signature cannot bind is an evaluation-time error, never a parse-time error, and an unevaluated wrong-arity call is inert. The error is `ArityMismatch` for every callee category whose cardinality the supply misses: a user or builtin callee, and a clause family, whose wrong argument count no clause head accepts (NEED-05, PAT-03). It is `NoMatchingBranch` for a clause family supplied an accepted count that no clause matches (PAT-02).
- A callee position that denotes no algorithm is `NotAnAlgorithm`. Examples are a parameter bound only to a value, a number, a call result, or a list.
- Dispatch then follows the selected kind: builtin (CALL-03), clause family (PAT), user call (CALL-02), or alias, which calls or forwards to its target (FWD-03).

**Qualifications**
- This rule owns "no overloading; wrong arity is an evaluation-time error, and an unevaluated wrong-arity call is inert". RES-06 (identity and shadowing) and COLL-01 (the builtin signature inventory) point here. SYN-13 owns only the parser side: no parse counts arguments.
- Callee resolution precedes argument evaluation: `F(g) = g(trace(1))` / `F(5)` is `NotAnAlgorithm`, and it traces nothing.
- Shadowing of prelude names is RES-06's rule. This rule says only that once a callee is selected, its signature alone decides binding.
- `load` is still recognized by spelling. That is a deliberate MOD carve-out, not a call (MOD-07).
- The redundant group `(F)(1)` is `F(1)`. `(a.b)(1)` is a call on the argumentless edge `a.b` (DOT-09, SYN-09). A structural member path carries the member's own callable, so `(Box.G)(3)` is the member call `Box.G(3)`. An edge resolved by lexical fallback or by the `.string` intrinsic is a computed value: `Inc(x) = x + 1` / `K(z) = (5.Inc)(1)` / `K(0)` is `NotAnAlgorithm`.

```katlang
if(x) = x + 1
Add(a, b) = a + b
Fam(0) = 0
Fam(n) = n
P = count(1, 2, 3)
Q = if(true, 1)
R = Add(1)
S = Fam(1, 2)
if(7), 7.if
```
⇒ `S[8, 8]`

The wrong-arity properties are never evaluated, so they are inert. The user `if` hides the builtin completely: `if(x) = x + 1` / `if(true, 2, 3)` is `ArityMismatch`.

`F(g) = g(2)` / `F(5)` is `NotAnAlgorithm`. A family's wrong count is its arity error before any argument is demanded: `Pick(0, y) = y` / `Pick(x, y) = x` / `Pick(trace(1), trace(2), trace(3))` is `ArityMismatch` with an empty host log, and so is the call `Fam()` of a source family. `P(0, y) = y` / `P(x, 0) = x` / `P(1, 1)` is `NoMatchingBranch`.

### CALL-02 — A user call forms one argument supply before any binding decision: each non-spread slot supplies a suspended computation of the caller, evaluated only if its value is demanded

- For a user-defined callee (flat fixed, collecting or mixed, patterned, or clause family), the argument supply is formed completely before any cardinality check, clause selection or pattern binding. Forming it evaluates no ordinary argument (NEED-01, NEED-05, NEED-07).
- A non-spread slot contributes exactly one item (SUP-01): a supplied computation of the slot's expression, captured in the caller's environment. An argument list owns no scope. A parameter passed on as an argument transports its existing computation, with every available channel, unevaluated.
- A spread slot contributes the items of one boundary (SUP-02). An arbitrary spread operand is evaluated while the supply is formed, before the cardinality check, before any later slot and before the callee runs, and its items are ready values. Re-spreading a known collector slice transfers that slice's existing computations without evaluating them (VAR-03). A spread whose last star opens a call reference's argument view (`F(R.Arguments*)`) transports that call's original argument computations, unevaluated and with every available channel, instead of ready items (CR-11).
- The supply's cardinality is then checked against the callee, before any non-spread computation is evaluated.
- A supplied computation is evaluated at most once, when its VALUE is first demanded, by an inspecting pattern (NEED-04) or by a consumer the callee executes, and that outcome is final for the call (CALL-06). A slot whose VALUE is never demanded is never evaluated: its effects, random draws and failures never happen. The order of first demands, not the written order, decides the order of argument effects, draws and failures (NEED-03). Projecting a slot's callable identity is not a VALUE demand (NEED-06).
- A written slot never disappears from the supply. A written argument whose expression has no output fails as that argument (`MissingOutput`) whenever its value is demanded; it is never treated as an omitted argument.
- No callee shape receives a second, written-slot view of a slot.

**Qualifications**
- A demanded computation that reaches a resource limit ends the run there (RUN-03); one that is never demanded reaches nothing.
- Formation is bounded (C#-only host policy): an expanded supply whose item count exceeds the effective `MaxCollectionItems` continues count-only to the end of formation, so later explicit spreads still run and their own failure wins, and it is then refused terminally as `CollectionSizeLimitExceeded`, before the cardinality check.
- Builtin callees (the 22 prelude builtins) form their supply the same way and also check cardinality before any non-spread VALUE demand; which slots they then demand, and in what order, is CALL-03's. Math, random and host-operation wrappers are user callees.
- Name resolution is demand; validation is not. A supplied argument's names are resolved when it is demanded, in the caller's retained environment (NEED-01, NEED-10), so an unused argument never fails a run-time lookup. Static validation is independent of demand: a written name that is undeclared in a closed body, or that reaches an open level with two providers (RES-03), is a front-end error whether or not its slot is ever demanded (NEED-05). With `open A, B` both providing a public `X`, `F(p, q) = p` / `F(trace(1), X)` and `F(trace(1), X + 0)` are both `AmbiguousOpen` before anything runs.

```katlang
F(a, b, c, d) = a * 1000 + b * 100 + c * 10 + d
P = 2, 3
F(trace(1), trace(P)*, trace(4))
```
⇒ `1234`

The host log is `[trace(S[2, 3]), trace(1), trace(4)]`: the spread slot runs while the supply is formed, then the body demands `a`, `b`, `c` and `d` in its own order.

```katlang
K = 7
F(x) = {
  K = 100
  x
}
F(K)
```
⇒ `7`

A supplied computation runs in the caller's environment.

- `F(0, 0) = 100` / `F(x, y) = x + y` / `A = (0, 0)` / `F(A*)` gives `100`: the spread is expanded before clause selection.
- `Ignore(f) = 0` / `Ignore(trace(42))` gives `0` with an empty host log. `F(x, y) = y + x` / `F(trace(1), trace(2))` gives `3` with host log `[trace(2), trace(1)]`: demand order, not written order.
- `F(a, b) = a` / `F(trace(1), trace(2), trace(3))` is `ArityMismatch` with an empty host log.
- `F(x) = 7` / `F(trace(1), [trace(2) / 0]*)` is `DivisionByZero` after `[trace(2)]`: a required spread is formed, and fails, before the cardinality check, and the plain slot never runs.
- `Coll(*xs) = xs` / `Coll(), Coll(()), Coll([])` gives `S[L[], L[S[]], L[L[]]]`. `Coll(*xs) = xs` / `Coll({})` is `MissingOutput`, when `xs` is read, while `Coll(*xs) = 7` / `Coll({})` gives `7`.

### CALL-03 — A builtin callee forms its supply like every call; the builtin decides which non-spread slots it demands, and in what order

- A call whose selected callee is a builtin forms its supply exactly like every other call (CALL-02; NEED-01, NEED-05, NEED-07): only arbitrary explicit spread slots are evaluated at formation, left to right among the spread slots, and expanded into ordinary slots; a known collector slice transfers its computations unevaluated; every non-spread slot stays a suspended computation. The builtin's arity is then checked against the formed supply, before any non-spread slot is evaluated. What the builtin owns is which slots it demands, and in what order.
- **Which callables are builtins.** Only the 22 prelude builtins are builtin callees. Math functions, their lowercase aliases, `random`/`randomInt` and host operations are C#-only prelude user wrappers, so they are user callees (CALL-02). When the native runs, a Math or random wrapper demands its arguments in parameter order and requires each to be a number before demanding the next (`pow(trace('a'), trace(1))` is `TypeMismatch` after `[trace('a')]`); a host operation demands all its arguments in parameter order before the host is invoked.
- **Non-sequence builtins** (`if`, `while`, `repeat`, `range`, `atoms`): the builtin demands its value slots (through CALL-05) or invokes its step slots in its own order, and a slot it does not select is never evaluated. Each value slot is demanded and validated before the next one is demanded: the `if` condition before any branch, and then only the selected branch (BOOL-05); `repeat`'s count only after the inert capture of its `meta step` and the preparation of the captured call's supply, whose explicit spreads open first, never demanding the non-spread initial cells (LOOP-01, LOOP-05); the `range` start before the stop.
- **Collection builtins** (a collection plus controls), each slot by the role its position has in the builtin's metadata:
  - a value slot, which is the collection and every value or whole-number control (`contains`'s `item`, `take`/`skip`'s `count`), is demanded once, when the builtin executes, the collection first (or its retained slice for a selective observer, NEED-07; CALL-05 for a callable-shaped argument); its outcome, a value or a failure, is final and never retried (CALL-06). Demanding a list reads none of its positions: the builtin reads them by its own rule (COLL-04). `reduce`'s `initial` is a value slot whose demand is deferred: binding keeps it undemanded, and the fold demands it at most once, when it reaches its start (HO-02);
  - a callback slot (the `map` mapper, the `filter` predicate, the `reduce` reducer) is never VALUE-demanded: its callable identity is projected only when the builtin first needs to invoke it — when a `map` position or a `filter` candidate is first read, or when a fold over a nonempty collection starts (COLL-04, HO-02) — so an empty collection, and a stage that no consumer reads, never projects it (HO-04; NEED-06). A callback slot with no callable identity reports `NotAnAlgorithm` at that point;
  - a spread slot is supply formation: its operand is evaluated at once and either supplies exactly its items, which take the roles of the positions they land on, or its failure, of any kind, is the call's failure, raised before the arity check and before any later slot (SUP-02);
  - a surplus position (past the signature) makes the arity check fail before any slot is demanded.

**Qualifications**
- `tick` is a builtin with no slot (RUN-09).
- Laziness belongs to the resolved builtin identity: a user `if` or a parameter named `if` is an ordinary callee (RES-06), which demands what its own body and patterns demand (BOOL-05).
- No callee makes an already-built value lazy: in `if(true, Risky*)`, `Risky` is evaluated, and the level its spread opens read, while the supply is formed.
- Cardinality comes first for every callee category (NEED-05): `count(trace(1), trace(2))` and `map(trace(1), trace(2), trace(3))` are `ArityMismatch` with no host event, and `count(1 / 0, 2)` and `F(a) = a` / `F(1 / 0, 2)` are both `ArityMismatch`. A failed spread is still the first failure: it is raised during formation, so no arity verdict outranks it (`BadT = 1 + 'a'` / `take(1 / 0, BadT*)` is `TypeMismatch`).
- A value slot that is demanded and reaches a resource limit ends the run at once (RUN-03), exactly like the same argument read by a user-defined consumer. A slot that is never demanded reaches nothing, so a wrong-arity call's verdict precedes any limit its slots would reach.

```katlang
range(trace(1), trace(3)*), if(trace(true), trace(10), trace(20)), take(trace([1, 2, 3]), trace(2)*)
```
⇒ `S[L[1, 2, 3], 10, L[1, 2]]`

The host log is `[trace(3), trace(1), trace(true), trace(10), trace(2), trace(L[1, 2, 3])]`: each call forms its spread first, then the builtin demands its value slots in its own order. A user callee forms its supply the same way: `F(a, b) = [a, b]` / `F(trace(1), trace(3)*)` gives `L[1, 3]` with host log `[trace(3), trace(1)]`.

Per-slot validation order:
- `pow('a', 1/0)` is `TypeMismatch` and `randomInt('a', 1/0)` is `TypeMismatch`: a wrapper finds `x` not to be a number before it demands `y`.
- `take('a', 1/0)` is `DivisionByZero`: the collection `'a'` is one item, and the `count` control is demanded next.
- `range('a', 1/0)` is `TypeMismatch`: `start` is validated before `stop` is demanded.
- `if('a', 1/0, 2)` is `TypeMismatch`: the condition is validated before any branch.
- `Inc(x) = x + 1` / `Inc(trace(1)).repeat(trace('a'))` is `TypeMismatch` with host log `[trace('a')]`. `pow(trace(2), trace('a'))` is `TypeMismatch` after `[trace(2), trace('a')]`.

Slot roles:
- `A = tock()` / `map([], A)` is `L[]` with no host event, and `L = L + 1` / `map([], L)` is `L[]`: a callback slot is never value-evaluated merely because it was supplied. `map([], 5)` is `L[]`, while `map([1], 5)` is `NotAnAlgorithm`.
- `reduce([], {x + y}, trace(1) / 0)` is `DivisionByZero` after one trace: an empty fold demands `initial` once. `Pick(item, acc) = item` / `reduce([1, 2], Pick, 1 / 0)` is `2`: a fold whose steps never reach the start never demands it.
- `Bad = 1 / 0` / `take(Bad*)` is `DivisionByZero`, and so is `Bad = 1 / 0` / `reduce([], Bad*, 0)`: a failed spread is the call's failure before the arity check.

### CALL-04 — Arity counts supplied items, and a fixed parameter binds its item unchanged in every call form

- A parameter list is satisfied by the number of supplied items, never by the element count of any value. The supplied items are the call's supply cells (CALL-02): one per non-spread written slot, whatever its kind or eventual value, and one per item an explicit spread opens (NEED-01, NEED-07).
- A fixed parameter binds exactly one supplied item, unchanged, whatever its kind: a sequence, a list, `()` or `[]` stays one value. Binding attaches the item's cell without demanding it; when that VALUE is demanded it is the item's value, unchanged (NEED-01, NEED-04).
- No binder unpacks an argument implicitly. Only the caller's spread `v*`, a structural pattern parameter (PAT-06, PAT-08), or selection (`v[0], v[1]`) can supply several parameters from one value; a multi-selection `v[0, 1]` is one sequence value, so it supplies several only when spread (`v[0, 1]*`).
- A supplied count that the selected callee does not accept is `ArityMismatch`, raised before any non-spread supplied computation is demanded (NEED-05). This holds identically for the direct call `F(v)`, the dotted call `v.F` (DOT-03), a callback (HO-02) and every callee category, a clause family included: a family rejects a count no clause head accepts as `ArityMismatch` before trying any clause, and reports `NoMatchingBranch` only for an accepted count that no clause matches (PAT-02, PAT-03). A failed spread supplies no item, so it never takes part in an arity verdict: its own failure is raised first (SUP-02).

**Qualifications**
- A collecting parameter requires no slot and a nested pattern requires one; collector allocation is VAR's rule (VAR-01, VAR-02).
- The structured payload of an arity mismatch is the selected signature's minimum supplied slots and the complete supply count (NEED-05): `Add(1)` is (2, 1), and so is `F(x, y) = x(y)` / `F(Inc)`, although `Inc` is a callable whose VALUE demand would fail, because every supplied slot is one cell and none drops out of the count. Payload numbers and wording are presentation (RUN-06).

```katlang
Pair = 10, 20
Add(x, y) = x + y
Id(v) = v
Add(Pair*), Add(Pair[0], Pair[1]), Id(Pair), Id([1, 2]), Add(Pair[0, 1]*)
```
⇒ `S[30, 30, S[10, 20], L[1, 2], 30]`

A value's element count never fills parameters, in any call form: `Pair = 10, 20` / `Add(x, y) = x + y` / `Add(Pair)` is `ArityMismatch`, `Add(x, y) = x + y` / `(1, 2).Add` is `ArityMismatch`, and `Add(x, y) = x + y` / `map([(1, 2)], Add)` is `ArityMismatch`.

Cardinality is decided before any argument is demanded, and only an explicit spread is evaluated to find it: `Add(x, y) = x + y` / `trace(1).Add(trace(2), trace(3))` is `ArityMismatch` with an empty host log, while `Add(x, y) = x + y` / `Add((1 / 0)*, trace(2), trace(3))` is the spread's `DivisionByZero`.

### CALL-05 — A zero-argument value demand is accepted exactly when an ordinary zero-argument call can bind the callable

*Open: whether "a written parameter list is never empty" is deliberate law and the zero-arity family arm host-only (Q-46); whether open-provider eligibility is deliberately stricter than this law (Q-58); the error category of a bare root name (Q-42, PAR-03).*

- Several reads demand a callable's value with no arguments supplied: a bare reference in value position, a parameter read as a value whose supplied computation is a bare callable reference (its cell's one VALUE demand is that reference's own demand; NEED-01, NEED-02), a builtin value slot (the `if` condition or branch, the `repeat` count, `atoms`, `range`, a collection argument), and the `.string` receiver.
- **Acceptance (user algorithms).** A demand of a user algorithm is accepted if and only if an ordinary call supplying zero arguments could bind it: the ordinary binder accepts the empty supply, that is, the minimum supplied slot count is 0 (no top-level pattern, or only a top-level collector). A syntactically empty parameter list is not the test. An accepted demand evaluates through the ordinary binder against the empty supply.
- **Clause families.** A family is not accepted or rejected on a parameter list. It is accepted only through a clause of top-level arity 0, and only an accepted demand dispatches it against the empty supply. Source cannot write such a clause (`F()` is not a clause head), so every demand of a source family is rejected before any dispatch, as `NoMatchingBranch` (PAT-11), never `ArityMismatch`. The explicit call `Fam()` is different: its empty supply fails the family's cardinality check, which is `ArityMismatch` (CALL-01, NEED-05).
- **Rejection report.** The callee body is never entered. The report depends on the demanded callable and on how the demand was written:
  - a user algorithm reached through a name, a parameter or a dot reference: `ArityMismatch` at the reference, reporting the true minimum supplied-slot count (a property reference also carries the property context);
  - a written brace block demanded as a value (`count({x + 1})`): `UnresolvedImplicitParams` over the block's own inferred parameters;
  - a block whose one row is a bare reference (`{ F }`, a structural forwarding carrier, FWD-03) has no signature and no report of its own, so its demand is reported exactly as its written target reference `F` reports it, the target's ordinary contract located at that reference: a user algorithm's `ArityMismatch`, a clause family's `NoMatchingBranch` named by the reference, a member path's (`{ Lib.F }`) bare arity, a builtin's own arity error. Such a block never reports the target's parameters as `UnresolvedImplicitParams`. A named alias delegates in the same way, under the written name (`A = Inc` / `count(A)`);
  - a clause family, whatever the source: `NoMatchingBranch`. Only a host-built single-branch flat-binder family keeps an arity error. Source never produces one, because a single literal-free clause elaborates to a user algorithm (PAT-01).
- **Collecting slots are not special (VAR-03).** Collecting an argument makes no demand, and re-spreading the collected slice makes none. Reading the collected list makes this zero-argument value demand of each element, with the rejection reports above, exactly as a fixed parameter's read does.
- **Builtins.** A builtin is not judged by this law; it keeps its own rejection: its arity error, or `tick`'s invocation-required `IllegalInEval` (RUN-09).
- **Invoking slots.** Callback and loop-step slots invoke the algorithm and never consult the law.

**Qualifications**
- Eligibility and the rejection report are all this law decides. Whether a bare demand reads the property cache, and why `A()` is fresh, is PROP's rule (PROP-04, PROP-06).
- Whether a bare reference reaches this law is the front end's lifting decision (PAR-07), and it asks this law's question: a reference to a callable this law accepts is never lifted, so it reaches the law, and the cache, in every position except the lone written row of a non-root body, which is an alias or bare forwarding (FWD-02, FWD-03): `Only(*xs) = xs` / `A(xs) = Only` / `A(5)` is `L[5]`, the call `Only(xs)`. A callable that requires supplied arguments is still lifted where PAR-07 lifts. `Roll(*xs) = randomInt(1, 1000000)` / `Roll == Roll` is `true` for every seed. The lifting predicate and this law's acceptance are one rule.
- The `open` provider rule uses "empty parameter list", not this law: a collecting-only library cannot be opened (MOD-04).
- The accepting family arm (a zero-arity clause) is reachable only through host-built ASTs.

```katlang
Only(*xs) = xs
Answer = 42
Only, Only(), count(Only), Answer, Answer()
```
⇒ `S[L[], L[], 0, 42, 42]`

Rejected demands of user algorithms, each `ArityMismatch`:
- `Head(x, *rest) = x` / `Head` is `ArityMismatch`, reporting the minimum 1, and so are `Tail(*rest, z) = z` / `Tail` and `P((*xs)) = xs` / `P`: a structural pattern binds one supplied value, it never accepts none.
- `A = x` / `A` is `ArityMismatch`.
- `Inc(x) = x + 1` / `K(z) = if(true, Inc, 0)` / `K(1)` is `ArityMismatch`, at `Inc`. At the root, `Inc(x) = x + 1` / `if(true, Inc, 0)` is a formula whose `if` branch is a value role, so it lifts `x` into the root and is `UnresolvedImplicitParams` (PAR-07).
- `Inc(x) = x + 1` / `F(g) = g` / `F(Inc)` is `ArityMismatch`, at the argument `Inc`: the cell retains the original supplied computation.

Rejected demands reported differently:
- `Fam(0) = 0` / `Fam(n) = n` / `Fam` is `NoMatchingBranch`. So are `Fam(0) = 0` / `Fam(n) = n` / `K(z) = count(Fam)` / `K(1)`, and the same `K` with `if(true, Fam, 0)` or `Fam.string`. At the root those three are formulas: `Fam(0) = 0` / `Fam(n) = n` / `count(Fam)` lifts the family's nameable signature and is `UnresolvedImplicitParams`. Through a parameter, `Fam(0) = 0` / `Fam(n) = n` / `F(x) = x + 1` / `F(Fam)` is `NoMatchingBranch`, naming `Fam`.
- `count({x + 1})` is `UnresolvedImplicitParams`.
- `Inc(x) = x + 1` / `K(z) = count({ Inc })` / `K(1)` is `ArityMismatch`, located at the `Inc` inside the block, exactly the report of `count(Inc)` at its own reference. `E(0) = 0` / `E(n) = n` / `K(z) = count({ E })` / `K(1)` is `NoMatchingBranch`, `K(z) = count({ count })` / `K(1)` is `ArityMismatch`, and the formula block `Inc(x) = x + 1` / `K(z) = count({ Inc + 0 })` / `K(1)` keeps `UnresolvedImplicitParams`, over its own inferred `x`.
- `Fam(0) = 0` / `Fam(n) = n` / `Coll(*xs) = xs` / `Coll(Fam)` is `NoMatchingBranch` when the collected list is read, as for a fixed parameter.

An invoking slot does not demand: `Only(*xs) = xs.count` / `map([1, 2], Only)` is `L[1, 1]`.

### CALL-06 — A written argument slot is evaluated at most once, on its first value demand, and that outcome is final for the call; a slot whose value is never demanded is never evaluated

- Within one call, a written argument slot is one supplied computation (CALL-02). It is evaluated at most once, when its VALUE is first demanded, in the caller's retained environment. If that evaluation succeeds, that is its value. If it fails with an ordinary error, that is its failure. If it reaches a resource limit, its cell stores that failure as terminal completion and the run ends there: that completion cannot restart work and is never a recoverable argument value (RUN-03, NEED-09; distinct from the success-only property cache, NEED-10). A slot whose VALUE is never demanded is never evaluated, so an unused argument cannot fail, run an effect or draw (NEED-01, NEED-03).
- The demand uses the proper semantic route once (a named property through its ordinary property access and cache, NEED-10; a brace block through its own evaluation; a dot expression through ordinary dot resolution), and every later demand reuses the outcome it established. That outcome is immutable for the lifetime of the call activation (NEED-02). A builtin value demand preserves a parameter's established failure, including its kind and payload, before considering the independent callable channel's signature.
- A VALUE demand of the slot is any consumer that needs its value: a value-position read of the parameter, a builtin value slot, the `.string` receiver, a native (Math, random, host) wrapper's argument read, the materialization of a collector that holds it (VAR-03), an inspecting pattern (a literal, a structural pattern, a repeated parameter name (PAT-09), a clause-family clause that inspects it; NEED-04), or a forwarding call whose slot is then demanded. Every demand after the first reports the same outcome and none re-evaluates the argument, so a failure cannot heal, the argument's effects and random draws are never repeated, and one parameter never has two values in one activation.
- Binding the slot to a plain parameter, transporting or forwarding it, collecting it and projecting its callable identity are not VALUE demands (NEED-01, NEED-06, NEED-07, NEED-08).
- Capturing the slot's call as a META reference, obtaining or counting its argument view and spreading that view into another supply are not VALUE demands either; selecting from the view (`R.Arguments[i]`, `first`, `last`) demands only the selected cell. The original VALUE and every fresh `R.Invoke()` or rebuilt `R.Algorithm(R.Arguments*)` execution read the plan's one sticky supply, the same cells, so each slot is still evaluated at most once and every execution observes its one outcome (CR-3, CR-5, CR-9, CR-10, CR-11).
- The algorithm channel stays usable where the language uses it: invoking the parameter (`f(x)`, `f()`, an invoking builtin slot) is an ordinary invocation, and an explicit call is fresh (PROP-06); structural member access through the parameter (`o.X`) navigates the algorithm (DOT-02). Invoking never reads, repairs or replaces the VALUE outcome.
- The outcome belongs to the slot of that call activation, not to the property the slot named. A failed property evaluation is never stored in the property cache (PROP-09; distinct from the completed cell failure, NEED-02), and a separate demand of the property (another slot, another call, a root row) reads it under PROP-04; because a demanded failure ends the run (VAL-10), a property whose evaluation failed is never read again in that run.

**Qualifications**
- "At most once" is per written slot of one call activation. Two slots naming one property are two computations, each demanding the property under PROP-04: `Bad = trace(1) / 0` / `I(f) = 0` / `I(Bad), I(Bad)` is `S[0, 0]` with no trace, because neither slot is demanded.
- A clause family demands exactly what its clauses' patterns inspect (NEED-04, PAT-07): `Choose(true, yes, no) = yes` / `Choose(false, yes, no) = no` / `Choose(true, trace(1), trace(2) / 0)` is `1` after `[trace(1)]`.
- `0.Div` and `Div(0)` are both suspended computations with no callable identity (DOT-09), so as unused arguments they behave alike.
- What a repeated name demands at each occurrence is NEED-04's (PAT-09). A slot it demands still runs at most once, and a later demand reads the completed failure without re-evaluating it: `Bad = trace(1) / 0` / `Q(x, x) = x` / `Q(Bad, 7)` is `DivisionByZero` after one trace, and so is `Bad = trace(1) / 0` / `Q(x, x) = x` / `Q(7, Bad)`. A slot that reaches a resource limit there ends the run.
- A builtin decides which of its slots it demands, and in what order (CALL-03). A builtin value slot keeps the outcome of its first demand, exactly like a user parameter read; `reduce`'s `initial` is demanded at most once, when its fold reaches the start (HO-02); a callback slot is never value-evaluated; a failed spread is the call's failure. A parameter reaching a builtin value slot is read through this rule: `Add(a, b) = a + b` / `Bad = trace(1) / 0` / `G(v) = reduce([1], Add, v)` / `G(Bad)` traces once.
- A demanded limit ends the run at once and an undemanded slot reaches no limit, which leaves the at-most-once law untouched: an ordinary failure is evaluated once, recorded and never re-derived, and a limit simply ends the run.
- Blame is presentation (RUN-06): a named argument's failure keeps the report its own evaluation made (`F(a) = sum(a)` with `F(NoOut)` reports "Property 'NoOut' has no defined output", as `sum(NoOut)` does), while an unnamed written argument read through a parameter keeps the parameter blame.

```katlang
Bad = 1 / 0
Ignore(f) = 0
Ignore(Bad), Ignore({ 1 / 0 }), Ignore(1 / 0)
```
⇒ `S[0, 0, 0]`

```katlang
B = tick()
ThenRead(f) = f(), f, f(), f
ThenRead(B)
```
⇒ `S[1, 1, 2, 1]`

Invoking is not reading: each `f()` runs `B` afresh, and the first, finding `B`'s entry empty, establishes it (PROP-06); `f` demands the slot once, through `B`'s cache entry, and reuses that value; no invocation reads or replaces the slot's outcome.

At most once:
- `Bad = trace(1) / 0` / `F(v) = v` / `F(Bad)` is `DivisionByZero` with host log `[trace(1)]`.
- `B = if(tock() < 2, 1 / 0, tock())` / `Pair(x) = x, x` / `Pair(B), B` is `DivisionByZero` with host log `[tock#1]`: one parameter never has two values.
- `Bad = trace(1) / 0` / `I(f) = f` / `K2(f) = I(f) + I(f) + 1 / 0` / `K2(K2(K2(Bad)))` traces once.
- `F(x) = x, x` / `F(tick())` is `S[1, 1]` after one tick.
- `G(a) = a + a` / `R(meta c) = c.Invoke(), c.Invoke()` / `R(G(tock()))` is `S[2, 2]` after one `tock`: two executions over one sticky supply.

Only a demand runs a slot:
- `B = if(tock() < 2, 1 / 0, tock())` / `Ignore(x) = 0` / `Ignore(B), B, B` is `DivisionByZero` after `[tock#1]`: `Ignore` never demands `B`, and the first root read fails and ends the run.
- `Plus(f, x) = f + x` / `Plus({x + 1}, 5)` is `UnresolvedImplicitParams`, and so is `Show(v) = v.string` / `Show({x + 1})`: a callable read as a value reports what the written argument raises.
- `Bad = 1 / 0` / `Coll(*xs) = 0` / `Coll(Bad)` gives `0`, `Div(a) = 1 / a` / `F(x, y) = x` / `F(1, 0.Div), F(1, Div(0))` gives `S[1, 1]`, and `F(x, y) = x` / `F(1, {})` gives `1`.

With a computation that reaches a resource limit, `Use(x) = 0` and `Use(x) = if(false, x, 0)` and a forwarding `Keep(w) = 5` / `Use(x) = Keep(x)` never reach it, while `Use(x) = x` (or `x, x`, `x.string`, `sum([x])`) reaches it and nothing after it runs. With `G(x, y) = y + x`, a failing `x` beside a limit-reaching `y` is the limit: `y` is demanded first, its limit ends the run, and `x` never runs.

### PAR-01 — A parameter binds on the value channel, the algorithm channel, or both, and owns its name on every channel

- A user-call parameter binds its argument's supplied computation (CALL-02), which carries two independent channels: the VALUE channel, whose computation runs at most once, on the parameter's first VALUE demand (CALL-06), and the CALLABLE (algorithm) channel, available when the written slot names a callable: a name, a brace block, an argumentless structural dot path, an `.Algorithm` link (CR-15), or a parameter already bound to a callable (NEED-01, NEED-06, DOT-09).
- A parameter read in value position demands the value channel: the first read evaluates the supplied computation, and every later read reuses its completed outcome, a failure included (CALL-06); a read never invokes the CALLABLE channel.
- A parameter in call position (`g(...)`, dot fallback `x.g`, an invoking builtin slot) uses only the CALLABLE (algorithm) channel; projecting it demands no VALUE (NEED-06). A binding without callable identity is `NotAnAlgorithm`, reported when an invocation needs it. Forwarding the parameter transports its whole cell, both channels, demanding nothing (NEED-08).
- **META parameters.** A parameter declared `meta name` (only a plain, fixed name written once at the top level of an ordinary explicit parameter list, otherwise the front-end `InvalidMetaParameter`; a host-built tree is refused before evaluation as `IllegalInEval`) binds neither of its argument's channels. After the cardinality check, when written-order inspection reaches it (an earlier inspecting pattern's failure wins, PAT-10), it reifies the supplied cell's invocation plan, evaluating nothing, and binds one Ready cell whose VALUE is the run-scoped call reference (VAL-01) and which has no CALLABLE. Only a written invocation is capturable (a call through a name, parameter or argumentless path, or an argument-bearing dot edge); any other argument, a Ready reference included, is `NotAnAlgorithm` "meta: not a supplied call computation". The builtins `while(meta step)` and `repeat(meta step, count)` bind their step the same way (LOOP-01). Formula lifting gives callers an ordinary binding of the name, and a callable alias keeps its target's META mode.
- Every binding site shadows the callee's parameter names out of all inherited tiers: the supplied-cell (need) tier and the value tier. A parameter that is unusable in the requested position therefore never falls through to a same-named binding of the caller.
- Names the callee does not bind keep the meaning their declaration's own lexical chain gives them (RES-07): shadowing removes only the callee's parameter names from the inherited tiers, and a callee's body never resolves a name against the caller's environment.

**Qualifications**
- Clause-family binders bind both channels of their cells, demanding only what the family's patterns inspect (PAT-07, NEED-04): `Inc(x) = x + 1` / `App(f, 0) = 0` / `App(f, n) = f(n)` / `R(z) = App(Inc, 5)` / `R(0)` is `6`. Written at the inferring root, `App(Inc, 5)` is `UnresolvedImplicitParams`: a family argument is a value role, so the root lifts `Inc` (PAR-07).
- Callback parameters bind the cells the builtin supplies: each element is a Ready VALUE with no CALLABLE identity, and a `reduce` accumulator is a deferred VALUE-only cell with no CALLABLE identity, invocation plan or retained slice (HO-02).
- An invoking builtin slot reads a forwarded parameter's algorithm channel (HO-04).
- An explicit call `g()` re-runs the algorithm and never reads or reuses the VALUE outcome of the parameter's cell (PROP-06).

```katlang
K = 3
Inc(x) = x + 1
Both(g) = g + g()
Call(f) = f(10)
Both(K), Call(Inc), Call({ x * 2 })
```
⇒ `S[6, 11, 20]`

```katlang
Inc(x) = x + 1
Apply(f) = {
    Inner(f) = f(2)
    Inner(5)
}
Apply(Inc)
```
⇒ `NotAnAlgorithm`

`Inner`'s value-only `f` hides `Apply`'s callable `f`.

`y = 100` / `G(o) = o + y` / `H(y) = G(5)` / `H(1)` gives `105`: `H`'s parameter never reaches `G`'s `y`. `Pick(k) = if(k, {trace(1)}, {trace(2)})` / `Apply(f) = f()` / `Apply(Pick(true))` is `NotAnAlgorithm` with no host event: a call result carries no callable identity (NEED-06), and projecting it demands no VALUE, so `Pick(true)` never runs.

### PAR-02 — (retired: merged into RES-07)

### PAR-03 — A free name that nothing binds becomes an inferred parameter of the outermost inferring level whose own rows use it

*Open: whether the error category of an unresolved bare root name should be unified (Q-42): a bare root row naming a parameterized callable is its own `ArityMismatch` after earlier rows ran (PAR-07), while a root formula over it is `UnresolvedImplicitParams` before any row.*
*C#-only by design.*

- A bare-name occurrence that no owner level declares and no `open` provides is promoted to an implicit parameter. The ordering of this decision relative to the owner walk and opens is RES-04's rule: promotion only after both.
- "Inferred parameter" (this group) and "implicit parameter" (RES and the error name `UnresolvedImplicitParams`) are the same thing: a parameter the front end adds to a level that has no written parameter list.
- The promoted name belongs to an inferring level: an algorithm body without a written parameter list. Each property body and each brace block is its own level. Ownership is claimed top-down:
  - A level claims every unbound free name used by its own rows: its output rows and hoisted deconstruction right-hand sides. Occurrences inside call arguments, captures, list items, operands and dot receivers count as the level's own. Occurrences inside nested brace blocks and property bodies do not.
  - A nested level sees a claimed name as a captured ancestor parameter. An inline `{ … }` open target and a loaded module are not nested levels here, because they are rooted at the prelude: a free name used in them becomes an implicit parameter of their own member, never a capture from the opener (MOD-06, MOD-08).
  - A name used only inside a nested level is claimed by that level.
- There is no casing rule. Promotion never happens inside a written parameter list's own level (PAR-04) or a clause-branch body (PAT-04).
- **Parameter-rooted member paths.** A parameterless body whose one written row is an argumentless member path rooted at an enclosing parameter (`A = b.C`, `A = b.C.D`) promotes no member name: it is a runtime member reference (FWD-03). Nothing else is exempt: `A = b.C + 0` still infers `C`.
- **Self-dependent inference.** Whether a name is an input can depend on the aliases, `open` providers and members that inference itself decides. When such a decision depends on its own answer with no well-founded reason (two consistent answers, none, or one reachable only through a self-read), the body is the front-end error `SelfDependentInferredParameters`: exactly one deterministic diagnostic per body, at its definition, listing the undecided names in first-occurrence order. The verdict never depends on declaration or traversal order. A decision whose answer does not actually depend on the unknown is decided, so as little as possible is rejected. An explicit parameter list closes the body, which is the way out. The rejected unit is never evaluated.
- The program root is never called. A root that still requires a supplied argument is an evaluation error (`UnresolvedImplicitParams`), unless its signature accepts the empty supply. This check runs before any root row is evaluated, so no row effect happens. A parameterized block in a row, by contrast, fails only at its own value demand, after earlier rows (CALL-05).

**Qualifications**
- Promotion of a free name is transparent through call arguments and captures. Lifting of a reference to a parameterized property is not (PAR-07).
- An assignment-deconstruction right-hand side is a row of the enclosing body, so its free names are the enclosing body's (VAR-06).
- An ambiguous opened name counts as bound. It is never promoted; written, it is the front-end `AmbiguousOpen` (RES-03).
- In a loaded module, "the outermost inferring level whose own rows use it" never extends past the module root (MOD-08): a module's free names are promoted inside the module, the same at every load site.

```katlang
Tax = price * 0.2
Scale = values.map{n * factor}, factor
Apply(f) = f(4)
Tax(50), Scale([1, 2], 10), Apply({ x + 1 })
```
⇒ `S[10.0, S[L[10, 20], 10], 5]`

```katlang
Outer = {
  Mid = {
    Inner = z + 1
    Inner + z
  }
  Mid(5)
}
Outer
```
⇒ `11`

`Mid` claims `z` and `Inner` captures it.

```katlang
Box = { G(x) = x * 10 }
Use(b) = {
  A = b.G
  A(3), 3.A
}
Use(Box)
```
⇒ `S[30, 30]`

`A` infers no `G`: it is a runtime reference to the member `b` provides.

```katlang
L = { public m = P.R }
L2 = { public n = { public m = 1 } }
P = {
    public R = C
    C = {
        open L
        public n = 1
        m
    }
    N = {
        open L2
        public S = n
        0
    }
    R.n + N.S.m
}
5
```
⇒ `SelfDependentInferredParameters`

`m` is an input of `P` exactly when `n` is, and `n` exactly when `m` is not, so the decision has no answer.

- `Scale = values.map{n * factor}` / `Scale([1, 2], 10)` is `ArityMismatch`: `factor` belongs to the block.
- `Id(v) = v` / `F = Id(q + 1), (r, 2)` / `F(5, 7)` gives `S[6, S[7, 2]]`: free names inside call arguments and captures belong to `F`.
- `x + 1` is `UnresolvedImplicitParams`, and `trace(1), x + 1` is too, with an empty host log, while `trace(1), {z}` is `UnresolvedImplicitParams` after `trace(1)`.

### PAR-04 — An explicit parameter list is closed for its own level: nothing is inferred there, and forwarding never adds a parameter to it

*C#-only by design.*

- A written parameter list `F(p1, …) = body` is the complete input specification of F's own level.
- No name is promoted there. A free name that nothing binds is the front-end error `UndeclaredIdentifier`, which blocks evaluation whether or not F is ever called. That includes the fallback name of a dot edge whose fallback is statically certain (DOT-05); a MAY-selected fallback name is not a written-name use.
- Nested levels without a list of their own still infer (PAR-03).
- Clause-branch patterns are closed in the same way (PAT-04).
- An explicit parameter list is closed. Bare forwarding may reuse compatible existing bindings by name but never introduces a new binding into that list. If F's body is one written row that is a bare reference to a callable declaring parameters, that row is bare forwarding (FWD-02): each callee parameter is supplied from an existing binding of the same name, one of F's own top-level parameters of that name (for a callee capture, a top-level capture, collecting or not, the source binding's kind deciding any re-spread, FWD-01; for a structural callee pattern, only a top-level pattern with the same contract), or, for a name F binds nowhere, an accessible enclosing parameter binding. A callee parameter nothing supplies makes the definition the front-end error `UnforwardableParameter`, never a renamed, positional or added parameter. A parameter of F that the callee does not need stays unused.
- Otherwise a bare reference inside F, in a formula, to a property that requires supplied arguments is forwarded (PAR-07) only when every parameter the callee needs is available by name as a parameter binding at the reference: F's own list, or an accessible parameter of an enclosing owner, which forwarding reuses exactly as an inferring body does. Nothing is ever added to F's list, by either route. In a formula, a list consisting only of one collecting parameter may also forward by shape to one grouped collecting callee stream (FWD-02).
- Otherwise the reference stays bare. It is the ordinary zero-argument VALUE demand (CALL-05), rejected only when a consumer actually demands it at run time; an uncalled definition, an unselected branch or an unused argument never runs it (NEED-05), unless the reference is the operand of an explicit spread, which supply formation evaluates whatever the callee later demands (NEED-07).
- No position diagnoses a blocked reference statically, a registry-strict Math argument included (NEED-05): static roles decide elaboration, never a proof that a demand executes. Directly written undeclared names and invalid forwarding structure (`UnforwardableParameter`, `UnforwardableCallable`) stay static.
- A formula reference to a callable that accepts zero supplied arguments is never a forwarding candidate (PAR-07), so a closed list never blocks it: it is the cached zero-argument value demand in every formula position. A lone row names it as the callee instead, and bare forwarding supplies its collector from a compatible same-named binding: a fixed source contributes its one cell as one item, and a collecting source re-spreads its collected cells (NEED-08); otherwise it forwards nothing and the row reads the cached value (FWD-02).

**Qualifications**
- Closedness does not change runtime lookup of visible properties: `x = 10` / `F(y) = y + x` / `F(2)` gives `12`.
- Grace under a closed list is an error (PAR-06).
- No position statically rejects a blocked forwarding: `Speed = distance / time` / `Q(m) = m * Speed` / `1` gives `1`, `Speed = distance / time` / `Q(m) = abs(Speed)` / `1` gives `1`, and each fails only if its demand executes. Even an eager condition, `A = x + 1` / `K(y) = if(abs(A) > 0, 1, 2)` / `1`, gives `1` until `K` is called.

```katlang
Speed = distance / time
KE(mass, distance, time) = mass * Speed ^ 2 / 2
KE(2, 10, 5)
```
⇒ `4`

`distance` and `time` are handed on by name.

```katlang
F(y) = {
  G = z + y
  G(5)
}
F(2)
```
⇒ `7`

The nested `G` still infers `z`.

- `F(x) = x + y` / `F(1)` is `UndeclaredIdentifier`.
- `Speed = distance / time` / `KE(m, d, t) = m * Speed ^ 2 / 2` / `KE(2, 10, 5)` is `ArityMismatch`, at run time.
- `A = q + 1` / `F(x) = Math.Abs(A)` / `F(7)` is `ArityMismatch`, raised when `Math.Abs` demands its argument; `A = q + 1` / `F(x) = trace(x) + Math.Abs(A)` / `F(7)` traces `7` first, `A = q + 1` / `F(x) = if(true, 0, Math.Abs(A))` / `F(7)` gives `0`, and with no call of `F` the program is valid.
- `Cnt(*ys) = ys.count` / `H(k) = abs(Cnt) + k` / `H(5)` gives `5`: `Cnt` accepts zero supplied arguments, so it is no forwarding candidate.
- `A(x) = x + 1` / `F(a) = if(true, a, A*)` / `F(5)` is `ArityMismatch`, while `A(x) = x + 1` / `F(a) = if(true, a, A)` / `F(5)` gives `5`, and `A(x) = x + 1` / `Ignore(v) = 1` / `G(a) = Ignore(A*)` / `G(5)` is `ArityMismatch`.
- `C((*xs)) = xs` / `Use(*items) = [C][0]` / `Use(1, 2)` gives `[1, 2]`, forwarded by shape as `C((items*))`, while the lone row `C((*xs)) = xs` / `Use(*items) = C` is `UnforwardableParameter`, and `C((*xs)) = xs` / `Use((*xs)) = C` / `Use((1, 2))` forwards the same pattern and gives `[1, 2]`.
- `F(p) = p * 2` / `A(p) = F` / `A(5)` gives `10`; `F(q) = q * 2` / `A(p) = F` is `UnforwardableParameter`, never `F(p)`; `F(p, q) = p + q` / `A(p) = F` is `UnforwardableParameter`, never an inferred `q`, and `A(p, q) = F` or `A(p) = F(p, 10)` says what is meant; `F(p) = p * 2` / `A(p, unused) = F` / `A(5, 999)` gives `10`.
- `Only(*xs) = xs` / `F(p) = Only` / `F(3)` gives `L[]`: nothing supplies the collector, so the row reads the cached value. `Only(*xs) = xs` / `F(xs) = Only` / `F(3)` gives `L[3]`.
- A closed formula adds nothing and renames nothing either: `F(q) = q * 2` / `A(p) = F + 1` / `A(5)` is `ArityMismatch` at run time, and so is `F(q) = q * 2` / `A(p) = abs(F)` / `A(5)` in a strict Math position, while `F(p) = p * 2` / `A(p) = F + 1` / `A(5)` gives `11`.

```katlang
A = y + 1
G = {
  F(x) = Math.Abs(A)
  F(1) + y
}
G(10)
```
⇒ `21`

A `y` written in the closed `F` already denotes `G`'s inferred `y`, so forwarding reuses it and `F`'s list stays `(x)`. The lone row `F(x) = A` is bare forwarding, which reuses the same `y` by name and leaves `F`'s own `x` unused, with the same result.

### PAR-05 — An inferred signature lists the level's own names by first semantic occurrence, followed by the names it forwards

*C#-only by design.*

- The inferred parameter list of a level is built in two parts.
- First, the level's own promoted names, in order of first semantic source occurrence:
  - rows are read in written order, with hoisted deconstruction right-hand sides merged at their written position;
  - a call contributes its callee, then its arguments;
  - a dot edge contributes as DOT-05 states;
  - Grace (PAR-06) reorders this own-name list only.
- Second, the names lifted from referenced callees (PAR-07), appended in order of first callee reference and each callee's own parameter order, skipping names already present and names an existing parameter binding already supplies: an accessible parameter of an enclosing owner is reused, never appended. The merge is by binding name, however many times a name occurs in a callee's patterns: a name repeated within one callee, at the top level, inside a group, or across groups, is appended once, at its first occurrence, exactly as a name shared across callees is, and its one binding feeds every occurrence (PAR-07).
- Own names and lifted names are never interleaved. The order in which a runtime fallback assembles its call never determines the signature order.
- An alias infers nothing: it has no signature of its own, and a transparent reference's or carrier's callable signature is its target's (FWD-03). Bare forwarding keeps its written list. A destination callable's parameter order never reorders an explicit source list: `F(y, x) = y - x` / `G(x, y) = F` keeps `G(x, y)` and supplies `F(y, x)` by name.
- **Pattern shape.** Deduplication removes later captures, and a group keeps its kind for the names that are new there. A sequence group left with one non-collecting binder is that binder, because the singleton `(x)` is not a pattern (PAT-06). A list group keeps its brackets. A group left with no new binder contributes nothing. This follows the partial-group rule, not an exception for repeated names; a further formula forwards each surviving group as its own kind again (FWD-02).

**Qualifications**
- Which dot members participate (MAY versus MUST selection) and the dot-edge occurrence order are DOT's rules (DOT-05, DOT-04).
- A direct call `t(a)` independently infers `(t, a)`.
- Lifted parameters keep their callee's pattern shape and kind, except that a callee's `meta` capture lifts as an ordinary binding of the same name, which transports its supplied cell into the callee's META slot (CR-1).
- The signatures of a recursive group are completed simultaneously by this same law (PAR-08).

```katlang
Divide = y / x
A = x - y
F = A - z
K = a.t(b)
Divide(10, 2), F(1, 10, 3), K(7, { x + y }, 1)
```
⇒ `S[5, 6, 8]`

`Divide` is `(y, x)`, `F` is `(z, x, y)` (own `z` first, then the lifted `x, y`), and `K` is `(a, t, b)`.

```katlang
P((x, x)) = x
Some = [P][0]
Some(7), Some([7]), Some((7, 8))
```
⇒ `S[7, L[7], S[7, 8]]`

`Some` infers `Some(x)` and calls `P((x, x))`, so `Some(v)` is the written `Some(x) = [P((x, x))][0]` for every `v`.

```katlang
P = x * 2
R = y * 3
F = {
  a, b = P, 10
  R + a + b
}
F(1, 2)
```
⇒ `18`

- `A = x + 1` / `F = A + x * 10` / `F(2)` gives `23`: a name that is both own and lifted is one parameter.
- `P([x, x]) = x` / `Some = [P][0]` / `Some([7])` gives `7`: `Some([x])` calls `P([x, x])`. `P([x, x]) = x` / `Some = [P][0]` / `Some(7)` is `TypeMismatch`, and `P([x, x]) = x` / `Some = [P][0]` / `Some([7, 8])` is `ArityMismatch`.
- An alias is not inferred at all: `P((x, x)) = x` / `Some = P` / `Some((7, 7))` gives `7`, and `P((x, x)) = x` / `Some = P` / `Some(7)` is `TypeMismatch`, the kind mismatch of `P(7)`.

### PAR-06 — Grace `~` moves the OWN inferred parameters of the owner whose rows contain it; saturation is never an error

*C#-only by design.*

- Grace belongs to the owner whose written rows contain the marked occurrence. A marker is valid exactly when that occurrence becomes one of the owner's own inferred parameters. Its weight is applied as far as the ordering allows; saturation is never an error.
- Each Grace marker requests one adjacent exchange of its parameter. Parameters with postfix (positive) weight take one turn each, from the last-occurring to the first-occurring; then parameters with prefix (negative) weight take one turn each, from the first-occurring to the last-occurring. No parameter passes a neighbour moving the same way with at least as much remaining weight, a passed parameter keeps its weight, and unused weight stays effective.
- A Grace marker decorates exactly one directly attached bare-name occurrence. Attachment and line locality are SYN-12's rule.
- **Owner.** The owner of an occurrence is the innermost algorithm-level scope (the program root, a property body, a brace block in any expression position, a clause-branch body) whose written rows contain it: its output rows and its deconstruction right-hand sides (hoisting never moves an occurrence to another owner), through every transparent construct (operators, calls and their arguments, dot edges, captures, lists, redundant groups). A nested brace block or property is an owner of its own; lexical containment in another owner, a clause branch included, does not matter.
- **Weights.** `~x` weighs −1 and `x~` weighs +1. Markers on one occurrence, and on repeated occurrences of one name in one owner, add up exactly, as unbounded integers, never saturated, wrapped or clamped; opposite markers cancel before anything moves. A cancelled weight (`~x~`) is still a written marker and is validated like any other.
- **Eligibility.** A marker is valid only on an occurrence that its owner promotes to one of its own inferred parameters. Every other occurrence is `InvalidGraceMarker`, because there is no inferred parameter for the weight to attach to: an explicit parameter or clause binder of the owner, a parameter of an enclosing owner, a visible property, a builtin, an opened name, a structurally resolved dot member, a dot-only intrinsic edge (`.string`, `.Invoke`, `.Arguments`, `.Algorithm`), and any occurrence on a closed level, which infers nothing: under a written parameter list, and on a clause branch's own level (PAT-04). Grace in a clause-head pattern is a pattern-grammar error.
- **Movement.** The owner's own promoted names (PAR-05) start in first semantic occurrence; each starts with its summed weight as its remaining weight. A step exchanges a name with its neighbour on the side its weight points to (the next name for a positive weight, the previous name for a negative weight) and moves its remaining weight one unit toward 0. A step is impossible at the end of the own list, and when that neighbour moves the same way with at least as much remaining weight, compared on current remaining weights before the step: toward the end, a neighbour whose remaining weight is not smaller; toward the front, one whose remaining weight is not greater. An unmarked neighbour or one moving the other way never blocks. A name that is passed keeps its remaining weight.
- **Order of movement.** Names move one at a time, each in exactly one turn, in two passes fixed by their first-occurrence identities and initial weights, never by current positions or spellings: first every name with a positive weight, from the last-occurring to the first-occurring; then every name with a negative weight, from the first-occurring to the last-occurring. In its turn a name takes steps until its remaining weight is 0 or a step is impossible; a name with weight 0 takes no turn. Prefix-first movement is not the rule: the mover nearer the end it heads for always moves first, so no movement is lost because a same-direction blocker had not moved yet, and a rightward and a leftward mover can only meet when the rightward one is written first, so the passes resolve every meeting in source order.
- **Residual weights.** Weight a name cannot use, at an end or against such a neighbour, ends its turn but stays with it, and keeps blocking later movers that push the same way no harder: `F = ~a * 100 + b * 10 + ~~c` is `F(a, c, b)`, and `SumOfParams = a~~ + b~` is `SumOfParams(b, a)`.
- **The lifted tail.** Forwarded names are appended after the own names (PAR-05, PAR-07); they have no weight, never move, and are never crossed.
- **Invariants.**
  1. Without effective markers the order is first occurrence.
  2. A single marked name moves exactly as many places as its weight, stopping at the end; the others keep their order.
  3. One more postfix marker never moves its name earlier and one more prefix marker never later, and the name never overtakes, in the wrong direction, a name it was behind.
  4. Names with equal accumulated weights keep their first-occurrence relative order.
  5. Every marked name takes its turn, and no movement is lost to the order of turns: in the result, each name with remaining weight is held by the end it points to or by a same-direction neighbour with at least as much remaining weight.
  6. A contiguous equal-weight run moves as a unit in either direction when every parameter outside that run has zero weight.
  7. Prefix markers alone (one per earlier-written name that must end up after it) give exactly the intended order; so do postfix markers alone (one per later-written name that must end up before it).
  8. An unmarked name added at either end changes nothing among the others.
  9. The order depends only on each own name's first-occurrence position and total weight.
  10. At most n(n − 1) exchanges happen for n own names, whatever the weights.
- **Not guaranteed.** Mirror symmetry: `K = a * 100 + b~ * 10 + ~c` is `K(c, a, b)`, while `K = c~ * 100 + ~b * 10 + a` is `K(b, c, a)`. Independence: a marker on one name may change how two others end up. Displacement bounded by a name's own markers: `K = a + b~ + c~ + d~ + ~e` is `K(e, a, b, c, d)`, because b, c and d carry e one place left before e takes its own turn. A move never undone: a strictly stronger same-direction mover may pass a name back (`K = a + ~b + ~~c` is `K(c, b, a)`). Contiguity of an equal-weight run when other parameters also move: other movers can split the run while preserving its relative order, and `K = a~ * 1000 + b~ * 100 + ~c * 10 + ~d` takes `(c, a, d, b)`. "Desired position minus written position" is not a recipe.
- **Saturation is not an error.** A marker whose weight leaves its name in place (the owner's only inferred parameter, a name already at the boundary it points to, excess weight, a neighbour moving the same way with at least as much remaining weight, a cancelled weight, or the own/lifted boundary) is valid. Its unused weight still counts (Residual weights): `F = ~a * 100 + b * 10 + ~~c` is `F(a, c, b)`, whereas an unmarked `a` lets `c` reach the front. Validity never depends on the owner's other parameters or on whether the name moves.
- **No semantic effect otherwise.** Grace is stripped before evaluation and never changes resolution, selection, values, callability or evaluation. A graced name in redundant parentheses is the graced name.

**Qualifications**
- In a load-bearing branch (a deferred compilation unit, MOD-10) a marker on the branch's own level is reported when the unit is selected, like the unit's other elaboration errors; an unselected unit is never materialized to report it.
- The Grace forms on dot edges are DOT-06's rule.

```katlang
Divide = y / ~x
Weighted = a + 10 * b + 100 * ~~c
Divide(2, 10), Weighted(1, 2, 3)
```
⇒ `S[5, 132]`

```katlang
K = a~.t
L = a.~t
M = a.t
K({ x + 1 }, 7), L({ x + 1 }, 7), M(7, { x + 1 })
```
⇒ `S[8, 8, 8]`

Both graced dot forms are `(t, a)`.

- `F = ~x + 1` / `F(3)` gives `4`: the owner's only inferred parameter, saturated and valid.
- `K = s * 100 + ~x * 10 + ~y` is `K(x, y, s)`, and `Z = s~ * 100 + x~ * 10 + y` is `Z(y, s, x)`: neighbours moving the same way move together, the front one first.
- `K = a * 100 + b~ * 10 + ~~c` / `K(1, 2, 3)` gives `231`: b passes c; c, displaced but still owed its own turn, passes a, so `K(c, a, b)`, as without `b~`.
- `K = a~ * 100 + b * 10 + ~c` / `K(1, 2, 3)` gives `312`: postfix first, a passes b, then c passes a, so `K(b, c, a)`. Prefix-first movement would give `(c, a, b)`.
- `F = ~a * 100 + b * 10 + ~~c` / `F(1, 2, 3)` gives `132`: a is already first and keeps its unused −1; c passes b but not a, whose remaining weight equals its own, so `F(a, c, b)`. Unmarked, `F = a * 100 + b * 10 + ~~c` / `F(1, 2, 3)` gives `231`. `K = ~a * 100 + ~b * 10 + c` / `K(1, 2, 3)` gives `123`.
- `A = p - q` / `F = A - z~` / `F(1, 2, 3)` gives `-2`: `F(z, p, q)`, because `z~` cannot cross into the lifted `p, q` (saturated, valid).
- `K = a~ * 1000 + b~ * 100 + ~c * 10 + ~d` / `K(1, 2, 3, 4)` gives `2413`.
- `F = ~a - b` / `F(10, 3)` gives `7`, because `a` is already first. `A = x - y` / `G = A - z~` / `G(1, 10, 3)` gives `6`, because `z` cannot move past the lifted `x, y`.
- `Apply(f) = f(1, 10)` / `F(0) = Apply({ y - ~x })` / `F(0)` gives `9`: the block infers `(x, y)` and owns its marker; without the marker it is `-9`.
- `X = 1` / `K = ~X + 2` is `InvalidGraceMarker`; `F(a) = ~a + 1` is `InvalidGraceMarker` (explicit parameter); `Apply(f) = f(1)` / `F(0) = 0` / `F(n) = Apply({ x - ~n })` is `InvalidGraceMarker` (an enclosing parameter, reported once).

### PAR-07 — In a formula, a value-role reference to a callable that requires supplied arguments becomes a call that forwards the parameter bindings its site already sees; automatic forwarding never changes what an existing name refers to

*C#-only by design.*

- Automatic parameter forwarding must not change what an existing name refers to. Automatic forwarding reuses parameter bindings only. Properties, opened names and builtins are not forwarded as parameters.
- A formula lifts a reference exactly when the reference's **role** is a value use and the callable it **resolves** to has a lifting signature that requires supplied arguments. The two facts are independent. The role is the immediate consumer's, recursive and blind to laziness; the signature is keyed by the resolved callable's identity, never by the route that reached it. Forwarding sources are unaffected: the law decides which callees lift, never what supplies them.
- The front end rewrites such references in formulas into synthesized calls (automatic parameter forwarding, or lifting). A non-root body whose one written row is a bare reference to an algorithm is no formula: an open body is an alias of it (FWD-03), and a closed body is bare forwarding by name when the target declares parameters (FWD-02), both decided before this rule. Inside an inferring formula, a bare reference to a parameterized callable may lift that callable's required parameter bindings into the containing inferred signature; this rule is never the explanation of a closed body's lone row. The rewrite applies when all three of the following hold.
- **Signature.** The reference resolves, by the language's own order (the owner walk over the document's properties, then the prelude: builtins, the Math module and its aliases, the run's host operations, while `load` has none; then the opens level by level, or a structural dot path to its member), to a callable whose lifting signature requires supplied arguments: one an ordinary call supplying zero arguments cannot bind (CALL-05).
  - The lifting signature is keyed by that identity, resolved through aliases to their normalized target: a user algorithm's processed parameter patterns (an alias has none of its own and lifts its target's); a builtin's one callable interface (a loop's is `(meta step)` or `(meta step, count)`, whose `meta` position gives a caller an ordinary binding, CR-1); a Math member's or host operation's declared parameters; an opened or dotted member's own; and a clause family's one whole-value slot per position, named by the plain binders of its clauses (literal, structural and binderless patterns vote nothing; the votes must agree and the positions' names must be distinct).
  - A family without such names has no lifting signature and no name is invented: an inferring formula that would lift it is the front-end error `UnliftableClauseFamily`, while a closed level keeps its runtime zero-argument demand.
  - A callable that accepts zero supplied arguments (no parameter, or only a top-level collector) is never lifted, whatever its position: declaring a parameter does not by itself make a reference a call, so its bare name is the cached zero-argument value demand (CALL-05, PROP-04). A lone row naming it is an alias of any arity (FWD-03), or, under a closed list when it declares a parameter, bare forwarding (FWD-02).
  - A reference to nothing static (a parameter, an unresolved name, an ambiguous open, a runtime receiver's member) has no lifting signature.
- **Role.** It appears in a value-role position of its immediate consumer, a static classification of the written position, never a run-time demand: an output row (other than a lone row) or deconstruction right-hand side, an operator or comparison operand, a selection receiver or selector slot (a spread selector included), a spread operand, a list or capture element, the receiver of a dot-only intrinsic edge (`.string`, `.Invoke`, `.Arguments`, `.Algorithm`), a builtin's collection, value, whole-number or surplus slot (all three `if` slots; `repeat`'s count), an argument of a Math member, a host operation or a clause family, or a slot of a selected dot fallback that is one of these (`R.F(args)` is `F(R, args)` slot by slot).
  - A loop has no initial-state position: its `meta step` position is a callable role that transports its cell, and its state is the captured call's own arguments, which take that call's roles.
  - The role is recursive: an expression nested in any slot takes its own consumer's role. It is blind to laziness: an `if` branch lifts whether or not a run selects it. No role depends on how many arguments a call supplies. After a spread slot a builtin's positions are known only at run time, so a later position is a value role only when every declared position of that builtin is one. A slot the front end spreads for a declaration marked with `*` counts as a spread slot here, whether the marked call is written or created by this lifting (SUP-08).
  - The role decides only the rewrite: the synthesized call is an ordinary supplied computation, demanded only when a consumer demands it at run time (NEED-01, NEED-05).
- **Supply.** Every callee parameter can be supplied: by an existing parameter binding (below) or, at an inferring level, by a new forwarded parameter. At a closed level, a callee parameter that no existing binding supplies leaves the reference bare (PAR-04).
- **The forwarding source.** For each callee parameter `n`, the synthesized call passes the binding that a written parameter reference of `n` would already denote at the reference: name resolution's own answer (RES-01), restricted to parameters.
  1. The level's own written or inferred parameter `n`.
  2. Otherwise the nearest enclosing parameter binding `n` that the owner walk reaches before any same-named property: a written or inferred parameter of an enclosing owner, a clause-branch binder, or an inferred name of the never-called root.
  3. Otherwise, at an inferring level only, a new forwarded parameter `n`, appended to the level's signature after its own names (PAR-05) and keeping the callee pattern's shape and kind (a callee's `meta` capture becomes an ordinary binding, CR-1).
- A property, a structural member, an opened or module-provided name, or a prelude builtin never supplies `n`: when the walk reaches one first, or nothing, case 3 applies. Lifting is transitive through siblings. How the synthesized call passes the chosen bindings (their kind, spread, and the same-kind reconstruction of a callee's structural group) is FWD-02's rule.
- **A forwarded parameter never changes a written name.** It is an ordinary parameter for every caller (arity, order, binding, activation, exposure), and a same-named property of its owner, or of a body nested in it, is still `ParameterPropertyCollision` (RES-05). But it is never what a written identifier denotes. Name resolution decides every written name before forwarding, and nothing re-selects a binding afterwards. So adding a reference to a formula can never change what a previously resolvable identifier denotes, and extracting a sub-expression into a property keeps every binding the expression had.
- **Callable roles.** These positions keep a bare reference, because the consumer calls it, passes it on, or navigates it, while an expression nested in them takes its own consumer's role:
  - a call's callee;
  - a builtin callback (`map`, `filter` and `reduce` steps) and a loop step;
  - a whole argument of a user callable: its binder decides at run time and a plain capture keeps both channels, so `Twice(A)` passes `A` itself, while `Twice(A + 0)` lifts it;
  - an argument of a callee known only at run time (a parameter, an unresolved name, a computed value);
  - a dot receiver the edge navigates (a structural member) or whose dispatch only the runtime receiver decides.
- **Formula forwarding is by binding name.** Implicit forwarding is by binding name, regardless of how many times that name occurs in a callee's parameter patterns. A caller owns one binding for a given parameter name. If a callee uses that name in several parameter positions, at the top level, inside a group, across groups, or beside a collector (`P(x, x)`, `P(x, y, x)`, `P((x, a), x)`, `P((x, y), (z, x))`, `P((x, *rest), x)`, `P(x, *rest, x)`, `P((x, x))`), the forwarding source above is decided once for the name and supplied to every occurrence: `D = P + 1` over `P(x, x)` means `D(x) = P(x, x) + 1`, exactly as `H = F + G` over `F(x)` and `G(x)` means `H(x) = F(x) + G(x)`. The language does not distinguish a name shared by two callees from a name used twice by one callee. One binding name is one caller parameter (PAR-05): `P(x, x, x)` lifts one `x`, `P((x, a), x)` lifts `(x, a)`, `P(x, (x, a))` lifts `x, a`, `P((x, x))` lifts `x`, never `D(x, x)` and never one parameter per occurrence. A closed level that binds the name forwards its own binding into a formula; one that does not follows PAR-04.
- Forwarding one binding to several occurrences manufactures nothing: each occurrence is an ordinary argument slot that receives that same complete binding, the one supplied cell with its VALUE and CALLABLE channels and, once demanded, its completed failure (CALL-06, NEED-08). So PAT-09's constraint over independently supplied arguments holds by construction on a value, and a callable-only or failed argument behaves exactly as through the written `Same(x) = P(x, x)`. No lifting, neutral, closed or root position has a repeated-name case.
- A lone row is not a formula: `Some = P` is `P` itself, so a call through it supplies `P`'s two independent arguments, which must be equal, and `Q(x) = P` is bare forwarding, which reuses `Q`'s one binding `x` by name for both occurrences (FWD-02).

**Qualifications**
- `C = count` / `C((1, 2))` gives `2`, with `C` an alias of `count`, and the formula `C = count + 0` / `C((1, 2))` gives `2` too. `S = abs` / `S(-2)` gives `2`.
- **The root clause.** A bare root row naming a callable that requires supplied arguments is its own zero-argument demand whatever the category: `abs` is `ArityMismatch` at the reference, and `Math.Abs` is too, like `A = x + 1` / `A`; a root formula lifts (`abs + 0` is `UnresolvedImplicitParams`, needing `x`).
- The laziness-blind role has a bounded, deliberate cost: a bare read of a formula whose unselected branch uses a parameterized reference needs its argument (`A = x + 1` / `F = if(false, A, 0)` / `F` is `ArityMismatch`, and `A = x + 1` / `if(false, A + 0, 5)` is `UnresolvedImplicitParams`), and a signature may grow in code that never runs (`ParameterPropertyCollision`, `UnforwardableParameter` for a bare forwarding row over the grown callee).
- Forwarding into a closed list follows PAR-04; a closed level reuses an accessible enclosing parameter exactly as an inferring one does.
- The spread synthesized for collecting-to-collecting forwarding in a formula (`Target(tag, *items) = items` / `Use(tag, *items) = [Target][0]` / `Use(0, 1, 2)` gives `[1, 2]`, calling `Target(tag, items*)`) is FWD's rule; a reused enclosing binding counts as the source binding. The lone row `Target(tag, *items) = items` / `Use(tag, *items) = Target` / `Use(0, 1, 2)` is bare forwarding by name, `Target(tag, items*)`, and gives `[1, 2]` too. A bare alias of a callable that works with no arguments is an alias: `Cnt(*xs) = xs.count` / `Alias = Cnt` / `Alias, Alias(1, 2), map([1, 2], Alias)` gives `S[0, 2, L[1, 1]]`.
- A forwarded parameter gives no meaning to a name nothing declares: a closed branch's `v` stays `UndeclaredIdentifier` whatever its owner forwards.
- Reuse can be partial, in a formula: an owner that reuses its enclosing `x` and forwards only `*rest` accepts zero supplied arguments, so "a lifted signature always requires arguments" holds only where nothing is reused. A grouped callee pattern keeps its reused capture: in `P((a, b))` inside `F(a)`, the formula `G = P + 0` takes `b`, a sequence group left with one binder being that binder (PAR-05).
- One body shared by reference under owners with different parameter bindings is forwarded per context.
- Lifting reads final signatures only, whatever the order of declarations (PAR-08).

```katlang
Speed = distance / time
KineticEnergy = mass * Speed ^ 2 / 2
KineticEnergy(2, 10, 5)
```
⇒ `4`

`KineticEnergy(mass, distance, time)`: callee parameter names are observable in formulas, deliberately, because formula forwarding is by name.

```katlang
A = y + 1
F(y) = {
  G = y * 1000 + A
  H(y) = G
  H(100)
}
F(3)
```
⇒ `3004`

Exactly the inlined `G = y * 1000 + (y + 1)`: `G` reuses `F`'s `y` for `A` and takes no parameter of its own, so `H`'s unrelated `y` cannot reach it.

```katlang
Area = width * height
Report(width, height) = {
  Doubled = Area * 2
  if(width > 1, Doubled, 0)
}
Report(3, 4)
```
⇒ `24`

`Doubled` is an ordinary zero-parameter property of `Report` (PROP-08).

```katlang
v = 99
Need(v) = v
Outer = {
  Inner = v
  Inner + Need
}
Outer(7)
```
⇒ `106`

`Outer` receives a forwarded `v` for `Need`, while `Inner`'s written `v` keeps denoting the root property. The root property never supplies `Need`'s parameter: `v = 99` / `Need(v) = v` / `Outer = Need + 1` / `Outer(7)` gives `8`.

```katlang
A = y + 1
Outer(y) = {
  Inner(y) = A * 2
  Inner(10) + y
}
Outer(3)
```
⇒ `25`

Explicit shadowing is intentional: inside `Inner` the reused `y` is `Inner`'s own.

```katlang
Head(x, *rest) = x + rest.count
F(x) = {
  H = [Head][0]
  H(10, 20)
}
F(4)
```
⇒ `6`

The formula `H` reuses `F`'s `x` and forwards only `*rest`. With the lone row `H = Head`, `H` is `Head` itself, whose own binders take both arguments, and the same program gives `11`.

```katlang
P((a, b)) = a + b
F(a) = {
  G = P + 0
  G(5)
}
F(10)
```
⇒ `15`

`G` takes only `b` and calls `P((a, b))` with `F`'s `a`. So `G((1, 2))` there binds `b` to the pair, and `P((10, (1, 2)))` is the `+` `TypeMismatch`.

```katlang
A = y + 1
F = {
  y = 3
  A + 0
}
F
```
⇒ `ParameterPropertyCollision`

The forwarded `y` collides with `F`'s own property. With the lone row `A`, the body has no parameter of its own and its declaration `y = 3` never reaches the target's parameter:

```katlang
A = y + 1
F = {
  y = 3
  A
}
F(5)
```
⇒ `6`

```katlang
Need(v) = v
Outer = {
  F(0) = 0
  F(n) = v
  F(1) + Need
}
Outer(7)
```
⇒ `UndeclaredIdentifier`

- `A = x + 1` / `F = A + 1, 2` / `G = [A + 1, 2]` / `F(5), G(5)` gives `S[S[7, 2], L[7, 2]]`. `A = x + 1` / `Id(v) = v` / `F = Id(A + 1)` / `F(5)` gives `7`; `A = x + 1` / `F = (A + 1, 2)` / `F(5)` gives `(7, 2)`; `Inc(x) = x + 1` / `K = sum(Inc)` / `K(4)` gives `5`; `A = x + 1` / `F = A.string` / `F(3)` gives `'4'`.
- A family lifts through its plain binders: `E(0) = 100` / `E(n) = n` / `Fam = E + 1` / `Fam(5)` gives `6`. `S(1) = 1` / `S(-1) = -1` / `G = S + 0` is `UnliftableClauseFamily`, while the closed `S(1) = 1` / `S(-1) = -1` / `G(x) = S + 0` / `G(1)` is the runtime `NoMatchingBranch`.
- `NeedMin(min) = min + 1` / `Safe = NeedMin + min((3, 4))` / `Safe(10)` gives `14`: the written `min(...)` still calls the builtin. `Clamp(x, min, max) = if(x < min, min, if(x > max, max, x))` / `Safe = Clamp + 0` / `Safe(15, 0, 10)` gives `10`: parameters named like builtins stay parameters to forward.
- `A = x + 1` / `Twice(f) = f(f(1))` / `F = Twice(A)` / `F` gives `3`: a user callable's whole argument is neutral, so `A` is passed as a callable.
- `A = trace(x) + 1` / `Choose(0, a) = 0` / `Choose(n, a) = a` / `F = Choose(0, A)` / `F(5)` gives `0` with no trace, yet `x` joins `F`'s signature, because the matching clause's plain binder `a` demands nothing (NEED-04), while `A = trace(x) + 1` / `Choose(0, a) = 0` / `Choose(n, a) = a` / `F = Choose(1, A)` / `F(5)` gives `6` and traces `5` once.
- `Roll(*xs) = randomInt(1, 1000000)` / `R0 = randomInt(1, 1000000)` / `Roll == Roll, R0 == R0, Roll, sum(Roll), Roll + 0` gives `S[true, true, 889632, 889632, 889632]`: `Roll` accepts zero supplied arguments, so no position lifts it and every read is the one cached draw.
- `Cnt(*xs) = xs.count` / `Twice = Cnt + Cnt` / `Twice(1, 2)` is `ArityMismatch`: `Twice` lifts nothing. `Head(x, *rest) = x + rest.count` / `H = Head + 0` / `H(5, 6, 7)` gives `7`: a callee that requires an argument still lifts.
- `P(x, x) = x` / `D = P + 1` / `D(7)` gives `8`, and `P(x, x) = x` / `D = P + 1` / `D(7, 7)` is `ArityMismatch`: one binding name, one caller parameter. The same holds in every formula position, for nested repetitions (`P((x, a), x) = a` / `Some = [P][0]` / `Some((7, 8))` gives `8`), and under a closed list that binds the name (`P(x, x) = x` / `Q(x) = P + 1` / `Q(7)` gives `8`). A closed list that does not bind it keeps the reference bare: `P(x, x) = x` / `Q(y) = P + 1` / `Q(7)` is `ArityMismatch`.
- A call through the alias is `P`'s own call: `P(x, x) = x` / `Some = P` / `Some(7)` is `ArityMismatch`, `P(x, x) = x` / `Some = P` / `Some(7, 7)` gives `7`, `P(x, x) = x` / `Some = P` / `Some(7, 8)` is `ArityMismatch`, and `P((x, a), x) = a` / `Some = P` / `Some((7, 8), 7)` gives `8`.
- Who supplies the occurrences decides what is checked: `Common(x, x) = x` / `Twice(v) = Common(v, v)` / `Twice(8)` gives `8`, while `Common(x, x) = x` / `Both(a, b) = Common(a, b)` / `Both(7, 8)` is `ArityMismatch`, and `Common(x, x) = x` / `Some = Common` / `Some(9, 9)` gives `9`. `F(x) = x + 1` / `G(x) = x * 2` / `H = F + G` / `H(3)` gives `10`.

### PAR-08 — Inferred signatures are selected jointly before any rewrite: a recursive inference that settles completes, and only a group with no unique grounded settled answer is refused

*C#-only by design.*

- Inference has two phases before anything is rewritten. Analysis records one equation per written open body per declaring context: the body's own patterns and its value-role references in written order, each with its static callee identity, so an alias and its target are one callee. A nested helper's reads belong to the helper, never to its owner. Selection then decides every inferred signature of the operation jointly, and with it whether each `.Algorithm` link is a calculation (exactly when its selected signature is nonempty).
- No read observes a provisional signature, so declaration order is unobservable in signatures and results (RES-10). Only the order of diagnostics follows the traversal.
- Inference uses the same composition law for ordinary and recursive dependencies (PAR-05, PAR-07): own parameters first, then lifted callees in written reference order, with the same duplicate handling, forwarding sources, group shapes and `meta` lifting. Completing a cycle adds no second law.
- A cycle is first read with every member declaring nothing, while own patterns and every fixed lower or external fact are included. If no read inside the cycle then lifts, that is the cycle's one meaning.
- Otherwise it is a genuine lifting cycle, completed simultaneously: from that first state, every member is recomposed in each round from the preceding round's facts, never from a partly updated neighbour, and facts outside the cycle stay fixed during its rounds.
- Rounds stop when two successive rounds have the same full ordered state: every member's pattern tree (kinds, grouping, names, order) and its validity flag. The reached signatures are the result. Another structural fixed point of the same equations creates no ambiguity by itself, and a parameter or requirement that appears and later disappears during the rounds refuses nothing.
- Processing order, declaration order that preserves bindings, allocation identity and scheduling select nothing. Written reference order stays meaningful, because the composition law gives it meaning.
- A written parameter list is final as written: rounds never change it, and it remains the way to choose an order the rounds did not reach.
- **Refusal.** A group is refused only when it has no unique grounded settled answer. A reading of the `.Algorithm` links is consistent when every link evaluates to its class and every body has a meaning, and grounded when no set of its calculation links holds only through its own support. A group fails when a recursive inference does not settle (a state repeats an earlier one with period greater than one), or when the links have two grounded readings, none (no coinductive reading is added), only self-supporting readings, or an undetermined one. Selection is joint: a reader can exclude a reading of what it reads, so a group's answer is decided with its readers.
- The refusal is the front-end error `SelfDependentInferredParameters`, reported at each body that failed on its own and worded by its category. A body that failed only because it reads a refused group is not reported again. The unit is never evaluated.
- **Validity belongs to the settled state.** An inferred signature must be one a programmer could write (VAR-02). A round's composition that breaks that rule is a step of the computation: its fact is the recovered list with the violation flagged, the next round reads that list, and the flag compares as part of the state. A flag a later round clears refuses nothing, and the settled list has passed the same validator as a written head. A flag the settled state keeps is the definition's own front-end error, and the program never runs. There is no refusal of an intermediate state and no weaker validator for a settled one.
- **Origins.** Every inferred capture records where it came from: its first provider, followed to the end of the chain, or, for a chain that closes on itself and every node whose chain enters it, one generated cycle origin, naming the cycle's members and the sources reachable from it through active, lifted providers. Such an origin can have no source at all, and no source is then invented; a reader and a later unit inherit it unchanged. It is a set, it describes the final provider graph rather than the history of the rounds, and it is never reported as a source declaration. Origins serve diagnostics and editors only.

**Qualifications**
- The promise is limited on purpose. Not every recursive program is accepted. Inference evaluates nothing: no user expression, `tick()`, callback or runtime effect. So a completed recursion can still fail or run forever when used. A completed answer need not be the only structural fixed point.
- An explicit recursive call never lifts, nor does a self read that infers nothing (PROP-09).
- A completed recursion can make an additional `.Algorithm` classification meaningful and leave two grounded readings. The group is then refused, never resolved by choosing one; writing the affected parameter lists resolves it.
- Rounds are bounded by the operation's static resource ledger, not by a language-wide polynomial law (C#-only host policy). Exhausting it is `StaticStructureLimitExceeded`, a resource refusal and never an inference rule; cancellation is the operation's cancellation; neither is ever reported as non-settling, and neither publishes anything.
- A deferred unit selects its own signatures when it is selected (MOD-10), reading what the eager unit published.

```katlang
F = if(tick() > 3, x, F + 1)
F(10)
```
⇒ `13`

`F` completes as `F(x)`, as its written form would.

```katlang
C = B + z
A = {
  H = B + 0
  x + 1
}
B = y + A
C(1, 2, 3)
```
⇒ `7`

`C` is `C(z, y, x)` in every declaration order: the helper `H` reads `B`, never `A`.

```katlang
X(x) = x
Y(y) = y
A = B + X
B = A + Y
A(1, 2)
```
⇒ `SelfDependentInferredParameters`

The two members alternate between two orders. Each refused body reports once, and a reader `C = A + 0` adds no report.

```katlang
E(e) = e * 10
F = if(tick() > 2, 0, F + G + E)
G = p + F + 0
F(1, 2)
```
⇒ `24`

The rounds reach `F(e, p)`. The written `F(p, e) = …` is equally consistent and gives `42`: reaching one fixed point is no ambiguity, and a written list is how to choose the other.

```katlang
C1(a, *p) = a
C2(b, *q) = b
A = if(tick() > 2, 0, B + C1 + C2)
B = A + 0
A(1, 2, 3, 4, 5)
```
⇒ `10`

`A`'s first round breaks the collector rule; `B` picks up the recovered list, and reading `B` first gives `A` a plain `q` before `C2`'s `*q` arrives, so the settled `A(a, *p, b, q)` is writable. With `C1 + C2 + B`, both collectors are rebuilt in every round, the flag stays, and `C1(a, *p) = a` / `C2(b, *q) = b` / `A = if(tick() > 2, 0, C1 + C2 + B)` / `B = A + 0` is `InvalidCollectingBinding`.

- `A = if(tick() > 3, x, B + 1)` / `B = A + 1` / `A(10)` gives `16` in both orders of the two declarations.
- `A = if(x <= 0, 0, B)` / `B = if(x <= 0, A, A(x - 1)) + 1` / `A(3)` gives `3`.
- Written reference order stays meaningful: `A = if(tick() > 3, x + y, B + 1)` / `B = A + z` makes `A` `A(x, y, z)` and `B` `B(z, x, y)`.
- `Fact = if(n <= 1, 1, n * Fact(n - 1))` / `Fact(5)` gives `120`, and `A = if(tick() < 3, A + 1, 0)` / `A, A` gives `S[2, 2]`: neither lifts.

## NEED — Call by need: supplied computations, demand and transport

A call supplies computations, not values, and these laws govern how they are acquired and forced wherever another law seems to say otherwise. A **cell** holds one supplied computation with its captured caller context, and a **supply** is the ordered list of cells one call forms. A cell has two independent channels: **VALUE**, read by a **demand** that runs the computation at most once, and **CALLABLE**, read by a **projection** that obtains its algorithm identity. A **ready cell** holds an already computed value and has no CALLABLE identity. **Transport** hands on an existing cell or an exact slice of cells and reads neither channel.

### NEED-01 — Supply computations in the caller environment

- After one callable identity is selected, the call forms an ordered supply in the caller's captured lexical environment.
- Each non-spread written argument supplies one cell, whatever its eventual value: scalar, sequence, list or empty. Distinct written computations create distinct cells.
- A parameter supplied as an ordinary argument transports its existing cell, with every available channel. It does not read VALUE first.
- Already computed components use ready cells.
- Allocation and transport execute no supplied computation and introduce no invocation.

```katlang
Ignore(x) = 0
Twice(x) = x + x
Pass(y) = Twice(y), y
Ignore(tick()), Pass(tick()), tick()
```
⇒ `S[0, S[2, 1], 2]`

### NEED-02 — One immutable completed VALUE outcome

- The first VALUE demand starts the supplied computation once. The cell stores its completed counted value, with the established value boundary, or its ordinary runtime failure with original provenance.
- Later VALUE demands observe that outcome without re-execution, redraw, repeat effect or restart.
- A separately available CALLABLE identity is not derived from a successful VALUE outcome.
- Static diagnostics are never cell outcomes.
- A reached resource limit terminates the run. It is never a recoverable argument value or a clause mismatch, and a stored terminal completion cannot restart work (RUN-03).

**Qualifications**
- *C#-only:* a computation that ends by cancellation stores a sticky cancellation outcome (NEED-09).

```katlang
Twice(x) = x, x
Stable(x) = x == x
Twice(tick()), Stable(randomInt(1, 1000000))
```
⇒ `S[S[1, 1], true]`

### NEED-03 — Executed demands determine effects

- Only executed supply opening, inspecting patterns and semantic consumers demand computations.
- Effects, random draws, suspensions and failures follow first-demand order. Supply positions do not prescribe effect order.
- Plain unused bindings execute nothing.
- Operators, output rows, collection construction and other consumers keep the internal order and demand policy their own laws fix: `and` and `or` evaluate their right operand only when the left one does not decide (BOOL-04), and a list literal and the `map`, `filter` and `take` stages evaluate a position only when it is read (SEQ-02, COLL-04).
- Failure stops subsequent work on that path.
- No evaluation may speculate on an undemanded computation.
- `tick()` (RUN-09) makes executed demands observable and adds no law. Each actual execution is an effect like a host call: an undemanded supply runs nothing, a supplied `tick()` demanded twice is one cell outcome, a bare `tick` reference is CALLABLE transport only, and the effect is never rolled back by a later failure.

```katlang
Swap(x, y) = y, x
Ignore(x) = 0
Swap(tick(), tick()), Ignore(tick()), tick()
```
⇒ `S[S[1, 2], 0, 3]`

### NEED-04 — Ordered pattern inspection and shared clause supply

*Open: the design area of repeated-name interpretation is deferred; this states the implemented law.*

- After cardinality validation, patterns are traversed left to right, recursively in written order.
- A non-repeated plain binder retains its complete cell: it neither projects CALLABLE nor demands VALUE.
- A literal demands its position.
- A structural pattern demands the supplied value and checks its kind and cardinality before binding its fields. Checking a `filter` result's cardinality can demand candidates. A sequence's elements are values. A list's positions stay deferred: binders and collecting binders bind the original positions, and a literal, a nested pattern, a repeated-name inspection or a later use can demand a field (SEQ-02): `P([a, b]) = b` / `P([1 / 0, 2])` is `2`. Every opened child has only a VALUE channel.
- Collector positions establish exact slice boundaries without reading slice elements. The same traversal rule applies to their fixed prefix and suffix and to nested patterns.
- Each clause attempt uses the same supply cells. A non-match may try the next clause and retains previous outcomes. A runtime failure during required inspection aborts dispatch and is never a non-match. A successful branch retains both channels of its bound cells.

**Repeated names are group-aware.** Every occurrence of a repeated name is an inspecting pattern, including its first.

- At each visited occurrence the binder first projects that original cell's CALLABLE through the ordinary protocol, single flights and cycle detection included. A successful identity makes the occurrence **callable-bearing**, contributing its normalized full structural identity (through transparent references, stopping at structural carriers). A successful absence makes it **value-only**. A projection failure propagates unchanged, and is never absence, a mismatch or a family non-match.
- Per repeated name, binder activation and clause attempt, the binder keeps the group's first callable identity, the first value-only contribution's counted VALUE (the **anchor**), and the earlier callable-bearing contributions whose own VALUE no anchor has checked yet (the **pending** contributions, in occurrence order).
- A callable-bearing contribution is compared with the group's identity first. A conflict rejects at once with `TypeMismatch`, before later patterns and before any VALUE demand. Without an anchor the contribution becomes pending and its output is not demanded. With an anchor its own counted VALUE is demanded and compared with the anchor.
- A value-only contribution demands its own counted VALUE first. The first one becomes the anchor, and then every pending contribution's own counted VALUE is demanded and compared in occurrence order, stopping at the first failure or incompatibility. A later one is compared with the anchor.
- Counted-value inequality (the value up to `==`, and its emitted count) is ordinary binding `BadArity`, public `ArityMismatch`. In a family either incompatibility is a non-match. An executed CALLABLE or VALUE failure stays the dispatch's failure.
- The binding is the first callable-bearing original contribution when the group has one, otherwise the first value-only one: one original cell with its own address, owner, VALUE and CALLABLE, never a splice of one contribution's identity with another's VALUE. On the Decimal128 tier the representative keeps its exact representation: `A = 1.50` / `P(x, x) = x.string` / `P(1.5, A), P(A, 1.5)` is `S['1.50', '1.50']`.
- The first value-only occurrence's VALUE is demanded before the earlier pending VALUEs, which are then demanded in occurrence order.
- The binder never inspects a future occurrence, projects through an unopened structural value or passes an intervening pattern speculatively. A non-matching literal between two occurrences ends the attempt before the waiting reference is demanded.

**What follows**
- `docs/design/language-rules/call-by-need.md` § NEED-04 holds the worked consequences. This law restates that accepted text and adds none.
- Failure reporting is ordered: `A = 1.0` / `B = 1.00` / `P(x, x, x) = x` / `P(A, B, 2)` is `TypeMismatch`, while `A = 1.0` / `B = 1.00` / `P(x, x, x) = x` / `P(A, 2, B)` is `ArityMismatch`. Both are unsatisfiable.

**Permutation**
- On the stable domain (successful, stable channel observations under the identity domain's stated premises), a group succeeds exactly when all present identities agree and, if any contribution is value-only, every contribution's own counted VALUE agrees. That acceptance is invariant under permuting the group's contributions.
- A successful mixed group also preserves the bound counted VALUE up to `==`.
- A successful reference-only group preserves identity, callable availability and the first original representative, not counted VALUE. Two cells of one identity may hold different completed VALUEs, and a later body read sees the first callable contribution's.
- Error category, blamed contribution, effect order, diagnostics and spans are not permutation-invariant.

**Qualifications**
- The pending list is matching state only: no parameter, value, cache domain or spliced cell. It is released on success, mismatch, exception and cancellation.
- Sharing one cell twice reuses its memo. Independent equal spellings do not share.
- Cancellation and reached resource limits stay terminal for reference-only groups too.
- Repeated collecting names and repeated `meta` binders stay invalid. Fixed repeated names beside collectors use the same group state.

### NEED-05 — Whole-source validation, then runtime demand phases

- The whole-source boundaries come first: parsing, resolving written names, and validating signatures, patterns and forwarding contracts all precede executing validated code. Deferred source regions are validated at their established materialization boundary (MOD-10).
- Argument laziness excuses none of those checks on available written definitions, an uncalled invalid forwarding definition included: `F(q) = q` / `A(p) = F` / `1` is `UnforwardableParameter`.
- Formula lifting still follows the immediate consumer's role and zero-supply acceptance (PAR-07). Closed heads gain no new bindings.
- A resolved callable reference whose implicit lift a closed head cannot supply remains its ordinary zero-supply VALUE demand, rejected when it executes with the callable's established runtime rejection. No static blocked-lift diagnostic exists for Math, another value consumer, a selector branch, an alias or a forwarding route. Static roles decide elaboration, not a proof of eventual execution, and actual consumers validate the values they demand.
- Directly undeclared closed-list names and invalid structural forwarding remain static errors.
- Runtime order is: resolve one callable identity → form supply and open spreads → validate supplied cardinality → inspect patterns and dispatch → execute body consumers.
- A callee-resolution failure precedes opening. A required spread failure precedes cardinality rejection and later supply slots. Wrong cardinality rejects before any non-spread VALUE demand, for every callee category.
- A family of that cardinality with no matching clause reports `NoMatchingBranch`. Wrong cardinality reports `ArityMismatch`. Source families still require consistent branch-head arity: mixed heads are the static `BranchArityMismatch`.

**Qualifications**
- Arity payloads name the selected signature's actual supplied-slot requirement, not flattened captures (CALL-04). A builtin's acceptance facts are its own (CALL-03).

```katlang
Inc(x) = x + 1
K(z) = abs(Inc)
7
```
⇒ `7`

```katlang
Inc(x) = x + 1
K(z) = abs(Inc)
K(1)
```
⇒ `ArityMismatch`

`F(x) = x` / `F(1 / 0, 2)` is `ArityMismatch`, while `F(x) = x` / `F(1, (1 / 0)*)` is `DivisionByZero`.

### NEED-06 — CALLABLE projection and fresh invocation

- CALLABLE projection reads a supplied computation's resolved identity and captured owner without demanding that computation's VALUE. Identity-only projection evaluates nothing. A **runtime projection** (a reference's `.Algorithm` link, and navigation through a parameter whose cell is one) may demand other cells' VALUE on its callee route, through their ordinary single flights, never the projected cell's own VALUE.
- Identity distinctions, aliases and availability are preserved. No identity is invented for a scalar, capture, list, selection or computed value. A reference exposes its callee only through `.Algorithm` (CR-14).
- Actual invocation is fresh, with an ordinary supply and normal invocation charges.
- Callbacks and loop steps request CALLABLE. Native value slots, operators and selected results request VALUE. If both occur, effects follow their executed order.
- A VALUE failure does not erase independent identity. Neither channel bypasses terminal run state.
- Absence of callable identity is a successful projection outcome, never an error. A projection whose computation fails has failed: its error, whatever its kind, `NotAnAlgorithm` and `IllegalInEval` included, keeps its kind, span and context everywhere it is observed. No consumer converts it into absence, a clause non-match, a value-receiver route, a fallback or another error. Absence reports are produced only from an absence outcome.

**Missing callable identity**
- When an invoking consumer finds no CALLABLE identity, the rejection is `NotAnAlgorithm` for every consumer: a user higher-order parameter, a builtin callback (the `map` transform, the `filter` predicate, the `reduce` reducer), a `while` or `repeat` step, and an invoking slot reached through a builtin used as a step.
- It is produced by CALLABLE projection only when an invocation is required, never by demanding VALUE. An unused invoking slot is never projected.
- A cell that has CALLABLE identity keeps its callable's ordinary binder and dispatch verdicts: a zero-parameter callable given an item is `ArityMismatch`.
- There is no value-to-thunk fallback.

**Results are calculation values**
- A supplied input may expose VALUE and CALLABLE, and binding, transport, forwarding and collector-slice opening preserve both.
- Result construction demands VALUE and produces data: output rows, `if` and clause selection, sequence construction, selection, spreading a result, a loop's final state and a property's value. A list literal defers each ordinary slot to a position whose VALUE a reader demands (SEQ-02). No data carries callable identity, a list position included.
- CALLABLE projection exists only for written references: a name, a transported parameter, an inline block, a structural dot path, an alias and an `.Algorithm` link. It never exists for a call, selection, collection or capture.
- So a call result cannot be invoked, and a callable read as a result is its zero-supply VALUE demand.
- An invocation must satisfy its supply contract. An undersupplied call is an arity failure, never a partially applied callable. KatLang has no implicit partial application, and collector arity keeps its own rules.
- Bare forwarding (`Wrapper(x) = Target`) invokes `Target` with existing supplies and yields its result. It never returns `Target`. A bare nested callable in a closed body is bare forwarding, so a nested algorithm cannot escape its creator either.

**Dot expressions**
- A dot expression has one callable identity wherever a callable is used: supplied argument, forwarded parameter, builtin callback, loop step and callee (DOT-09). An argumentless structural path carries its member's own callable, aliases normalized. Every other dot expression (a fallback result, an intrinsic `.string`, an argument-bearing edge) is a computed value with no identity, so calling it is `NotAnAlgorithm`.
- Invocation through the projected member is fresh. `(Box.V)()` evaluates `V` again and never reads `Box.V`'s property entry, while the bare read `Box.V` keeps that entry. A `(Box.V)()` that finds the entry empty establishes it, exactly as `Box.V()` does (NEED-10).
- On a structural miss an argumentless edge spelled `Algorithm` is the one dot expression whose identity is a runtime projection (CR-14). Member access never navigates through it.

```katlang
Box = { public V = 5
1 / 0 }
Inc(x) = x + 1
Apply(f, x) = f(x)
Member(f) = f.V
Member(Box), Apply(Inc, 3)
```
⇒ `S[5, 4]`

```katlang
Inc(x) = x + 1
Apply(f, x) = f(x)
ReturnF(g) = g
Apply(ReturnF(Inc), 3)
```
⇒ `NotAnAlgorithm`

```katlang
Box = { public V = tick() }
Box.V, (Box.V)(), Box.V
```
⇒ `S[1, 2, 1]`

`Apply(f, x) = f(x)` / `Z = 3` / `Apply(Z, 1)` is `ArityMismatch`, while `Apply(f, x) = f(x)` / `Apply(5, 3)` is `NotAnAlgorithm`.

### NEED-07 — Lazy supply, eager collection VALUE

- Explicit `E*` opens one supply level. An arbitrary `E` is evaluated during supply formation to discover its ordinary value and items, and those items become ready cells.
- An existing collector already is an exact, known-cardinality slice: opening it transfers its element cells directly, without VALUE materialization, and opens no element value.
- In an argument or selector supply, a spread whose last star opens an argument view transports the captured plan's original cells, and a star that would open a view into values is `TypeMismatch` (CR-11).
- A postfix selection forms its selector supply by the same law (SEQ-05). After obtaining the receiver's retained slice or its VALUE, every explicit spread selector runs during formation and contributes its items, while each ordinary selector stays a suspended computation, demanded left to right only when the selection reaches it.
- A collector's ordinary VALUE demand materializes all its cells left to right into one exact eager list, preserving nested and empty values as elements. An empty slice yields `[]`.
- Every consumer of that VALUE (`.sum`, `.skip`, `.map`, a list or capture element, a structural pattern, an output row, a result boundary) receives the complete list: `F(*xs) = xs` / `F(1, 1 / 0)` is `DivisionByZero`, and a written list holding a collector's spread items holds their values (`F(*xs) = [xs*][0]` / `F(10, 1 / 0)` is `DivisionByZero`).
- Five observers read a retained collector's slice instead of its VALUE (owner-approved November 2026, `772d936e`): `count` reads its length and demands no element; `first` and `last` check that a position exists and demand only that element; postfix selection validates each selector before it demands its one element; and `take` validates its count before it demands exactly its prefix. They reach the slice through a transparent reference too, while a brace carrier is a computed value that they read whole. `CountItems(*xs) = xs.count` / `CountItems(1 / 0)` is `1`, and `F(*xs) = xs[1], xs[1]` / `F(tick(), tick())` is `S[1, 1]`.
- A list's own positions are a different rule (SEQ-02, COLL-04): they are evaluated on demand wherever the list goes, while a collector's VALUE contains all its top-level items. Nested lists keep their own positions.
- A collector passed without opening is one collection-valued computation. A capture demands it when forming the slot. A list literal holding it in an ordinary slot demands it when that position is read (SEQ-02). A spread in either construct reads it during construction (SUP-02).

**Qualifications**
- *C#-only:* every expanded supply is bounded before its items are retained or wrapped in ready cells. An overflowing supply still forms, count-only, to its end, and is then refused terminally, with ordinary slots undemanded (RUN-03).

```katlang
Ignore(*xs) = 0
Fwd(*xs) = Ignore(xs*)
Ignore(tick()*), Fwd(1 / 0), tick()
```
⇒ `S[0, 0, 2]`

`[10, 20][99, (1 / 0)*]` is `DivisionByZero`: formation precedes selection. `[10, 20][99, 1 / 0]` is `BadIndex`: the second selector is never demanded.

### NEED-08 — Forwarding transfers supplies

- NEED-FWD, the short statement of this law: forwarding transfers demandable supplies; it does not force them. Pattern matching or supply formation may demand values before forwarding, but the forwarding edge itself performs no VALUE demand.
- Bare forwarding keeps its selection by binding name and compatible pattern or structure, with its ownership and source-kind rules (FWD-02).
- Forwarding transfers complete cells with their available VALUE and CALLABLE channels, or exact collector slices, preserving identity, provenance, memoized outcome and caller ownership.
- A collecting source opened for a collecting destination transfers its slice. A fixed source stays one item. Where the contract permits a collecting source for a fixed destination, its collector cell passes as one collection-valued computation, not as expanded slots.
- Incompatible structure is still refused statically. A structural reconstruction uses the demand rule of the corresponding written construct. A sequence capture evaluates its slots at construction. A list literal forms its spreads at construction and defers its ordinary positions (FWD-02, SEQ-02).
- Alias indirection introduces neither a force nor a wrapper memo domain.
- Unnameable families stay callable and aliasable with call-by-need, but have neither a by-name forwarding contract nor a formula-lifting signature.
- Explicit `F(x)` transports `x`'s cell. That does not equate every static or property aspect of explicit calls with bare forwarding.

```katlang
Collect(*xs) = xs.count
Count(x) = x.count
Open(*items) = Collect(items*)
Whole(*items) = Collect(items)
ToFixed(*x) = Count
Ignore(y) = 0
Bare(y) = Ignore
Open(1, 2, 3), Whole(1, 2, 3), ToFixed(1, 2, 3), Bare(1 / 0)
```
⇒ `S[3, 1, 3, 0]`

### NEED-09 — Single flight, cycles, cancellation and resources

- A cell's VALUE and a cell's runtime CALLABLE projection are each a computation under one protocol: suspended, active or completed. The transition to active and one shared completion are published atomically before the computation starts. An observer from another flow records its wait-for edge and then joins that completion. At most one computation per cell and channel is ever active, and its outcome is every observer's outcome.
- Identity-only projections evaluate nothing, cannot be re-entered and keep their first published outcome.
- Serial evaluation is sufficient. Speculative parallelism is forbidden.
- Both channels are nodes of the run's one wait-for graph. A dependency cycle is detected before awaiting the edge that closes it, including indirect and asynchronous cycles and a cycle across independently started overlapping chains.
- Re-entering a computation that is active in the current logical flow, through either channel, is the ordinary evaluation error `DemandCycle`, for the re-entering observation only. It is not published at the re-entered computation, which continues. The completed computation's outcome, a `DemandCycle` it received and returned included, is sticky, so a failed dependency chain memoizes it.
- `DemandCycle` blames the cyclic cell's original supplied-expression span, with a written demand or call context, and exposes no heap or force frame. With no source provenance the span is absent.
- Fresh recursive calls and cells remain ordinary recursion governed by normal limits.

**Cancellation and terminality**
- Cancellation belongs to the original run. Cancellation during evaluation completes that cell as cancelled and never restarts it, and an overlapping observer joins the same completion. A waiter acquires no separate restart or replacement cancellation policy.
- A pre-cancelled run executes no argument effect.
- Cancellation after value completion does not rewrite the stored value, but run-level cancellation observation still rejects subsequent language work.
- A resource limit reached by a computation completes it terminally and is retained by the run. Cancellation and host exceptions complete it exceptionally: stored and shared by in-flight observers, never published as a callable outcome and never restarted.
- Reached cancellation and resource terminality are checked before further semantic work, memo observation included, at every observation entry, without making a completed failure a branch non-match.

**Charges**
- Cell allocation, cell and slice transport, in-flight joining, memo hits and pure callable-identity projection have zero additional semantic step or invocation-depth charge.
- Existing expression-read, resolution, consumer and materialization charges still apply when their operations execute. A first force charges the original expression's actual executed work exactly once. Each actual wrapper, target or callback invocation incurs its normal charge and depth. Supply opening retains its evaluation and materialization cost.
- A cell's implementation frame is not a language invocation, and bookkeeping allocation is not a language step.
- Charges go to the run's one monotone budget. Optimization cannot spend on undemanded computations, reset a budget or turn a reached limit into another success.
- Address transport shares or normalizes iteratively and builds no recursive thunk chains.

**Qualifications**
- *C#-only:* overlapping flows, atomic publication, cancellation, host exceptions, resource terminality and all charges. Lean models the serial protocol, including `DemandCycle` on re-entry, and no host scheduling.

`A = A.Algorithm` / `A` is `DemandCycle`, while `F(n) = if(n == 0, 0, F(n - 1))` / `F(5)` is `0`.

### NEED-10 — Retained ownership and separate property cache

- A cell retains the caller's resolved lexical bindings, owning activation, run context, hosts, random stream and cancellation token for as long as it is reachable. Delayed evaluation does not re-resolve names in a receiver's later stack. Ownership, accessibility and open-provider identity are unchanged.
- Cell memoization and the per-run resolved property-binding cache are distinct domains. A demanded bare property uses that cache. A demanded explicit `Z()` remains a fresh call, once inside its supplied cell. Two independent supplied `Z()` computations remain independent executions. An unused property expression performs no access.
- A demanded explicit `Z()` is a qualifying zero-supply invocation of `Z`'s binding. When that entry is empty and the call owns publication, its success establishes the entry a later bare `Z` reuses (PROP-06, PROP-09). An established entry is never replaced. A completed cell is never re-executed, so it never publishes twice.
- An invocation through a CALLABLE projection names the binding of the cell's written source in its own caller context. No cell is completed, demanded or projected to find the binding.
- Sticky cell failure does not make property failures globally cached.
- No returned-algorithm result and no cross-run cell API exist. The call reference a `meta` parameter binds is no returned algorithm: it holds an invocation plan, has no CALLABLE identity, is executed only by `R.Invoke()`, and is run-scoped like its argument view (CR-4, CR-6).
- `R.Algorithm` adds no result kind. It is a CALLABLE channel of a written expression, the captured callee cell, reached through a supplied `.Algorithm` link or a callee position, and read bare it is that callee's ordinary VALUE. The callee cell keeps the captured call's lexical owner, activation and run.
- Nothing that carries a VALUE carries callable identity. A list, sequence, selection, `if`, call result or formula containing or computed from `R.Algorithm` is ordinary data. The lone row `A = R.Algorithm` is a runtime reference, not a computed value (FWD-04).

```katlang
Z = tick()
Show(x) = x, x
Ignore(x) = 0
Ignore(Z), Show(Z()), Z, Show(Z()), Z
```
⇒ `S[0, S[1, 1], 1, S[2, 2], 1]`

A supplied computation reads its names where it was written:

```katlang
v = 1
F(x) = { v = 100
x + v }
F(v)
```
⇒ `101`

## REF — Call references: `meta`, `Invoke`, `Arguments`, `Algorithm`

A `meta` parameter captures the written invocation supplied to it, unevaluated, as a **call reference**: an opaque run-scoped value (VAL-01) whose identity is one **invocation plan**, the supplied cell itself (NEED-01). A plan has one **route**, which says what its written form invokes (CR-2), one sticky **supply** of argument cells (CR-9) and at most one **callee cell** (CR-13). Three intrinsics observe it: `R.Invoke()` executes it afresh, `R.Arguments` is a lazy view of its supply, and `R.Algorithm` projects its callee. Capture, transport and comparison of a reference run nothing. The examples use `Capture(meta op) = op`, which hands the reference to the caller.

### CR-1 — META is a binder capability

- `meta name` is a contextual modifier: `meta` followed on the same line by another pattern item. `F(meta)` and `meta = 3` keep the ordinary name.
- It may modify only a plain, fixed parameter name written once at the top level of an explicitly written ordinary parameter list.
- Collecting, nested, structural, literal, repeated and clause-family positions are `InvalidMetaParameter`. A host-built tree that places it there is refused before evaluation with `IllegalInEval`.
- An inferred parameter has no `meta` spelling.
- Formula lifting gives a caller an ordinary binding, which transports its cell into the callee's `meta` slot. Bare forwarding transports it the same way. A callable alias keeps its target's modes.

```katlang
F(meta) = meta
meta = 3
Run(meta op) = op.Invoke()
Inc(x) = x + 1
Alias = Run
Lifted = Run + 0
Forward(op) = Run
F(4), meta, Alias(Inc(1)), Lifted(Inc(2)), Forward(Inc(3))
```
⇒ `S[4, 3, 2, 3, 4]`

`F(meta *xs) = 0` / `1` is `InvalidMetaParameter`, `F((meta x, y)) = 0` / `1` is `InvalidMetaParameter`, and `F(meta x, x) = 0` / `1` is `InvalidMetaParameter`.

### CR-2 — Written-order, inert capture

- After the ordinary cardinality gate, the one binder reaches a `meta` capture in written traversal order (NEED-04), so an earlier inspecting pattern's failure wins.
- Capture reifies the supplied cell: a pure read of its suspension, then one fresh ready cell holding the reference. Nothing executes: no target, no argument VALUE, no supply preparation, no spread, no route resolution. The original cell is not written.
- The capturable cells are the **written invocations**: a call whose callee is a name, a parameter or an argumentless dot path (every call the parser produces), and an argument-bearing dot edge `t.N(args)`, an explicitly empty list included. The decision is syntactic, total and evaluation-free, and it never asks what the form invokes.
- Every other cell is refused with `NotAnAlgorithm`: a value, a property read, a bare callable, an argumentless dot edge (`Box.G`, `5.Inc`), a computed or host-built callee, an existing reference, a collector. Nothing is evaluated to discover a call, and there is no implicit provenance.
- So `Box.Step(0)`, `Math.Abs(-3)`, `(Box.Step)(0)`, `op.Algorithm(op.Arguments*)`, `5.Add(1)` and `Box.V()` are captured, while `Box.Step`, `5.Inc` and a property read `Start` are not. Member or property access and explicit invocation stay distinct, and no cell changes kind by runtime lookup.
- A refusal at a binding site names the `meta` parameter being bound, a builtin's included, and for a forwarded reference the failing inner binding, never the outer capture. Its position (C#-only metadata) is the argument as written at that call, so a forwarded parameter read is its own occurrence. Only that refusal gains the frame: a later route-dependent refusal, cancellation, a resource limit and every other error pass unchanged.

**The route**
- Each plan has one route, decided by its first route-dependent operation and then retained: VALUE, `R.Invoke()`, reading the argument supply, `.Algorithm`, or a loop's setup. Capture, reference identity, obtaining or comparing the argument view and an empty selection need no route.
- The route is the ordinary decision for the written form, through the one dot decision ordinary evaluation takes (DOT-01): member first whatever the spelling, accessibility after selection, a branch-only member its error. A route failure is the plan's failure with its kind, span and context, never absence.
- **Call route:** a written call, including `(t.Algorithm)(args)` when `t` declares `Algorithm`. A name, parameter or path call has this route by its source, with nothing classified.
- **Member route:** `t.N(args)` selecting a declared member. The callee is the argumentless path `t.N` and the supply is `args`.
- **`.Algorithm` route:** `t.Algorithm(args)` or `(t.Algorithm)(args)` on a structural miss. The callee is the link `t.Algorithm` (CR-15).
- **Extension route:** any other miss, the call `F(t, args)` (DOT-03). The receiver is the first supplied argument.
- **Intrinsic route:** `t.string(…)`, `t.Invoke(…)` or `t.Arguments(…)` on a miss. Capture is inert and legal, and the plan's VALUE is the intrinsic's ordinary evaluation. It has no callable, so every route-dependent reference operation is `NotAnAlgorithm` at that operation: `R.Invoke()`, `R.Algorithm`, `R.Algorithm(args)`, reading the supply of `R.Arguments`, and a loop over it. No intrinsic name is refused earlier than an equivalent runtime-selected intrinsic.
- The plan's original VALUE is the ordinary evaluation of the written form along its route, with the same frames, spans, charges and error kinds, over the plan's one supply.

```katlang
Ignore(meta op) = 0
Add(a, b) = a + b
Box = { public G(x) = x * 2 }
Ignore(tick()), Ignore(Box.G(1 / 0)), Ignore(5.Add(1)), Ignore(5.string()), tick()
```
⇒ `S[0, 0, 0, 0, 1]`

```katlang
Ignore(meta op) = 0
Step(x) = x
Start = Step(0)
Ignore(Start)
```
⇒ `NotAnAlgorithm`

`F((a, b), meta op) = 0` / `Inc(x) = x` / `F(1 / 0, Inc(1))` is `DivisionByZero`, while `F(meta op, (a, b)) = 0` / `F(5, 1 / 0)` is `NotAnAlgorithm`.

### CR-3 — Identity

- A reference is its plan: the supplied cell. Any number of plain forwarding hops reach the original cell, so repeated `meta` observations of one cell yield one reference, before or after its VALUE completed, successfully or not.
- Distinct written calls are distinct references however alike they are spelled, for every invocation form. A rebuilt `op.Algorithm(op.Arguments*)` is a new plan, distinct from `op`'s, whose supply holds `op`'s original argument cells (CR-11).
- `==` compares plan identity. There is no ordering.
- A reference is generative: each evaluation of a written call cell is a new plan. So its identity follows the property cache (NEED-10): a bare property `R = Capture(F(1))` read twice is one reference, while the explicit call `R()` evaluates the body again and captures a new cell.

```katlang
Capture(meta op) = op
Two(meta a, meta b) = a == b
Hop(x) = Capture(x)
Both(x) = x + 0, Capture(x) == Hop(x)
F(x) = x
R = Capture(F(1))
Two(F(1), F(1)), Both(F(1)), R == R, R == R()
```
⇒ `S[false, S[1, true], true, false]`

### CR-4 — The reference value

- A reference is a ready, opaque, transportable value. Properties, parameters, lists, sequences, selection and `if` carry it.
- It has no CALLABLE identity, no members, and no number, Boolean or text view. Calling it is `NotAnAlgorithm`, and executing it is the explicit `R.Invoke()`, never projection.
- Every inspecting consumer (operators, `if` conditions, numeric aggregates, `.string`) rejects it with its ordinary kind verdict.
- A `meta` capture of the ready cell that holds a reference refuses: there is no value-to-reference bridge.

```katlang
Capture(meta op) = op
Inc(x) = x + 1
R = Capture(Inc(1))
[R][0] == R, if(true, R, 0) == R, (R, 2)[0] == R, count([R, R]), R == 1
```
⇒ `S[true, true, true, 2, false]`

`Capture(meta op) = op` / `Inc(x) = x + 1` / `R = Capture(Inc(1))` / `R + 1` is `TypeMismatch`.

```katlang
Twice(meta a) = Again(a)
Again(meta b) = b.Invoke()
Inc(x) = x + 1
Twice(Inc(1))
```
⇒ `NotAnAlgorithm`

### CR-5 — `R.Invoke()`

- On a structural miss an edge spelled `Invoke` is the call-reference intrinsic. A declared member `Invoke` wins. A lexical `Invoke` is never consulted by dot syntax, the plain call `Invoke(x)` is unaffected, and the front end never infers `Invoke` as an implicit parameter.
- The argument list is a route fact, checked before the receiver is demanded. Bare `R.Invoke` is `IllegalInEval` and never executes. A written list forms its ordinary supply first and must supply nothing, so `R.Invoke(8)` fails with `ArityMismatch`: there are no replacement arguments.
- The receiver is read as `.string` reads it (DOT-08) and must be a reference of this run. Any other value, an argument view included, is `TypeMismatch`.
- Invocation is a fresh execution along the plan's route, with the ordinary call's phases: the callee resolved in the captured caller context, never the invoking site, alias normalization, clause families redispatched, and normal charges, frames and cancellation.
- It runs over the plan's one supply, prepared at most once and sticky, so spreads run once and the same memoized argument cells are bound.
- It never reads or writes the original cell's VALUE and is never a property read.

```katlang
Capture(meta op) = op
F(x) = x + tick()
H(x) = x, Capture(x).Invoke(), x
R = Capture(F(tick()))
R.Invoke(), R.Invoke(), H(F(10))
```
⇒ `S[3, 4, S[14, 15, 14]]`

`Invoke(x) = x + 1` / `5.Invoke()` is `TypeMismatch`, `Invoke(x) = x + 1` / `Invoke(2)` is `3`, and `(1 / 0).Invoke(8)` is `ArityMismatch`.

### CR-6 — Run scope

- A reference never leaves its run. A run result containing one at any depth and a host-operation argument are `TypeMismatch`, and `.string` rejects one as a non-number (DOT-08). Ordinary internal containers stay valid, and no reference display syntax exists.
- A host cannot construct a reference.

**Qualifications**
- *C#-only:* one ownership check guards every operation that decodes a reference, before any plan work and again after a successful invocation. A foreign run's reference is `IllegalInEval`. A run that has exited on success, failure or exception cannot execute again, and a cancelled, resource-terminal or required-source-failed run cannot be revived. A host operation that returns a reference breaks the host contract and fails loud. Serial Lean has one run per state and no cross-run channel.

```katlang
Capture(meta op) = op
Inc(x) = x + 1
[Capture(Inc(1))]
```
⇒ `TypeMismatch`

```katlang
Capture(meta op) = op
Inc(x) = x + 1
R = Capture(Inc(1))
[R, 2][1], (R, 1)[1]
```
⇒ `S[2, 1]`

### CR-7 — Plan retention is decided once and is unobservable

*C#-only by design.*

- Whether a run retains invocation plans is decided once, before any supplied cell exists, from the whole admitted program, and never changes during the run. A run that can reach a `meta` capture, a `meta` builtin or a deferred module region retains plans.
- The decision is an implementation gate. It changes no outcome, effect or charge. A `meta` binder reached in a run that retains no plans is an internal failure, never a language refusal.

### CR-8 — The view

- On a structural miss an edge spelled `Arguments` is the argument-view intrinsic. A declared member `Arguments` wins. A lexical `Arguments` is never consulted by dot syntax, the plain call `Arguments(x)` is unaffected, and the front end never infers `Arguments` as an implicit parameter.
- It is a property: any written argument list, `R.Arguments()` included, is `IllegalInEval` before anything is formed or demanded.
- The receiver is read as `Invoke` reads it and must be a reference of this run. Any other value, an argument view included, is `TypeMismatch`.
- Obtaining the view is inert: no target or route resolution, supply preparation, argument VALUE, allocation of cells or cloning. It yields the reference's one read-only view, whether or not the original VALUE completed.
- A view equals only itself, never its reference, and is never invocable.

```katlang
Capture(meta op) = op
F(a, b) = a + b
R = Capture(F(1 / 0, (1 / 0)*))
R.Arguments == R.Arguments, R == R.Arguments
```
⇒ `S[true, false]`

### CR-9 — The view's supply

- Every view operation that reads the supply reads the plan's one sticky supply: the recorded preparation, or exactly one formation through the ordinary former in the plan's caller context, shared with the original VALUE and every `Invoke()`. The target is never dispatched.
- Which bundle the supply is depends on the plan's route, so reading the supply first establishes the route. That is identity resolution only. Through a runtime-projection receiver it performs that projection's existing single-flight receiver demand once, with its effects and failures at that point, before `repeat`'s count. Establishing the route never authorizes executing the captured target.
- An extension's receiver is supplied: `5.Add(1)` supplies `5, 1`. A member's receiver selects the member and is not supplied. An intrinsic route has no supply (CR-2).
- Preparation demands no ordinary argument VALUE. Only an explicit arbitrary spread among the arguments runs during it, once for every observer, and its failure is sticky.

```katlang
Capture(meta op) = op
Add(a, b) = a + b
Box = { public G(x) = x * 2 }
E = Capture(5.Add(1))
M = Capture(Box.G(2))
E.Arguments.count, E.Arguments[0], E.Invoke(), M.Arguments.count, M.Invoke()
```
⇒ `S[2, 5, 6, 1, 4]`

### CR-10 — Count and selection

- `R.Arguments.count` and `count(R.Arguments)` are the number of effective supplied cells, explicit spreads and an extension's receiver included. They demand no cell.
- Postfix selection over a view keeps ordinary selection order and validation. An empty selection reads nothing: no supply, no route. Each selector is demanded and validated before the supply is read: a non-number is `TypeMismatch`, and a negative or non-whole number is `BadIndex`. A valid index then reads the supply, `BadIndex` past its end, and demands only the selected cell, whose VALUE is selected whole.
- Repeated selection reuses the cell's memoized outcome, success or failure.
- `first` and `last` select the first and last cell likewise. On an empty supply they are the ordinary empty-collection selection failure, `BadIndex`.
- Every other collection builtin given a view as its whole collection, `atoms` included, is `TypeMismatch`. It never reads the view as a one-element collection or materializes it. A list containing a view is an ordinary collection.

```katlang
Capture(meta op) = op
F(*x) = 0
R = Capture(F(tick(), 1 / 0, (2, 3)*))
R.Arguments.count, R.Arguments[0], R.Arguments[0], first(R.Arguments), R.Arguments[], last(R.Arguments)
```
⇒ `S[4, 1, 1, 1, S[], 3]`

```katlang
Capture(meta op) = op
F(*x) = 0
R = Capture(F((1 / 0)*))
R.Arguments[-1]
```
⇒ `BadIndex`

```katlang
Capture(meta op) = op
F(a, b) = 0
R = Capture(F(1, 2))
sum(R.Arguments)
```
⇒ `TypeMismatch`

### CR-11 — The cell-preserving spread

- In an argument or selector supply, a spread slot whose last star opens a view (`F(R.Arguments*)`, `F((R.Arguments)*)`, `X[R.Arguments*]`) transports the plan's original cells, in order, each with its own written source. There is no copy, ready wrapper, second preparation or demand.
- So undemanded arguments stay suspended, callable arguments stay callable, and destination and original share memoized VALUEs.
- A star that would open a view into values is `TypeMismatch`: any spread in a value position (`[R.Arguments*]`, `(R.Arguments*, 1)`, a spread row) and an inner star of a stacked spread (`F(R.Arguments**)`). Every other spread is unchanged.

```katlang
Capture(meta op) = op
F(a, b) = 0
Use(x, f) = f(1) + x
G(a) = a, a
Inc(z) = z + 1
R = Capture(F(5, Inc))
T = Capture(G(tick()))
Use(R.Arguments*), G(T.Arguments*), T.Arguments[0], tick()
```
⇒ `S[7, S[1, 1], 1, 2]`

```katlang
Capture(meta op) = op
F(a, b) = 0
R = Capture(F(1, 2))
[R.Arguments*]
```
⇒ `TypeMismatch`

### CR-12 — Boundaries

*Open: whether assignment deconstruction treats an argument view as one opaque value or refuses it (Q-84). Today the view is one item.*

- A view obeys CR-4 and CR-6 unchanged. It is opaque and has no text: run results and host-operation arguments and returns refuse it at any depth, and `.string` rejects it as a non-number.

**Qualifications**
- *C#-only:* every view operation (obtaining, preparing, counting, selecting, spreading) passes the run-ownership check before plan work and again after it, so foreign, ended, cancelled, resource-terminal and required-source-failed runs are refused.

```katlang
Capture(meta op) = op
F(a, b) = 0
R = Capture(F(1, 2))
[1, [R.Arguments]]
```
⇒ `TypeMismatch`

### CR-13 — The callee cell

- Every invocation plan has at most one canonical callee cell: its route's callee, supplied in the plan's captured caller context through the ordinary supply-cell construction.
- The callee is the written callee of a call route, the argumentless member path of a member route, the link `t.Algorithm` of the `.Algorithm` route, and the lexical fallback of an extension route. An intrinsic route has none.
- A parameter callee is that parameter's existing cell (NEED-01), and a name callee an identity-only cell over the name.
- The cell is established lazily, by the first observation that needs it, after the plan's route. Once the route is established, establishing the cell evaluates, prepares and demands nothing. Establishing the route itself may demand a runtime-projection receiver (CR-9).
- Exactly one cell is retained, and every observation (CALLABLE projection, bare VALUE, fresh invocation) uses it.
- The callee cell belongs to the plan's run. It is available whether or not the plan's own VALUE completed, and using it never reads or writes that VALUE.

**Qualifications**
- *C#-only:* concurrent establishment may construct candidates that are discarded unused.

```katlang
Capture(meta op) = op
F(y) = y + tick()
H(x) = x, Capture(x).Algorithm(100), x
H(F(10))
```
⇒ `S[11, 102, 11]`

`Capture(meta op) = op` / `Add(a, b) = a + b` / `Apply(f, x) = f(x)` / `R = Capture(5.Add(1))` / `Apply(R.Algorithm, 7)` is `ArityMismatch`.

### CR-14 — The `.Algorithm` intrinsic

- On a structural miss an edge spelled `Algorithm` reads its receiver exactly as `Invoke` and `Arguments` read theirs and requires a call reference of the current run. A number, text, list, argument view or ordinary computed value is `TypeMismatch`. A foreign or ended run's reference is `IllegalInEval`.
- It denotes the decoded plan's callee cell, in three uses.
- **CALLABLE use.** A supplied or forwarded argument, a callback, a loop step or a callee (`(R.Algorithm)(x)`) uses the callee cell's CALLABLE.
- **Bare read.** `R.Algorithm` is the callee cell's VALUE: the captured callee read as an ordinary value in its captured context, with its ordinary zero-supply demand, property cache, computation or arity rejection.
- **Fresh call.** `R.Algorithm(args)` is a fresh ordinary call of the callee cell's CALLABLE with exactly `args`. `R.Algorithm()` supplies nothing and is never `R.Invoke()`. A callee with no CALLABLE identity is `NotAnAlgorithm`.
- A family is redispatched by the new supply, and a nested callee keeps its owner's activation, never the consumer's names. No builtin or optimizer treats a projected callee specially.
- A declared member named `Algorithm` wins in every position. Dot syntax never consults a lexical `Algorithm`, the plain call `Algorithm(x)` is unaffected, and the front end never infers `Algorithm` as an implicit parameter.
- Member access does not navigate through the intrinsic edge: `R.Algorithm.n` is the extension call `n(R.Algorithm)`, and `R.Algorithm.n(args)` the extension call `n(R.Algorithm, args)`.
- `R.Algorithm` and `R.Arguments` are independent. Obtaining `R.Algorithm` never forms the plan's supply, obtaining `R.Arguments` never resolves the callee, preparing `R.Arguments*` forms the supply once, each argument VALUE is demanded only where used, and invoking the target is a separate step.
- So `R.Algorithm(R.Arguments*)` calls the captured callee afresh over the original argument cells, shared with `R.Invoke()`, and reconstructs the captured invocation for every route.
- A written `R.Algorithm(args)` or `(R.Algorithm)(args)` is itself a written invocation. `meta` captures it as a new plan on the `.Algorithm` route, so `R.Algorithm(R.Arguments*).while` loops the captured step from its original arguments. Its original VALUE keeps this intrinsic's semantics and accounting.
- `A = R.Algorithm` is a runtime reference to the captured callee, whatever its arity (FWD-04): `A(9)` is the fresh call `R.Algorithm(9)`, `A()` the fresh `R.Algorithm()`, `Apply(A, 9)` passes the callee, and bare `A` is the link's VALUE.

```katlang
Capture(meta op) = op
F(0) = 10
F(n) = n * 2
Apply(f, x) = f(x)
R = Capture(F(0))
Apply(R.Algorithm, 3), (R.Algorithm)(4), R.Algorithm(5), R.Algorithm(R.Arguments*), R.Invoke()
```
⇒ `S[6, 8, 10, 10, 10]`

```katlang
Capture(meta op) = op
Z = tick()
R = Capture(Z())
R.Algorithm, Z, R.Algorithm(), R.Algorithm(), R.Algorithm
```
⇒ `S[1, 1, 2, 3, 1]`

`Capture(meta op) = op` / `Square(x) = x * x` / `R = Capture(Square(5))` / `R.Algorithm` is `ArityMismatch`, and `Algorithm(x) = x + 1` / `5.Algorithm` is `TypeMismatch`.

```katlang
Capture(meta op) = op
Box = { public N = 1
7 }
N(x) = 9
R = Capture(Box())
R.Algorithm, R.Algorithm.N
```
⇒ `S[7, 9]`

### CR-15 — The link

- A supplied `X.Algorithm` is one link cell whose receiver `X` is one receiver cell, established lazily and retained exactly as in CR-13, shared by the link's VALUE and CALLABLE.
- Each channel demands that one receiver VALUE, at most once per written slot with its effects and failures shared, decodes the same reference and delegates to the same callee cell's corresponding channel.
- The link's VALUE is the callee's VALUE, passed through as the callee reports it.
- The link's CALLABLE is a runtime projection, a node of the run's wait-for graph under the single flight of NEED-09. It never demands the link's own VALUE or the callee cell's VALUE.
- A plan on the `.Algorithm` route has such a link as its callee cell. Its one receiver cell is demanded at most once for the plan and is shared by the plan's VALUE, every `Invoke()`, its `.Algorithm` and a loop over it. Its first demand is the ordinary invocation receiver read, and a parameter receiver is that parameter's own cell.
- Each ordinary invocation still takes the ordinary parameter receiver read, its checkpoint and error provenance included. Transporting the cell never replaces that read with an uncharged raw demand.
- A different written occurrence is a different plan with its own receiver.

```katlang
Capture(meta op) = op
Inc(x) = x + 1
Mk(k) = tick(), Capture(Inc(k))
Twice(f) = f(1), f(2)
Twice(Mk(0)[1].Algorithm), tick()
```
⇒ `S[S[2, 3], 2]`

### CR-16 — What obtaining and using `R.Algorithm` does (qualified inertia)

- Obtaining it evaluates the receiver through the receiver's ordinary VALUE route, once per link, with that computation's effects, failures, dependencies and source admission, and decodes the reference through the ordinary ownership check.
- CALLABLE use then projects the callee cell's identity. This is identity-only resolution in the captured context, except that a callee route through another runtime projection demands that projection's own receiver, each such cell at most once.
- Bare VALUE use is the callee cell's VALUE, and fresh invocation is an ordinary call.
- Projection itself never executes the plan's captured invocation, prepares or reads its original argument supply, opens its original spreads, demands an argument cell as an argument, reads or writes the plan owner's VALUE, or changes the reference.
- A failure of receiver VALUE, decode (ownership included) or a projection on the callee route is the projection's failure (NEED-06). A completed link publishes it as its CALLABLE outcome with its original kind, span and context, and a parameter-rooted path over it propagates it.
- A re-entry is NEED-09's flow-local `DemandCycle`, never a host stack overflow or an unproductive async retry.

```katlang
Capture(meta op) = op
Apply(f, x) = f(x)
G(o) = 7
Bad = 1 / 0
Use(p) = Apply(p.G, 0)
Use(Bad.Algorithm)
```
⇒ `DivisionByZero`

```katlang
Capture(meta op) = op
Apply(f, x) = f(x)
G(o) = 7
Use(p) = Apply(p.G, 0)
Use(5)
```
⇒ `NotAnAlgorithm`

```katlang
Capture(meta op) = op
Hold(g) = Capture(g(0))
R = Hold(R.Algorithm)
R.Algorithm(1)
```
⇒ `DemandCycle`

### CR-17 — A builtin may declare META parameters

- A builtin's one signature may declare `meta` parameters. Such a builtin is an ordinary fixed-arity callable: after ordinary supply formation and its arity gate it binds its supplied cells through the one inspecting binder over that signature, exactly as a user algorithm does, and its native arm runs over the bound environment. CR-2's written-order inert capture and refusal and the run-continuation check are inherited.
- Every route to a builtin reaches it through the one builtin dispatch, with supplied cells: a direct or dot-fallback call, an alias, a higher-order parameter, a loop step, `Invoke()`. A callback's element cells are ready data, which `meta` refuses.
- A `meta` position has the CALLABLE lifting role: it transports its cell.
- `while(meta step)` and `repeat(meta step, count)` are the two META builtins. The step is the captured plan's canonical callee cell (CR-13) and the initial state its one sticky supply (CR-9). The captured call itself is never dispatched. `repeat` prepares that supply before it demands its count. An empty supply is the ordinary zero-slot state. The loop's own laws are LOOP.
- The captured step may be any written invocation: a member or module call, a grouped member callee, an extension call, a rebuilt projection. Its callee is the route's callee cell and its initial state the route's effective supply.
- `W(step) = while(step)` forwards the supplied call. `W(meta step) = while(step)` hands on a reference, which the inner capture refuses (CR-4).

```katlang
Step(x) = x + 1, x < 3
Box = { public S(x) = x + 1, x < 3 }
Loop(meta op) = op.Algorithm(op.Arguments*).while
W = while
Lifted = while + 0
Step(0).while, W(Step(0)), Lifted(Step(0)), Box.S(0).while, Math.Abs(-3).repeat(2), Step(0).Loop
```
⇒ `S[3, 3, 3, 3, 3, 3]`

```katlang
Ten(x) = x * 10
repeat(Ten(tick()*), tick())
```
⇒ `100`

`Step(x) = x + 1, x < 3` / `Start = Step(0)` / `Start.while` is `NotAnAlgorithm`, and `Z(*xs) = xs.count > 5` / `Z().while` is `S[]`.

## VAR — Collecting bindings, deconstruction, and forwarding

A collecting binding (`*name`) is the one place where KatLang turns a variable number of supplied items into a value: it collects exactly the items allocated to it into one exact list, and it never opens or inspects them. A **cell** is one supplied computation (NEED-01), with its VALUE computation and any CALLABLE identity. In this family **capture** means only SUP-06's supply-to-value operation, and a parameter pattern is called a parameter. A **lone reference body** is a non-root body whose one written row is a bare name or an argumentless dot path: FWD-02 decides it under a closed parameter list, FWD-03 and FWD-04 otherwise. CALL owns the item supply, SUP spread, DOT the dot receiver, PAT nested patterns and failure order, HO the callback law, and LOOP loop state.

### VAR-01 — A collecting binding collects exactly its allocated items as one exact list

- A collecting binding `*name` binds `name` to one list value. The operation is `collect : Supply -> ListValue`.
- The list's elements are exactly the items the binder allocated to that binding, in supply order, each unchanged: zero items give `[]`; one item gives `[item]`, never erased to `item`; several items give `[a, b, …]`.
- The collected value always has emitted count 1, `[]` included.
- A collector never opens, flattens, normalizes or inspects an item. A sequence, a list, `()` or `[]` that arrives as one item becomes one element.
- A collector counts supplied arguments, while `x.count` on a fixed parameter counts one value's elements.
- `F(A)` and `F(A*)` coincide only when `A` is not a sequence or list value.
- How the items are produced is owned elsewhere. CALL: each non-spread slot supplies exactly one item. SUP: `v*` opens one boundary, and its items are never reopened.

**Qualifications**
- Two explicit openers act before allocation and are not collector behaviour: a nested pattern `F((*xs))` opens its one slot's value first (PAT-08), and assignment deconstruction opens its right-hand side first (VAR-05).
- Collection builtins are not collectors. They are fixed-arity, with one `collection` parameter read through a one-level view after binding (COLL): `count((10, 7))` is `2`, while `Cnt(*xs) = xs.count` / `Cnt((10, 7))` is `1`.
- After binding, the collected value is an ordinary exact list (SEQ: `[7] != 7`, `[] != ()`).
- Callbacks supply each element as one argument (HO-02): `Coll(*xs) = xs` / `[(1, 2)].map(Coll)` is `[[(1, 2)]]`.

```katlang
Coll(*xs) = xs
Cnt(*xs) = xs.count
CntValue(x) = x.count
Coll(), Coll(7), Coll(()), Coll((1, 2)), Coll([1, 2]), Coll((1, 2)*), Cnt((10, 7)), Cnt((10, 7)*), CntValue((10, 7))
```
⇒ `S[L[], L[7], L[S[]], L[S[1, 2]], L[L[1, 2]], L[1, 2], 1, 2, 2]`

### VAR-02 — One collector per pattern level; fixed positions bind from both ends first and the collector takes the exact middle

*Open: whether refusing collecting bindings in clause families is permanent (Q-47).*

- A collecting binding may appear in three positions only: an ordinary explicit parameter list; a nested structural parameter pattern, sequence `(…)` or list `[…]` (`F([h, *t])`, `F((a, [b, *c]))`); and a deconstruction head.
- It is never legal in a clause family, multi-clause or literal-headed. It is never inferred from an unresolved name.
- Each pattern level (one list, or the item list of one nested group) contains at most one collecting binding, and a collecting binding's name is never repeated elsewhere in the parameter pattern list. A violation of either limit is the front-end error `InvalidCollectingBinding`.
- **Allocation.** Take a level with `n` top-level patterns and a collector at index `i`. The level accepts at least `n − 1` supplied items; without a collector it accepts exactly `n`. The first `i` items bind the prefix patterns, the last `n − i − 1` items bind the suffix patterns, and the collector collects the remaining middle exactly (VAR-01), possibly zero items.
- **What a slot is.** Every top-level pattern, a nested group included, consumes exactly one supplied item. A fixed position binds its item unchanged and never opens it. Arity is counted in supplied items, never in a value's elements.
- **Inferred signatures are held to the rules of written ones.** A signature the front end infers must be one a programmer could write. One validator decides every signature: no one-item sequence pattern (PAT-06), at most one collecting parameter per pattern level (this rule), and no repeated name that includes a collector (a repeated fixed name stays a constraint, PAT-09).
  - It applies to a written head and to an inferred one. Before evaluation it applies all three rules to every host-built user signature anywhere in the tree, a host-built parent scope's open targets and properties included, where each violation is `IllegalInEval`. C# alone also refuses a host-built collecting clause binder, because Lean's clause binders have no kind.
  - Validity belongs to the settled signature (PAR-08). An intermediate round of a recursive inference refuses nothing; a violation the settled state keeps is the definition's error.
  - A lift that would compose an invalid signature is the definition's front-end `InvalidCollectingBinding`, reported at elaboration and naming both collectors and the callees that need them, whether or not the definition is ever called, on every route and with no host exception.
  - A collecting name shared by two callees is one binding. Collectors in their own groups stay legal, and a collector-only callee is never lifted (PAR-07). The loops have no collector, so `K = while + repeat` is `K(step, count)`, sharing `step` by name.

**Qualifications**
- The minimum supply is also the rule for zero-argument value demand (CALL-05): `Only(*xs) = xs` / `Only, Only()` is `S[L[], L[]]`, while `Head(x, *rest) = x` / `Head` is `ArityMismatch`.
- Allocation inside a nested group happens after that group's value is opened (PAT-08): `F((*a), *b) = a, b` / `F((1, 2), 3, 4)` gives `([1, 2], [3, 4])`.
- When a binding fails and a name repeats across the collector, which error is reported first is owned by PAT-10 (the NEED-04 inspection order).
- Loop-state binding uses the same one binder and the same arithmetic (LOOP); only its cardinality failure is reported as the loop-state `ArityMismatch`.
- A callback element is one argument (HO-02), so `[(1, 2, 3)].map(F)` with `F(first, *rest)` binds `rest = []`: `F(first, *rest) = rest` / `[(1, 2, 3)].map(F)` is `[[]]`.
- `open` refuses a collecting-only provider, although it is value-demandable (MOD-04).

```katlang
F(x, *middle, z) = middle
G(x, *rest) = x, rest
F(0, 9), F(0, 1, 2), F(0, (1, 2), 3, 4), G((1, 2))
```
⇒ `S[L[], L[1], L[S[1, 2], 3], S[S[1, 2], L[]]]`

`F(x, *middle, z) = middle` / `F((1, 2))` is `ArityMismatch`. `F(*a, *b) = a` / `1` is `InvalidCollectingBinding`, and so are `P(x, *x) = x` / `1` and `C(0) = 0` / `C(*xs) = xs` / `1`.

`C1(a, *p) = a` / `C2(b, *q) = b` / `K = C1 + C2` / `1` is `InvalidCollectingBinding`, whether or not `K` is called. `C1(a, *p) = a` / `C3(b, *p) = b` / `K = C1 + C3` / `K(1, 2, 3)` is `4`: the signature is `K(a, *p, b)`.

### VAR-03 — A collecting binding preserves its cells for re-spread, selective reads demand only the needed cells, and a whole read demands every cell

*Resolved (audit finding A-2, owner decision November 2026): a transparent reference to a retained collector cell is a known slice, written as a name or as an accessible member path. With `Coll(*ys) = 0`, `F(*xs) = { A = xs` / `Coll(A*) }` makes `F(1 / 0)` `0`, as does `Box = { public A = xs` / `0 }` with `Coll(Box.A*)`, in C# and Lean alike. This changed the earlier behavior of both, where it was `DivisionByZero`. `Pass(A)` supplies one argument. A later `v*` inside `Pass(v)` can still reach that slice (NEED-07).*

- A collecting binding `*name` at the top level of a parameter list binds an exact slice of the supplied argument cells (NEED-01): the cells VAR-02 allocates to it, in supply order.
- A nested structural collector (`F((x, *r))`, `F((*xs))`, `F([*xs])`) and a deconstruction collector (`x, *r = …`) instead collect elements of a value that their pattern (NEED-04) or the unpacking receiver (VAR-05) has demanded: a sequence's elements are values, and a list's are its positions, collected as VALUE-only computations that run when read (SEQ-02). A collector of those positions retains their slice. Each opened child supplies only its value (NEED-04): `P((x, *r)) = x` / `K(z) = P((1, 1 / z))` / `K(0)` is `DivisionByZero`, while `P(x, *r) = x` / `K(z) = P(1, 1 / z)` / `K(0)` is `1`, and `P([a, *rest]) = rest.count` / `P([1, 1 / 0, 1 / 0])` is `2`.
- Collecting and re-spreading a retained slice demand no element. A selective observer demands the cells it needs (NEED-07).
- **Collecting.** Binding the slice demands no element's VALUE and projects no element's CALLABLE identity. An unused collected argument is never evaluated, whether it is a callable that requires arguments, a failing calculation or an output-less block.
- **Re-spreading a known slice.** `name*`, where the parameter binding retains a collector cell (of the current body or an enclosing one, or transported whole through a fixed parameter), transfers the original cells into the new supply without forcing them (NEED-07, NEED-08). A name that reaches such a parameter through transparent references only (`A = xs`, `B = A`, FWD-03) is the same known slice.
  - Each cell keeps the capabilities it was supplied with: its VALUE computation and, where it has one, its CALLABLE identity. A callable that flows through a collector and is re-spread can be invoked again, every invocation is fresh (NEED-06), and a later VALUE demand runs the original computation once (NEED-02).
  - Bare forwarding of a collecting source into a collecting destination is the same transfer (FWD-02).
  - This transfer belongs to supply formation: a call's arguments, a loop's initial state included. An output row `name*`, a loop step's row included (LOOP-03), is result construction: it demands each element's VALUE, left to right with the other rows, and its items carry no CALLABLE identity (NEED-06, LOOP-02).
- **Reading the collector as a value.** An ordinary read of `name` materializes one exact list (VAR-01): elements are demanded left to right by their own VALUE contracts (NEED-07), success requires every element, and the read stops at and reports the first failure. A callable element gives its own zero-argument demand verdict (CALL-05), the same one it gives when value-demanded through a fixed parameter; there is no collector-specific error.
- **No capability is invented.** The collector itself is one collection-valued computation with no CALLABLE identity: invoking it unspread is `NotAnAlgorithm`. A value, a capture, or a computed or selected result that passes through a collector stays value-only (NEED-06).
- **Only a known slice transfers cells.** Any other spread operand (a list literal, a call result, a property that is no such transparent reference, a selection, a member path that does not reach a retained collector by transparent references, a structural carrier `A = { xs }`, or a fixed parameter holding an ordinary list value or a callable rather than a transported collector cell) is evaluated during supply formation, and its items become ready values (NEED-07). Spread items are never reopened (SUP-03), and nothing spreads recursively.
- An error therefore arises at the operation that demands the failing computation. Independently required checks are the exception: static front-end validation (NEED-05) and the supply formation of an arbitrary spread. Supply cardinality (VAR-02), bare forwarding's selection by binding name and compatible pattern (FWD-02), parameter ownership (PAR-07) and the structural-pattern kinds (PAT-06) are unchanged.

**Qualifications**
- Collectors and fixed parameters agree on unused arguments: `Bad = 1 / 0` / `Fix(x) = 1` / `Ignore(*xs) = 1` / `Fix(Bad), Ignore(Bad)` is `S[1, 1]`. An unused output-less block is no error either: `Coll(*xs) = 1` / `Coll({ X = 1 })` is `1`, while reading it, `Coll(*xs) = xs` / `Coll({ X = 1 })`, is `MissingOutput`.
- A collector of an enclosing body re-spread inside a nested block is still a known slice: `Inc(x) = x + 1` / `Apply(f) = f(9)` / `Fwd(*fs) = { Inner = Apply(fs*)` / `Inner }` / `Fwd(Inc)` is `10`.
- A fixed parameter retaining an existing collector cell keeps that cell's known slice: `Inc(x) = x + 1` / `Apply(f) = f(9)` / `Pass(v) = Apply(v*)` / `Outer(*fs) = Pass(fs)` / `Outer(Inc)` is `10`. Spreading a fixed parameter that holds an ordinary value or callable is an arbitrary spread, raised during supply formation although the callee never reads its collector: `Inc(x) = x + 1` / `Coll(*xs) = 1` / `Pass(f) = Coll(f*)` / `Pass(Inc)` is `ArityMismatch`.
- Callback elements are ready values too, and a reducer's accumulator is a VALUE-only cell (HO-02): neither has a CALLABLE identity or a retained slice.
- Effects follow first demand. One cell has one completion: `Use(*ys) = ys` / `Twice(*xs) = Use(xs*), Use(xs*)` / `Twice(trace(5))` is `S[L[5], L[5]]` after one `trace(5)`. Each invocation of a re-spread callable is fresh: `Apply(f) = f(9)` / `T(x) = trace(x) + 1` / `Twice(*fs) = Apply(fs*) + Apply(fs*)` / `Twice(T)` is `20` after two `trace(9)`.
- Bare forwarding never renames a binding: `Inc(x) = x + 1` / `Apply(f) = f(9)` / `Use(*fs) = Apply(fs*)` / `Relay(*fs) = Use` / `Relay(Inc)` is `10`, while `Inc(x) = x + 1` / `Apply(f) = f(9)` / `Use(*fs) = Apply(fs*)` / `Relay(*gs) = Use` / `Relay(Inc)` supplies nothing to `fs`, so it is `Apply`'s `ArityMismatch`.
- A loop's initial state is the captured call's own argument cells, so only the first iteration still receives a callable: `Zc(*xs) = 7` / `Ap(f) = f(1)` / `S(n, *g) = { Ap(g*), g* }` / `repeat(S(0, Zc), 1)` is `(7, 7)`, while `Zc(*xs) = 7` / `Ap(f) = f(1)` / `S(n, *g) = { Ap(g*), g* }` / `repeat(S(0, Zc), 2)` is `NotAnAlgorithm`.

```katlang
Inc(x) = x + 1
Apply(f) = f(9)
Fwd(*fs) = Apply(fs*)
ApplyFirst(*fs) = map([1, 2], fs*)
Ignore(*xs) = 1
Bad = 1 / 0
Fwd(Inc), ApplyFirst(Inc), Ignore(Inc), Ignore(Bad)
```
⇒ `S[10, L[2, 3], 1, 1]`

Reading the list demands each element by its own VALUE contract: `Coll(*xs) = xs` / `Only(*ys) = ys` / `K = 5` / `Coll(K), Coll(Only), Coll({ 3 })` is `S[L[5], L[L[]], L[3]]`. A callable that requires an argument gives its own verdict: `Inc(x) = x + 1` / `Collect(*xs) = xs` / `Collect(Inc)` is `ArityMismatch`, like `Inc(x) = x + 1` / `Id(x) = x` / `Id(Inc)` is `ArityMismatch`. `Coll(*xs) = xs` / `Coll(sum)` is `sum`'s own `ArityMismatch`, and `Coll(*xs) = xs` / `Fam(0) = 0` / `Fam(n) = n` / `Coll(Fam)` is `NoMatchingBranch`.

The unspread collector is not callable: `Inc(x) = x + 1` / `Apply(f) = f(9)` / `Fwd(*fs) = Apply(fs)` / `Fwd(Inc)` is `NotAnAlgorithm`, and so are `Apply(fs[0])`, `Apply((fs*))` and `Fwd(5)`. The explicit `fs*` in this list demands the collector's items when the list is built (SUP-02): `Inc(x) = x + 1` / `Apply(f) = f(9)` / `Fwd(*fs) = Apply([fs*]*)` / `Fwd(Inc)` is `ArityMismatch`. A read stops at the first failure: `Use(*ys) = ys` / `Fwd(*xs) = Use(xs*)` / `Fwd(trace(1), 1 / 0, trace(3))` is `DivisionByZero` after the single host call `trace(1)`.

### VAR-04 — No binder carries supply provenance: binding sees only the supplied items

- No binder, collector, forwarding step or dot-call mechanism may carry or consult per-item supply provenance. What a parameter list binds is determined entirely by the ordered list of supplied items: for each supplied cell its VALUE computation and any available CALLABLE identity (NEED-01, NEED-07, NEED-08, VAR-03; owned by CALL, PAR-01).
- An item that a spread produced binds exactly like the same value written as its own slot (SUP-03).
- A dot receiver binds exactly like the same value written as the leading argument (DOT-03).
- A forwarded collected list re-supplies its elements as ordinary items (FWD-01), and they bind like items the caller wrote.
- The general invariant that values carry no provenance, with its list of producing routes (group, property, call result, `if`, selection, block, capture), is VAL-09.

**Qualifications**
- Diagnostics may record where an item came from, but binding may not. A cell's written source and span serve its suspended computation and diagnostics: written-argument blame and the position of a `DemandCycle` or a missing CALLABLE projection.
- The one declared exception is a `meta` parameter: its head asks for the supplied call itself, and it binds a call reference to that written invocation (CR-1, CR-2). No other binder reads how an item was written.
- The number of items a value contributes is changed only by explicit openers: the spread marker written at the supply site (SUP), an explicit structural pattern (PAT), or deconstruction (VAR-05). These are written syntax, not provenance.

```katlang
Coll(*xs) = xs
F(x, *m, z) = m
Fwd(*items) = Coll(items*)
P = 1, 2
Coll((1, 2)*, 3), Coll(1, 2, 3), P.Coll, Coll(P), Fwd(P), Fwd(P*), F(P*, 3), F(1, 2, 3)
```
⇒ `S[L[1, 2, 3], L[1, 2, 3], L[S[1, 2]], L[S[1, 2]], L[S[1, 2]], L[1, 2], L[2], L[2]]`

### VAR-05 — Assignment deconstruction is the explicit unpacking receiver

*Resolved (Q-51, owner decision 2026-11-28): a written spread right-hand side that opens one level beyond the bare value is intended, because the binding follows from the value supplied. The spread only contributes items to the ordinary capture of step 1, and step 2's one opener opens the captured value, so naming that value first binds the same targets; no receiver reopens a spread-produced item (SUP-03).*
*Open: whether an argument view is one opaque item or is refused as a right-hand side (Q-84).*

- This rule covers `t1, …, tn = RHS` (flat targets, at most one of them `*name`) and the lone form `*name = RHS`. Binding happens in three steps:
  1. The right-hand side's rows are captured into one value by ordinary capture.
  2. That one value is opened by exactly one level. A sequence value or list value opens to its immediate items. Any other value (number, string, Boolean) supplies itself as one item.
  3. The opened items are allocated by VAR-02. Without a collector the count must match exactly. Fixed targets take items from both ends, and a collecting target collects the rest exactly, never reopening an item.
- This opening belongs to deconstruction alone. A call never unpacks an argument this way: `Coll(A)` collects `[A]`, while `*all = A` binds A's items.
- The receiver is its own construct: each target elaborates to a helper whose one parameter is the unpacking receiver, one receiver shared by every target of the deconstruction, never a written sequence pattern. So the structural kind law (PAT-06) does not apply to it: it opens a lone sequence or list and takes a scalar as one item.
- It demands the right-hand side's value, so a right-hand side without output is its own `MissingOutput`.
- There is no bracketed deconstruction target (`[x, y] = …`), and none is added for symmetry: the unpacking receiver already accepts both kinds.
- A written spread on the right-hand side contributes its immediate items to the capture in step 1 (SUP-06). If it contributes the only item, capture returns that item itself and step 2 opens it: a list or sequence exposed by singleton capture supplies its immediate elements to the targets. `x, y = A*` therefore opens one level deeper than `x, y = A` when `A`'s only element is itself structured, and binds exactly what `P = A*` / `x, y = P` binds. Several spread items are captured as one sequence of those items, each kept whole.

**Qualifications**
- Deconstruction heads are flat. `x, (y, z) = 1, (2, 3)` is a parse error; deeper structure needs a patterned helper such as `F((x, (y, z)))` or, for lists, `F([x, [y, z]])` (PAT-06).
- A single target `x = RHS` is an ordinary property: it captures and does not open.
- Two collecting targets are `InvalidCollectingBinding`.
- A count mismatch is reported only when a target is used (VAR-06).
- Unpacking a list checks kind and cardinality before binding targets. Checking a filtered list's cardinality can run predicates. Each fixed target then demands its bound position when read (SEQ-02): `a, b = [trace(1), 1 / 0]` / `a` is `1` after `[trace(1)]`. A right-hand side that reads a collecting binding demands that collector's VALUE first, which runs every collected computation (NEED-07).
- An argument view is today neither a sequence nor a list, so it is one item: `Capture(meta op) = op` / `F(a, b) = a + b` / `R = Capture(F(1, 2))` / `x, y = R.Arguments` / `x` is `ArityMismatch`, and `Capture(meta op) = op` / `F(a, b) = a + b` / `R = Capture(F(1, 2))` / `*all = R.Arguments` / `count(all)` is `1`. Spreading the view on the right-hand side is the value-position `TypeMismatch` (CR-11): `Capture(meta op) = op` / `F(a, b) = a + b` / `R = Capture(F(1, 2))` / `x, y = R.Arguments*` / `x` is `TypeMismatch`.

```katlang
Coll(*xs) = xs
A = [1, (2, 3), 4]
x, *y, z = A
*all = A
a, *b = 7
x, y, z, all, Coll(A), a, b
```
⇒ `S[1, L[S[2, 3]], 4, L[1, S[2, 3], 4], L[L[1, S[2, 3], 4]], 7, L[]]`

`x, y = [(1, 2)]` / `x + y` is `ArityMismatch`, while `x, y = ([(1, 2)]*)` / `x + y` is `3`. With `Points = [(10, 20)]`, naming the captured value first binds the same coordinates: `Point = Points*` / `x, y = Point` / `x, y` is `S[10, 20]`, like `x, y = Points*` / `x, y`. With `Points = [(10, 20), (30, 40)]`, `x, y = Points*` / `x, y` is `S[S[10, 20], S[30, 40]]`: the two spread items are captured as one sequence, and each target binds a whole pair. `*f = [[1, 2]]` / `f` is `L[L[1, 2]]`, one level only, and `*a = ()` / `a` is `L[]`.

### VAR-06 — Deconstruction declares properties of the enclosing algorithm; its right-hand side is one row of that body, successfully evaluated at most once

*Open: whether a count mismatch with a literal right-hand side should be a front-end error (Q-70, post-release backlog).*

- **Targets.** Each deconstruction target is an ordinary property declared in the enclosing algorithm. It cannot be `public`, because the grammar has no public deconstruction form. A target whose name is already declared in that scope is `DuplicateProperty`.
- **The right-hand side is a row of the enclosing body**, and the front end elaborates it that way. A synthetic source property only stores it; that property is no scope.
  - Its free names become implicit parameters of the enclosing algorithm, ordered together with the body's rows by written position.
  - Under a closed parameter list or a branch pattern, an undeclared name in it is a front-end error.
  - It never acquires parameters of its own. A lone reference there is a formula row of the enclosing body, never an alias (FWD-03).
  - An inline block in it is a block of the enclosing body: it reads that body's parameters and members exactly as a block in an output row does, on every elaboration route.
- **Evaluation.** The right-hand side is successfully evaluated at most once per cache identity of its shared source (PROP-04): once in each call of the owner the deconstruction is declared in, whether or not the source reads the call's input, and once per run where no call owns it (PROP-08). It runs on the first demand of any target: a demand, not a declaration and not the passing of a target to a callee that never reads it (NEED-01, NEED-03).
- A failing right-hand side creates no entry, like a failed property (PROP-09). Its failure is raised at that first demand and ends the run (VAL-10), so no later demand in that run evaluates it again.
- All targets are projections of that one successful evaluation. Its value is remembered even when a target's allocation then fails (a count mismatch), so a mismatch never re-runs the right-hand side.
- An explicit target call `a()` freshly invokes the target's projection wrapper and never reads `a`'s own property-cache entry; an `a()` that finds that entry empty establishes it (PROP-06). The wrapper reads the separately cached shared right-hand side, so `a()` does not request fresh right-hand side evaluation. A first target call can cause the right-hand side's first demand. Successful source caching remains per run for exported sources and per owner activation for local-only sources, with PROP-09's publication unchanged.
- If no target is demanded, the right-hand side is never evaluated. A count mismatch is therefore an error only when a target is used.

**Qualifications**
- C# may reuse one shared bind of the source across targets and consumers, and Lean may rebind the same cached source. The reuse never changes what a target computes: values, effects and their order, and non-resource errors are unchanged. Its only observable effect is resource accounting, so a run near a limit may complete, or reach the limit at a later operation (RUN-03).
- A deconstruction in a parameterless nested owner follows that owner's binding context (PROP-08): its group is evaluated once per call of the enclosing `F`, whether the owner is first read inside a callback or helper or through a member; an explicit call of the owner is a fresh calculation of its own, and two calls of `F` never share one. `F(k) = { B = { a, b = tick(), k` / `a }` / `B.a, B.a, B(), B.a }` / `F(1)` is `S[1, 1, 2, 1]`.
- Targets can be reached by structural dot access: `Obj = { a, b = 1, 2 }` / `Obj.b` is `2`.
- Targets can never be provided by `open`: they are never public, so with `open Obj` the name `b` is an unresolved implicit parameter.
- Caching of the shared source follows the zero-parameter property rules (PROP-04, PROP-09): success is remembered per cache identity of the source, and failure never is.

```katlang
F = { a, b = x, 10
  a + b }
p, q = trace(1), trace(2)
F(5), q, p, q
```
⇒ `S[15, 2, 1, 2]`

Each `trace` runs once. An undemanded failing right-hand side never runs: `p, q = trace(1) / 0, 2` / `I(f) = 0` / `I(p), I(q), I(p)` is `S[0, 0, 0]` with an empty host log. Demanded, it fails once and ends the run: `p, q = trace(1) / 0, 2` / `I(f) = 0` / `I(p), q, p` is `DivisionByZero` after `trace(1)`. A count mismatch behaves the same way: `p, q = trace(1), 2, 3` / `I(f) = 0` / `I(p), I(q)` is `S[0, 0]` with an empty host log, while `p, q = trace(1), 2, 3` / `p` is `ArityMismatch` after one `trace(1)`, and `x, y = 1, 2, 3` / `7` is `7`.

Passing is no demand: `p, q = trace(1), trace(2)` / `I(f) = 0` / `I(p), q, p` is `S[0, 2, 1]` with one `trace(1)` and one `trace(2)`. Explicit target calls keep the shared source: `a, b = tick(), 5` / `x = tick()` / `a, a(), a(), x, x(), x()` is `S[1, 1, 1, 2, 3, 4]`.

A free name of the right-hand side belongs to the enclosing body, so `F(y) = { a, b = x, 10` / `a + b }` / `F(1)` is `UndeclaredIdentifier`, and a lone reference there lifts into that body: `F(a) = a, 1` / `K = { x, y = F` / `x }` / `K(5)` is `5`. An exported source runs once per run: `F(n) = { a, b = random(0, 1000000), 5` / `a }` / `F(1) == F(2)` is `true`, while a local-only one runs per activation: `F(n) = { a, *b = n, n + 1, n + 2` / `b }` / `F(1), F(10)` is `S[L[2, 3], L[11, 12]]`.

```katlang
Sibling = 100
F(p) = {
  x, y = { p + 1 }, { Sibling + p }
  x + y * 10
}
F(2)
```
⇒ `1023`

### FWD-01 — Forwarding collected arguments re-spreads the collector's own cells: spread(collect(S)) = S

- For every supply `S`, re-spreading the collector bound to `S` re-supplies exactly `S`. So `Forward(*items) = Target(items*)`, or equivalently `items*.Target`, hands `Target` the same items, in the same order, that `Forward` received: the same supplied cells, each with its VALUE computation and any CALLABLE identity it was supplied with, and the transfer demands none of them (VAR-03, NEED-07, NEED-08). This includes zero items, `()`, `[]` and nested structures, and a collecting `Target` re-collects an equal list.
- At the value level, reading the collector materializes one exact list (VAR-01) whose spread supplies the values of `S`: spread(collect(S)) = S.
- Passing the collector without the spread passes one argument: the collector's own cell, one collection-valued computation, transported undemanded (NEED-08). A collector then collects it as the one item of `[items]`, and a fixed parameter binds it; its VALUE, when demanded, is the exact list, and a later `v*` of that fixed parameter still re-spreads the original cells (VAR-03).
- Conversely, `collect(spread L) = L` for a list value `L`.
- Read as a value, a collected binding is an ordinary exact list: the read materializes every cell left to right, and the first failing cell is the read's failure (VAR-03, NEED-07). Forwarding carries no runtime supply provenance beyond the transferred cells themselves (VAR-04).

**Qualifications**
- A collected list is passed to a collection builtin whole (`values.sum`). `sum(values*)` instead supplies the collector's cells individually: its count is accepted exactly when there is one cell, and zero or more than one is `ArityMismatch` before ordinary VALUE demand (CALL-04, NEED-05). The accepted cell is then demanded as the builtin's collection argument: `F(*values) = sum(values*)` / `F(3)` gives `3`.
- Lists collected by a nested pattern forward the same way: `CountItems(*xs) = xs.count` / `Use((*history), last) = CountItems(history*, last)` / `Use((1, 2, 3), 4)` is `4`.

```katlang
Target(*xs) = xs
Forward(*items) = Target(items*)
ForwardOne(*items) = Target(items)
Forward(), Forward(7), Forward((), [], (1, 2), [()]*), ForwardOne(1, 2)
```
⇒ `S[L[], L[7], L[S[], L[], S[1, 2], S[]], L[L[1, 2]]]`

`Coll(*xs) = xs` / `L = [1, 2]` / `Coll(L*) == L` is `true`. Re-spreading demands nothing: `Target(*xs) = 0` / `Forward(*items) = Target(items*)` / `Forward(trace(1), trace(2))` is `0` with an empty host log, and `Target(*xs) = 0` / `ForwardOne(*items) = Target(items)` / `ForwardOne(trace(1))` is `0` with an empty host log. A demanded read stops at its first failing cell: `Target(*xs) = xs` / `Forward(*items) = Target(items*)` / `Forward(trace(1), trace(1) / 0, trace(3))` is `DivisionByZero` after two `trace(1)`.

### FWD-02 — Bare forwarding reuses existing compatible bindings by name, and a written call means what it writes; every synthesized call forwards bindings unchanged and rebuilds each structural pattern as its own kind

*C#-only by design.*
*Open: whether to state a rename-invariance law with its decided exclusions (Q-44).*

- A lone reference body is not a formula. Its meaning, and that of the forms near it, is decided by what is written, never by compiler internals:

| You write | Meaning |
|---|---|
| `A = F`, `A = { F }` | an alias of `F`: a transparent reference or a forwarding carrier (FWD-03, FWD-04) |
| `A(p) = F` | bare forwarding: reuse A's existing compatible binding named `p` for F's parameter `p`; infer nothing, rename nothing |
| `A(p) = F(p)` | an explicit call (CALL): the written arguments; caller and callee names need not match |
| `A = F(p)` | a formula whose parameter `p` is the free name written in it (PAR-03, PAR-05) |
| `A = F + 1` | formula lifting (PAR-07): F's required parameter names become A's inferred parameters, by name |
| `A(p) = F + 1` | a formula under a closed list (PAR-04): it may reuse existing bindings, never add one |

- **Do not equate `A(p) = F` with `A(p) = F(p)`.** Bare forwarding is by compatible existing binding name, an explicit call is an ordinary written argument call, and formula lifting is a separate by-name inference mechanism. The two forms agree only when the names do.
- **Bare forwarding.** A closed body (a written parameter list, or a clause branch) whose one written row is a bare reference to a callable that declares parameterized structure reuses already-existing compatible source bindings by name. It never renames a binding, never creates a new binding inside the closed list (PAR-04), never matches parameters by position, and never converts an incompatible top-level parameter pattern because nested leaf names coincide. For each top-level parameter pattern of the target:
  - a capture `n` is supplied by the body's own top-level capture `n`; when the body binds no `n` at all, by the enclosing parameter binding a written `n` would denote there (PAR-07's forwarding source, never a property, opened name or builtin); a body that binds `n` only inside one of its structural patterns holds an element of that pattern, not a whole-value parameter, so the capture is unforwardable;
  - a structural pattern is supplied only by one of the body's own top-level patterns with the same contract (kind, shape, names and collectors, compared structurally rather than by display text), rebuilt as itself; it is never assembled from same-named leaves, and an enclosing binding, a plain named value, never supplies one;
  - a collector that nothing of its name supplies receives no argument;
  - any other parameter nothing supplies makes the definition the front-end error `UnforwardableParameter`, reported at the bare reference, with no evaluation.
- Unused parameters of the body stay unused. A row that forwards nothing (every callee parameter an unsupplied collector) is the bare name: CALL-05's cached read, never an invented call.
- Binding kind follows the source: a collecting source re-spreads its collected cells only into a collecting destination, and every other pair passes the binding whole, as its one cell (FWD-01). Forwarding transports cells and demands none of them (NEED-08): a bare-forwarding definition keeps its own evaluation frame and written signature, an unused forwarded argument never runs, and a demanded one runs at most once (CALL-06).
- **Which callables are targets.** The row names the callable itself, so the rule reads the declared structure of the one identity name resolution selects (owner walk, prelude, opens, structural dot path, through aliases to the normalized target), never the lookup route, the spelling or zero-argument acceptance.
  - Declared parameterized structure: every builtin, every clause family, nameable or not, a user algorithm with at least one completed parameter pattern (a callable that also works with no arguments included), a Math member and a host operation, reached directly, opened, dotted, from a loaded module or through an alias.
  - A zero-parameter identity is no target: the row reads it.
  - A row with no static identity is no target: a parameter, an unresolved name, an ambiguous open, a member only a run-time receiver can provide, an `.Algorithm` link, a parameter-rooted member path. A runtime-target alias is none either: it has no forwarding contract (FWD-04).
- **Forwarding contract.** Bare forwarding needs a static, named top-level parameter interface: the identity's lifting signature (PAR-07), which is a user algorithm's processed parameter patterns (an opened, dotted or module member's, a Math member's and a host operation's included), a builtin's registry signature, a nameable clause family's clause-named whole-value slots, and through an alias its target's. The completed row is exactly the explicit call.
  - An unnameable family has no forwarding contract, so a closed lone row naming one, directly or through an alias, is the front-end error `UnforwardableCallable` at the bare reference, with the row left as written. The explicit call is the repair.
- **Written calls.** Explicit call expressions are authoritative: `A(p) = F(p)` passes its written arguments whatever F calls its parameters. Parameter inference comes from unresolved free names written in those expressions (PAR-03, PAR-05), not from internal parameter names of resolved callees.
- **Every synthesized call forwards existing bindings unchanged and rebuilds each structural pattern as its own kind.** This covers bare forwarding and a formula's lifted call (PAR-07); an alias synthesizes none.
  - A fixed binding is supplied whole, its one cell with VALUE and CALLABLE channels intact and undemanded (NEED-08), never opened and never wrapped.
  - A collecting binding is re-spread as exactly its collected cells only when both the destination capture and the source binding collect. The source binding is the one this rule or PAR-07 selects, a reused enclosing binding included, and its kind decides: an ordinary parameter is never re-spread into a collecting destination, and a collector forwarded into a fixed destination stays one argument, the collector's own cell.
  - A reconstructed sequence pattern is a sequence: the capture of its items, `()` for none, or its one lone non-spread item itself, because the written `C((xs))` is `C(xs)` and a one-item sequence pattern does not exist (PAT-06). A reconstructed list pattern is a list, the list literal of its items, at every nesting level.
  - No forwarding step converts between sequence and list kinds, so every synthesized call is exactly the call a programmer would write.
- **Formula lifting keeps its by-name rules (PAR-07).** In a formula a callee group is rebuilt around the caller's bindings of the same names, and a group that binds no new name contributes nothing to the lifted signature and is rebuilt as the empty structure of its own kind.
  - Forwarding by shape forwards a caller whose whole list is one top-level collector into a callee whose whole list is one grouped collecting stream, `((*xs))` or `([*xs])`, as that group's own kind, whatever the two names are. The rebuilt group is exactly the written call `H((xs*))` or `H([xs*])`, so a sequence group given a one-item stream receives that item itself (VAL-03, PAT-06). The list form `([*xs])` keeps every cardinality.
  - Forwarding by shape is a formula rule only. It is an established conflict with by-name bare forwarding, minimized rather than excepted: `Use(*items) = [C][0]` with `C((*xs))` calls `C((items*))`, while the lone row `Use(*items) = C` forwards by name and is `UnforwardableParameter`.
- **Renaming a callee's parameters.** An alias takes the new names with it. Bare forwarding may become unforwardable, as intended. An explicit call is unaffected. Formula lifting lifts the new name.

**Qualifications**
- The root's rows are never completed: a root row is a value read (PROP-05).
- A deconstruction's right-hand side is a written row of its body, so a body with a deconstruction beside the bare callee has two written rows and is a formula: `P(x, x) = x` / `A = { a, b = 1, 2` / `P }` / `A(7)` is `7`, and `P(x, x) = x` / `A = { a, b = 1, 2` / `P }` / `A(7, 7)` is `ArityMismatch`.
- A closed body may be written in braces: `F(p) = p * 2` / `A(p) = { F }` / `A(5)` is `10`.
- The elaboration is front-end work. Lean specifies bare forwarding and the synthesized arguments as surface support and evaluates the elaborated result (FORMAL-02).

```katlang
Double(x) = x * 2
Other(y) = y * 2
Alias = Double
Forward(x) = Double
Explicit(x) = Other(x)
Formula = Double + 1
Alias(5), Forward(5), Explicit(5), Formula(5)
```
⇒ `S[10, 10, 10, 11]`

- **By name, never renamed.** `F(p) = p * 2` / `A(p) = F` / `A(5)` is `10`, while `F(q) = q * 2` / `A(p) = F` / `1` is `UnforwardableParameter`. `F(q) = q * 2` / `A(p) = F(p)` / `A(5)` is `10`.
- **A callee that declares nothing is no target.** `F = 10` / `A(p) = F` / `A(999)` is `10`.
- **Never added.** `F(p, q) = p + q` / `A(p) = F` / `1` is `UnforwardableParameter`, and `F(p) = p * 2` / `A(p, unused) = F` / `A(5, 999)` is `10`.
- **Never positional.** `Sub(y, x) = y - x` / `G(x, y) = Sub` / `G(10, 3)` is `-7`, while `Sub(y, x) = y - x` / `G(x, y) = Sub(x, y)` / `G(10, 3)` is `7`.
- **Never reshaped.** `Single([x]) = x` / `G(x) = Single` / `1` is `UnforwardableParameter`, while `Single([x]) = x` / `G(x) = Single(x)` / `G([7])` is `7` and `Single([x]) = x` / `G([x]) = Single` / `G([7])` is `7`. `Add((x, y)) = x + y` / `G((x, y)) = Add` / `G((2, 3))` is `5`, while `Add((x, y)) = x + y` / `G(x, y) = Add` / `1` is `UnforwardableParameter`. Positions inside a pattern are never renamed: `F([a, b]) = a` / `A([x, y]) = F` / `1` is `UnforwardableParameter`. The `x` inside a pattern is an element: `F(x) = x` / `A([x]) = F` / `1` is `UnforwardableParameter`.
- **Collectors.** `Coll(*vs) = vs` / `Many(*vs) = Coll` / `Many(), Many(7), Many(1, 2)` is `S[L[], L[7], L[1, 2]]`. A fixed source is one item: `Coll(*vs) = vs` / `One(vs) = Coll` / `One((1, 2))` is `L[S[1, 2]]`. A collected list reaches a fixed parameter whole: `Id(vs) = vs` / `Many(*vs) = Id` / `Many(1, 2)` is `L[1, 2]`. `C((*xs)) = xs` / `Use(*items) = C` / `1` is `UnforwardableParameter`, while `C((*xs)) = xs` / `Use((*xs)) = C` / `Use((1, 2))` is `L[1, 2]`.
- **Nothing forwarded.** `Target(*items) = items` / `UseFixedOther(values) = Target` / `UseFixedOther([1, 2])` is `L[]`, the cached read, while `Target(*items) = items` / `Use(items) = Target` / `Use([1, 2])` is `L[L[1, 2]]`.
- **Repeated names (PAT-09).** One binding reaches both occurrences: `P(x, x) = x` / `Q(x) = P` / `Q(7)` is `7`. `F(x, y) = x * 10 + y` / `G(x, x, y) = F` / `G(3, 3, 4)` is `34`, and `F(x, y) = x * 10 + y` / `G(x, x, y) = F` / `G(3, 4, 4)` is G's own `ArityMismatch`.
- **Nested scopes.** `F(x) = x` / `Outer(x) = { Local(y) = F` / `Local(5) }` / `Outer(100)` is `100`: Local declares no `x`, so the binding a written `x` denotes there is reused. `F(x) = x` / `Outer(x) = { Local(x) = F` / `Local(5) }` / `Outer(100)` is `5`. `A = y + 1` / `G = { F(x) = A` / `F(1) + y }` / `G(10)` is `21`.
- **Clause branches.** `F(n) = n * 10` / `G(0) = 0` / `G(n) = F` / `G(0), G(3)` is `S[0, 30]`, while `F(a) = a * 10` / `G(0) = F` / `G(1) = 1` / `1` is `UnforwardableParameter`: the pattern binds no `a`.
- **Closed formulas (PAR-04).** `F(p) = p * 2` / `A(p) = F + 1` / `A(5)` is `11`. `F(q) = q * 2` / `A(p) = F + 1` / `A(5)` is the runtime `ArityMismatch` of `F`'s own zero-argument demand: nothing renamed, nothing added. A strict Math position is the same runtime demand: `F(q) = q * 2` / `A(p) = abs(F)` / `A(5)` is `ArityMismatch`.
- **Written-call formulas.** `Add((a, b)) = a + b` / `G = Add((x, y))` / `G(2, 3)` is `5`, whatever `Add` calls its binders, and `Add((a, b)) = a + b` / `G = Add((x, y))` / `G(2)` is `ArityMismatch`.
- **Forwarding by shape.** A one-item stream gives a sequence group that item itself: `C((*xs)) = xs` / `Use(*items) = [C][0]` / `Use(7)` is `C(7)`, the sequence pattern's `TypeMismatch`, while `C((*xs)) = xs` / `Use(*items) = [C][0]` / `Use((7, 8))` is `[7, 8]`, like `Use(7, 8)`.
- **Laziness.** `F(p) = 0` / `A(p) = F` / `A(trace(1))` is `0` with an empty host log, and `F(p) = p + p` / `A(p) = F` / `A(trace(3))` is `6` after one `trace(3)`.
- **Unnameable family.** `S(1) = 1` / `S(-1) = -1` / `SA = S` / `W(x) = SA` / `1` is `UnforwardableCallable`, while `S(1) = 1` / `S(-1) = -1` / `SA = S` / `W(x) = SA(x)` / `W(1), SA(-1)` is `S[1, -1]`.

### FWD-03 — Whole-algorithm transport: an open body whose one row is a bare algorithm reference is a transparent reference when unbraced and a structural forwarding carrier when braced, and neither owns a zero-argument entry

- **Formation.** A non-root open body (no written parameter list, not a clause branch, and no parameter of its own after inference) whose one written row is a bare reference that name resolution resolves to an existing algorithm, of any arity, is an alias. Identity decides, never the lookup route: owner walk, prelude, opens, structural dot path, through references to their normalized targets. The target may be a parameterized user algorithm, a zero-parameter property, a builtin, a clause family, nameable or not, a Math member, a host operation, or an opened, dotted or module member of these.
- **What is written decides the kind.**

| You write | Meaning |
|---|---|
| `A = P`, `A = (P)` | a transparent reference to `P` |
| `A = B.C`, `A = B.C.D` | a transparent reference to the selected member, with its structure and original context; a genuine structural hit only |
| `A = R.Algorithm`, `A = p`, `A = b.C` | a transparent runtime reference to the call reference's callee, the parameter, or the parameter's member (FWD-04) |
| `A = { P }`, `A = { Helper = 0 ⏎ P }`, `A = { open L ⏎ P }`, an inline `{ P }` | a structural forwarding carrier of `P` |
| `A = { B.C }`, `A = { R.Algorithm }` | a carrier, never a full alias of the member or callee |

- A loaded module's root whose one row is a reference is a carrier too: a source unit keeps its own namespace (MOD-08).
- **Transparent reference.** Every observation is its target's: structural identity (NEED-04), members, open provider, invocation, bare VALUE and publication origin. `A(args)` is the target's call with exactly the written supply. Written member access through `A` navigates the target and evaluates no unrelated output, and a reference passed on is its target (HO-01). `A` keeps only its binding: its declaration, its exposure and its written name.
- **Structural forwarding carrier.** Its structural identity and structure are its own: its declaration, its declaring activation, its own declarations as its only members, and its own public declarations for `open`. It inherits no member from its target: a miss takes the ordinary dot route (DOT-01, DOT-04), and an own-member hit never resolves or executes the forwarding target. A carrier passed on stays its own structure.
- **Invocation through either kind is the target's.** A call with supply `S`, written directly, reached by dot fallback, as a callback or loop step, or through a parameter that received the alias, is the target's own invocation with `S` (user binder, builtin adapter, clause dispatch, Math or host wrapper). The exact supplied computations are forwarded freshly, so the accepted and rejected supplies, argument roles, cardinality before inspection, laziness, value, effects and their order, random draws, failures, suspension and cancellation points are the target's. Lifting signature, forwarding contract, arity and zero-argument acceptance are asked of the normalized target too.
- **Resolved once, in the alias's own scope.** The target is resolved at the alias's declaring activation, never at a use site, never at the caller, and never in a new activation per hop. A later nearer name, a parameter of that name or another open cannot change it.
- **Nothing is synthesized.** There is no wrapper algorithm, no inherited signature and no call. An alias is no invocation: the hop charges no step, no depth and no activation, and a call through it reports the target's failures under one frame naming the written alias.
- **Transport does not loosen invocation.** Passing or navigating `B` can preserve its members, its output structure and its lexical ownership, while `B(...)` invokes it under its parameter and pattern requirements. An empty call is not valid merely because a bare reference can be transported: a zero supply over a target that requires arguments is that target's arity rejection, and it never returns the target.
- **No alias owns a zero-argument entry.** A bare read is the target's bare view, under the target's own owner and context (PROP-07). An explicit invocation is fresh and publishes under the target's eligible origin: a qualifying zero-supply call that finds the target's entry empty may establish it (PROP-06, PROP-09), and it never replaces an established one. Builtin, native and host operations publish nothing.
  - Forwarding's fresh invocation and the property cache stay separate: a call through an alias never reads the target's entry, and a bare read is no call. Fresh describes the invocation of the target, not every computation beneath it (ALG-10).
- **Parameter-rooted member references.** In a parameterless open body whose one written row is an argumentless member path rooted at an enclosing parameter (`A = b.C`, `A = b.C.D`), the member names are member references, never new inferred parameters. This is the one exemption from DOT-05's inference, applied after parameter resolution, and the body is a runtime member reference (FWD-04). Nothing else is exempt.
- **Static open through references.** `open` is owned by MOD. A static transparent reference opens its target's public namespace under the target's provider identity, judged by the target's own provider rule (MOD-04). `open Alias, Lib` with `Alias = Lib` is one provider, and two different providers of one name stay `AmbiguousOpen` (RES-03).
  - Resolution is stratified: an open target's reference head and member chain resolve through the direct chain and member steps only, never through an open, so a self-dependent open is `UnresolvedOpenTarget`, never a runtime fixed point (MOD-03).
  - A carrier opens only its own public declarations, without evaluating its output. A runtime reference stays a namespace of its own declarations (FWD-04). Private members are never opened.
- **Reference cycles.** A body whose static target chase returns to a body it already passed is no alias: it stays an ordinary lazy property with its ordinary cache entry, in every declaration order, and a demanded cycle fails by the ordinary recursion limits.
  - The target chase follows every lone reference body it reaches, a reference or a carrier alike, through the written opens of each level. So in `A = B` / `B = { public X = 1` / `A }` neither body is an alias, and `A` has no member `X`.
  - The check is stratified. Formation refuses a body whose chase returns in either of two readings, one whose open providers follow every reference and one whose open providers follow a reference only where the first reading finds no cycle. Every name lookup then reads providers whose references are followed exactly where alias formation follows them. Each reading reads only the check below it, so no source program reaches evaluation with a static alias cycle, and every layer selects what the evaluator selects.
  - A return through a receiver's unrelated member is no target cycle: `A = B.C` / `B = Lib` / `Lib = { public C = { public X = 1 }` / `public D = A }` / `A.X` is `1`.

**Qualifications**
- This rule covers bodies of exactly this shape. A brace block with any other row is an ordinary algorithm (ALG-01), and an assignment whose row is anything else is an ordinary property or formula.
- These are not references:
  - constants, `C = 6` and `C = { 6 }`: 6 is no algorithm reference;
  - calculations: `A = P()`, `A = B.C()`, `A = P + 1`, `A = 6.abs`, selections, lists, spreads and `if`;
  - an inferred input: `A = x`, where `x` is an inferred parameter of `A`;
  - a member miss: `A = B.foo` where `B` declares no `foo` is the call `foo(B)`;
  - a block row: `A = {{ F }}` is a body whose row is a block literal, never flattened into `A = F`;
  - the root, which is never an alias: a root row `F` is a VALUE consumer;
  - closed bodies, which FWD-02 decides;
  - a deconstruction's right-hand side, and a body with a deconstruction beside the row (VAR-06, FWD-02);
  - a name that selects no identity: an ambiguous open is `AmbiguousOpen`, and an unresolved name stays an implicit parameter.
- A rejected zero-argument VALUE demand of an alias is the target's ordinary contract, reported as the written reference reports it (CALL-05). An inline `{ Inc }` has no name or signature of its own, so it reports exactly what `Inc` reports. A block reports `UnresolvedImplicitParams` only over parameters it infers itself.
- A transparent reference's read is its target's read, so at a spread operand the target's own missing output is `SpreadMissingOutput`. A VALUE read that crosses a carrier is nested: the carrier's written row is a subordinate computation, so `{ G }*` keeps `G`'s `MissingOutput` (SUP-02).
- A missing output reached through an alias is the terminal binding's.
- Host root-property observations report the targets' entries. Nothing fakes an entry for a forwarding binding.
- A raw host-built `User` whose one row is a reference was never elaborated and keeps its written arity. A host-built `Alias` is a reference unless the host marks it otherwise. A host-built alias whose target is no static path or runtime row, or whose static chase cycles, is `IllegalInEval` before evaluation.

```katlang
Box = {
  public Q = 99
  F(x) = x * x
  F
}
A = Box
B = { Box }
GetQ(f) = f.Q
A.Q, GetQ(A), A(3), B(3)
```
⇒ `S[99, 99, 9, 9]`

`Box = { public Q = 99` / `F(x) = x * x` / `F }` / `Box()` is `ArityMismatch`, never `F`. `Box = { public Q = 99` / `F(x) = x * x` / `F }` / `B = { Box }` / `B.Q` is `UnresolvedImplicitParams`: `B` has only its own members, so `B.Q` is the fallback `Q(B)`, and nothing declares `Q`.

```katlang
P = tick()
A = P
B = { P }
A, P, A, B(), B
```
⇒ `S[1, 1, 1, 2, 1]`

The bare reads share `P`'s one entry, and `B()` is a fresh call of `P`. A first zero-supply call establishes the target's empty entry: `P = tick()` / `A = P` / `A(), P` is `S[1, 1]`. Later calls stay fresh: `P = tick()` / `B = { P }` / `B(), B(), P()` is `S[1, 2, 3]`. A carrier's own member and its bare read are separate from a fresh call: `B = { public P = tick()` / `public Q = 99` / `P }` / `B.P, B(), B, B.P` is `S[1, 2, 1, 1]`. One evaluation serves an alias and its target: `Only(*xs) = tick()` / `A = Only` / `A, Only, A` is `S[1, 1, 1]`.

Declarations beside the row make a carrier: `F(x, y) = x - y` / `A = { k = 1` / `F }` / `B = A` / `B(10, 3), A.k` is `S[7, 1]`. A carrier's call runs at its declaring activation: `F(k) = { B = { V = trace(k)` / `V }` / `B() + B.V }` / `F(3)` is `6` after one `trace(3)`. The target is fixed where the alias is written: `F(x) = x` / `A = F` / `H = { F(x) = x * 100` / `A(2) }` / `H` is `2`. Roles are the target's: `Inc(x) = x + 1` / `A = abs` / `K = A(Inc)` / `K(-5)` is `4`. Builtin laziness survives: `I = if` / `I(true, 1, 1 / 0)` is `1`, `A = { if }` / `A(true, 1, 1 / 0)` is `1`, and `Eff(x) = trace(x)` / `M = map` / `M([], Eff)` is `[]` with an empty host log. Cardinality comes first: `C = count` / `C(1 / 0, 2)` is `ArityMismatch`, and a loop keeps its exact contract: `Inc(x) = x + 1` / `R = repeat` / `R(Inc)` is `ArityMismatch`. A family dispatches as itself: `Fact(0) = 1` / `Fact(n) = n * Fact(n - 1)` / `F = Fact` / `F(4)` is `24`, while `Fact(0) = 1` / `Fact(n) = n * Fact(n - 1)` / `F = Fact` / `F(1, 2)` is its cardinality `ArityMismatch`. An unnameable family can be aliased: `Sign(1) = 'p'` / `Sign(-1) = 'n'` / `SA = Sign` / `map([1, -1], SA)` is `['p', 'n']`.

Parameter-rooted member references: `Box = { G(x) = x * 10 }` / `Use(b) = { A = b.G` / `A(3), 3.A }` / `Use(Box)` is `S[30, 30]`.

Open through a reference: `open A` / `Lib = { public Z = 2 }` / `A = Lib` / `Z` is `2`, while a carrier exposes nothing of its target: `open A` / `L = { public X = 5 }` / `A = { L }` / `X` is `UnresolvedImplicitParams`. A parameterized target is refused by its own rule: `open A` / `F(x) = 7` / `A = F` / `1` is `IllegalInOpen`. A self-dependent open: `Lib1 = { public X = { public X = 1` / `0 }` / `0 }` / `G = { open A, Lib1` / `A = X` / `X }` / `G` is `UnresolvedOpenTarget`.

Reference cycles: `A = B` / `B = A` / `1` is `1`, and `A = B` / `B = { public X = 1` / `A }` / `G(p) = A.X` / `1` is `UndeclaredIdentifier`, the certain fallback name.

Calculations keep their own entry: `P = tick()` / `A = P()` / `A, A, P` is `S[1, 1, 1]`. A block row is not flattened: `F(x) = x` / `A = {{ F }}` / `A(1)` is `ArityMismatch`.

Rejected demands: `Inc(x) = x + 1` / `K(z) = count({ Inc })` / `K(1)` is `ArityMismatch`, while `Inc(x) = x + 1` / `K(z) = count({ Inc + 0 })` / `K(1)` is `UnresolvedImplicitParams`.

Missing outputs: `G = { public X = 1 }` / `A = G` / `A*` is `SpreadMissingOutput`, while `G = { public X = 1 }` / `C = { G }` / `C*` is `MissingOutput`.

### FWD-04 — A runtime-target alias takes its callable from one binding cell per declaring activation: an identity of any arity is invoked freshly, absence leaves a value view, and a failure stays a failure

- **Classification.** A lone reference body is a runtime-target alias when it is open, is left with no parameter of its own after inference (PAR-03, DOT-05 and PAR-07 run first), and its row is one of:
  - an enclosing parameter binding (`A = f`), written, inferred at an enclosing level, or a branch binder;
  - an argumentless `.Algorithm` link whose receiver does not statically declare a member `Algorithm` (`A = R.Algorithm`, `A = Mk(5).Algorithm`), whose class signature selection decides (PAR-08);
  - an argumentless member path whose head is a parameter (`A = b.G`, `A = b.H.G`; FWD-03);
  - a name or static structural path whose identity resolution selects another such alias: a chain, forward references included.
- Written unbraced it is a transparent reference whose target only the run supplies (FWD-03). Written in braces or beside its own declarations it is a carrier over a runtime row.
- The classification is a front-end fact. A runtime-target alias records no target, arity, lifting signature or forwarding contract: every front-end question is answered as for an ordinary zero-parameter property, with dynamic argument roles, so nothing static is fabricated.
- **One binding cell.** Its target is the projection of one binding cell per declaration and declaring activation: the row supplied in the alias's own declaring context, never a consumer's. A parameter row is the parameter's own cell, with nothing allocated. A link row is CR-15's link with its one receiver. A parameter-rooted path carries an identity only on a structural hit (DOT-09); on a miss it is a computed value with none, never the lexical fallback as a callee.
- **Lifetime.** The cell is established lazily, once per declaring binding activation, a computed receiver included. Establishing it evaluates nothing. Cells are never shared across activations, runs or ownerless host objects (PROP-07).
- **Two channels, one cell.** The alias's bare read is the cell's VALUE, with property-style provenance, and a VALUE read never initiates the CALLABLE projection. Every callable use is the cell's CALLABLE projection. For a callable target both channels share every receiver demand, whichever comes first.
- **An identity of any arity.** When the cell projects a callable identity, that identity is the alias's callable in every callable position: direct, grouped and structural calls, lexical dot calls, higher-order arguments and forwarding, callbacks, clause dispatch, loop steps and META capture. The decision is per declaring activation and per supplied identity, so one declaration can be a callable in one activation and a value view in another.
- **Fresh invocation.** `A(args)` and `A()` on an identity are fresh ordinary calls with exactly the written supply, under the target's publication origin. `A = R.Algorithm` never reuses `R`'s captured arguments. The cell's sticky outcomes are its VALUE and its identity, never a call result.
- **Absence: the value view.** When the cell projects no identity (a value-only row: a member path's miss, a value parameter), bare `A` and `A()` answer the cell's once-demanded VALUE, never a rerun of the row. A non-empty supply is the row's arity rejection, and a passed `A` is no callable identity (`NotAnAlgorithm` at invocation).
- **Failure is not absence.** A projection failure (receiver, decode, ownership, route, callee, `DemandCycle`, cancellation, a resource limit) stays a failure with its kind, never absence, never an ordinary property and never a retry (NEED-06). A projection that re-enters its own active cell is `DemandCycle` (NEED-09), and a completed chain that leads back into itself is the alias-cycle `IllegalInEval`.
- **Members and open.** Written member access `A.K` through a transparent runtime reference reads its target's members, and a callable passed through it is its normalized target. A carrier keeps its own members, whether written or passed. For `open`, a runtime-target alias, through static chains and forward references too, is a namespace of its own declarations, and nothing of its target is imported or projected.

**Qualifications**
- Formula lifting runs first: `Mk(t) = …` / `A = Mk.Algorithm` is the formula `A(t) = Mk(t).Algorithm`, never a runtime alias.
- Under a closed list these rows are no aliases and no bare-forwarding targets: the row is an ordinary read (FWD-02).
- A declared member wins over the intrinsic in every position (DOT-01): a receiver that declares `Algorithm` makes the row an ordinary static path.
- A host-built alias over a runtime row is admitted before evaluation.

```katlang
Square(x) = x * x
Apply(f, x) = f(x)
Use(f) = {
  A = f
  A(9), 2.A, Apply(A, 4)
}
Use(Square)
```
⇒ `S[81, 4, 16]`

```katlang
Only(*xs) = tick()
Use(f) = {
  A = f
  B = A
  A, B, B(), A()
}
Use(Only)
```
⇒ `S[1, 1, 2, 3]`

```katlang
G(o) = tick()
Use(b) = {
  A = b.G
  A(), A, A(), A
}
Use(5)
```
⇒ `S[1, 1, 1, 1]`

`G` is the extension fallback here, a computed value, so every read answers one cell. With no lexical `G` the same miss is `UnknownName`: `Use(b) = { A = b.G` / `A }` / `Use(5)` is `UnknownName`, and `Use(b) = { A = b.G` / `A(3) }` / `Use(5)` is `ArityMismatch`. A value view is no callable: `Call(g) = g()` / `Use(f) = { A = f` / `Call(A) }` / `Use(5)` is `NotAnAlgorithm`.

```katlang
Capture(meta op) = op
Only(*xs) = tick()
R = Capture(Only())
A = R.Algorithm
A(), A, A(), A
```
⇒ `S[1, 1, 2, 1]`

The first call establishes `Only`'s entry and the bare reads share it. A receiver is demanded once for both channels: `Capture(meta op) = op` / `Only(*xs) = 7` / `Mk(t) = if(trace(t) > 0, Capture(Only()), 0)` / `A = Mk(5).Algorithm` / `A, A()` is `S[7, 7]` after one `trace(5)`.

Members follow the target, and a carrier keeps its own:

```katlang
Lib(*xs) = {
  public K = 99
  0
}
K(v) = 7
Navigate(f) = f.K
Use(f) = {
  A = f
  C = { public K = 5
    f }
  Navigate(A), A.K, Navigate(C), C.K
}
Use(Lib)
```
⇒ `S[99, 99, 5, 5]`

A runtime alias opens as its own namespace: `Outer(n) = {` / `Lib = { public X = 10` / `n }` / `P = { open Lib` / `X }` / `P + Lib` / `}` / `Outer(1)` is `11`. Failures keep their kind: `R = 5` / `A = R.Algorithm` / `A(9)` is `TypeMismatch`, and `Capture(meta op) = op` / `A = R.Algorithm` / `R = Capture(A(1))` / `A(2)` is `DemandCycle`.

## DOT — Dot syntax: member access, the `.string` intrinsic, and extension calls

A *dot edge* is `R.n` or `R.n(args)`, with *receiver* `R`. One structural lookup gives it one of three meanings: access to a declared *structural member*; on a *structural miss*, a dot-only intrinsic (`.string`, DOT-08; `.Invoke`, `.Arguments` and `.Algorithm`, CR-5, CR-8, CR-14); or otherwise *extension fallback*, also called dot fallback or lexical fallback, the route that makes `R.F(args)` the ordinary *extension call* `F(R, args)`. A *fluent receiver* (or spread receiver) `R*.F(args)` is not a dot edge: it is the written call `F(R*, args)`. The laws below fix which meaning an edge takes, how chains navigate, how the receiver reaches the callee, how dot edges take part in inference and Grace, and what a dot expression denotes on the algorithm channel.

### DOT-01 — A declared structural member wins; the extension call happens only on a structural miss

- This law covers every ordinary (non-spread) dot edge `R.n` or `R.n(args)`, whatever its member's spelling, `string` included.
- **Selection.** If the resolved receiver has algorithm identity and declares a member `n`, the edge denotes that member. "Declares" means the member is written in the receiver: `public` or not, a property or a callable. Selection is by declaration (RES-08).
- **Accessibility, checked afterwards.** A selected member that is not accessible from the site is a `LocalOnlyProperty` error, never a fallback. The main case is a member that depends on an owner activation the site does not have. A member defined only inside clause-family branches is the same error.
- **No argument list.** A selected member with no argument list is a zero-argument value demand of that member (CALL-05, PROP-04, VAL-06).
- **With an argument list.** A selected member called with arguments is an ordinary call of the member with exactly the written arguments. The receiver is not injected, and nothing of it is evaluated.
- **Miss.** Only when the receiver declares no `n`, or has no algorithm identity at all, does the edge become the extension call of DOT-03. On such a miss `string` is instead the number-to-text intrinsic (DOT-08), `Invoke` the call-reference intrinsic (CR-5), `Arguments` the argument-view intrinsic (CR-8), and `Algorithm` the callable-projection intrinsic (CR-14). An intrinsic takes the extension call's place, and no intrinsic's lexical name is consulted: `5.Algorithm` is `TypeMismatch`.
- Values without algorithm identity include numbers, strings, Booleans, lists, captures, call results and argument-bearing dot results.

**Qualifications**
- **Aliases.** A receiver's members are those of its structure. A transparent reference has its target's members. A structural forwarding carrier has only its own declarations, never its target's. A value-only runtime reference has no structure, so it is a value receiver (FWD-04).
- **Private members are reachable.** Structural dot reaches private members, including private members of a loaded module (`M.Priv`). `open` and dotted open steps provide only public members (MOD-05).
- **Branch-only members.** A family exposes no branch members, and a branch-only member is an error, not a miss, even when a lexical callable of that name is visible.
- **Call results never navigate.** `Mk.V` navigates a parameterized container without calling it, while `Mk(3).V` is the extension call `V(Mk(3))`.
- A member named `string` is an ordinary member (DOT-08).

```katlang
V(x) = 99
Obj = {
    public V = 42
    W = 7
    0
}
B(a, c) = a * 100 + c
Lib = {
    public B(c) = c + 1
}
Obj.V, Obj.W, 5.V, Lib.B(5), 3.B(5)
```
⇒ `S[42, 7, 99, 6, 305]`

`Obj.W` reaches the private `W`, `5.V` is `V(5)`, `Lib.B(5)` calls the member with no receiver, and `3.B(5)` is `B(3, 5)`.

```katlang
F(0) = { Q = 1
    0 }
F(n) = n
Q(x) = 99
F.Q
```
⇒ `LocalOnlyProperty`

```katlang
V(x) = x + 100
Mk(x) = { public V = 7
    x + 3 }
Lib = { public Q = 1 }
Ref = Lib
Car = { Lib }
Q(x) = 99
Mk.V, Mk(3).V, Ref.Q, Car.Q
```
⇒ `S[7, 106, 1, 99]`

```katlang
Lib = { public F(x) = x + 1
    trace(9) }
Lib.F(1)
```
⇒ `2`

There is no host event: only the extension fallback supplies the receiver as an argument.

### DOT-02 — Structural-first holds at every level of a chain, and navigation evaluates nothing

- A receiver that is itself an argumentless dot edge `X.M`, whatever `M`'s spelling (`string` included), is resolved by navigation:
  1. `X` is resolved the same way, recursively.
  2. If `X` declares `M`, the receiver is that member's algorithm, read through its structure (DOT-01). It is subject to the same accessibility and branch-only errors as DOT-01, which here are errors of that intermediate edge.
  3. Otherwise the inner edge is an ordinary dot result: a value. This happens when `X` lacks `M`, or has no algorithm identity. The chain then continues by extension fallback, so `3.A.B` is `B(A(3))`.
- Navigation is identity-only. No intermediate container's output is evaluated, and a parameterized container is navigated without being called.
- A parameter head is navigated through its supplied cell's callable projection, never its own VALUE. When that projection is a runtime one, such as a parameter bound to an `.Algorithm` link, it may demand the link's receiver cell (NEED-06, CR-15, CR-16).
- Some receivers are never navigated: an argument-bearing edge (`Lib.Sub().Q`, `Mk(3).V`) and a capture. Each is a value.
- A `.string` edge is navigated like any edge: it selects a declared member `string` (`Obj.string.Q`), and otherwise it is the intrinsic's value (step 3).
- The edges `Invoke`, `Arguments` and `Algorithm` behave alike: a declared member of that name is navigated, and otherwise member access never navigates through the intrinsic. So `R.Algorithm.n` is the extension call `n(R.Algorithm)` (CR-14).

**Qualifications**
- **An inaccessible intermediate is an error, never a fallback.**
- **Explicit empty arguments make the receiver a value.** `Lib.Sub().Q` is `Q(Lib.Sub())`.
- **A value-only runtime member** has no structure, so the edge that reads it is a dot result and the chain continues by fallback (FWD-04).
- **The higher-order channel is separate.** A dot chain used as a callable is covered by DOT-09.

```katlang
Lib = {
    public Sub = {
        public Q = 1
    }
}
Q(x) = 99
A = x + 7
B = x * 5
Lib.Sub.Q, (Lib.Sub).Q, 3.A.B, B(A(3)), Lib.Sub().Q
```
⇒ `S[1, 1, 50, 50, 99]`

```katlang
F(x) = { public Sub = { public Q = 5
        tick() }
    tick() }
Q(v) = 99
F.Sub.Q, tick()
```
⇒ `S[5, 1]`

Neither inner `tick()` runs, and `F` is never called.

```katlang
G(x) = { public Sub = { public Q = 1
        x }
    0 }
Q(v) = 99
G.Sub.Q
```
⇒ `LocalOnlyProperty`

### DOT-03 — Extension fallback passes the receiver as the ordinary leading argument: `R.F(args)` ≡ `F(R, args)`

*Formal evidence (2026-11-08, the Q-66 dot-funnel item): the end-to-end equivalence is PROVED over production Lean in this qualified form (`lean/KatLangArityLaws/DotFunnel.lean`, `dot_funnel`). After a receiver probe that completes with an extension miss (a structural miss whose name is not an intrinsic), for a receiver that is not a spread (`R*.F` is lowered to `F(R*)`) and an elaborated name fallback, `R.F(args)` run from the probe's entry state and the written call `F(R, args)` run from the probe's exit state are both incomplete, or both complete with the same final state and the same value, or the same inner error under their own context frames (the dot-call frame and the call frame). Incomplete runs are related by outcome only. When their fallback resolves to the prelude builtin and every supplied slot is non-spread (including the count `n`), the loop spellings `Step(x).repeat(n)` and `Step(x).while` reach the ordinary `repeat` and `while` arms over the same supply cells (`dot_repeat_funnel`, `dot_while_funnel`). The C# side is tested (`DotCallValueBoundaryTests`), not proved.*

- On a structural miss (DOT-01, DOT-02), `R.F(a₁, …, aₙ)` behaves exactly as the written call `F(R, a₁, …, aₙ)`, and `R.F` exactly as `F(R)`.
- **One call assembly.** The original receiver expression becomes the first written argument slot of the one shared call assembly, and dispatch takes the one call route. No callee shape is inspected, and no receiver-specific supply, binder or builtin path exists.
- **An ordinary supplied computation.** The receiver is supplied like any argument (CALL-02, NEED-01, NEED-03). A non-spread receiver is evaluated at most once, when the callee first demands its VALUE, and never if nothing demands it. The receiver and the written arguments are demanded in the callee's own order, not receiver first. A spread receiver `R*` is opened while the supply is formed, like every explicit spread (DOT-07, NEED-07).
- **The receiver is one argument, whatever its value** (a scalar, a sequence, a list, `()`, `[]`, a block, a property, a call result, a selection):
  - its item count never satisfies arity;
  - a fixed parameter binds it whole;
  - a collecting parameter collects it as one item (VAR-01);
  - a builtin binds it as its ordinary `collection` or value argument, judged by the zero-argument value-demand law and read through the property cache exactly like `count(A)` (COLL-02, CALL-05, PROP-05);
  - a META builtin's `meta` parameter captures it exactly as it would capture the written argument, so `Step(0).while` is `while(Step(0))`, while a property receiver `Start.while` is the ordinary META refusal (CR-2, CR-17).
- **Same observables on every path.** Value, emitted count, error kind, caching and host effects equal those of the written call on every execution path (RUN-01).
- **Static validity.** Where the fallback is statically certain (DOT-05), the dotted call also has the written call's static validity: under a closed list or in a branch body its fallback name is checked exactly like the written callee name.

**Qualifications**
- **An empty value is one argument.** `One(a) = 1` / `().One` is `1`. Only `()*` supplies nothing.
- **A receiver that names a callable** is passed on both channels, exactly as the written argument would be: `Inc(x) = x + 1` / `Apply1(f) = f(1)` / `Inc.Apply1, Apply1(Inc)` is `S[2, 2]`.
- **The equivalence holds on both channels.** Used as an argument or as a callee, an argumentless structural path is its member (DOT-01, DOT-09), and every other dot expression, an extension-call result among them, is a value with no callable identity, exactly like the written call.
- **A runtime-decided receiver** (a parameter) is projected for its callable identity only, never VALUE-demanded to choose the route (NEED-06). The fallback then supplies it unevaluated: `Ign(x) = 0` / `G(p) = p.Ign` / `G(trace(1))` is `0`, with no host event.
- **Not covered.** The `.string` intrinsic (DOT-08), the call-reference intrinsics `.Invoke`, `.Arguments` and `.Algorithm` (CR-5, CR-8, CR-14) and structural members (DOT-01) are not extension calls. A dot edge is never the `load` directive (MOD-07): `load(x) = x + 1` / `5.load` is `6`, while the written `load(5)` is the directive.
- **Captured extension calls.** A `meta` parameter captures an argument-bearing extension edge as the written call it is. The plan of `5.Add(1)` is that of `Add(5, 1)`, with the receiver as its first supplied cell, so `R.Arguments.count` counts it and `R.Invoke()` runs `Add(5, 1)` afresh (CR-9, CR-10).
- The equivalence is about the call. The occurrence order an inferring body reads from the two spellings differs (DOT-05).

```katlang
Add(x, y) = x + y
Coll(*xs) = xs
Sub(a, b) = a - b
10.Sub(3), Sub(10, 3)
(1, 2)*.Add
(1, 2).Coll, Coll((1, 2))
(1, 2)*.Coll
[1, 2].Coll
().Coll, ()*.Coll
(1, 2).Coll(3)
```
⇒ `S[7, 7, 3, L[S[1, 2]], L[S[1, 2]], L[1, 2], L[L[1, 2]], L[S[]], L[], L[S[1, 2], 3]]`

- `Add(x, y) = x + y` / `(1, 2).Add` is `ArityMismatch`, exactly like `Add((1, 2))`.
- `Coll(*xs) = xs` / `A = ((1, 2), 3)` / `A[0].Coll, Coll(A[0])` is `S[L[S[1, 2]], L[S[1, 2]]]`.
- `A = tick()` / `A.sum, sum(A), A` is `S[1, 1, 1]`, with one tick.
- `Second(a, b) = b` / `trace(1).Second(trace(2))` is `2`, with host log `[trace(2)]`: the receiver is never demanded.
- `Flip(a, b) = b + a` / `trace(1).Flip(trace(2))` is `3`, with host log `[trace(2), trace(1)]`: the callee's demand order, not receiver first.
- `Second(a, b) = b` / `trace(1).Second(trace(2), trace(3))` is `ArityMismatch` with no host event: cardinality is checked before any demand, the receiver's included.
- `Twice(a, b) = a + a + b` / `tick().Twice(10)` is `12` after one tick: demanded at most once.
- `Third(a, b, c) = c` / `trace((1, 2))*.Third(trace(3))` is `3`, with host log `[trace(S[1, 2]), trace(3)]`: a spread receiver is formed with the supply.
- `B = tick()` / `Ign(x, y) = y` / `B.Ign(5), B` is `S[5, 1]` after one tick, at the root read: an unused property receiver performs no access (NEED-10).

### DOT-04 — The fallback callee is resolved by ordinary callable resolution; a missing member on a known receiver falls back like any other

- In an extension call, the callee `F` is the name `F` resolved exactly as the callee of a written call `F(…)` at the same site:
  1. the owner walk, which covers parameters (algorithm-valued parameters included), properties, and the prelude (builtins, Math aliases, host operations; RES-01);
  2. then opens (RES-02);
  3. then promotion to an implicit parameter (RES-04).
- The front end decides this identity once, as a lexical name or a parameter, and the evaluator consumes that decision. Neither reconstructs it from spelling.
- A receiver that is statically known but lacks the member falls back exactly like a runtime receiver. Examples are `Math`, a block and a loaded module. The fallback is valid when a lexical callable of that name is visible. Otherwise the name is promoted like a bare name in an inferring body, and under a closed list or in a branch body it is the written callee name's `UndeclaredIdentifier` (DOT-05).
- Static receiver knowledge never shapes selection. It shapes diagnostics (report wording, member suggestions, member-token positioning) and decides only whether the fallback is statically certain. No layer may branch on the receiver's spelling.

**Qualifications**
- `Math.cos(1)` is `ArityMismatch`, expected 1 and actual 2: it is `cos(Math, 1)`, not an unknown-member error, because `Math` has no lowercase members.
- **Missing member without a lexical callable.** At an inferring root, `Lib.Dubel(4)` promotes `Dubel` to an implicit parameter of the root, so the run reports `UnresolvedImplicitParams` for a program that supplies none.
- **Open ambiguity.** A fallback name that reaches an open level with two providers is `AmbiguousOpen`: at the front end when the fallback must be selected, at run time when it only may be (RES-03).

```katlang
D(a, t) = a.t
K(a, t) = t(a)
Lib = { public Double(x) = 2 * x }
Dubel(a, b) = b * 3
Ceiling(a, b) = b * 2
D(7, {a + 1}), K(7, {a + 1}), Lib.Dubel(4), Math.Ceiling(2.1), Lib.Double(4)
```
⇒ `S[8, 8, 12, 4.2, 8]`

`Lib.Dubel(4)` is `Dubel(Lib, 4)`, and `Math.Ceiling(2.1)` is `Ceiling(Math, 2.1)`.

`0.5.cos == cos(0.5), cos(0.5) == Math.Cos(0.5)` is `S[true, true]`.

### DOT-05 — In parameter inference a dot edge contributes receiver, then member (only if the fallback may be selected), then arguments; a closed list checks a certain fallback name

*C#-only by design.*

- When an algorithm's implicit signature is inferred (PAR-03, PAR-05), a dot edge contributes free-name occurrences in this order:
  1. its receiver;
  2. its member name, as the lexical-fallback occurrence, only when the fallback may be selected at run time. This holds when the receiver statically lacks the member, or when its algorithm identity is not statically known (a parameter, an unresolved name);
  3. its written arguments.
- Some members never contribute: a member the receiver statically declares, a branch-only member, a member of a receiver that statically fails, and the dot-only intrinsic edges `.string`, `.Invoke`, `.Arguments` and `.Algorithm`.
- The order is source order and is independent of the run-time invocation order `t(receiver, args)`. `K = a.t(b)` infers `(a, t, b)`, while `K = t(a)` infers `(t, a)`.
- The fluent receiver is no dot edge: `a*.t(args)` is the written call `t(a*, args)` (DOT-07) and contributes in call order. So `K = a*.t` infers `(t, a)`, while `K = a.t` infers `(a, t)`.
- Under a closed explicit parameter list or in a clause-branch body nothing is inferred, and the member name is checked exactly when the fallback must be selected: a value receiver, or a statically known receiver that declares neither the member nor a branch-only member. An undeclared one is `UndeclaredIdentifier` at the member token, whether or not the definition is called.
- A fallback that only may be selected is not checked. The run-time receiver may supply the member, and a run-time structural miss with no resolvable callee is a run-time error.

**Qualifications**
- **A receiver decided by inference.** A receiver's structure may depend on what inference and lifting leave a body, such as a navigated body whose head is its own input, or an `.Algorithm` link body that keeps an input (PAR-08). Such a receiver counts as known once that is decided: where it certainly lacks the member, the fallback must be selected and the closed-list check applies. This refinement turns *may* into *must*, never into *never*, so inferred signatures do not change.
- **Parameter-rooted member paths.** A parameterless open body whose one row is an argumentless member path rooted at an enclosing parameter (`A = b.C`) infers no member name: it is a runtime member reference (FWD-03). Nothing else is exempt: the bodies `A = b.C + 1` and `A = b.C(1)` contribute `C`.
- **`load`.** A fallback named `load` that nothing binds is never inferred. One that must be selected is `UnboundLoadReference`, and one that only may be selected stays a run-time question (MOD-07).
- **A marked receiver call.** An extension edge whose receiver is a written call to a declaration marked with `*` is no dot edge for this order: from parameter detection onward it is the lowered call `F(R*, args)`, which contributes in call order (SUP-08). With `A(x, y)* = x, y`, `H = A(x, y).F(3)` infers `(F, x, y)`.
- This is own-occurrence order, before lifting. Names lifted from callees follow it (PAR-05), and the lifting roles of a dot edge are PAR-07's.

```katlang
K = a.t(b)
K(7, {x - y}, 1)
```
⇒ `6`

```katlang
K = Obj.V
Obj = { public V = 42 }
Get(obj) = obj.size
Box = { public size = 3 }
K, Get(Box)
```
⇒ `S[42, 3]`

`K` takes no parameter. Under the closed list, `Box` supplies the member at run time.

```katlang
Box = { G(x) = x * 10 }
Use(b) = { A = b.G
    A(3), 3.A }
Use(Box)
```
⇒ `S[30, 30]`

- `K = a*.t` / `K({x + 1}, 5)` is `6`.
- `Get(obj) = 5.size` is `UndeclaredIdentifier`, the same verdict as `Get(obj) = size(5)`.
- `F(x) = Math.Ceiling(x)` is `UndeclaredIdentifier`, reported at the member. Its diagnostic suggests `Math.Ceil`.
- `Get(obj) = obj.size` / `Get(5)` is `UnknownName`, only at run time.
- `A = x` / `Get(o) = A.size` is `UndeclaredIdentifier`: `A` is a calculation with an inferred input, so it certainly has no such member.
- `5.load` is `UnboundLoadReference`, and `G = u.load` / `G(5)` is `UnknownName`: `G` infers only `u`.

```katlang
F(0) = 5.size
F(n) = n
F(1)
```
⇒ `UndeclaredIdentifier`

The branch is checked whether or not it is ever selected.

### DOT-06 — Grace on a dot edge (`a~.t`, `a.~t`) only reorders inferred parameters; it never changes dispatch

*C#-only by design.*

- Grace combines with a dot edge in two ways. Each is ordinary Grace (PAR-06):
  - `a~.t` is postfix Grace on the bare receiver name, followed by an ordinary dot;
  - `a.~t` is an ordinary dot with prefix Grace on the member (fallback) occurrence.
- Both elaborate to the same executable dot edge as `a.t`. Only the enclosing algorithm's inferred parameter order may differ: from the base order `(a, t)` (DOT-05), both reach `(t, a)`. Structural-first selection, fallback and `.string` are therefore unaffected.
- Grace requires an inferred parameter (PAR-06). On a receiver or member whose binding is already fixed it is `InvalidGraceMarker`. That covers an explicit or captured parameter, a visible property, a member the receiver structurally owns, a dot-only intrinsic edge (`.string`, `.Invoke`, `.Arguments`, `.Algorithm`), and any occurrence on a closed level (a closed list, a clause branch's own rows).
- A free receiver that cannot move, the lone `o` in `Read = o~.V`, is valid saturation.
- Postfix Grace applies to one bare name, so on a compound receiver, a chain's second `~.` included, it is `InvalidGraceMarker`. Prefix member Grace stays eligible because it decorates the bare member occurrence.
- There is no dotless form: `a~t` is two unseparated same-line items.

```katlang
V(x) = 99
Obj = { public V = 42
    0 }
Read = o~.V
K = a~.t
J = a.~t
Obj.V, Read(Obj), Read(5), K({a + 1}, 7), J({a + 1}, 7)
```
⇒ `S[42, 42, 99, 8, 8]`

The graced edge still reads `Obj`'s own `V`, and a number still falls back.

These are parse failures:
- `K(a, t) = a~.t` is `InvalidGraceMarker`: `a` is an explicit parameter.
- `Obj = { public V = 42 }` / `Obj~.V` is `InvalidGraceMarker`: the receiver is a visible property.
- `Obj = { public V = 42 }` / `K = Obj.~V` is `InvalidGraceMarker`: `Obj` structurally owns the member.
- `K = a.~string` is `InvalidGraceMarker`.
- `K = a.b~.c` is `InvalidGraceMarker`, while `K = a.b.~c` is valid.
- `K = a~t` is `UnseparatedSameLineItem`.

`K = a~.string` / `K(5)` is `'5'`: the intrinsic is unchanged.

### DOT-07 — A fluent receiver `R*.F(args)` is exactly the lexical call `F(R*, args)`; a grouped spread `(R*).F` is a capture receiver; a redundant group is erased

- **Fluent receiver.** `R*.F(args)` is the fluent spelling of the written lexical call `F(R*, args)`. The receiver's items are supplied as separate leading argument items, one boundary (SUP-02). Structural lookup and the dot-only intrinsics never apply to a spread receiver: `F` is always the lexical callable `F`. Its parameter inference is the written call's: callee first, then the receiver (DOT-05).
- **Grouped spread.** The parenthesized form `(R*).F` is an ordinary dot edge on a capture: one value, with no structural members and no algorithm identity (SUP-07). It is therefore the extension call `F((R*))`.
- **Redundant group.** A redundant group (one slot, not a spread) around a receiver is erased: `(E).M` is `E.M`, and it navigates exactly as `E` does (SYN-06).

**Qualifications**
- **`R*.string` is not the intrinsic.** It is the lexical call `string(R*)`. Without a user `string`, it is an ordinary unresolved name.
- **Multi-slot group receivers.** A receiver such as `(1, 2).F` is also a capture: one value (DOT-03).

```katlang
Add(x, y) = x + y
Coll(*xs) = xs
A = (1, 2)
A*.Add
A*.Coll, (A*).Coll, Coll((A*)), (A)*.Coll, A.Coll
```
⇒ `S[3, L[1, 2], L[S[1, 2]], L[S[1, 2]], L[1, 2], L[S[1, 2]]]`

`Add(x, y) = x + y` / `A = (1, 2)` / `(A*).Add` is `ArityMismatch`.

```katlang
V(x) = x + 99
Obj = { public V = 7
    0 }
Obj.V, Obj*.V, (Obj*).V, (Obj).V
```
⇒ `S[7, 99, 99, 7]`

The fluent and capture receivers never see the member.

```katlang
string(x) = 99
A = 5
A.string, A*.string, string(A)
```
⇒ `S['5', 99, 99]`

`A = 5` / `A*.string` is `UnresolvedImplicitParams`.

### DOT-08 — `.string` is a dot-only, zero-parameter intrinsic, selected on a structural miss

- An ordinary (non-spread) dot edge spelled `string` whose resolved receiver declares no member `string` (and no branch-only one) is the number-to-text intrinsic. It takes the extension call's place (DOT-01), and `Invoke`, `Arguments` and `Algorithm` are the other structural-miss intrinsics (CR-5, CR-8, CR-14). A receiver that declares a member `string` selects that member.
- **Receiver.** The receiver is demanded as a zero-argument value under the one zero-argument value-demand law (CALL-05). A named property is read through its binding's ordinary cached access (PROP-05), an alias through the binding it reads (FWD-03), and a parameter through its bound value (CALL-06). A callable that needs arguments is that law's `ArityMismatch`.
- **Kinds.** Only a number converts. Any other value kind is `TypeMismatch`.
- **Arguments.** The intrinsic accepts exactly zero supplied arguments: `x.string` writes no argument list and `x.string()` an empty one, and neither supplies an argument. The route is decided first: the receiver's structural lookup, which evaluates nothing, selects the intrinsic. A written argument list then follows NEED-05's run-time order, like every callee's. The intrinsic has no order of its own:
  - **Supply formation.** The list is formed like any call's supply (CALL-02).
  - **Spread execution.** An explicit arbitrary spread executes while the supply is formed and supplies its items. Its failure is raised there, before the cardinality check (SUP-02).
  - **Suspension.** Every ordinary non-spread slot stays a suspended computation, and nothing demands it.
  - **Cardinality.** A supply of one or more items is rejected with `ArityMismatch` before the receiver or any ordinary argument is demanded. The rejection demands neither.
  - **Receiver VALUE demand.** Only a supply of zero items (no written list, an empty one, or spreads that supply no item) reaches the intrinsic, which then demands its receiver's VALUE and converts it.
  - **Extension fallback is a different route.** `R.F(args)` is the call `F(R, args)`, whose callee demands its arguments, the receiver among them, in its own demand order (DOT-03). Neither route has an argument-first or a receiver-first rule.
- **Never an extension call.** A user-declared `string(x)` is not consulted by `x.string`.
- **Text.** The result is a string value holding the number's canonical positional text, which OP-14 fixes. Strings compare exactly (VAL-02), so this text is semantics, not presentation.
- **Representation.** `.string` exposes representation that `==` ignores (VAL-11): `1.0 == 1, 1.0.string == 1.string` is `S[true, false]`.

**Qualifications**
- **A declared member `string` wins.** `Obj = { public string = 5 }` / `Obj.string` is `5`. A declared member without output reports its own missing output: `Obj = { public string = { X = 1 } }` / `Obj.string` is `MissingOutput`.
- **A user `string` does not pre-empt the intrinsic.** `string(x) = 99` / `3.string, string(3)` is `S['3', 99]`.
- **Fluent receiver.** `A*.string` is the lexical call (DOT-07).

```katlang
A = tick()
A.string, A, A.string, 2.string, (3 + 4).string, 1.5.string
```
⇒ `S['1', 1, '1', '2', '7', '1.5']`

There is one tick.

- `Inc(x) = x + 1` / `Probe(u) = Inc.string` / `Probe(0)` is `ArityMismatch`: under a closed list the receiver is the zero-argument value demand.
- `Inc(x) = x + 1` / `Inc.string` is `UnresolvedImplicitParams`: at the inferring root the receiver has a value role, so the root lifts `Inc` and gains a parameter (PAR-07).
- `true.string` is `TypeMismatch`.
- `trace(5).string(tick())` is `ArityMismatch` with no host event: cardinality rejects the call before the argument or the receiver is demanded.
- `trace(5).string([trace(6)]*)` is `ArityMismatch` after `[trace(6)]`: the explicit spread is formed first.
- `trace(5).string(trace(())*)` is `'5'`, with host log `[trace(S[]), trace(5)]`: a supply of zero items is the intrinsic itself, and the receiver is demanded after formation.
- `trace(5).string` and `trace(5).string()` each give `'5'` with host log `[trace(5)]`.

### DOT-09 — A dot expression carries one callable identity in every position: a structural path is its member, everything else is a value

*Resolved (2026-11-10 record; audit finding C-1, fixed in `a4181877`): C# follows Lean and this law. For a value-only runtime member, `(Box.A)()` and `(Box.A)(1)` are the member calls `Box.A()` and `Box.A(1)` in C# (`Evaluator.ResolveNoIdentityDotCallee`) as in Lean (`resolveCalleeAlgWith`); C# `GroupedRuntimeMemberCallTests` and the `grouped-runtime-member-*` spec cases pin it. Previously C# gave `NotAnAlgorithm` for both.*

- This law is the sole owner of the dot-identity law. A dot expression `R.M` or `R.M(args)` carries one callable identity in every algorithm-capable position: a supplied argument of a user call, forwarded through further parameters; a builtin callback slot (`map`, `filter`, `reduce`); a loop step, which is the callee of the captured step call, so in `Lib.Step(0).repeat(2)` it is the member path `Lib.Step` (CR-13, CR-17); and the callee of a call written on a grouped dot expression, `(R.M)(args)`.
- That identity is the callable projection (NEED-06), an identity-only structural navigation. Which observation is made is the consumer's choice (ALG-10).
- **A structural path is its member.** An argumentless dot path whose every edge selects a declared structural member (DOT-02, with its accessibility check) carries that member's own callable: its identity, its parameters, its clauses and its members. A member that is a transparent reference carries its target, and a structural forwarding carrier carries itself (FWD-03). Invoking it is the member's ordinary fresh call. Transport keeps that one identity, so every supply of one member, written dotted or opened, is the same callable, and `(R.M)(args)` is `R.M(args)`.
- **Anything else is a value.** An argument-bearing edge `R.M(args)`, an edge resolved by lexical fallback, and an intrinsic edge other than `.Algorithm` are calculation values (the result boundary): they have no callable identity, and invoking one is `NotAnAlgorithm`.
- **The one exception** is the `.Algorithm` intrinsic on a call reference of the current run. In every algorithm-capable position its identity is the runtime projection of the reference's captured callee (CR-13, CR-15), and a projection failure keeps its kind (NEED-06). Its bare VALUE is that callee's ordinary VALUE, never a callable result, and `R.Algorithm(args)` is a fresh call.
- **VALUE is separate.** Projection never demands the projected expression's VALUE. A VALUE demand of the same expression is the ordinary dot-call value (DOT-01, DOT-03), a structural member being read through its property cache. `(R.V)()` is the fresh call `R.V()`: it never reads or replaces `R.V`'s entry, and its owning success may establish an empty entry (PROP-06).
- **Parentheses never change identity** (SYN-06), and a call is written only after a callable reference (SYN-09), so `R.M(a)()` is a parse error.
- **No Math exception.** A qualified `Math.X` is an ordinary structural member reference of the prelude `Math` module, the same callable as the opened `X`. The lowercase alias stays a distinct binding (OP-11).
- **Receiver position is different.** There, DOT-02 navigation applies. A dot result used as a receiver is a value, and no internal carrier of it is ever a program-visible callable.

**Qualifications**
- A member that is a value-only runtime reference has no callable identity when passed on (FWD-04).
- `(F)(1)` is `F(1)` for every callable reference (SYN-06), a dotted callee included.
- `X.Mk(1)()` is `UnseparatedSameLineItem` exactly like `Mk(1, 1)()`: the parser admits a call only after a name, an argumentless dot edge or Grace.
- **META capture is a separate channel.** A `meta` parameter captures an argument-bearing edge (`Box.G(1)`, `Box.V()`, `5.Add(1)`) as a written invocation whose route is DOT-01's one dot decision. A member route's callee is the argumentless path, carrying this law's identity (CR-2, CR-13). An argumentless edge (`Box.G`, `5.Inc`) is never captured. Capture yields a call reference, not a callable identity, so the value clause above is unchanged.

```katlang
Box = { public G(x) = x * 10 }
Apply(f, v) = f(v)
Lib = { public F(x) = x + 1 }
Box.G(2), (Box.G)(2), Apply(Lib.F, 5), map([1, 2], Lib.F), Lib.F(0).repeat(2), Apply(Math.Abs, -5)
```
⇒ `S[20, 20, 6, L[2, 3], 2, 5]`

```katlang
Box = { public V = tick() }
Box.V, Box.V(), (Box.V)(), Box.V(), Box.V
```
⇒ `S[1, 2, 3, 4, 1]`

The grouped call is fresh, and the first read's entry survives.

```katlang
Sub3 = { public Q = 1
    0 }
Lib = { public Sub = { public Q = 1
        0 } }
Q(x) = 99
F(p) = p.Q
Inner = { public T = { public Q = 2
        0 } }
Lib2 = { public R = Inner.T
    public C = { Inner.T } }
F(Sub3), F(Lib.Sub), F(Lib2.R), F(Lib2.C)
```
⇒ `S[1, 1, 2, 99]`

A parameter bound to a structural path keeps the member's members. `Lib2.R` carries its target, while `Lib2.C` is a carrier that declares no `Q`, so the edge falls back.

- `Twice(f) = f() * 2` / `Sub(a, b) = a - b` / `Twice(10.Sub(1))` is `NotAnAlgorithm`, exactly like `Twice(Sub(10, 1))`.
- `Inc(x) = x + 1` / `(5.Inc)()` is `NotAnAlgorithm`.
- `Call0(f) = f()` / `Call0(5.string)` is `NotAnAlgorithm`.
- `Lib = { public V = tick() }` / `Call0(f) = f()` / `Call0(Lib.V), Call0(Lib.V), Lib.V` is `S[1, 2, 1]`: each supplied call is fresh, and the first establishes the empty entry.

## RES — Name resolution and ownership

KatLang decides what every written name denotes by one ordered model, the same in every layer. The **owner walk** searches outward over owning scopes, asking parameters before properties at each level, with the **prelude** as the outermost property level. `open` **providers** are consulted only after the whole walk, level by level, and a name that neither supplies is **promoted** to an implicit parameter. **Selection** picks a declaration by visibility alone, and **accessibility** of the selected member is checked afterwards. Lean models the runtime lookup chain, open ambiguity and accessibility and states the owner walk over hand-supplied chains; front-end elaboration, exposure classification and editor tooling are C#-only.

### RES-01 — The owner walk: the nearest owning scope that declares a name decides

*Open: whether to state a rename-invariance law, with its exclusions (Q-44).*

- A bare-name occurrence resolves by walking outward over its owning scopes, in this order: the body the name is written in; each enclosing algorithm body or clause-branch body; the program root; and the prelude, the outermost property level, which holds the builtins, `Math`, the Math aliases and the run's host operations.
- At each level two kinds of declaration are asked, in this order: first the parameters that level binds for name resolution (written, inferred, collecting, pattern or grouped captures, or clause-branch binders); then the properties it declares, of any visibility.
- A parameter that automatic parameter forwarding added is never asked: it belongs to the level's call interface, not to what a written name can denote (PAR-07).
- The first level that declares the name decides, and farther levels are never consulted. So a captured ancestor parameter beats a same-named property of any farther owner, root and prelude included; of several same-named enclosing parameters the nearest wins; and a nested property hides an outer one.
- Nesting depth adds no barrier to the walk. A reference written directly in an algorithm's body and one written in a body nested inside it select the same binding when the owner walk selects a declaration and no level between them, the nested body included, declares the name.
- Names compare exactly (case-sensitive), and no naming convention decides what a name is.

**Qualifications**
- Opens are not levels of this walk (RES-02). If the name is left to the opens, an open of the nested level is consulted first (RES-03): `F = {` / `open { public x = 1 }` / `x + {` / `open { public x = 5 }` / `x` / `}` / `}` / `F` gives `6`. An inline `{ … }` open target and a loaded module are rooted at the prelude and are not nested bodies in this sense (MOD-06, MOD-08).
- "Parameter before property" at one level matters only in invalid source, because such a pair is a declaration error (RES-05). Recovery trees still select the parameter deterministically; that is editor behaviour only.
- Which channel a bound parameter occupies, and that it shadows caller bindings on every channel, is PAR-01's law.
- Indentation is not nesting. `Inner = v + 1` / `Outer(v) = Inner` / `Outer(7)` is `8` because `Outer`'s lone bare row reuses its own parameter `v` by name (FWD-02), not through ownership.

```katlang
v = 99
Outer(v) = {
    Mid = {
        Inner = v + 1
        Inner
    }
    Mid
}
B(0) = 0
B(v) = {
    Inner = v + 1
    Inner
}
F(pi) = { pi + 1 }
count = 7
Outer(7), B(7), F(2), count
```
⇒ `S[8, 8, 3, 7]`

The parameter `v` beats the root `v` through two nested levels, a clause-branch binder owns its name the same way, a parameter named `pi` beats the prelude alias, and the root `count` beats the builtin. `x = 1` / `X = 2` / `F = Rate * 2` / `x + X, F(5)` gives `S[3, 10]`: names are case-sensitive, and the capitalised free name `Rate` is inferred like any other.

### RES-02 — `open` is consulted only after the whole owner walk; an opened name never overrides anything owned

- The `open` providers are consulted only when no owning level of RES-01, prelude included, declares the name.
- They are consulted level by level, from the innermost opening algorithm outward, so an inner level's opens come before an outer level's. Each target contributes only its public members.
- An opened name therefore never overrides a parameter of any enclosing owner that binds the name for name resolution (RES-01), a property of any enclosing level, the root's included, or a builtin, a Math alias or a host operation.
- A parameter that automatic parameter forwarding added binds no written name (PAR-07), so it does not stop the search: `Lib = { public v = 99 }` / `Need(v) = v` / `Outer = {` / `open Lib` / `v + Need` / `}` / `Outer(7)` is `106`.

**Qualifications**
- What an open target may be, how its head resolves, and why a provider must need no call are MOD-02 to MOD-04.
- Private members are never provided (RES-04, RES-08).
- Opened members evaluate in their own declaring chain, not the opener's (RES-07).
- A Math alias and an opened canonical Math member are distinct bindings (OP-11).

```katlang
V = 9
Lib = {
    public count = 101
    public trace(x) = 100
    public V = 1000
    public v = 99
    public W = 3
}
A = {
    open Lib
    count([1, 2, 3]) + W
}
Outer(v) = {
    open Lib
    Inner = v + V
    Inner + trace(0)
}
A, Outer(7)
```
⇒ `S[6, 16]`

In `A`, the prelude `count` (3) beats the opened `count`, while `W` comes from the open. In `Outer`, the parameter `v`, the root `V` and the host operation `trace` all beat the opened members of the same names.

### RES-03 — At the deciding open level one provider selects; two or more providers are an error, never a fall-through

- Opens are searched innermost level first, and the first level at which any target publicly provides the name decides.
- One provider selects its member, subject to RES-08.
- With two or more providers the name is the error `AmbiguousOpen`. The search does not continue to an outer level, and it never falls back to promotion.
- Written targets of one `open` list that resolve to the same provider count once, and the first occurrence names it. The same provider means the same declaration in the same declaring scope and activation, the callable identity of ALG-07. Spelling and position decide nothing: `open A, A`, `open M, (M)`, `open Sub, Lib.Sub` for one declaration, and `open 'u', 'u'` (one module, MOD-09) are one provider each. Two separately written inline blocks are two providers even when their text is identical, and so is any path headed by one (`open { ... }.S`).
- A transparent reference is its target's provider. A forwarding carrier provides only its own public declarations, and a runtime reference stays a namespace of its own (FWD-03, FWD-04).
- A written name occurrence that reaches a level with two or more providers is the front-end error `AmbiguousOpen` at the occurrence, whether or not evaluation demands it: a never-read property and an unselected `if` branch count alike. A must-selected dot-fallback name counts (DOT-05); a dot member that resolves structurally never does. The overlap itself is valid source: nothing is reported for a name nobody writes.
- Only a lookup the front end cannot decide, a may-selected dot fallback or a host-built tree, raises the run-time `AmbiguousOpen`.
- Exposure analysis follows the same rule per level: a sole provider charges its member's requirements, and an ambiguous level charges nothing. The verdict therefore never depends on the order of targets in the list.

**Qualifications**
- An owned declaration of the name at any level wins before opens are consulted (RES-02).
- Private members are not providers at all, so `open Pub, Lib`, where `Lib.X` is private, reads `Pub.X`.
- Local-only members are providers regardless of accessibility (RES-08).
- A bare `load` is checked by its own rule (MOD-07): two providers of a member named `load` keep the run-time `AmbiguousOpen`, raised only if the name is read.

```katlang
A = { public X = 1 }
B = { public X = 2 }
F = {
    open A, B
    X
}
F
```
⇒ `AmbiguousOpen`

Replacing the row `X` by `5` makes the program valid. Adding a root `open C` with `C = { public X = 3 }` changes nothing, because the inner level decides.

```katlang
open A
A = { public X = 1 }
B = { public X = 2 }
Carrier = { A }
Alias = A
G = {
    open Alias, A, A
    X
}
H = {
    open B
    X
}
I = {
    open Carrier
    Y
}
G, H, X, I(5)
```
⇒ `S[1, 2, 1, 5]`

`Alias` and the duplicate `A` are one provider, and the inner `open B` beats the root's `open A`. `Carrier` provides nothing of `A`.

### RES-04 — A name becomes an implicit parameter only when nothing declares it and no open provides it

- Promotion is the last resort, after RES-01 and RES-02. A bare name is promoted to an implicit parameter only when no owning level, prelude included, declares it and no `open` provides it.
- A name that an open provides is never promoted, even ambiguously (two providers) or as a member inaccessible from the site. A written use of an ambiguous name is then the front-end ambiguity error (RES-03), and reading an inaccessible member the accessibility error (RES-08).
- A private member of an opened target is not provided, so its name is promoted exactly like an undeclared one.
- Promotion is the only way a written name becomes a new parameter. Automatic parameter forwarding (PAR-07) adds a parameter only for a callee's genuinely unbound dependency, when no parameter binding of that name is available, and that parameter never becomes what a written name denotes: `Need(v) = v` / `Outer = {` / `F(0) = 0` / `F(n) = v` / `F(1) + Need` / `}` / `Outer(5)` is `UndeclaredIdentifier`, in the closed branch body, although `Outer` receives a forwarded `v` for `Need`.
- PAR-03 owns where a promoted name lives: the outermost inferring level (an algorithm without a written parameter list) whose own rows use it, a nested level seeing it as a captured ancestor parameter, while a name used only inside a nested level is claimed by that level. PAR-04 and PAT-04 own the front-end error under a closed parameter list or in a clause-branch body, and PAR-05 and PAR-07 own inference order and lifting.
- Whether a name is an input can depend on that same answer, through a receiver or open provider whose structure depends on what the body infers. A body with such a name and no well-founded answer is the front-end error `SelfDependentInferredParameters`, one report per body, listing the undecided names in first-occurrence order. A written parameter list closes the question. Recursive signature completion is PAR-08's.

**Qualifications**
- A dot edge's member name is an occurrence under DOT-05's selection rule, which also exempts a parameter-rooted member reference.
- A bare `load` is never promoted. Unless a real binding or an opened member supplies it, it is `UnboundLoadReference` (MOD-07).
- A free name inside a nested block of a closed-list algorithm is promoted in the outermost list-less level below the closed list whose own rows use it (PAR-03), and the closed list never gains it (PAR-04). `F(a) = {` / `H = {` / `public G = y * 2` / `y + a` / `}` / `H.G(4)` / `}` / `F(1)` is `LocalOnlyProperty`, because `H` claims `y` (RES-08). Used in a formula, `F(a) = {` / `Inner = y + a` / `Inner + 0` / `}` / `F(1)` is `ArityMismatch`, the run-time zero-argument demand. Written as the lone bare row, `F(a) = {` / `Inner = y + a` / `Inner` / `}` / `F(1)` is `UnforwardableParameter`, because that row is bare forwarding (FWD-02).
- A promoted root name has no caller, so the root reports `UnresolvedImplicitParams` (PAR-03).

```katlang
F = x + 1
Lib = {
    public x = 10
}
G = {
    open Lib
    x + 1
}
Priv = {
    x = 10
    public Y = 1
}
P = {
    open Priv
    x + 1
}
F(4), G, P(4)
```
⇒ `S[5, 11, 5]`

In `F`, `x` is promoted. In `G`, the public `Lib.x` is provided, so `x` is not promoted. In `P`, the private `Priv.x` is not provided, so `x` is promoted. A closed list forbids promotion: `H(a) = a + y` / `H(1)` is `UndeclaredIdentifier`.

Ambiguity is not promotion. A lookup that only evaluation decides keeps the arity of the unpromoted signature: with `L1 = { public X(v) = v + 101 }`, `L2 = { public X(v) = v + 202 }` and `K = {` / `open L1, L2` / `p.X` / `}`, `X` was not promoted, so `K` takes one argument: calling it with two is an arity error, and calling it with one is the run-time `AmbiguousOpen`.

### RES-05 — A property may not share a name with a parameter of its own or of any enclosing owner

- The collision check runs after parameter signatures are completed by automatic parameter forwarding.
- A property whose name equals a parameter of its own owner or of any enclosing owner, at any depth, is the front-end declaration error `ParameterPropertyCollision`, and the program is not evaluated. The parameter may be written, inferred, forwarded (PAR-07: a forwarded parameter counts here although it is never what a written name denotes), collecting, grouped, or a clause-branch binder. Visibility, reference order, and whether the name is used at all do not matter.
- The never-called program root's completed signature is checked only against the root's own properties.
- An alias of either kind has no parameters of its own, so nothing about it can collide: a property of the alias or of a body nested in it may share a name with a parameter of its target. A formula's forwarded parameter still counts.
- Parameter-over-parameter shadowing and property-over-property shadowing (nested scopes) stay legal, and so does a parameter shadowing a farther property.

**Qualifications**
- Independent sibling scopes never collide: `F = {` / `x = 3` / `Inner = x + y` / `Inner` / `}` / `G = {` / `y = 1` / `y + 1` / `}` / `F(4), G` gives `S[7, 2]`.
- A name the root cannot resolve is the root's input, not a collision inside a nested owner: `Lib = { public Q = 1 }` / `Q + 1` is `UnresolvedImplicitParams`.
- An inline open target and a loaded module meet none of the enclosing parameters (MOD-06, MOD-08): `F(x) = {` / `open { public x = 5 }` / `x` / `}` / `F(1)` is `1`.
- Two definitions of one property name in one algorithm are PROP-01's error.
- Inside a load-bearing clause branch a collision surfaces only when the branch is selected, as an evaluation error (MOD-10).

```katlang
x = 10
F(x) = x + 1
G(x) = {
    H(x) = x * 2
    H(x + 1)
}
F(2), G(3)
```
⇒ `S[3, 8]`

An inner parameter legally shadows a root property and an outer parameter. By contrast `Outer(v) = {` / `Mid = {` / `v = 5` / `v + 1` / `}` / `Mid` / `}` / `Outer(1)` is `ParameterPropertyCollision`.

`F(x) = x + 1` / `A = {` / `x = 100` / `F` / `}` / `A(5)` is `6`: the call is the target's own, whose parameter `x` the carrier's property never reaches. With the formula row `F + 0`, `A` receives a forwarded `x`, and the same program is the collision.

### RES-06 — Builtins are ordinary, shadowable prelude bindings: the resolved identity decides, never the spelling or the argument count

*Open: whether to prohibit or warn on a binding named `load` (Q-62).*

- Builtin callables, `Math`, the Math aliases and host operations are ordinary properties of the prelude, the outermost owning level.
- Resolution selects exactly one declaration and never looks at the argument count or at the callee's spelling: resolve → select one identity → assemble the ordinary supply → bind against that identity's signature → invoke.
- A nearer property or parameter named like a builtin shadows it completely, wherever the name is visible, dot fallback included (`7.if`, `[1, 2].sum`). There is never a fallback to the builtin; arity is then CALL-01's rule, and the one-signature inventory is COLL-01.
- A builtin's intrinsic behaviour, for example `if` evaluating only its selected branch, belongs to the builtin's identity. It travels with the builtin when the builtin is passed through a parameter or named through an alias, and it is absent from a user definition of the same name.
- No name is reserved except the lexer keywords (SYN-01). Builtin names, `Math`, and words such as `self`, `Author` or `Version` are ordinary declarable identifiers. So is `meta`: the parser recognizes it by spelling only as a contextual parameter modifier, where it directly precedes another pattern item on the same line of a parameter list (`Capture(meta operation)`). `F(meta)` and `meta = 3` keep the ordinary name, and a misplaced modifier is `InvalidMetaParameter` (SYN-13, CR-1).
- Spelling selects behaviour only in these deliberate exceptions:
  - A call written `load(...)` is recognised by spelling as the front-end module directive, whatever a nearer scope binds (MOD-07).
  - The structural-miss dot intrinsics `.string` (DOT-08), `.Invoke` (CR-5), `.Arguments` (CR-8) and `.Algorithm` (CR-14) take a dot edge's extension-call place on a structural miss. A declared member of that name wins, and a lexical callable of that name is never consulted (DOT-01): `string(x) = 99` / `3.string` is `'3'`, and `5.Algorithm` is `TypeMismatch`.
  - The engine reads the root's own `MinDecimalPlaces` and `MaxDecimalPlaces` as the source decimal-places settings, each composed with the host setting of the same name by their minimum (RUN-06). This does not change resolution: both names resolve like any other, and a nested or opened one is ordinary and has no display effect.

**Qualifications**
- The `load` privilege also intercepts a user binding: `F(load) = load(2)` / `F({ n + 1 })` is `LoadElaborationUnavailable`. Only the call form is special, so a bare `load` is an ordinary reference to whatever binds it (MOD-07).
- An opened member named like a builtin does not shadow it (RES-02).
- The alias `sin` and the canonical `Math.Sin` or opened `Sin` are distinct bindings of one native identity (OP-11).
- Host operations are prelude members in every layer (RUN-05).

```katlang
Apply(f) = f(true, trace(1), trace(2))
Pick(if, x) = if(x)
Neg(x) = -x
Apply(if), Pick(Neg, 4)
```
⇒ `S[1, -4]`

The builtin `if`, forwarded through `f`, stays lazy: `trace(2)` is never evaluated. The parameter named `if` carries `Neg`.

`if(x) = x + 1` / `if(7), 7.if` gives `S[8, 8]`. With the same definition, `if(x) = x + 1` / `if(true, 2, 3)` is `ArityMismatch`: the builtin `if` is not consulted as a fallback. `self = 1` / `Author = 2` / `Math = 3` / `self + Author + Math` gives `6`.

### RES-07 — A name inside a declaration denotes what its declaration site sees (lexical scoping), never what the caller or opener sees

- The declaration's own lexical chain fixes what every name inside it denotes. This rule is the single owner of that law for captured parameters, closures (named algorithms and brace blocks), and opened or structurally reached members.
- **Captured parameters and closures.** The free names of a named algorithm or a brace block resolve where it is written, through the owner walk (RES-01): properties of enclosing scopes, parameters of the enclosing activation, and callables.
- A reference to an enclosing owner's parameter is fixed statically to that owner. At run time it reads the binding of the owner activation in which the referencing code was written, entered or wired: a brace block created during that activation, or a nested property of that activation's body. Each activation of the enclosing algorithm gives its own captured parameter values.
- A later invocation never rebinds such a reference to a same-named parameter of whatever callee is active when the code runs. This holds under recursion (code created in one activation keeps reading it inside a deeper one), under forwarding through callees that bind the same name, inside nested callees that shadow the name, and through callbacks.
- **Opened and structurally reached members.** A member reached through `open` or a structural dot path is evaluated in its declaring chain: its own siblings, the enclosing declarations of its declaration site (with their activations), and the prelude. It sees nothing declared by the opener or the caller: the opener's properties, parameters and prelude shadows never capture a provider's free names. Calling an opened member directly therefore means the same as the owner-qualified call, in every algorithm-capable position (DOT-09).
- **Automatic parameter forwarding changes none of this** (PAR-07). What a written name denotes is decided by its declaration site alone; a parameter that forwarding adds to a body for a referenced formula is never what a written name there denotes. So referencing a formula never changes what an existing name refers to: `A = y + 1` / `F(y) = {` / `G = y * 1000 + A` / `H(y) = G` / `H(100)` / `}` / `F(3)` gives `3004`, exactly the inlined helper.
- A callee's body never resolves a name against the caller's environment.

**Qualifications**
- An inline `{ … }` open target and a loaded module have no declaration site in their opener or loader. Each resolves its free names, members reached through `open` included, against its own declarations, its own opens and the prelude only (MOD-06, MOD-08). `F = {` / `open { public A = q * 2 }` / `q + A(100)` / `}` / `F(5)` gives `205`: `A` infers its own `q` instead of capturing `F`'s. `abs(x) = 100` / `K = {` / `open { public A = abs }` / `A(-3)` / `}` / `K` gives `3`: the target never sees the root's `abs`. A written block (`M = { … }`) keeps its definition site, so a named provider declared inside a parameterized owner sees that owner's parameter.
- A transparent reference reads its target in the target's own context, and a forwarding carrier resolves its target at its own declaring activation (FWD-03).
- Free names of a property that nothing declares are not resolved dynamically either. They become that property's implicit parameters, and elaboration forwards them as explicit arguments (PAR-03, PAR-07; a lone bare row is FWD-02's bare forwarding).
- Only the callee's own names are shadowed: its parameter names shadow inherited bindings of the same name on every channel (PAR-01), and a callable that does not bind a name still sees its lexical owner's binding: `Inc(x) = x + 1` / `Apply(f) = {` / `Inner(x) = f(x)` / `Inner(5)` / `}` / `Apply(Inc)` gives `6`.
- Whether a member that captures an ancestor parameter may be accessed from a site outside that owner's activation is RES-08 (`LocalOnlyProperty`). Caching such members per activation is PROP-08.

```katlang
Rec(p, cb) = {
    H = p * 10
    if(p == 1, Rec(2, H), cb())
}
Run(f, n) = if(n == 0, f(), Run(f, n - 1))
Forward(n) = Run({ n * 100 }, 3)
Shadow(n) = {
    Q = n
    Mid(n) = {
        X = Q + n
        X
    }
    Mid(7)
}
Apply(f, k) = f(1)
Callback(k) = {
    Add(x) = x + k
    Apply(Add, 1000)
}
Rec(1, 0), Forward(7), Shadow(5), Callback(5)
```
⇒ `S[10, 700, 12, 6]`

Recursion: `H` keeps reading `p = 1` inside the activation `p = 2`. Forwarding: the block reads `n = 7`, never `Run`'s `n = 0`. Shadowing: `Q` reads the outer `n = 5` inside `Mid`, which binds `n = 7`. Callback: `Add` never sees the callee's `k = 1000`.

```katlang
A = 10
Vec = {
    public Test(x) = A + x + sum((1, 2))
}
Scope = {
    open Vec
    A = 100
    sum(v) = 999
    Test(5), Vec.Test(5)
}
Scope
```
⇒ `S[18, 18]`

`Test` reads the root `A` and the prelude `sum`, never the opener's `A` or `sum`.

### RES-08 — Visibility selects; accessibility is checked on the selected member afterwards (K1-08)

*C#-only by design for the exposure classification; Lean models the accessibility check.*
*Open: whether Lean should state how exposure is classified (Q-59).*

- Selection of a member never depends on exposure.
  - Structural dot access `R.M` selects any declared member of the receiver, private included.
  - An `open`-provided name and a dotted `open` path step select only public members.
  - `public` has no other semantic effect.
- A member is local-only when its value requires an input that only a call of an enclosing owner binds: a parameter or clause binder of that owner. The requirement counts whether it is reached directly, via a sibling, via a structural path, via an opened name, or via a dot fallback that may be selected, unless its check can never pass where it is made (Qualifications). The classification is static and dependency-based, not value-based: `Outer(p) = {` / `public B = if(false, p, 5)` / `B` / `}` / `Outer.B` is `LocalOnlyProperty`.
- After a unique member is selected, one check applies to it:
  - An exported member is accessible everywhere.
  - A local-only member is accessible only from a site whose lexical chain contains that owner's declaration and a matching activation. A same-named parameter of some other callable never qualifies.
  - A member declared only inside clause branches is never reachable structurally.
- An inaccessible selected member is the error `LocalOnlyProperty`. It is never a reason to select another candidate, to fall back to an outer declaration or to lexical dot fallback, or to promote the name.

**Qualifications**
- Private members are hidden only from `open`: `M = {` / `Hidden = 5` / `public Shown = 1` / `}` / `P = {` / `open M` / `Hidden + 1` / `}` / `P(10)` is `11`, because `open M` leaves `Hidden` to promotion, while `M.Hidden` reads it.
- A capture through a sibling is local-only, and a self-contained sibling of the same owner stays exported.
- Exposure follows the owner walk. A member is local-only whether the ancestor parameter is reached bare, through a capture row, through a nested block, or through a call argument, and it is still provided to the opener's own body inside the owner. A nearer local declaration keeps a member self-contained.
- A transparent reference gives no wider access than its target: with `B = Outer.A`, `B.X` is the same refusal as `Outer.A.X`.
- **A check that can never pass.** An access check is made in one scope. When the owner of a parameter it needs is not a static ancestor of that scope, the check can never pass: it is an error of the path that makes it, when that path runs, and never a requirement of the algorithm around it. With `F(y) = {` / `A = y + 1` / `A` / `}`, `Box = { public R = if(false, F.A, 0) }` / `Box.R` is `0`: `R` requires nothing. The read is refused with `LocalOnlyProperty` only where the branch that makes it runs: `G(x) = {` / `Box = { public R = if(x > 100, F.A, x) }` / `Box.R` / `}` gives `1` for `G(1)` and the refusal for `G(200)`.
- Dot navigation through an inaccessible intermediate member is that edge's error, not an extension fallback (DOT-02). Exposure does not decide how long a value lives: storage follows the owning invocation (PROP-08).
- The classification is the front end's, and Lean takes it as an input. Both evaluators enforce it (PROP-08): an exported member is evaluated detached from its enclosing calls — every activation of a level enclosing it that exists when its evaluation starts — and a captured parameter is used only through its lexical owner's activation. On the paths the evaluators check — every executed operation on a captured parameter (its value read, a call through it, its transport as an argument), a local-only member access and a local-only property read — a classification that misses a dependence is therefore a refusal (`UnknownName`, `LocalOnlyProperty`) instead of a value read from a caller. A retained runtime-alias binding cell is judged at every reuse, before its channel runs, and the input reads of its computation at the demand (PROP-08). That every source program is classified completely rests on C# tests.

```katlang
M = {
    Hidden = 5
    public Shown = Hidden + 1
}
Outer(n) = {
    Inner = {
        public X = n
    }
    Inner.X
}
M.Hidden, M.Shown, Outer(4)
```
⇒ `S[5, 6, 4]`

The private member is structurally reachable, and a captured member is accessible inside its owner's activation. From outside, a same-named parameter of another function does not qualify: `Loan(rate) = {` / `public MonthlyRate = rate / 12` / `MonthlyRate` / `}` / `G(rate) = Loan.MonthlyRate` / `G(12)` is `LocalOnlyProperty`.

```katlang
Outer(p) = {
    public A = { public X = p }
    A.X
}
B = { public X = 2 }
F = {
    open Outer.A, B
    X
}
F
```
⇒ `AmbiguousOpen`

Selection ignores exposure: the result is neither `2` nor `LocalOnlyProperty`. With `Outer.A` as the sole provider the result is `LocalOnlyProperty`, not promotion.

### RES-09 — One resolution for every layer, position and execution path

- Every layer answers "what does this occurrence denote?" by the same six ordered rules: the owner walk (RES-01), opens after the whole walk (RES-02, RES-03), promotion after both (RES-04), structural-first dot edges (DOT-01, DOT-02), static `open` (MOD-02 to MOD-04), and identity over spelling (RES-06).
- For every name occurrence, all layers therefore select the same declaration for the same reason:
  - parameter detection (parameter, property lookup or promotion);
  - implicit-argument resolution, in its signature analysis and its rewrite alike;
  - exposure and dependency analysis, which charges exactly what the evaluator reads and nothing for an ambiguous open;
  - open validation;
  - the editor model;
  - the evaluator on every path (sync, async twin, generic, planned or optimized).
- The value view and the callable view of one occurrence are one decision projected onto two channels, and the consumer never changes the decision (ALG-10). The program the front end elaborates is therefore the program the evaluator runs.
- Module-loading configuration does not change the decision. Module elaboration replaces only `load` directives (MOD-07). For load-free source, with the same host-operation configuration, supported parses and runs select the same declarations with or without a downloader. In load-bearing source, written owner boundaries remain intact, and successfully imported declarations can legitimately change surrounding resolution and inference. Compare those routes with the same completed module environment, not with an unavailable-module analysis tree.

**Qualifications**
- Coherence covers callable identity as well as selection. An argumentless structural dot path carries its member's own callable in every position (DOT-09): `Box = { public G(x) = x * 10 }` / `map([1, 2], Box.G)` gives `L[10, 20]`, like `open Box` with `map([1, 2], G)`. A transparent reference is its target's identity, while a forwarding carrier is a structure of its own (FWD-03).
- Lean parity checks evaluation of the C#-elaborated tree, so it cannot detect a front-end elaboration error (FORMAL-02).

```katlang
v = 99
Lib = {
    public count(x) = 100
}
F(v) = {
    open Lib
    Inner = v(1) + count([1, 2, 3])
    Inner
}
F({a + 1})
```
⇒ `5`

In call position `v` selects the enclosing parameter, exactly as it would in value position, and `count` selects the prelude builtin over the opened `count(x)`.

### RES-10 — Declaration order within a scope is not observable

- Name resolution within an algorithm uses the complete set of its declarations, never their textual order. A property may be referenced anywhere in its owning scope and in nested scopes, by rows and properties written above or below its definition.
- Permuting sibling definitions, or interleaving them with output rows, must change neither which declaration a name selects, nor the inferred signatures, nor results.
- This holds on sibling dependency cycles too. Signatures are selected jointly before any body is rewritten, no read observes a provisional signature, and a lifting cycle is completed simultaneously, or refused, in every order (PAR-08).
- The only ordered declarations are the branches of one clause family, which are tried first to last (PAT-02), and the `open` declaration, which must precede every property, a clause definition included, and every output row (MOD-01).

**Qualifications**
- Order can reach only the presentation of diagnostics: their order, and the order in which a report names a refused group, follow traversal. The refused bodies and the error kinds do not change.
- A deconstruction's right-hand side is a row of its body (VAR-06). Moving it among that body's rows moves its first occurrences, and so can reorder the body's inferred parameters (PAR-05): `F = {` / `a, b = G` / `p + a` / `}` / `F((1, 2), 10)` gives `11`, and with the two rows swapped the same call is `ArityMismatch`.
- Output rows are not declarations: their written order is the order of the program's output (VAL-07).
- The order of implicit parameters follows first occurrence and written reference order within a body, not declaration order across siblings (PAR-05, PAR-08).
- Runtime lookup is order-free: a level's properties are searched as a set.

```katlang
C = B + z
A = {
    H = B + 0
    P + 1
}
B = y + A
P = p * 10
C(1, 2, 3)
```
⇒ `34`

Every ordering of these four definitions gives `34`: `C` is `C(z, y, p)`, and the helper `H` reads `B`'s selected signature.

`A = B * 10 + x` / `B = y` / `A(1, 2)` gives `21`, and so does `B = y` / `A = B * 10 + x` / `A(1, 2)`. `A = 3` / `A + B` / `B = 2` gives `5`, and so does `B = 2` / `A + B` / `A = 3`.

Clause branches are ordered: `F(0) = 2` / `F(x) = 1` / `F(0)` gives `2`, while `F(x) = 1` / `F(0) = 2` / `F(0)` gives `1`. This is first-matching-branch selection within one family (PAT-02), not a sibling-order effect.

## MOD — The `open` declaration, `load`, and modules

`open` is a static declaration that makes the public members of a named or inline algorithm available under their own names inside the opening body. `load('url')` and `open 'url'` replace a directive with a separately parsed **module**: the one prelude-rooted declaration of its canonical URL. Neither creates a runtime value or an activation, and the evaluator never evaluates an unresolved `load`. A **provider** is the algorithm an open target finally resolves to, and a **deferred unit** is a load-bearing clause branch (MOD-10). RES owns how provided names compete with owned declarations, the prelude and each other, and member accessibility; DOT owns structural dot access; PROP owns cache identity; RUN owns general front-end gating and sync/async routing.

### MOD-01 — An algorithm has at most one `open` declaration, written before its properties and output rows, with one comma-separated target list

*C#-only by design.*

- `open` is a declaration. It is never an output row or an expression.
- Each algorithm body (the root or a `{ … }` block) may contain at most one `open` declaration. Each nested block has its own single open list.
- It comes before every property definition, a clause definition included, and every output row of that body.
- It takes one comma-separated target list, and the first target starts on the `open` line. A comma, or a leading `.`, continues the list onto the next line. A plain newline ends the list. `;` and juxtaposition never separate targets.
- These are front-end errors, and the program is not evaluated: a second `open` in the same body, an `open` after a property, a clause definition or an output row, an `open` between two clauses of one family, `public open`, and `open` inside parentheses.

**Qualifications**
- Declarations are allowed only in brace scopes (SYN).

```katlang
open Math
Math.Pi
```
⇒ `3.141592653589793238462643383279503`

The newline ended the list, so `Math.Pi` is one output row. `P(a) = a` / `open Math` / `Pi` is `InvalidOpenDeclaration`, exactly like `A = 1` / `open Math` / `Pi`.

### MOD-02 — An open target names an algorithm, never a value: a name, an argumentless dotted path, a brace block, or a module

*Open: whether opening an algorithm with no public members should be diagnosed (Q-58). Today it provides nothing.*

- Redundant parentheses are erased first (SYN): `open (M)` and `open ((M))` mean `open M`.
- After that, each target is exactly one of these forms:
  - a bare name;
  - an argumentless dotted path `A.B.C` whose head is a name, a `{ … }` block, or a module;
  - a `{ … }` block;
  - a direct `load('url')` directive;
  - a string literal `'url'`, which is sugar for `load('url')` (MOD-07).
- Every other shape, as the whole target or as the head of a dotted path, is `BadOpenForm`: a multi-slot group (a capture), a spread `A*`, a call `F(1)`, an argument-bearing dot edge `M.N()`, a literal, a list, an operator expression, and a Grace-marked target. A head fails with the message of the bare form: `open 5.N`, `open F(1).N`, `open (A, B).N`, `open [A].N` and `open ('url').N` fail like `open 5`, `open F(1)`, `open (A, B)`, `open [A]` and `open ('url')`.
- A double-quoted target is the lexical error `UnsupportedDoubleQuotedString`: its recovery text is never an open target and starts no download (SYN-15).
- Only a string written directly in the target list is load sugar, and it takes no dotted continuation: the dotted form is `open load('url').S`. A property whose value is a string is an ordinary algorithm with no members, not an alias.

**Qualifications**
- A `{ … }` block or a `load` module may head a dotted path. Its steps follow MOD-03.

```katlang
open (M).S
M = { public S = { public X = 7 } }
X
```
⇒ `7`

`open { public S = { public Q = 3 } }.S` / `Q` is `3`. `open Lib` / `Lib = 'https://mods.test/lib.kat'` / `1` is `1`: the string property provides nothing. `open (M, N)` / `M = 1` / `N = 2` / `1` is `BadOpenForm`.

### MOD-03 — Open targets resolve statically: the head through the owner walk and the direct chain, dotted steps through public members, and every written target must resolve

*Resolved (2026-11-10 record; audit finding C-2, fixed in `a4181877`): every C# layer now provides what Lean provides. With `open A` / `Lib = { Sub = { public Q = 1 } }` / `A = Lib.Sub`, the front end's namespace certificate walks the reference's own path by declared members (`openNavigateWith` in Lean), so `Q` is provided, as by the C# evaluator's open lookup and Lean. `ownership-and-lookup.md` (§ Static open through references) now states the reading: a reference's own path is no open path, `open` provides only PUBLIC members of what it resolves to, and the written `open Lib.Sub` stays `UnresolvedOpenTarget`; C# `OpenReferenceProviderAdmissionTests` and the `open-reference-private-*` spec cases pin it.*

- `open` never opens a runtime value. The errors below are front-end errors.
- **Head.** The target's head name is an ordinary occurrence, classified by the owner walk (RES-01).
  - If the nearest owner binds it as a parameter of any kind (written, inferred, collecting, branch binder, or captured), the target is `OpenTargetIsParameter`, and resolution never looks farther outward. A parameter that automatic forwarding added is never what a written name denotes, so it never owns the head.
  - Otherwise the head resolves through the direct lexical chain of the opening algorithm: its own and enclosing declarations (any visibility, including declarations written later) and the prelude. It never resolves through another `open`.
- **Dotted steps.** Each written step selects a public member declared by the receiver, whatever the head: a name, a `{ … }` block, or a loaded module. A private, missing, or branch-only step is an error. A static transparent reference (FWD-03) is navigated as its target; a structural forwarding carrier and a runtime reference are navigated by their own declarations.
- **References are stratified.** A transparent reference that a target reaches resolves through direct chains and member steps only, never through an `open` and never by evaluating anything. Its head follows the direct lexical chain of its own declaration, and its own member path selects declared members, each checked for accessibility from the site. A reference whose target only an `open` provides is `UnresolvedOpenTarget`, so a self-dependent open is an error, never a runtime fixed point.
- **Completeness.** Every written target must resolve, whether or not any lookup ever consults it (`UnresolvedOpenTarget`).

**Qualifications**
- The never-called root's phantom (unresolved) names are not parameters for this decision, although they take part in ordinary name resolution (RES-01). A head naming one resolves through the direct lexical chain like any other head, and is `UnresolvedOpenTarget` if nothing declares it: `x + 1` / `F = { open x ⏎ 2 }` / `F` is `UnresolvedOpenTarget`. The collision exemption of RES-05 is the analogous rule, not this one.
- A parameterized intermediate of a dotted path is navigated by identity (MOD-04).
- Whether a local-only step is accessible is an evaluator check made per site, not a static-validity question (RES-08).
- Lean evaluates the same failures lazily, when a lookup consults the level. The static `UnresolvedOpenTarget` rule exists only in the C# front end.

```katlang
Outer = {
  open Lib
  X + 1
}
Lib = { public X = 41 }
Outer
```
⇒ `42`

The head is private and declared later. `open Lib.Sub` / `Lib = { Sub = { public Q = 1 } }` / `Q` is `UnresolvedOpenTarget`, while `Lib = { Sub = { public Q = 1 } }` / `Lib.Sub.Q` is `1`.

- `Lib = { public X = 1 }` / `F(Lib) = { open Lib ⏎ X }` / `F(2)` is `OpenTargetIsParameter`: the root `Lib` is never reached.
- `G(Lib) = Lib + 1` / `Lib = { public X = 5 }` / `F = { open Lib ⏎ G + X }` / `F(10)` is `16`: `F`'s `Lib` is a forwarded parameter, so the head is the root `Lib`.
- `A = { open Nope ⏎ 5 }` / `A` is `UnresolvedOpenTarget`, although nothing reads through it.
- `open Base, A` / `Base = { public Found = { public X = 1 } }` / `A = Found` / `1` is `UnresolvedOpenTarget`: only an open provides `A`'s target.

### MOD-04 — An open provider must need no call, and opening it neither activates nor evaluates it

*Open: whether provider eligibility should stay stricter than the zero-argument demand (Q-58).*

- **Eligibility.** The provider must have an empty effective parameter list: written, inferred and lifted parameters all count. It must be neither a clause family nor a prelude builtin, whether the builtin is written bare or as the head of a dotted path. Otherwise the target is `IllegalInOpen`.
- **Aliases.** A static transparent reference is judged by its target's rule, because the provider is its target. A structural forwarding carrier and a runtime reference are namespaces of their own declarations, so they are eligible whatever their target. A body whose static target chase returns to a body it passed is no alias: it stays an ordinary property and is judged as one.
- **Intermediates.** A parameterized or inferred-parameter intermediate of a dotted path is navigated by identity and is allowed.
- **No activation.** Opening evaluates nothing. `open` never demands a provider's output rows, and it never resolves a carrier's forwarding target. Members are evaluated only when a provided name is read.

**Qualifications**
- The eligibility test is "has any parameter", not the zero-argument value-demand law (CALL). So a provider whose only parameter is collecting is refused, although it accepts an empty supply: `open Only` / `Only(*xs) = { public X = 1 ⏎ xs }` / `1` is `IllegalInOpen`, while `Only(*xs) = { public X = 1 ⏎ xs }` / `Only, Only.X` is `S[L[], 1]`.
- A member of an eligible provider that captures an enclosing parameter is still selected. Its accessibility is then checked per site (RES-08).

```katlang
open Lib
Lib = {
  public X = 1
  trace(9)
}
X, X
```
⇒ `S[1, 1]`

`trace` is never called. With `Lib` as a third row the result is `S[1, 1, 9]`, with one call.

- `open F` / `F(p) = { public X = 1 ⏎ p }` / `X` is `IllegalInOpen`, and so is the inferred-parameter `open Lib` / `Lib = { public X = 1 ⏎ p + 1 }` / `X`.
- `open F.S` / `F(p) = { public S = { public Q = 7 } ⏎ p }` / `Q` is `7`.
- `open A` / `Lib = { public X = 7 }` / `A = Lib` / `X` is `7`. `open A` / `F(x) = x` / `A = F` / `1` is `IllegalInOpen`, exactly as `open F` is.
- `open A` / `F(x) = x` / `A = { public X = 1 ⏎ F }` / `X` is `1`: the carrier opens its own declaration.
- `Outer(n) = { Lib = { public X = 10 ⏎ n } ⏎ P = { open Lib ⏎ X } ⏎ P, Lib, Lib.X }` / `Outer(1)` is `S[10, 1, 10]`: a runtime target leaves `Lib` a namespace of its own declarations.
- `open A` / `A = B` / `B = { public X = 1 ⏎ A }` / `X` is `UnresolvedImplicitParams`: neither body is an alias, so `A` has no member `X`.

### MOD-05 — `open` provides exactly the provider's own public members, and only to the opening body and its nested scopes

- A resolved provider contributes exactly the public members that it declares itself. It never contributes its private members, names it obtains through its own `open` (no transitive re-export), or its output rows.
- A static transparent reference opens its target's public namespace under the target's provider identity. A structural forwarding carrier contributes only its own public declarations, never its forwarding target's: `{ Lib }` exposes nothing of `Lib`. A runtime reference contributes only its own declarations, so nothing is opened dynamically.
- Provided names are visible in the opening algorithm's body and in bodies nested inside it. They are invisible to the enclosing algorithm, to sibling algorithms, and to sibling branches of a clause family.
- How provided names compete is RES: they are consulted only after the whole owner walk, level by level; two different providers are ambiguous; targets count once per provider identity.
- Structural dot access still reaches private members (DOT, RES).

**Qualifications**
- A provided name never beats an owned name: `open Lib` / `Lib = { public X = 5 }` / `X = 1` / `X` is `1` (RES-02).
- An inline open in one clause branch is invisible to sibling branches, also when an enclosing `open` provides the same name: the sibling reads the enclosing provider.
- Selection is by visibility only. A public member that captures an enclosing parameter is still provided, and is then refused outside its owner (RES-08).
- A string-valued property opened by name provides nothing (MOD-02).

```katlang
open Lib
Lib = {
  public Area = 4
  Helper = Area / 2
}
Area, Lib.Helper
```
⇒ `S[4, 2]`

The same program with the row `Helper` is `UnresolvedImplicitParams`.

- `open Lib` / `Lib = { open Base ⏎ public X = Y + 1 }` / `Base = { public Y = 2 }` / `X` is `3`, and with the row `Y` it is `UnresolvedImplicitParams`: `open` is not transitive.
- `open { public V = 5 }` / `F(0) = { open { public V = 7 } ⏎ V }` / `F(1) = V` / `F(n) = 2` / `F(0), F(1), F(2)` is `S[7, 5, 2]`: the sibling branch reads the enclosing provider.
- `Lib = { public K = 7 ⏎ 0 }` / `C = { public Own = 5 ⏎ Lib }` / `P = { open C ⏎ K + Own }` / `P(1)` is `6`: `K` stays `P`'s own input.

### MOD-06 — Opened members keep their definition site; inline open targets and every loaded module are rooted at the prelude

- **Named providers** keep their definition site (RES-07(b)). A named provider whose value is a loaded module is that module, rooted at the prelude (MOD-08).
- **Inline targets and loaded modules.** An inline `{ … }` target has no declaration site of its own, and neither has a loaded module, however it is reached: opened directly by string or `load`, held by a property (`M = load('u')`), or nested in another module (MOD-07, MOD-08). Such a target is elaborated and evaluated as a separate region under the prelude:
  - it sees the builtins and the run's host operations;
  - it sees none of the opener's properties, parameters, branch binders or opened names;
  - names it cannot resolve become implicit parameters of its own members.
- **Rooting is visibility, not validity.** Prelude rooting decides what such a target can see, never which front-end rules apply inside it. Every ordinary front-end rule applies there exactly as in any other body, in every phase (eager, or in a selected deferred unit, MOD-10): name resolution, bare forwarding (FWD-02), formula lifting and the rules for inferred signatures, and every validator. A declaration that is invalid as a property body is invalid as an open-target member; nothing about an open target exempts a declaration from validation.

**Qualifications**
- A named provider declared inside the opener, or inside an enclosing parameterized owner, does see that owner's declarations and parameters, because that is its definition site: `Outer(n) = { open Inner ⏎ Inner = { public X = n } ⏎ X + 0 }` / `Outer(5)` is `5`. Accessibility is then checked per RES-08.
- By RES-07(b), a directly called opened member means the same as the owner-qualified call in every position, because an argumentless structural path is its member's own callable (DOT-09): `Box = { public G(x) = x * 10 }` / `map([1, 2], Box.G)` and `open Box` / `Box = { public G(x) = x * 10 }` / `map([1, 2], G)` are both `L[10, 20]`.

```katlang
X = 5
Named = { public Y = X + 1 }
A = {
  open Named
  Y
}
B = {
  open { public S = sum((1, 2)) }
  sum(v) = 999
  S
}
A, B
```
⇒ `S[6, 3]`

The named provider reads `X` at its definition site. The inline target sees the prelude `sum`, not the opener's.

- `X = 5` / `A = { open { public Y = X + 1 } ⏎ Y }` / `A` is `ArityMismatch`: `X` became `Y`'s implicit parameter.
- `F(p) = { open { public Y = p } ⏎ Y }` / `F(3)` is `3`: `Y` owns the parameter `p`, and `F`'s closed body forwards its `p` by name (FWD-02). `F(q) = { open { public Y = p } ⏎ Y }` / `F(3)` is `UnforwardableParameter`.
- `open { N(y) = y ⏎ public P(x) = N ⏎ public X = 1 }` / `X` is `UnforwardableParameter`, as for the same block written `M = { … }`.

### MOD-07 — `load('url')` is a static source directive that splices a separately parsed module as the one prelude-rooted declaration of its canonical URL, and module elaboration transforms nothing else; `open 'url'` is `open load('url')`

*C#-only by design.*
*Open: whether `F(y) = load(u)` should merge the module into the definition (Q-60). Today it stays one nested block.*
*Open: whether a binding named `load` should be prohibited or warned about (Q-62). Today it is neither, and `load` is not a keyword.*

- A call written `load(<one string literal>)` is a front-end directive, not a function.
- **Source-unit admission.** Static import elaboration belongs to the required admitted compilation unit; it acquires declarations without evaluating their outputs. Configurable source limits are host policy, not KatLang syntax validity (RUN-03).
- **Recognition.** It is recognized by its call shape and spelling, after redundant-group erasure. It is the one spelling-recognized callable form, so a user parameter or property named `load` never intercepts it (RES-06). Only the written call is special: a dot edge `M.load(…)`, a call through another spelling, and a callee that merely resolves to something named `load` are ordinary.
- **Bare `load`.** A written bare `load` that no property, parameter or opened member binds denotes nothing. It is the front-end error `UnboundLoadReference` at the occurrence, wherever it is written and whether or not evaluation would demand it, and it is never inferred as a parameter. This includes a dot edge whose fallback is certainly selected (`5.load`). A fallback only the runtime receiver decides stays a run-time question, and a real binding named `load` is ordinary.
- **Argument.** Exactly one literal URL, a single-quoted string. A computed URL is not allowed. A double-quoted run is `UnsupportedDoubleQuotedString`, and its recovery text is never a URL (SYN-15).
- **Recovery cannot authorize acquisition.** A string token rejected by the lexer retains its text for analysis, but cannot be an `open` or `load` URL: an unterminated single-quoted string and every rejected double-quoted run cause no downloader invocation for that directive (SYN-15). The original lexical error explains the refusal even when the diagnostic-list cap omitted its report. Other valid imports retain their ordinary schedule (RUN-04).
- **Position.** Allowed only where a definition or an open list is being built: a property or clause definition's right-hand side, an open target, and positions nested in them that inherit that context. In a runtime position (operand, call argument, selection receiver or selector, root output row) it is `InvalidLoadDirective`.
- **Splicing.** Before parameter detection, the directive, and nothing else, is replaced by the fetched module, parsed as its own document: the one prelude-rooted declaration of its canonical URL (MOD-08, MOD-09). `open 'url'` is exactly `open load('url')`.
- **Everything else is kept as written.** Module elaboration changes no construct that is not a directive. Every other block boundary, member, declaration, row and `open`, in the loading document and in the module text alike, keeps its written shape. Source without a directive therefore keeps its meaning when downloader capability is enabled (RUN-01). In load-bearing source, non-directive syntax retains its semantic boundaries; imported declarations still participate in ordinary lookup, inference, exposure and evaluation.
- **After successful materialization.** No unresolved `load` remains in that region. Deferred branches keep their directives until selection (MOD-10); refused directives remain in an unevaluable analysis tree (MOD-11). Module acquisition evaluates no KatLang expressions. Module code then runs as ordinary code, with the run's prelude, host operations, and random stream.
- **Directive-only property bodies.** `P = load(u)` makes the module `P`'s value, as `P = { … }` makes a block `P`'s value, the module keeping its own root (MOD-08). `P` itself is its own binding (MOD-09).
  - A body with no parameter patterns, explicit parameter list, declarations or opens, and exactly one written directive is the module, just as SYN-05 makes `P = { … }` the block itself. `P = { load(u) }` and `P = (load(u))` have the same body after the parser's one merge and redundant-group erasure.
  - The module's declared members are `P`'s members (structural dot reaches the private ones), and its output rows are `P`'s value.
  - The written directive decides this, never the elaborated shape. A written `P = { { … } }` keeps both boundaries. A directive inside a written nested block is replaced where it stands, so `P = { { load(u) } }` means `P = { { { <module text> } } }`.

**Qualifications**
- The body merge excludes explicit parameter lists and deconstruction sources; explicit definitions and clause branches retain their own bodies. `F(y) = load(u)` keeps the module as one nested block output, which is `F(y) = { { <module> } }`.
- `UnboundLoadReference` is judged in every elaborated unit, a selected deferred unit at its materialization boundary. A provisional elaboration withholds it (MOD-11), a never-selected deferred unit is not judged, and a host-built tree that skipped source processing keeps the evaluator's `UnknownName`.
- A written bare `load` that reaches two different providers at one open level keeps the run-time `AmbiguousOpen`.
- Which nested positions inherit definition context is a C# detail: nested blocks, capture and list items, spreads, Grace and argumentless dot receivers do.
- Target admission (https, allow-list), URL canonicalization, limits, and async-only acquisition are host policy.

Bindings named `load` and bare uses run without any module:

- `load = 5` / `load + 1` is `6`.
- `X = load` / `X` is `UnboundLoadReference`.
- `load(x) = x + 1` / `map([1, 2], load)` is `L[2, 3]`.
- `F(load) = load(2)` / `F({ n + 1 })` is `LoadElaborationUnavailable`: without a downloader the call is still the directive, and with one it is `InvalidLoadDirective`.

Written nesting. With a module `blk.kat` holding `public X = 1` and the row `5`, beside `X(a) = 100`:

- `P = load('…blk.kat')` with the row `P.X, P` means what `X(a) = 100` / `P = { public X = 1 ⏎ 5 }` / `P.X, P` means, which is `S[1, 5]`.
- `P = { { load('…blk.kat') } }` with the row `P.X, P` means what `X(a) = 100` / `P = { { { public X = 1 ⏎ 5 } } }` / `P.X, P` means, which is `S[100, 5]`: `P.X` falls back to `X(a)`.
- `F(y) = load('…pp2.kat')`, with a module holding `public P = 7` and the row `3, 4`, reads `F.P` as `F(y) = { { public P = 7 ⏎ 3, 4 } }` / `F.P` does, which is `UnresolvedImplicitParams`, while `F(y) = { public P = 7 ⏎ 3, 4 }` / `F.P` is `7`.

### MOD-08 — A module has hygiene of its own: its free names resolve against the module itself and the prelude, never at the load site

- A loaded module, held by a property, opened directly, or nested in another module, is a separately rooted source unit.
- Its free names resolve over its own declarations, the prelude (builtins, `Math` and its aliases, the run's host operations) and its own opens, and nothing else (MOD-06). The order is the ordinary one (RES-01, RES-02): its own declarations beat the prelude, and its own opens come after both.
- The load site's properties, parameters, opened names and prelude shadows never capture a module name.
- A name the module cannot resolve becomes an implicit parameter of its own member that uses it (PAR-03). A free name in the module's output rows makes the module itself parameterized: callable as `M(x)`, never an open provider (MOD-04).
- A site parameter reaches a module member only as an argument: explicit, bare forwarding by name (FWD-02) or formula lifting by name (PAR-07).
- One module text therefore has one meaning, one set of signatures and one validity at every load site, and `open 'u'` ≡ `M = load('u')` + `open M` ≡ `M.Member`.
- A module's root is never a transparent reference. A module whose one row is a bare reference is a structural forwarding carrier with its own namespace, and it resolves that reference in the module, never in the scope that holds it.

**Qualifications**
- Deferred branches keep their schedule (MOD-10); a selected branch's module means what the eager module means.
- A written block `M = { … }` keeps its definition site (RES-07(b)); only a loaded module is rooted at the prelude.
- Lean does not load modules (FORMAL-02). Its elaborated core marks a module root and wires it at the chain root.

With `free.kat` holding `public V = Base + 1` and a load site that declares `Base = 10`, the row `M.V(10)` after `M = load('…free.kat')` evaluates to 11, and the bare `M.V` fails with `ArityMismatch`: the member's signature is `V(Base)`, and the site's `Base` is never seen. The written block keeps its site: `Base = 10` / `M = { public V = Base + 1 }` / `M.V` is `11`.

- A module `public V = sum((1, 2))` at a site declaring `sum(xs) = 999` evaluates to 3 in every spelling. A module that itself declares `sum(xs) = 777` evaluates to 777.
- A module whose one row is `abs`, held as `M` at a site declaring `abs(x) = 100`, evaluates `M(-3)` to 3. The written block does not: `abs(x) = 100` / `M = { abs }` / `M(-3)` is `100`.
- `F(Base) = { M = load('…free.kat') ⏎ M.V }` with the row `F(10), F(20)` evaluates to `S[11, 21]` by bare forwarding of `F`'s `Base`. A module member `public a = 3`, read in `F(a) = { M = load(…) ⏎ M.a + a }` with the row `F(1)`, evaluates to 4: a holder's parameter never collides with a module declaration.

### MOD-09 — One module per canonical URL per compiled program: every load and every open of it is the same declaration

*C#-only by design.*

- **Identity.** A load target's identity is its canonical module URL. Host policy fixes the canonical form.
- **Single fetch.** Within one operation, a canonical URL is fetched and elaborated at most once after it succeeds, so two sites can never see different module text.
- **One declaration.** Within one compiled program, one canonical URL denotes one module declaration; every load and every `open 'u'` of it, in any scope, at any position, eager or in a selected deferred unit (MOD-10), denotes it. Each member is one binding: one zero-parameter value per run (PROP-04, PROP-07; no load site, holder or scope takes part) and one callable identity (NEED-04).
- **Holders.** A property holding a module (`P = load(u)`) is its own binding, and a bare read of `P` (the module's output) caches under `P`. The exception is a module whose root is a carrier (MOD-08): no alias owns a zero-argument entry, so that read is its target's.
- **Distinct URLs.** Distinct canonical URLs are distinct sources and declarations, even when they serve identical bytes.
- **Open providers.** They are counted by identity (RES-03): `open 'u', 'u'` and `open A, B` over two loads of one URL are one provider. A reference to a holder opens the holder's module under that identity.

**Qualifications**
- Declarations are per compiled program, values per run; there is no module cache across parses.
- Failed loads are never cached; they are retried and charged again. Every cache-hit splice is still charged.
- The canonicalization rules (lower-case IDNA host, default port dropped, fragment dropped) are host policy.

Two written declarations are two bindings: `A = { public R = randomInt(0, 1000000) }` / `B = { public R = randomInt(0, 1000000) }` / `A.R, B.R` is `S[109699, 550292]`. A module `r.kat` holding the same `public R` makes one binding of `A = load('…r.kat')` and `C = { public B = load('…r.kat') }`, so `A.R, C.B.R` shows one draw twice. A module holding `public T = tock()`, loaded as `A` and `B`, evaluates `A.T, B.T, A.T()` to `S[1, 1, 2]` with two host calls. A module with the member `R` and a drawing output row, held by `A` and `B`, gives different `A` and `B` (holder bindings) and equal `A.R` and `B.R` (one member binding). Two URLs serving identical bytes give two draws, and a written name opened from both is `AmbiguousOpen`.

### MOD-10 — A clause branch that owns a load materializes its modules only when selected, and then means exactly what eager elaboration would have produced

*C#-only by design.*

- When loading is available, each alternative clause-family branch body that contains an unresolved `load` is deferred.
- **Unit and validation.** A load-bearing branch body is one deferred compilation unit: its written text together with the modules it loads. Its written text is parsed eagerly; the remainder of the unit is acquired, elaborated and judged when the branch is selected.
  - Once selected, the whole unit is elaborated and validated exactly as eager source in the same recorded context: every declaration is subject to the ordinary front-end rules, in every position (open targets included, MOD-06), whether or not the eventual runtime computation demands it. The member a computation requests never decides which declarations are validated.
  - Any load or front-end error then stops that evaluation at the selection boundary, before the branch body runs, with the diagnostic eager compilation of the same unit reports: its code, at the corresponding written or import-site position, never at the call that selected the branch, carried as MOD-11 prescribes for a required deferred unit.
- **Before selection.** Initial module elaboration performs no acquisition or module-budget charging inside the deferred branch. Parsing remains eager, so syntax errors in the written branch still block entry. Nothing else of the unit is judged before selection: no elaboration diagnostic is reported and no resolver or validator verdict is issued for it, not even one that no module could change. There is no eagerly reported "module-independent" subset.
- **At selection.** After ordinary supply formation, cardinality checking and inspecting pattern demands select a branch, and before its body runs, the whole deferred unit is materialized under the recorded contexts by the same walk as eager elaboration (MOD-07). Its static imports are processed even if no imported member later receives VALUE demand. Each directive is replaced by its module; every other written construct, load-free nested blocks included, keeps its written shape. This introduces neither global preflight of unselected regions nor per-member lazy imports.
  - Successful materialization uses the same transformations as eager elaboration under the same owner context and module environment.
  - The branch's load-free parts keep their written boundaries, as in an ordinary body or a branch that owns no load. Imported declarations may affect their ordinary lookup and inference.
  - A directive body inside the branch (`P = load(u)`) is the module exactly as it is eagerly.
  - A module materialized in a selected unit is the same declaration as every other load of its canonical URL in the program (MOD-09).
- **Never selected.** Such a branch performs no module work and reports nothing after parsing. Its unavailable or invalid module, and any post-parse error in its written text, cannot fail the program.
- **Call-by-need is not declaration validity.** NEED governs supplied computations, never the validity of declarations (NEED-05). A declaration of a selected unit that is invalid is an error although its value is never demanded; laziness never excuses it.
- **Required source information.** Source-size and acquisition limits are host admission policy, applied when the source-processing contract requires a source unit, before its contents are used. A deferred unit is processed only when an operation requires its compilation, including required identity information.
  - NEED-03 governs runtime supplied computations; MOD-07 and this rule govern required compilation units. An undemanded supplied computation selects no branch and performs no speculative source work. Initial source stays initially parsed.
  - CALLABLE projection does not demand a member's zero-argument VALUE, but may require compilation to discover declarations: `Apply(M.Inc, 3)` needs `M`'s compiled member identity, while `Ignore(F)` transports an already-known family identity without compiling its deferred body. These are source-information requirements, not a second runtime laziness mechanism or a metadata-manifest API.
  - NEED-07 is unchanged: an arbitrary spread `F(1)*` requires VALUE to form its supply, even before an ignoring callee, while opening an existing collector slice transfers cells without demanding them.
- **Required refusal.** A reached source refusal stops the requesting operation and its run before the body executes. It stays outside `IsResourceLimit`, yet `IsResourceLimit == false` does not make it recoverable: it is never a branch non-match or an alternative successful result. A META receiver can absorb neither a required failure nor observed source cancellation. Source failures keep their original diagnostics; cancellation keeps its original exception and token.
- **Caching.** A successful materialization is reused; a failure is never cached. Source-loader caches and NEED-09 cell completion are separate, and a retained failure belongs to one run, not to the loader's cache. Required acquisition observes the established source and evaluation cancellation rules.
- **Evaluator admission.** *(C# host policy.)* Every materialized body, fresh or reused, is admitted by the consuming run's own structural preflight before the evaluator descends into it, under the run's effective `MaxAstDepth` less the weighted prefix of the placeholder's position (its deepest root-to-placeholder path). The composed tree is thus judged as ordinary admission would judge the eager tree. A rejection (`AstDepthLimitExceeded` or `AstCycleDetected`) is terminal for the run; `AstDepthLimitExceeded` is a RUN-03 resource limit and `AstCycleDetected` is not. It is a run verdict, not a materialization failure: the shared materialization stays untouched, so a later run judges the body under its own limit.
- **Reentrant selection.** *(C# host policy; owner decision B16, 2026-11-10: fail fast, adopted the same day as the `RunOptions.DownloadCode` host contract.)* A unit's on-demand load is in progress for the whole loader turn it holds: every downloader call and the parsing and elaboration of what it returns. Eager loads during parsing are unaffected. While a load is in progress, an evaluation running in that downloader's execution context (the downloader, its continuations, and whatever it starts while context flows, also through nested loads of other programs that this context started) that selects a not-yet-loaded unit of the same parsed program is refused at once as `LoadCycle` at the unit's first load directive or import site, without a token and never as cancellation. A loaded unit is served; a cancelled source-processing token, then a cancelled evaluation token, take precedence over the refusal. The refusal counts, attempts and charges nothing; the load in progress publishes normally and the same selection succeeds after it. Never refused: code that loads nothing, a loaded unit, another parsed program, evaluations from any other execution context (they wait for the load as before), and a context captured during a load and used after it. The library cannot observe whether the downloader waits for the evaluation, so the refusal prevents a possible cycle and does not prove one: flowed work the downloader never waits for is refused too, and independent work must start after the load or with execution-context flow suppressed around its scheduling call. Outside the guard, and forbidden to the host: a downloader waiting for an evaluation of the program it is loading for from any context, including one another context started, and a cycle through another program's load that this context did not start, whether its evaluation joins that load or queues for that program's loader turn. *(Characterized 2026-11-11; formerly "that this context only joined". Such a cycle is neither refused nor bounded: cancelling the evaluations that started the loads need not end it, because a joined load keeps the other program's waiting evaluation as a consumer, and a waiting evaluation's own token does end it. No owner decision.)* No deadlock freedom is claimed. Evidence: `../deferred-reentrancy-closure/reviewer2-unified/` (decision memo), `../deferred-reentrancy-closure/contract-closure/`, and `../deferred-cross-tree-cycles/` (cross-program pins and mutation proof).
- **Exceptions.** A family-owned open list, which only a host-built tree has, loads eagerly, and so does a single-clause definition that elaborates to an ordinary algorithm (a literal-free binder, sequence-pattern or list-pattern clause, PAT-01). A single clause with a literal anywhere in its head is a one-branch clause family, and its load-bearing body is deferred like any other branch.

**Qualifications**
- Synchronous low-level entry points cannot await a materialization. They reject such trees with `InvalidOperationException`. This is host routing (RUN).
- The general rule "every front-end error blocks evaluator entry" (RUN-04) is deliberately relaxed inside a deferred region: a `ParameterPropertyCollision` in a load-bearing branch is a run-time error, and only when that branch is selected. This is the unit rule's schedule, not an exemption: the error is the same static invalidity eager compilation reports.
- Without a downloader there is no deferral: every directive is unavailable (MOD-11).

The branch below owns no load, so it runs without a downloader.

```katlang
F(0) = 0
F(n) = {
  open { public X = 41 }
  X + n
}
F(0), F(1)
```
⇒ `S[0, 42]`

The branch owning `open 'https://mods.test/lib.kat'`, with a module holding `public X = 41`, gives the same result, and `F(0)` alone acquires nothing. With `bad.kat` holding `public E = 1 +` and the branch `F(n) = { open '…bad.kat' ⏎ E + n }`, the rows `F(0), trace(5)` evaluate to `S[0, 5]` with one `trace`, while the rows `F(0), F(1)` fail with `InvalidLoadedSource`, raised while evaluating the call to `F`. An unrelated load changes nothing else in a branch: a written `P = { { public X = 1 ⏎ 5 } }` beside `L = load(…)` keeps its inner block, so `P.X` falls back to a lexical `X(a)`, as in a branch that owns no load.

### MOD-11 — A module that is not loaded never becomes a value, and a program with a missing module is never evaluated

*C#-only by design.*

- A `load` directive that the front end does not elaborate is an error at its site. It is either unavailable (no downloader) or refused (runtime position, bad argument, refused target, cycle, limit, failed fetch, or invalid module source).
- The directive stays as written. No stand-in value is ever substituted for the module.
- A result that contains such a directive outside a deferred branch (MOD-10) is never evaluated, so no host call, random draw, or other evaluation effect happens.
- A load cycle is one such refusal.
- **Failure phases.** Initial, main or eager compilation-unit refusal blocks evaluator entry as `RunResult.ParseFailure`. A required deferred unit fails at materialization as `RunResult.EvalFailure` carrying its underlying diagnostic and import provenance, before its body runs. An unrequired deferred unit performs no acquisition, parsing or admission and discovers no external source failure. Required source refusal is never branch non-match or an alternative successful result (RUN-03).

**Qualifications**
- Which other diagnostics are withheld during provisional elaboration, and how the editor models such a document, are diagnostics and tooling policy.
- General front-end gating is RUN.

```katlang
M = load('https://mods.test/nosuch.kat')
trace(1)
F(n) = {
  n = 1
  n
}
F(2)
```
⇒ `LoadElaborationUnavailable`

With a downloader that cannot serve the URL the only error is `LoadFetchFailed`. Either way the `ParameterPropertyCollision` in `F` is withheld and `trace` is never called. Two modules that load each other fail with `LoadCycle`, and a module with a syntax error fails with `InvalidLoadedSource`.

## PROP — Properties: declarations, demand, and one value per binding per owning invocation

A property is a named algorithm that its owning algorithm declares: an immutable declaration, bound once, whose body runs only on demand. A **property-style read** is a bare value read (`A`, `Obj.A`, an opened `A`), and an **explicit call** is an invocation (`A()`, `F(args)`, a call a slot makes). A property that accepts zero supplied arguments has at most one **entry** per resolved binding in each **owning invocation** — the nearest actual call of the owner chain it is declared under, or the run where there is none (PROP-08): the result its owning evaluation published (PROP-09), an identity of evaluation that `tick()`, random draws and host operations make observable. An **exported** property depends on no input that an enclosing owner's call binds, and a **local-only** property depends on such an input (PROP-08). Transparent references and forwarding carriers are the aliases of FWD-03, and neither owns an entry.

### PROP-01 — Each name is bound once per algorithm; a property is never redefined or reassigned

- Within one algorithm's declarations, a name is declared by at most one definition. The forms are a simple property (`A = …`, `public A = …`), a callable definition or clause family (`A(…) = …`; the repeated heads of one family count as one definition, PAT-01), and an assignment-deconstruction target (`a, b = …`, VAR-05).
- Any second definition is `DuplicateProperty`, whatever the mix of forms or visibilities, and the program never evaluates.
- There is no reassignment: once computed, a binding's value never changes.
- A property declared in a nested scope with the name of an outer property is legal. It is a new binding that shadows the outer one (RES-01).
- A property may not share its name with a parameter of its own owner or of an enclosing one (RES-05).

**Qualifications**
- Duplicate branch patterns inside one clause family are a separate error, `DuplicateBranchPattern` (PAT-02). A repeated name inside one parameter pattern is not a duplicate declaration (NEED-04, PAT-09).
- The C# front end rejects every source duplicate statically, including duplicates in algorithms that are never evaluated. Lean reports `duplicateProperty` only when it evaluates the output of the algorithm concerned, and the C# evaluator repeats that check at runtime for host-built ASTs.

```katlang
Rate = 5
Rate = 6
Rate
```
⇒ `DuplicateProperty`

`A = 5` / `A(x) = 6` / `A` is `DuplicateProperty`, and so is `a, b = 1, 2` / `b = 3` / `a`. A nested redeclaration is a new binding:

```katlang
A = 1
B = {
  A = 2
  A
}
A, B
```
⇒ `S[1, 2]`

### PROP-02 — A declaration evaluates nothing: a property body runs only when demanded

- Declaring a property evaluates nothing.
- A property's body is evaluated only when a value read or a call demands it. Demands occur in the order evaluation reaches them, not in declaration order.
- A property that is never demanded is never evaluated, so its runtime failures and effects (random draws, host operations, `tick()`) never happen. A failure is not a value and surfaces only where it is demanded (VAL-10).
- Front-end errors inside an undemanded property still reject the program (RUN-04). Static validation (duplicates, branch-arity invariants, collisions) covers unused declarations too.

**Qualifications**
- Laziness belongs to property bodies and to a few other demand points, such as the builtin-owned laziness of `if` branches, loop iterations and callbacks, and the supplied arguments of every call. RUN-08 holds the complete, closed list.
- A property named in a call is a supplied computation (CALL-02, NEED-10), so these uses differ:
  - A value access (`A`, `Obj.A`, a builtin value slot) evaluates the body at most once for its binding in its owning invocation (PROP-04).
  - Passing it as an argument is no access. A parameter that reads it demands the property's cached read once.
  - Invoking it with arguments runs its body afresh each time (PROP-06).
  - An explicit call `A()` stays fresh and never reads or replaces an entry. Its owning successful zero-supply invocation may establish an empty entry (PROP-06).
  - Caching keeps one successful value per binding. A failure is never cached (PROP-09), and a demanded failure ends the run (VAL-10).

```katlang
B, A
A = trace(1)
Unused = 1 / 0
B = trace(2)
```
⇒ `S[2, 1]`

`Unused` never runs, and `B` is evaluated first because the output row demands it first. `A = trace(1)` / `Ignore(x) = 0` / `Ignore(A), A` is `S[0, 1]` with one `trace(1)`, made by the root read. `A = tick()` / `Use(x) = x + x` / `Use(A), A` is `S[2, 1]` after one tick.

### PROP-03 — (retired: merged into RES-10)

### PROP-04 — A zero-parameter property is evaluated at most once for each resolved binding in its owning invocation: once per actual call of the owner around it, once per run where no call owns it

- A property-style read of a callable that an ordinary call supplying zero arguments can bind (CALL-05), a collecting-only `Only(*xs)` and a zero-argument host operation included, evaluates its body at most once for each resolved binding in its owning invocation: once in each actual call of the owner the property is declared under, and once per run where no call owns it — a root or module property, a member read from outside its owner's call (PROP-08).
- This holds in every value position, because the front end never lifts a bare name of such a callable into a call (PAR-07).
- Every value read of that binding that begins after its owning evaluation completed successfully reuses that evaluation's result for as long as that owning invocation's bindings are read: for the rest of the run when the binding is run-scoped. The owner is the binding's outermost qualifying evaluation: a property-style read, or an explicit zero-supply invocation that finds the entry empty (PROP-06, PROP-09).
- A re-entrant read, one that begins while the owner is still running, evaluates the body and returns its own, possibly different, intermediate result, publishing nothing (PROP-09).
- The rule is independent of purity. It holds identically for constant, random-backed and host-backed bodies.
- No other expression result, call result, or callable with a required argument is memoized by this cache. A supplied argument's at-most-once completion is a separate memo of that one supplied computation, never shared with another slot or with this cache (CALL-06, NEED-02, NEED-10).
- What counts as the same binding is PROP-07 and PROP-08, what creates the entry is PROP-09, and explicit calls are PROP-06.

**Qualifications**
- FWD-02 and FWD-03, not this rule's value position, decide the one written row of a non-root body (a root row is a value read):
  - An open body `A = Only` is an alias. It owns no entry: its bare read is `Only`'s own read under `Only`'s entry, so `A` and `Only` are one value.
  - Under a written list, `A(xs) = Only` is bare forwarding, the explicit call `Only(xs)`, fresh on every call of `A` (PROP-06).
  - A lone row that forwards nothing (`B(p) = Only`) is this cached read of `Only`.
- A callable that requires a supplied argument is not a value: a bare read is the zero-argument demand's `ArityMismatch` (CALL-05). A builtin never takes this path.
- "Once" never crosses runs: separate runs never share entries. Within a run it is once per owning invocation (PROP-08).
- For a deterministic body the cache is unobservable: cached and uncached evaluation give equal values.
- The guarantee is at most once for successful, non-re-entrant evaluations. A property whose body reads itself, directly or through other properties and calls, evaluates its body again for each re-entrant read, and only the owner's result is reused (PROP-09).
- A failed evaluation is final for the slot that demanded it (CALL-06): a parameter reports it on every read and never re-runs the body. Since a demanded failure ends the run, no separate later demand of the property happens in that run.

```katlang
Roll = randomInt(1, 1000000)
Roll == Roll, Roll() == Roll(), Roll == Roll()
```
⇒ `S[true, false, false]`

Eligibility follows actual call arity: `Only(*xs) = xs.count + tick() * 10` / `Only, Only, sum(Only), Only(), Only(1)` is `S[10, 10, 10, 20, 31]` after three ticks. No value position lifts it: `Only(*xs) = tick()` / `Only + Only, [Only], Only[0], abs(Only)` is `S[2, L[1], 1, 1]` after one tick. An alias reads its target's entry: `Only(*xs) = randomInt(1, 1000000)` / `A = Only` / `A == Only` is `true`. Bare forwarding calls and a lone row that forwards nothing reads: `Only(*xs) = xs` / `A(xs) = Only` / `A(5)` is `L[5]`, and `Only(*xs) = tick()` / `B(p) = Only` / `B(0), B(1), Only` is `S[1, 1, 1]`. Passing a property is no demand, and the first root read's failure ends the run: `B = if(tick() < 2, 1 / 0, tick())` / `Ignore(x) = 0` / `Ignore(B), B, B` is `DivisionByZero` after one tick.

### PROP-05 — How a property's value is consumed never causes its body to run again

- The decision to reuse or evaluate belongs to the property access, never to the consumer. Every value consumer receives the value that the one access produced.
- This covers operator and comparison operands, list and capture elements, selection `A[i]`, spread `A*`, and a callback body that reads the property.
- It covers user-call arguments in either spelling (`F(A)`, `A.F`) and the parameter they bind, forwarded any number of times. The parameter's first value demand is the property access, and every later read reuses that outcome, a failure included, without re-running the body (CALL-06).
- It covers every builtin value slot in written, dotted or grouped spelling (`sum(A)`, `A.sum`, `sum((A))`, `(A).count`, `take`, `first`, `range` and `atoms` arguments), the selected `if` branch and the condition, `repeat`'s count and `reduce`'s initial accumulator. A loop's initial state is the captured call's own arguments, which take that call's roles.
- It covers the `.string` receiver (`A.string`, `Obj.A.string`, and a parameter's `v.string`).
- No builtin has property-evaluation semantics different from a user algorithm's.
- The lifting positions among these consumers are every value role of PAR-07, Math, host-operation and clause-family arguments included. They receive the one access for every callable that accepts zero supplied arguments, a collecting-only one included, because the front end never lifts it into a fresh call.

**Qualifications**
- Slots that invoke their argument (`map`, `filter` and `reduce` callbacks, loop steps, `f()` on a forwarded callable) perform an explicit call, fresh by PROP-06. They are not value consumers, and passing the property to them is no access: `f()` projects the callable without a value demand (NEED-06).
- The mechanism lives in argument supply and callable projection, never in individual builtins (HO-04).

```katlang
A = tick() * 10
Two(v) = v + v
A, sum(A), A.sum, if(true, A, 0), A.string, Two(A), A.Two, A[0], [A, A]
```
⇒ `S[10, 10, 10, 10, '10', 20, 20, 10, L[10, 10]]`

One draw describes every consumer: `Data = randomInt(1, 10), randomInt(1, 10), randomInt(1, 10)` / `Stats(xs) = xs.sum, xs.max` / `Data, Data.sum, Data.max, Stats(Data)` is `S[S[9, 1, 2], 12, 9, S[12, 9]]`. An invoking use is fresh, and its first call establishes the entry (PROP-06): `A = tick()` / `Call0(f) = f()` / `Apply(f) = f + 1` / `Call0(A), Call0(A), Apply(A), A` is `S[1, 2, 2, 1]`, and `A = tick()` / `Call0(f) = f()` / `Call0(A), A, Call0(A), A` is `S[1, 1, 2, 1]`. A parameter never re-runs a failed body: `B = if(tick() < 2, 1 / 0, tick())` / `Pair(x) = x, x` / `Pair(B), B` is `DivisionByZero` after one tick.

### PROP-06 — Only property-style reads reuse the entry: an explicit call invokes afresh and never reads or replaces it, a zero-supply call may only establish an empty one, and freshness is local

*Open: whether an entry that an explicit zero-supply call establishes may hold a value computed from that call's own local-only members (Q-83).*

*Open: whether an inline carrier counts as an anonymous block for publication. An explicit call through a carrier may establish its target's empty entry, while an anonymous block never establishes one, and `{ A }` is both. Today `A = tick()` / `Call0(f) = f()` / `Call0({ A }), A` is `S[1, 2]`, while a named carrier `B = { A }` / `Call0(B), A` gives `S[1, 1]`. No decision or test pins the difference (audit finding A-1).*

- An explicit call (`A()`, `Obj.A()`, `(Obj.A)()`, an opened `A()`, any call with arguments `F(args)`, every invocation made by an invoking slot) evaluates the callee's body afresh. It never reads or replaces the callee's entry.
- A zero-supply invocation of a property binding **qualifies** when three things hold: its callee came from an identifiable property binding (a name, a structural or grouped path, a parameter's supplied cell, a selected member, a captured callee cell); its effective supply is empty after supply formation; and its callee accepts zero supplied arguments.
- A qualifying invocation whose entry is empty takes part in PROP-09's ownership. As the successful owner it establishes the entry, which later property-style reads reuse.
- A qualifying invocation never obtains its result from an established entry. A failing invocation propagates its own failure, even when an entry exists.
- A call with supplied arguments, a builtin, host-operation or Math-member call, an anonymous block, a computed callee, a callback invocation and a loop step never establish an entry.
- Freshness is local: property-style reads nested inside the fresh evaluation keep their own caching. `A()` re-runs only A's own body, never the bodies of the properties it reads.
- In an effect-free program `A` and `A()` give the same value. They differ only in effects and evaluation count.

**Qualifications**
- An explicit spread that contributes no slot leaves the supply empty. One supplied `()` or `[]` is one slot.
- What an owning invocation publishes is its own execution's property-level result, the result a read would publish. Its caller receives that execution at the ordinary call boundary.
- No alias owns an entry. An explicit call through a transparent reference or a forwarding carrier is its target's fresh call under the target's binding, so a qualifying one may establish the target's empty entry and never replaces an established one (FWD-03).
- A runtime reference whose target has a callable identity behaves the same way. A value-only runtime reference has nothing to invoke: its zero-supply call answers its binding cell's one value, never a rerun, and publishes nothing.
- An explicit deconstruction-target call `a()` freshly invokes the target's projection wrapper. It never reads a's own entry, and an `a()` that finds that entry empty establishes it. The wrapper reads the separately cached shared right-hand side and does not request a fresh evaluation of it, though a first target call can cause the right-hand side's first demand. Successful source caching stays per run for exported sources and per owner activation for local-only sources, under PROP-09. C# may reuse its shared binding, and Lean may rebind the same cached source (VAR-06).
- A parameterless owner called explicitly binds a fresh activation, so its local-only properties are recomputed. This holds however the zero-supply call is reached, a META `R.Algorithm()` from a root row included. A property-style read of the owner instead inherits its declaring activation (PROP-08), so `B + B.V` evaluates `V` once and `B() + B.V` evaluates it twice.
- An entry that such a call establishes holds a value computed from the call's own locals, so a later bare read can disagree with the declaring activation's member (Q-83, the example below).
- A forwarding carrier is not such an owner: it binds no activation of its own (PROP-08), so `B() + B.V` evaluates `V` once when `V` is its forwarding target.

```katlang
A = tick()
A(), A, A(), A
```
⇒ `S[1, 1, 2, 1]`

The first `A()` finds the entry empty and establishes `1`, both reads reuse it, and the second `A()` is fresh and replaces nothing. Grouping changes nothing: `Box = { public V = tick() }` / `Box.V, Box.V(), (Box.V)(), Box.V(), Box.V` is `S[1, 2, 3, 4, 1]`, and `Box = { public V = tick() }` / `(Box.V)(), Box.V` is `S[1, 1]`.

Freshness is local, and a reference is its target: `A = tick()` / `B = A, A` / `B(), B(), A` is `S[S[1, 1], S[1, 1], 1]` after one tick. `A = tock + 0` / `A, A(), tock, tock()` is `S[1, 1, 1, 2]`: `A()` re-runs the formula, whose `tock` read hits that entry. `A = tock` / `A, A(), tock, tock()` is `S[1, 2, 1, 3]`: `A()` is `tock`'s own fresh call, which establishes nothing. Calls with arguments are never memoized: `F(x) = x + tick()` / `F(0), F(0)` is `S[1, 2]`.

An effect-free program cannot tell them apart: `A = 1, 2` / `Cnt(*xs) = xs.count` / `A, A(), Cnt(A), Cnt(A())` is `S[S[1, 2], S[1, 2], 1, 1]`.

Aliases publish under their target: `P = tick()` / `A = P` / `B = { P }` / `A(), P, B(), B` is `S[1, 1, 2, 1]`, and `Capture(meta c) = c` / `Only(*xs) = tick()` / `R = Capture(Only())` / `A = R.Algorithm` / `A(), Only` is `S[1, 1]`. A value-only runtime reference reruns nothing:

```katlang
G(o) = tick()
Use(b) = {
  A = b.G
  A(), A, A(), A
}
Use(5)
```
⇒ `S[1, 1, 1, 1]`

A target call shares the cached right-hand side: `a, b = tick(), tick()` / `a, b, a, b, a()` is `S[1, 2, 1, 2, 1]`, and `a, b = tick(), 5` / `x = tick()` / `a, a(), a(), x, x(), x()` is `S[1, 1, 1, 2, 3, 4]`.

An explicit call of an owner is a fresh activation:

```katlang
F(x) = {
  Inner = {
    P = x + tick()
    P, P
  }
  Inner, Inner, Inner()
}
F(0)
```
⇒ `S[S[1, 1], S[1, 1], S[2, 2]]`

The open case. `B()` establishes `B`'s entry from its own locals, and `B.V` then draws in the declaring activation:

```katlang
F(k) = {
  B = {
    V = k + randomInt(1, 1000000)
    V + 0
  }
  B() * 0, B == B.V
}
F(0)
```
⇒ `S[0, false]`

With `V` as the lone row, `B` is a forwarding carrier of `V`, and the same program gives `true` in the last place:

```katlang
F(k) = {
  B = {
    V = k + randomInt(1, 1000000)
    V
  }
  B() * 0, B == B.V
}
F(0)
```
⇒ `S[0, true]`

### PROP-07 — Cache identity is the resolved binding, never the spelling or the access path

- Two property reads share one entry exactly when they resolve to the same declaration in the same declaring scope and, for local-only bindings, the same activation (PROP-08).
- A read of one binding shares its entry whether it is spelled lexically (`V`), structurally (`M.V`, `o.V` through a parameter bound to the container) or through `open`, and whichever spelling reads first.
- A shadowing declaration is a different binding with its own entry. Two separately written declarations are different bindings, even when their names and bodies are textually identical.
- A bare read through an alias is a read of its target's binding, under the target's owner and activation. An alias adds no binding to this rule (FWD-03).
- A loaded module is one declaration per canonical URL per program (MOD-09), so every reach of a module member is one binding, while a property holding the module is a binding of its own.

**Qualifications**
- Identity here concerns the value channel. Callable identity is ALG-07 and DOT-09.
- *Host contract (FORMAL-08).* A property declared in a host-built scope with no evaluator owner, such as the parent an opened inline block keeps or the head of a dotted open target, is owned by that scope object, compared by reference. Every such host level on a declaring chain counts by reference too, an empty or opens-only level and any ancestor included. Record-equal or `with`-copied host scopes are therefore different owners, and a host level never equals an evaluator-owned one. Rebuilt evaluator-owned levels keep their structural identity, so equivalent rebuilt owners share an entry. Lean represents host-object identity by one supplied token per object, an input contract it checks for consistency but cannot derive. No ordinary source program reaches these scopes.

```katlang
open M
M = {
  public V = tick()
}
Get(o) = o.V
V, M.V, Get(M), V.string
```
⇒ `S[1, 1, 1, '1']`

Shadowing:

```katlang
A = tick()
Inner = {
  A = tick()
  A, A
}
A, Inner, A
```
⇒ `S[1, S[2, 2], 1]`

Identical text, distinct declarations:

```katlang
F(x) = {
  P = tick()
  P + x
}
G(x) = {
  P = tick()
  P + x
}
F.P, G.P, F.P, G.P
```
⇒ `S[1, 2, 1, 2]`

Read from outside every call, each declaration has its own run-scoped entry. (Inside calls the two are distinct too, and every call has its own: `F(0), G(0), F(0), G(0)` is `S[1, 2, 3, 4]`, PROP-08.)

### PROP-08 — Storage follows the declaring binding and its owning invocation: every actual call of an owner has fresh inner bindings, reads in one call share them, and a binding no call owns is one value per run; exposure decides accessibility and detachment, never lifetime

*Open: whether Lean should state how exposure is classified; it takes exposure as input (Q-59).*

- Storage follows the resolved declaring binding and its OWNING INVOCATION: the nearest actual call of the owner chain the property is declared under. An actual call is a user call, a selected clause of a family, a loop round and an explicit zero-supply call `B()`; a property-style read is none.
- Every actual call of an owner has fresh bindings for the properties and runtime aliases declared under it, whether their definitions use the call's arguments or are self-contained.
- Reads inside one owning invocation share its entry, whoever reads: the owner's own rows, a callback, a helper, an opened name, a structural path. The name `A` and the path `F.A` are one binding when they resolve to the same active one. No consumer gives a binding another lifetime.
- A declaring chain no actual call entered — a root or module property, a member read from OUTSIDE its owner's call — has the separate run-scoped binding: one entry per run per declaring scope, which no call supplies and no call replaces. Outside every call an explicit `F.A()` is fresh, may establish the empty outside entry and never reads or replaces an established one (PROP-06).
- An exported property differs from a local-only one in accessibility and detachment, not in lifetime: it can be read from outside its owner's call, where it is the run-scoped binding, and its evaluation is detached (below).
- A local-only property reads an input that an enclosing owner's call binds: a captured parameter or a clause-branch binder of an enclosing owner, directly or transitively. It has one entry per activation of its declaring owner, taken from that owner's retained activation and never from the consumer's context.
- Consumers nested inside that activation (calls, callbacks, loops, builtins, `.string`) share the entry. Two activations never share an entry, even when their argument values are equal, and a recursive activation never reuses its caller's per-activation value.
- A parameterless owner entered through a property-style read inherits the binding context of its declaring activation, never that of the consumer that reads it first. That context is the nearest activated level of its in-context declaring chain, the one its own entry already carries. Only when no declaring level is activated (the root, an unactivated host-built scope) is the reader's context used.
- So a callback, helper, loop step, branch or `R.Invoke()` that reads the owner, and the owner's structural (`B.V`) or opened (`V`) members, select one entry in either order (PROP-07).
- A property-style read of an owner whose pattern list accepts the empty supply (a collecting-only `Only(*xs)`) inherits the declaring context too. The read binds that empty supply through the ordinary binder, so `xs` is exactly `[]` in the body and shadows any outer `xs`, and then records the declaring activation's context, or the reader's when no declaring level is activated.
- Eligibility is the binder's actual cardinality: `Fix(x, *xs)` and a grouped `Grp((*xs))` still refuse the empty supply.
- An explicit call of the owner (`B()`, `Only()`, `Only(1, 2)`, a META `R.Algorithm()`, a qualifying invocation of PROP-06) binds a fresh activation whose locals are its own. Every call binding boundary is a fresh activation, however many cells it binds.
- The classification is the front end's static dependency summary (RES-08). A syntactically present but dead read of an owner's parameter therefore makes the property local-only: inaccessible from outside its owner's call. It does not change how often a call evaluates it.
- The evaluator enforces the classification. The evaluation of an exported property, whether its read or its qualifying invocation (PROP-06), takes no input from its ENCLOSING CALLS — the activations of the levels enclosing the property that exist when it starts: those activations stay identities for keys, and supply no parameter, no local-only member and no local-only property. Any other activation that exists then belongs to a computation the evaluation did not run inside, typically the level of a callable a retained cell or another exported evaluation returned, and supplies that callable's inputs as always: with `Build(z) = { G(x) = x + z ⏎ Cap(G(0)) }`, `B = Build(5).Algorithm` and `Observe = B(1) + 0`, `B(2), Observe` is `(7, 6)` in either row order. A captured parameter is used through its lexical owner's activation. When that owner has no usable activation — it is static, or it is an enclosing call whose activation existed before the exported evaluation started — every executed operation on the written parameter is refused with `UnknownName`: its value read, a call through it, and its direct transport as a supplied argument, which fails while the supply is formed even when the callee ignores the argument. It never falls back to a caller's bindings. For a correctly classified program this changes no value, key or charge.
- The enforcement extends to retained runtime-alias binding cells, which the alias chase reaches instead of a property read. A retained cell — the cell of any non-parameter alias row — records the input reads of its computation through the activations that existed when it was established: its captured parameter operations, its admitted local-only property reads, its admitted accesses of a local-only member by a dot access, a static alias path step or an `open` that provides the name (recorded where the selected member is used: the lookup itself records nothing), and the recorded reads of a cell it reuses as far as they are its inputs too. A read through an activation the cell's own computation recorded is the cell's own work and no input. The cell of a local-only alias is established at its declaring level, whichever reader reaches it first.
- A reuse of the cell's value or callable — the alias's bare read, a zero-supply call of its value view, a step of the alias chase — by an evaluation that detaches an input the cell is known to have read (one of the cell's recorded reads is an enclosing call of that evaluation) is refused before the cell's channel runs, with `LocalOnlyProperty` naming the alias: no demand, no effect and no work of the cell happens. Any other reader shares the cell and is admitted.
- The demand decides the reads that follow. An input read the cell's computation makes — in its row, in a lazy position, in a captured call's argument — is refused at the read, with that read's own refusal (`UnknownName` for a captured parameter, `LocalOnlyProperty` for a member or a property), exactly when a detached evaluation that detaches the read's activation is being served — an exported evaluation in progress, or an admitted reader's reuse running the cell's channel — and the read is an input of a cell that admitted such a reader. A read an attached reader demands afterwards uses its own inputs: a detached reader may count a lazy list without restricting a later attached reader.
- `F(y) = { A = Sel(y).Algorithm ⏎ P = A(5) + 0 ⏎ A(5), P }` with `Cap(meta r) = r`, `Inc(n) = n + 1`, `Dbl(n) = n * 2` and `Sel(k) = if(k == 1, Cap(Inc(0)), Cap(Dbl(0)))`: `F(1), F(2)` is `((6, 6), (10, 10))` as classified. When `P` alone is declared exported it is `LocalOnlyProperty` for `A` (the row read `A` first, and `P` reuses a cell known to depend on `y`), and `UnknownName(y)` with the rows `P, A(5)` (`P`'s own demand reads `y`). With `F(y) = { Mk(v) = { Z(*xs) = [1, 2].map{ n + y } ⏎ Cap(Z()) } ⏎ A = Mk(5).Algorithm ⏎ P = A.count + 0 ⏎ A.count, P, A[1] }` and `P` alone declared exported, `F(1)` is `(2, 2, 3)`, and also with the rows `P, A.count, A[1]`: neither count needs `y`, and the element read belongs to `F`. With `P = A[0] + 0` it is `UnknownName(y)` in either row order.
- The judgment is conservative and never a wrong value: the record belongs to the cell, so a reuse answers for everything the cell's computation has read so far — a detached reader that would only count the list is refused once the row has read an element that needs `y`. A cell whose computation read no such input is shared exactly as before. A deferred read of the returned callable's own activation supplies its captured input (`Mk(y) = { Z(*xs) = [1, 2].map{ n + y } ⏎ C = Cap(Z()).Algorithm ⏎ G(i) = C[i] + 0 ⏎ Cap(G(0)) }`, `B = Mk(1).Algorithm`, `Observe = B(1) + 0`: `B(0), Observe` is `(2, 3)`, `Observe, B(0)` is `(3, 2)`).

**Qualifications**
- A forwarding carrier is no owner in this sense. Its bare read and its explicit call are its target's, resolved at the carrier's declaring activation (FWD-03).
- No module member is local-only with respect to a load site (MOD-08): a site parameter reaches a member only as an argument, so such a dependency is a call, fresh per evaluation (PROP-06).
- Loops follow the same law on the generic and planned paths: a round is an actual call of the step, so every step-local property is evaluated once per iteration, whether or not it reads the state.
- The accessibility of a local-only member from outside its owner is a separate rule (RES-08).
- *Host contract (FORMAL-08).* A host-built AST that declares a parameter-reading property exported is refused where the property reads, calls or transports the parameter (`UnknownName`; `LocalOnlyProperty` where it reaches a local-only member or property). The evaluator enforces exposure metadata on those paths, at every reuse of a retained runtime-alias cell and at the input reads of its computation (above); correct exposure metadata remains the host's obligation, because the enforcement can only turn a wrong flag into a refusal. A falsely exported property declared inside a returned callable's level and read through the callable is refused like any other, since that level encloses it. One access is not recorded: the admitted access of a local-only member step of an `open` TARGET's path (`open Box.Sub`) made inside a retained cell's computation, so a falsely exported property that reuses a cell whose computation selected a name through such an `open` is not refused (formal ledger row R-1, qualified; no wrong value is known). A host level that names a parameter it never activates makes that parameter unavailable too. A property declared in an ownerless host-built scope follows PROP-04 to PROP-09, owned by the host scope object (PROP-07). A local-only host property has no declaring activation and keys on the access binding context.

```katlang
F(x) = {
  B = tick()
  B + x
}
G(x) = {
  C = tick() + x
  C + C
}
F(10), F(20), G(1), G(1)
```
⇒ `S[11, 22, 8, 10]`

`B` is exported and `C` reads `x`; each call evaluates its own either way, so equal arguments are still two entries. Read from outside every call, `B` is the run's own:

```katlang
F(x) = {
  B = tick()
  B + x
}
F(10), F.B, F(20), F.B
```
⇒ `S[11, 2, 23, 2]`

A consumer never splits the owner's entry, in either order:

```katlang
F(k) = {
  B = {
    V = k + tick()
    V + 0
  }
  [1].map{ n * 0 + B }[0] == B.V
}
F(0), tick()
```
⇒ `S[true, 2]`

A collecting-only owner reads the same way:

```katlang
F(k) = {
  Only(*xs) = {
    V = k + tick()
    V
  }
  Only == Only.V
}
F(0), tick()
```
⇒ `S[true, 2]`

A recursive activation keeps its own value:

```katlang
F(n) = {
  P = n * 10 + tick() * 0
  if(n == 0, P, P + F(n - 1))
}
F(2)
```
⇒ `30`

A dead read changes accessibility, not how often a call evaluates the property; with or without the `x` in the branch the two calls below evaluate `B` once each, and with it `F.B` from outside is `LocalOnlyProperty`:

```katlang
F(x) = {
  B = if(false, x, tick())
  B + x * 0
}
F(0), F(0)
```
⇒ `S[1, 2]`

Step-local properties, each once per iteration:

```katlang
Step(s) = {
  E = tick()
  L = s + tick()
  L + E * 0 + L * 0
}
repeat(Step(0), 3), tick()
```
⇒ `S[9, 7]`

### PROP-09 — A binding's entry is created only by its outermost evaluation, and only if it succeeds; the entry is final for the run

- A failed evaluation of a property is never stored: a later read of the same binding, if one occurred, would evaluate again.
- The entry of a binding, its cache key under PROP-07 and PROP-08, is created only by its **owning evaluation**: the qualifying evaluation that begins while no evaluation of the same key is running. A qualifying evaluation is a property-style read that misses, or a qualifying zero-supply invocation that finds the entry empty (PROP-06).
- While the owner runs, the key is **active**. A qualifying evaluation of the same key, a read or an invocation, directly or through other properties and calls, an explicit call's frame included, is **re-entrant**. It evaluates and returns its own, possibly intermediate, result, and it must not create, replace or otherwise affect the entry.
- When the owner completes successfully, its result becomes the entry, every later read of the binding in the run reuses it, and nothing replaces it.
- A failed owner creates no entry for its key: no same-key result computed during the failed attempt becomes the entry. The key stops being active on every exit.
- A failure of an enclosing evaluation does not roll back entries that the owning evaluations of other keys created.
- A qualifying explicit zero-supply call owns a key exactly as a read does: `A()` on an empty, inactive key is its owner, and a read or call of `A` nested inside it is re-entrant.

**Qualifications**
- KatLang has no error recovery, and every demanded failure ends the run (RUN-07, RUN-08). So no source program reads a property again after its evaluation failed, and "a failed evaluation is never stored" and "no rollback" are unobservable from source. A host can observe both through passive root-property observations for exported root properties; a forwarding binding is never observed under its own name, since it owns no entry.
- Ownership is observable through re-entrancy. Two ordinary reads of one binding always agree. Re-entrant reads made while the owner runs are evaluations, not reads of the entry, and may return intermediate values.
- Ownership is per key: another binding, or the same local-only binding under another owner activation, has its own owner. A parameterless owner's lexical `V` and a re-entrant structural `B.V` are one key, so the inner read is re-entrant rather than a second owner (PROP-08).
- Within one run evaluation is serial, so the active owners are the evaluations on the current chain, and a re-entrant read never waits for its owner.

```katlang
A = if(tick() < 3, A + 1, 0)
A, A
```
⇒ `S[2, 2]`

The first root read owns the key. Its body reads `A` again (re-entrant, second tick), which reads `A` again (re-entrant, third tick) and returns `0`; the middle read returns `1`; the owner returns `2` and publishes it, so the second root read returns the published `2` after three ticks.

Siblings each evaluate, since neither publishes: `A = if(tick() < 3, A + A, 1)` / `A, A` is `S[3, 3]` after five ticks. Each key's owner publishes what it computed: `A = if(tick() < 3, B + 1, 0)` / `B = A + 1` / `A, A, B, B` is `S[4, 4, 3, 3]`. An explicit call owns an empty key: `A = if(tick() < 3, A + 1, 0)` / `A(), A` is `S[2, 2]`, and `A = if(tick() < 3, A() + 1, 0)` / `A(), A` is `S[2, 2]` after three ticks.

A failure is never stored, and it ends the run: `B = if(tick() < 2, 1 / 0, 7)` / `K(f) = 5` / `K(B), B, B` is `DivisionByZero` after one tick. `K` never demands `B`; the first root read fails.

Ownership per key, by activation:

```katlang
F(x) = {
  P = if(x == 0, tick(), F(x - 1) + 10)
  P + P
}
F(1), tick()
```
⇒ `S[24, 2]`

One key through two spellings:

```katlang
F(k) = {
  B = {
    V = if(tick() < 3, B.V + 1, k)
    V
  }
  [0].map{ n + B }[0] + B.V
}
F(10), tick()
```
⇒ `S[24, 4]`

## BOOLCMP — Booleans, truth, comparison chains, and builtin `if`

KatLang has a Boolean value kind. Only that kind has a truth value, and Booleans and numbers never convert into each other. The six comparison operators share one tier and form **chains** whose meaning is the conjunction of adjacent links. A chain evaluates every operand exactly once, left to right, goes on past a `false` link and stops at the first error. `==`/`!=` is total structural equality, while ordering is defined only on numeric scalars. Builtin `if` is the language's one lazy selector: it demands its Boolean condition, then only the selected branch. `and` and `or` evaluate their right operand only when their left operand does not decide the result (BOOL-04).

### BOOL-01 — `true`/`false` are a scalar kind of their own, written only as reserved literals, with no Boolean-specific structural rules

- `true` and `false` are the two values of the Boolean kind, a scalar kind distinct from numbers, strings, sequence values and list values.
- Booleans are written only as the reserved literals `true`/`false` (SYN-01). In clause heads they are literal patterns (PAT-05).
- Booleans come from the literals, comparison chains (CMP-01), `and`/`or`/`xor`/`not` (BOOL-04) and `contains`. Host operations may also return them.
- Apart from their kind, Booleans obey the structural rules of every other scalar. There is no Boolean-specific rule for normalization, sequencing, lists, binding, collecting, callbacks, caching or selection.
- A Boolean displays as lowercase `true`/`false`.

**Qualifications**
- `true = 1` followed by a row `2` is the front-end `UnexpectedToken`: a reserved literal cannot be declared, shadowed or inferred as an implicit parameter. In `G = true and x` only `x` becomes a parameter, so `G(false), G(true)` is `S[false, true]`.
- `(true)` is `true` by redundant grouping (SYN-06). `[true]` is a one-element list, not a Boolean (SEQ-01).
- The list of all value kinds is VAL-01.

```katlang
F(true) = 'yes'
F(false) = 'no'
F(1) = 'one'
F(1 < 2), F(false), F(1), true == 1, [true, 1], (true), count((true, false))
```
⇒ `S['yes', 'no', 'one', false, L[true, 1], true, 2]`

### BOOL-02 — Only a Boolean has a truth value

*Open: Q-54, whether the formal singleton clause of the truth view is reachable from source.*

- Every position that needs a condition reads the one Boolean view, which accepts a Boolean value and nothing else. The positions are the builtin `if` condition, each `filter` predicate result, the `while` continuation flag (the step's last output), every operand of `not` and `xor`, the left operand of `and` and `or`, and their right operand when it is evaluated (BOOL-04).
- Everything else is rejected with `TypeMismatch`: numbers (0, nonzero, NaN), strings, `()`, lists (`[true]` included) and multi-item sequence values (`(true, true)` and `(true, ())` included).
- There is no 0/nonzero truth, no first-atom flattening and no truth for collections. A predicate or flag must be exactly one Boolean value.
- A non-Boolean `while` flag is reported at the row that supplied the flag.

**Qualifications**
- The formal view also accepts a redundant singleton sequence around a Boolean. No canonical value has that shape (VAL-03), so the clause is defensive, for host-built non-canonical values only.
- `(true)` is accepted because it is the same node as `true`.
- Where the flag sits and what `while` returns is LOOP-06. The callback shape of `filter` is HO-02 and HO-03.

```katlang
Sign(x) = if(x < 0, 'negative', 'non-negative')
Sign(-2), Sign(0), range(1, 6).filter{x mod 2 == 0}
```
⇒ `S['negative', 'non-negative', L[2, 4, 6]]`

Each of these is a `TypeMismatch`: `if(1, 10, 20)`, `if([true], 10, 20)`, `if((), 1, 2)`, `if('true', 1, 2)`, `range(1, 4).filter{x mod 2}`, `not 0`, `if(sqrt(-1), 1, 2)`, and `Step(x) = x - 1` / `Step(3).while` (the flag is the number 2). With `P(x) = true, true`, `range(1, 3).filter(P)` is a `TypeMismatch` too, because the result is a two-item sequence.

### BOOL-03 — A Boolean is never a number: no numeric projection, no implicit conversion

- No numeric consumer reads a Boolean as `0`/`1`. That covers arithmetic operands and unary `-`, the ordering comparisons (CMP-04), `range` bounds, `take`/`skip`/`repeat` counts, Math natives, and the elements of the numeric collection builtins (`sum`, `avg`, `min`, `max`, `order`, `orderDesc`). Each is a `TypeMismatch`.
- Atom views omit Booleans: `atoms` omits them.
- No operation implicitly converts a number to a Boolean, or a Boolean to a number or to text. `.string` keeps its numeric-receiver contract (`true.string` is `TypeMismatch`), so nothing in the language turns a Boolean into text. A conversion is written explicitly, for example `if(b, 1, 0)` or `x != 0`.

**Qualifications**
- Booleans are unordered (CMP-04). `==` stays total, so `true == 1` is `false`, not an error (CMP-03).
- `count` counts Booleans as ordinary items.

```katlang
ToNum(b) = if(b, 1, 0)
sum(map([3 > 1, 2 > 5, true], ToNum)), atoms((true, 1, [2, false])), count((true, false, 1))
```
⇒ `S[2, L[1, 2], 3]`

`true + 1`, `-true`, `true < false`, `range(1, true)`, `sqrt(true)`, `sum((1, true))`, `max((true, 1))`, `take((1, 2, 3), true)` and, with `Inc(x) = x + 1`, `Inc(0).repeat(true)` are all `TypeMismatch`. So is `Flag.string` for `Flag = 3 > 2`.

### BOOL-04 — `and` and `or` evaluate their right operand only when their Boolean left operand does not decide; `xor` evaluates both operands, left to right, before validating either; `not` takes one Boolean

- **`and` and `or`** (issue #202). The left operand is evaluated once and must be a Boolean (BOOL-02). Its failure, or its rejection, is the expression's outcome before any work on the right operand.
- When the left operand decides the operator — `false and _` is `false`, `true or _` is `true` — that Boolean is the result and the right operand is not evaluated: it runs no effect, draw or host call, raises no failure, is never checked for a Boolean, charges nothing, and demands no parameter or property that only it reads.
- Otherwise the right operand is evaluated once and must be a Boolean, and it is the result.
- **`xor`** needs both operands. It evaluates the left and then the right operand, and only then requires the left and then the right one to be a Boolean, so an error while evaluating its right operand takes precedence over a non-Boolean left one (OP-03).
- **`not`** evaluates its operand, which must be a Boolean.
- Every result is a Boolean. Only evaluation skips: both operands of each binary logical operator are parsed, resolved and elaborated as written, so a skipped operand still takes part in parameter inference, forwarding and lifting, and still reports its front-end errors (NEED-05).

**Qualifications**
- The short circuit belongs to `and` and `or` only. Arithmetic operators never short-circuit (OP-03), a comparison chain evaluates every operand past a `false` link (CMP-02), and builtin `if` stays the one lazy selector (BOOL-05). A guard can be written with `and` as well as with `if`: `Safe(n, d) = d != 0 and n / d > 1` never divides by zero.
- Every route agrees, and the planned loop never enters a skipped operand's plan: `Step(s) = s + 1, s < 5 and 60 / (5 - s) > 0` / `while(Step(0))` is `5`, and with `60 / (4 - s)` it is `DivisionByZero`, on every strategy.
- Where `not` sits on the precedence ladder and the parse error for a misplaced `not` are OP-01 and OP-02. `()` is never an operator identity (OP-04, VAL-04); as an evaluated logical operand it is a non-Boolean rejected by BOOL-02.

```katlang
false and tick() == 1, true or tick() == 1, tick()
```
⇒ `S[false, true, 1]`

Neither right operand runs, so the last row takes the run's first tick. `tick() == 1 and tick() == 9 and tick() == 3, tick()` is `S[false, 3]`: the chain stops at its first `false`. `true xor tick() == 1, tick()` is `S[false, 2]`: `xor` evaluates its right operand whatever the left one is.

`Safe(n, d) = d != 0 and n / d > 1` / `Safe(10, 0), Safe(10, 2)` is `S[false, true]`. `false and 1 / 0 > 0` is `false` and `true or 1 / 0 > 0` is `true`, while `true and 1 / 0 > 0` and `false or 1 / 0 > 0` are `DivisionByZero`. A parameter that only a skipped operand reads is never demanded: `F(a, b) = a and b` / `F(false, 1 / 0 > 0)` is `false`, and with `or` in place of `and` it is `DivisionByZero`.

The left operand is judged first: `1 and 1 / 0 > 0` is `TypeMismatch` and the division never runs, while `1 / 0 > 0 and 1` is `DivisionByZero`. `1 and true`, `true and 1` and `'x' and true` are `TypeMismatch`, naming the left, the right and the left operand respectively, while `false and 1`, `true or 'x'` and `false and ()` are `false`, `true` and `false`: a skipped operand's kind is never checked. `false xor 1 / 0 > 0` is `DivisionByZero`, and `true xor 1` is `TypeMismatch`. `F = false and missing` makes `missing` a parameter of `F`, and `F(x) = false and missing` / `F(1)` is `UndeclaredIdentifier`.

### BOOL-05 — Builtin `if` demands its Boolean condition first, then exactly the selected branch; the unselected branch is never demanded

When the name resolves to the prelude builtin `if(condition, whenTrue, whenFalse)`:

- Spread arguments are formed (and so evaluated) first, as in every call (CALL-02, CALL-03). Then exactly three arguments are required, and the arity is checked before any non-spread argument is evaluated. A wrong-arity `if` evaluates no written argument: `if(trace(true), trace(1))` is `ArityMismatch` with no host trace.
- The condition is demanded as a value and must be a Boolean (BOOL-02). It is always demanded, through a wrapper too.
- Exactly the selected branch is demanded as a value. A non-spread unselected slot is never evaluated, and a callable there is never entered.
- The result is the selected value as ONE value (VAL-06): with `X = 1, 2, 3`, `if(true, X, 0), if(true, X, 0)*` is `S[S[1, 2, 3], 1, 2, 3]`.
- The rule belongs to the resolved builtin identity and holds for every spelling that reaches it: `if(c, t, e)`, `c.if(t, e)`, an alias of `if`, and a parameter bound to `if` and called with written arguments.

**Qualifications**
- Spread slots are not lazy. A spread is formed before the condition is demanded, and the items it supplies are already evaluated: `A = trace(7)` / `if(trace(false), A*, 9)` is `9` after `trace(7), trace(false)`, and `T = true, 10, trace(20)` / `if(T*)` is `10` after `trace(20)`. A non-spread slot beside a spread stays lazy: with `A = true, trace(1)`, `if(A*, trace(2))` is `1` and `trace(2)` never runs.
- A wrapper keeps the selection, because its parameters are suspended computations passed on unevaluated: `MyIf(c, t, e) = if(c, t, e)` / `MyIf(true, trace(1), trace(2))` traces only `trace(1)`. `Apply3(f, a, b, c) = f(a, b, c)` / `Apply3(if, true, 10, 1 / 0)` is `10`.
- Shadowing `if` replaces the rule with the user callee's own demands: `if(a, b, c) = b + c` / `if(true, 1, 1 / 0)` is `DivisionByZero`, while `if(a, b, c) = b` demands only `b`. A clause family selects by inspection: `Choose(true, yes, no) = yes` / `Choose(false, yes, no) = no` / `Choose(true, trace(1), trace(2) / 0)` is `1` after `trace(1)`.
- A zero-argument value demand (CALL-05) applies only to the selected slot. With `Inc(x) = x + 1`, `K(z) = if(false, Inc, 7), if(true, 7, Inc)` / `K(0)` is `S[7, 7]`, while `K2(z) = if(true, Inc, 7)` / `K2(0)` is `ArityMismatch`. The same rows at the program root are formulas that lift `Inc` (PAR-07) and give `UnresolvedImplicitParams`.
- Laziness covers value demand, not name resolution. A written name that reaches an open level with two providers is `AmbiguousOpen` whether or not its slot is selected (RES).
- A named zero-parameter property in a slot is read through the run cache (PROP-05, PROP-06): `A = tick()` / `A, if(true, A, 0), if(false, 0, A), A()` is `S[1, 1, 1, 2]`.
- The planned loop and fused filter-count keep the laziness. Other lazy builtin slots (loop steps, `atoms`/`range` arity before evaluation) belong to LOOP, COLL and CALL.

```katlang
SafeDivide(n, d) = if(d == 0, 0, n / d)
SafeDivide(10, 4), SafeDivide(1, 0), if(trace(false), trace(1), trace(2))
```
⇒ `S[2.5, 0, 2]`

The host log is `trace(false), trace(2)`.

### CMP-01 — The six comparison operators form one chain of adjacent links; a chain is one Boolean, `true` iff every link holds; parentheses end a chain

- `<`, `>`, `<=`, `>=`, `==` and `!=` share one precedence tier.
- Consecutive unparenthesized comparison operators at one syntactic level form ONE chain `e0 op1 e1 op2 e2 … opn en`, meaning the conjunction of the adjacent links `e(i-1) opi ei`. Its value is a single Boolean, `true` iff every link holds.
- Operators mix freely, and `!=` constrains adjacent pairs only (`1 != 2 != 1` is `true`).
- A parenthesized comparison is an ordinary operand and never merges into an enclosing chain: `(a < b) == c` compares a Boolean, and `a < (b == c)` orders against a Boolean.
- A chain's running Boolean never becomes the operand of its next link, so the C-style left-associative reading exists only through written parentheses.

**Qualifications**
- `1 < 2` followed on the next line by `== true` is one chain (SYN-08): its links are `1 < 2` and `2 == true`, so the value is `false`.
- A spread is never a chain operand: `A* == A*` is the parse failure `MisplacedSpread` (SUP-05).
- `not` negates the whole chain, and arithmetic binds inside operands (OP-01, OP-02).

```katlang
1 < 2 < 3, 1 != 2 != 1, 1 == 1 == 1, 1 < 2 == true, (1 < 2) == true, 3 < 2 < 1, 1 == 1 < 2
```
⇒ `S[true, true, true, false, true, false, true]`

`IsTeen = 13 <= age <= 19` / `IsTeen(15), IsTeen(21)` is `S[true, false]`. `1 < (2 == 2)` is `TypeMismatch`. `not 1 < 2 < 3, 1 < 2 < 3 and 4 < 5, 1 + 1 < 3 * 1 <= 4 - 1` is `S[false, true, true]`.

### CMP-02 — A chain evaluates every operand exactly once, left to right and incrementally; a `false` link never stops it; the first error does

- A chain evaluates `e0`. Then, for each link in written order, it evaluates that link's operand once and immediately applies the link to the previous operand's value and the new value.
- Every operand is evaluated exactly once. The chain is never re-read as `a < b and b < c`.
- A `false` link does not stop the chain: every later operand is still evaluated and every later link applied.
- The first error, whether an operand's evaluation or a link's rejection, ends the chain, and no later operand is evaluated.
- The same order and counts hold on every execution path: generic, async twin, planned loop and fused filter-count.

**Qualifications**
- Resource-limit errors and host cancellation also end a chain (RUN-03).

```katlang
trace(1) < trace(3) < trace(2) < trace(5)
```
⇒ `false`

The host log is `trace(1), trace(3), trace(2), trace(5)`: every operand once, even after the false link `3 < 2`. `0 < tick() < 2, tick()` is `S[true, 2]`, so the middle operand is read once. `trace(3) < trace(2) < trace(true)` is `TypeMismatch` at the link `2 < true`, after all three traces. `trace(1) < trace(true) < trace(5)` is `TypeMismatch` after `trace(1), trace(true)`, and `5` is never evaluated. `3 < 2 < 1 / 0` is `DivisionByZero`. In `trace(1 / 0) < trace(true) < trace(1)` the first operand's error wins and nothing is traced.

The planned loop agrees: `W(n) = n + 1, 0 <= trace(n) < 3` / `W(0).while` is `3`, with `trace(0)` to `trace(3)` once each. So does fused filter-count: `range(1, 5).filter{1 < trace(x) < 4}.count` is `2`, tracing each of 1 to 5 once.

### CMP-03 — `==` and `!=` are total, kind-exact structural equality over every value

- `a == b` is defined for every pair of values and never raises an error of its own. `!=` is its negation.
- Two values are equal when they are the same kind and structurally equal:
  - numbers by numeric value (CMP-05 refines this on the runtime tier);
  - strings by exact ordinal text;
  - Booleans by value;
  - sequence values and list values by length plus pairwise equality, recursively, with the kind checked at every level;
  - call references exactly when they denote the same invocation plan, and an argument view only equals the same plan's view, never its reference (`R == R.Arguments` is `false`).
- Values of different kinds are simply unequal: a Boolean never equals a number, a list never equals a sequence, and `[] != ()`.
- Equality compares canonical values: redundant grouping has already normalized (`(7) == 7`, `(()) == ()`). It never opens a value; there is no element-wise comparison.
- `contains` and `distinct` use the same equality (COLL-07), and so does repeated-name pattern binding (PAT-09).
- Equality reads both operands whole, the left one first, before it compares: every position of a list evaluated on demand is read, depth first (SEQ-02), so a failing element fails the comparison even where earlier elements already differ. `[1, 1 / 0] == [2, 3]` is `DivisionByZero`, and `[trace(1)] == [trace(2)]` is `false` after `[trace(1), trace(2)]`.

**Qualifications**
- Only values can be compared. `A = {}` / `A == ()` is `MissingOutput`, because `{}` has no output (VAL-05). `A* == A*` is the parse failure `MisplacedSpread` (SUP-05), while the grouped `(A*) == A` is `true`.
- In C# the structural and long-string work of an equality is charged as host resource policy and observes host cancellation (RUN-03). A refused charge is the run's terminal resource-limit error, never inequality.

```katlang
(1, (2, 3)) == (1, (2, 3)), [1, 2] == (1, 2), [7] == 7, (7) == 7, true == 1, 'a' == 1, () == (()), [] == (), 'a' != 'A', [[1], 2] == [[1], 2]
```
⇒ `S[true, false, false, true, false, false, true, false, true, true]`

`[1, 2].contains(2)` is `true`, and `distinct((1, (1), [1], true, 1))` is `L[1, L[1], true]`.

### CMP-04 — Ordering (`<`, `>`, `<=`, `>=`) is defined only between numeric scalars

- An ordering link requires both operands to be numeric scalars.
- Each of these is a `TypeMismatch`: a string operand, a Boolean, `()`, a multi-item sequence value, and a list value (`[1]` included).
- No other value kind is ordered: there is no Boolean order (`false < true` is an error), no string order, and no structural or lexicographic order on collections.

**Qualifications**
- `order`/`orderDesc` use a separate relation, the stable sort under the Decimal128 total order (COLL-06). `min`/`max` use IEEE minimum/maximum (OP-13).

```katlang
2 < 3, -1 >= -1, 0.5 <= 1 / 2, 10 > 9.99
```
⇒ `S[true, true, true, true]`

`'a' < 'b'`, `'a' < 1`, `(1, 2) < (1, 3)`, `() < 1`, `[1] < 2` and `false < true` are `TypeMismatch`.

### CMP-05 — On the Decimal128 runtime tier, numeric equality is value equality — representation is not part of it — while ordering is IEEE

*Open: Q-56, whether the NaN split below is stated as an accepted exception.*
*C#-only by design.*

- Number leaves compare with `Decimal128.Equals` value semantics, so `==` is a reflexive equivalence relation: NaN equals NaN, `-0 == 0`, and quantum (trailing zeros) is ignored (`1.0 == 1.00`).
- The ordering operators follow IEEE: every ordering comparison involving NaN is `false`, and `-0 < 0` is `false`.
- Consequently `N == N` is `true` while `N <= N` is `false` for a NaN `N`. `contains` and `distinct` inherit the equality side.
- This equality is the language's one value relation (VAL-11). The representation it ignores (quantum, zero sign, NaN sign) is data the value carries, observable through `.string` (OP-14), never a second equality.

**Qualifications**
- Lean's `Int` numbers have no NaN, no signed zero and no quantum, so on the exact-integer tier CMP-03 alone applies (FORMAL-04).
- `order` uses a third relation (COLL-06). `min`/`max` decide `-0`/`0` by sign, while `==` does not (OP-13).

```katlang
N = (-2) ^ 0.5
M = (-3) ^ 0.5
N, N == M, N != M, N < M, N >= M, N <= N, 0 == -0, -0 < 0, 1.0 == 1.00, [N] == [M]
```
⇒ `S[NaN, true, false, false, false, false, true, false, true, true]`

The two NaNs are computed independently, so the result does not come from reference identity.

## OP — Operators and numerics

This section covers how operator expressions group, the order in which their operands are evaluated, the operand kinds they accept, what a number is, and the text a number converts to. In the runtime a number is an IEEE 754 Decimal128 value (34 significant decimal digits); the Lean model uses unbounded `Int`, and which numeric laws the two share is FORMAL-04's two-tier rule. A **quantum** is the trailing-zero scale a number carries. The Math library appears here only for two laws: every spelling of a Math member is the same function (OP-11), and a numeric-domain violation is a value (OP-07). Its inventory, accuracy and rounding modes are library surface and not constitutional.

Owned elsewhere and not restated here: the two-tier correspondence (FORMAL-04); comparison chains, total `==`/`!=` and IEEE ordering (BOOLCMP); the Boolean-only logical operators (BOOL-04); prelude shadowing (RES); random members (RAND); numeric collection-builtin elements and `order` (COLL, COLL-06); the error-kind taxonomy (FORMAL-06); literal spelling and line continuation (SYN-02, SYN-08); a spread as an operand (SUP-05); value and representation identity (VAL-11).

### OP-01 — Operators group by one fixed precedence ladder; `^` is right-associative and binds tighter than prefix minus

*Resolved (Q-57, owner decision 2026-11-27): the order `or` < `xor` < `and` is confirmed, with the reason given in the second bullet. The reason was adopted on that date; the original reason for the parser's ordering was undocumented.*
*C#-only by design.*

- From loosest to tightest: `or`, `xor`, `and`, prefix `not` (OP-02), the ONE comparison tier (`<` `>` `<=` `>=` `==` `!=`), `+` `-`, `*` `/` `div` `mod`, prefix `-`, `^`, and the postfix forms: member access `.`, postfix selection `[…]`, call application and the postfix spread marker `*`.
- `xor` binds less tightly than `and` so each side of an exclusive choice can express a conjunction. It binds more tightly than `or` so the whole exclusive choice can serve as one alternative in a larger disjunction. Thus `a or b and c xor d and e` groups as `a or ((b and c) xor (d and e))`.
- The only prefix operators are `not` and `-`. There is no unary `+`: `+1` is the parse error `UnexpectedToken`.
- `or`, `xor`, `and`, `+`, `-`, `*`, `/`, `div` and `mod` are left-associative (`10 - 4 - 3` is `(10 - 4) - 3`). Consecutive comparisons form one chain (BOOLCMP).
- `^` is right-associative. Its base is parsed at the postfix level and its exponent re-enters the prefix-minus level, so `-a ^ b` is `-(a ^ b)`, `a ^ -b` is legal and `a ^ b ^ c` is `a ^ (b ^ c)`.
- Postfix forms apply left to right in written order, each to the whole postfix expression before it: `A[0].G` is `G(A[0])`, `A.count[0]` selects from the result of `A.count`, and `A[0]*` selects and then spreads.
- Prefix minus binds looser than every postfix form, and there are no negative numeric tokens: `-2.abs` is `-(2.abs)` and `-A[1]` is `-(A[1])`.
- Unary `-` and negative literal pattern signs require direct attachment. `-2`, `--2`, `2 ^ -2` and `F(-2)` are eligible; detached `- 2`, `2 ^ - 2` and `F(- 2)` are syntax errors. Binary subtraction keeps ordinary spacing and grammar-priority continuation (SYN-08).
- Explicit parentheses override the ladder (SYN-06). Postfix Grace `~` is a marker on a bare name, not a tier (SYN-12).

**Qualifications**
- OP-03 governs arithmetic operand evaluation. Even though `^` groups to the right, `trace(2) ^ trace(3) ^ trace(2)` traces 2, 3, 2 in source order.
- BOOL-04 and issue #202 govern Boolean operand evaluation. `and` skips its right operand when its left is `false`, and `or` skips its right operand when its left is `true`. `xor` needs both Boolean operands.
- `(-2) ^ 2` is 4: the group makes the negation the base.
- A spread is not an operand. `A = (1, 2)` / `-A*, 0` is the parse failure `MisplacedSpread` at the closed `A*`, and so are `not A*, 0` and the attached line-final `-A*` and `not A*`. Only a detached `-A *` leaves line-final multiplication missing its operand (SYN-11).
- Newline and line-final-star classification belong to SYN-08 and SYN-11.

```katlang
true or false and false, true xor true and false, 2 + 3 * 4, 10 - 4 - 3, 2 * 3 ^ 2, -2 ^ 2, 2 ^ 3 ^ 2, 2 ^ -2
```
⇒ `S[true, true, 14, 3, 18, -4, 512, 0.25]`

`A = (10, 20)` / `G(x) = x + 1` / `A[0].G, A.count[0], G(A[1]), [5, 6].count[0], A[1].string` is `S[11, 2, 21, 2, '20']`. `2 ^ -2 ^ 2` is `0.0625`.

```katlang
Ready(testMode, mainOn, mainHealthy, backupOn, backupHealthy) = testMode or mainOn and mainHealthy xor backupOn and backupHealthy
Ready(true, true, true, true, true)
```
⇒ `true`

The body groups as `testMode or ((mainOn and mainHealthy) xor (backupOn and backupHealthy))`. Each conjunction describes one usable source. In normal mode exactly one source must be usable. A true `testMode` suffices on its own. Each boundary can be observed: `true or false xor true` is `true or (false xor true)`, which is `true`, while `(true or false) xor true` is `false`; and `true xor true and false` is `true xor (true and false)`, which is `true`, while `(true xor true) and false` is `false`.

### OP-02 — Prefix `not` sits between the logical operators and the comparisons, and is never silently regrouped

*C#-only by design.*

- `not` binds looser than every comparison, arithmetic and power operator, and tighter than `and`, `xor` and `or`: `not x > 3` is `not (x > 3)`, `not a < b < c` negates the whole chain, `not 0 ^ 0 == 1` is `not ((0 ^ 0) == 1)`, `not a and b` is `(not a) and b`, and `not not x` nests.
- A `not` written where a comparison, arithmetic, power or prefix-minus operand is required is a front-end syntax error at the keyword (`1 + not x`, `a == not b`, `2 ^ not x`, `-not x`). It is never reinterpreted with another grouping, and the program never evaluates. The verdict is the rule; the code is today `UnexpectedToken`.
- Written parentheses make the operand legal: `(not x) > 3` compares the negation itself.
- What `not` accepts (Booleans only) is BOOL-02.

**Qualifications**
- Same-line `x * not y` reports `InvalidSpreadMarker` under the malformed-spread recovery classification. After an attached line-final star the spread is complete and a later-line `not` is its own row; after a detached one SYN-11 diagnoses the missing multiplication operand.
- A line ending in `not` continues onto the next line (SYN-08).

```katlang
x = 1
not x > 3, not true and false, not 1 < 2 < 3
```
⇒ `S[true, false, false]`

`1 + not x` and `-not true` are the parse failure `UnexpectedToken`. With `x = 2`, `(not x) > 3` is `TypeMismatch`.

### OP-03 — Arithmetic operators evaluate operands in source order before checking their kinds

- Scope: the arithmetic operators `+ - * / div mod ^` and prefix `-`. `xor` follows the same evaluate-then-validate order, while `and` and `or` judge their left operand before the right one is evaluated (BOOL-04). Comparison chains have their own incremental rule (CMP-02).
- A binary arithmetic application evaluates its left operand to a value, then its right operand, each at its value boundary (VAL). Only then does it validate the operand kinds (OP-04): the string checks first, then the left operand, then the right. Then it applies the zero-divisor rule (OP-06) and computes the result.
- Evaluation follows the source order of the operands whatever the associativity or precedence. A subexpression's operator is applied as soon as both of its operands are available.
- Every operand is evaluated exactly once. The first error, in an operand's evaluation, in validation or in the application, ends the expression; operands not yet evaluated are never evaluated.
- Arithmetic operators never short-circuit; of the logical operators, only `and` and `or` do (BOOL-04).
- The order is identical on every execution path, the async twin and the planned loop included.

**Qualifications**
- Builtin argument slots are not operators. Their order follows CALL (argument assembly) and the builtin's own laziness (`if` demands only the selected branch).

```katlang
trace(1) + trace(2) * trace(3)
```
⇒ `7`

The host log is `trace(1), trace(2), trace(3)`. `trace(1) / trace(0) + trace(5)` is `DivisionByZero` after `trace(1), trace(0)`; `trace(5)` is never evaluated. `trace('x') + trace(1) / 0` is `DivisionByZero` after both traces: the right operand's own error precedes the string rejection of `+`. `(1, 2) / 0` is `TypeMismatch`: validation precedes the zero-divisor check. In the planned loop, `S(s) = trace(s) - trace(s * 10) / trace(2)` / `S(1).repeat(2)` is `16` with the same traces on every path.

### OP-04 — Arithmetic operators and Math functions take numeric scalars only: no vectorization, no identity element, no concatenation, no coercion

- `+ - * / div mod ^`, prefix `-`, and every Math function argument require a numeric scalar value.
- These operands are rejected with `TypeMismatch`: a Boolean; a string (strings support only `==`/`!=`, and `'a' + 'b'` is not concatenation: nothing joins text, VAL-02); the empty sequence `()` (never an identity, VAL-04); a multi-item sequence value, including a multi-output call result; a list value; a call reference or its argument view, which has no number view.
- An operator never maps over a collection. Element-wise work is written explicitly, for example `map(xs, sqrt)`.
- There is no conversion between Booleans or strings and numbers in either direction. `.string`'s rendering of a number is no coercion of an operand: it constructs a new string (DOT-08).
- A redundant singleton structure that normalizes to one number is that number (VAL).
- The kind of every rejected operand is the same: unary `-` (`-()`, `-(1, 2)`, `-[1]`), binary operators and Math arguments (`sqrt([4])`, `sqrt((4, 9))`) all report `TypeMismatch` (FORMAL-06).

**Qualifications**
- `==` and `!=` accept every kind (CMP-03). The ordering comparisons share the numeric-scalar rule (CMP-04).
- Empty neutrality belongs only to the supply operations capture, collect and spread (SUP).
- The operator kinds are Lean-modeled; the Math-argument kinds are C#-only (Math is not modeled).

`map([4, 9], sqrt)` is `L[2, 3]`, the explicit element-wise form.

```katlang
A = 1, 2
A + 1
```
⇒ `TypeMismatch`

`(1, 2) + 1`, `[1] + 1`, `() + 1`, `true + 1`, `'a' + 'b'`, `'a' + 1`, `-true`, `-'x'`, `sqrt(true)` and `F(x) = x, 0` / `F(1) * 2` are all `TypeMismatch`.

### OP-05 — A number is a 34-digit decimal floating-point value, and every arithmetic result is rounded once

*C#-only for the Decimal128 value model (FORMAL-04); the exact-integer instance is shared with the Lean `Int` core.*

- A KatLang number in the runtime is an IEEE 754 Decimal128 value: 34 significant decimal digits, exponent about ±6144.
- `+`, `-`, `*` and `/` give the exact mathematical result rounded once to 34 significant digits (round-half-even). `div` and `mod` follow OP-08, `^` follows OP-09. Hence decimal fractions are exact (`0.1 + 0.2 == 0.3`), non-terminating quotients are rounded (`1 / 3` has 34 threes) and `/` is ordinary rounded division (`7 / 2` is `3.5`).
- No binary floating-point stage exists anywhere in core numerics or in Math.
- A number carries its quantum: a literal keeps its written quantum (OP-10), and an arithmetic result carries the quantum IEEE Decimal128 assigns to it. The quantum is not part of numeric equality (CMP-05) but is observable through `.string` (OP-14) and display.

**Qualifications**
- Which quantum a given operation produces is not constitutional; that a number's quantum survives into `.string` is OP-14.
- Where Lean's `Int` core answers differently (its `/` truncates, `7 / 2 = 3`), that is a documented model limitation, not the runtime contract (FORMAL-04).

```katlang
0.1 + 0.2 == 0.3, 1 / 3, 7 / 2, -7 div 2, 2 ^ 100
```
⇒ `S[true, 0.3333333333333333333333333333333333, 3.5, -3, 1267650600228229401496703205376]`

`0.5 + 0.5` is `1.0`, and `(0.5 + 0.5).string` is `'1.0'`.

### OP-06 — Division, `div` and `mod` by an evaluated zero-valued divisor is an error, never an IEEE infinity or NaN

- `/`, `div` and `mod` reject a divisor whose EVALUATED value is zero with `DivisionByZero`. The zero may be a literal `0`, a computed `1 - 1`, `-0`, `0.000`, or a product that underflowed to zero.
- The check happens after both operands are evaluated and validated (OP-03), and whatever the dividend is: `0 / 0` and an infinite dividend are errors too.
- An infinite divisor is not zero: `1 / (1e6144 * 10) == 0` is `true`.

**Qualifications**
- Validation comes first: `(1, 2) / 0` is `TypeMismatch`.
- The analogous zero-base rule for `^` is OP-09 and reports `IllegalInEval`.
- Lean has one zero, so it expresses only the literal and computed-zero cases. The `-0` and underflow instances are the C# extension of the same rule.

```katlang
1 / (1 - 1)
```
⇒ `DivisionByZero`

`1 / 0`, `1 mod 0`, `5 div 0`, `1 / -0`, `1 / 0.000`, `0 / 0`, `(1e6144 * 10) / 0` and `1 / (1e-6000 * 1e-6000)` are all `DivisionByZero`, as is `x = 0.0` / `2 mod x`. In the planned loop, `S(s) = 1 / (1 - s)` / `S(0).repeat(2)` is `DivisionByZero`.

### OP-07 — A violation of a numeric domain yields an IEEE value, not an error; IEEE special values are ordinary numbers

*C#-only by design.*

- Arithmetic operators, and Math functions on their numeric (value) arguments, follow IEEE Decimal128: overflow produces a signed infinity (never an error, never saturation); an invalid operation produces NaN (`Infinity - Infinity`, `sqrt(-1)`, a fractional power of a negative base, `asin(2)`, a logarithm of a negative number, a logarithm to a degenerate base such as 0, 1 or a negative number); `ln(0)` is `-Infinity`; a computed or negated zero may be `-0`.
- A violation of a Math function's numeric domain is therefore a value. These remain errors: the zero divisor (OP-06) and the zero base (OP-09); an invalid control argument (`round`'s digits must be a whole number `>= 0`, else `IllegalInEval`; `random`/`randomInt` validate their bounds, RAND-03); the integral-power certification cap (OP-09); a non-numeric argument or operand (OP-04).
- NaN, `Infinity`, `-Infinity` and `-0` are ordinary numeric values. They propagate through later arithmetic, display as `NaN`, `Infinity`, `-Infinity` and `-0`, and can be stored, passed and returned.

**Qualifications**
- Specials are numbers with no truth value: `if(sqrt(-1), 1, 2)` is `TypeMismatch` (BOOL-02).
- `NaN == NaN` is `true` while every ordering comparison with NaN is `false`, and `-0 == 0` (CMP-05).
- The two zeros are one value for `==` but differ in display, in `.string` (OP-14), in `min`/`max` (OP-13), in IEEE-sign-sensitive Math results (`atan2(0 * -1, -1)` is `-3.141592653589793238462643383279503`, `atan2(0, -1)` is `3.141592653589793238462643383279503`), and in which representative an `==`-collapsing operation keeps (VAL-11).
- WHICH value a degenerate Math input returns (NaN, an infinity or a finite number; `atan2(0, 0)` is `0`) is the platform `Decimal128` function's verdict and is not constitutional. The rule is only that it is a value.
- Lean `Int` has none of these values.

```katlang
Big = 1e6144 * 10
Big, -Big, Big - Big, sqrt(-1), ln(0), -0, 0 * -1, 1 / Big == 0
```
⇒ `S[Infinity, -Infinity, NaN, NaN, -Infinity, -0, -0, true]`

`-7 div 8` is `-0`. `log(8, 1), log(8, 0), log(8, -2), Math.Log(1, 1), asin(2), lg(-1), sign(sqrt(-1)), exp(1e10), atan2(0, 0)` is `S[NaN, NaN, NaN, NaN, NaN, NaN, NaN, Infinity, 0]`. Control arguments stay errors: `round(1.5, 0.5)` and `round(1.5, -1)` are `IllegalInEval`, as are `random(2, 1)` and `randomInt(1.5, 3)`.

### OP-08 — `div` truncates the exact quotient toward zero, and `mod` is the matching remainder

- `x div y` is the EXACT mathematical quotient truncated toward zero, never a quotient first rounded to 34 digits and then truncated.
- `x mod y` is the exact remainder with the sign of the dividend, so `x == y * (x div y) + (x mod y)` whenever the truncated quotient is representable and the intermediate arithmetic is exact.
- Both operators accept fractional operands (`7.5 div 2` is `3`, `7.5 mod 2` is `1.5`).
- A truncated quotient needing more than 34 significant digits keeps its leading 34 digits, still rounded toward zero (C#-only).

**Qualifications**
- `/` is ordinary rounded division (`-7 / 2` is `-3.5`), not truncation.
- Specials keep IEEE behavior: `-7 div 8` is `-0`, and an overflowing quotient is a signed infinity.
- A zero divisor: OP-06.

```katlang
-7 div 2, -7 mod 2, 7 mod -2, 7.5 div 2, 7.5 mod 2, 8999999999999999999999999999999999 div 3
```
⇒ `S[-3, -1, 1, 3, 1.5, 2999999999999999999999999999999999]`

The planned loop agrees: `S(s) = s div 2, s mod 3` / `S(-7).repeat(1)` is `S[-3, -1]`.

### OP-09 — `^`, `pow` and `Math.Pow` are one operation; a zero base with any negative exponent is an error

- `x ^ y`, `pow(x, y)` and `Math.Pow(x, y)` are the same operation: once both operands have been demanded and are numbers, every spelling gives the same value or the same domain error.
- Operand demand order is not shared. The operator evaluates both operands before validating either (OP-03), while the `pow`/`Math.Pow` wrapper demands and validates its arguments one at a time (COLL-09): `'a' ^ (1 / 0)` is `DivisionByZero`, while `pow('a', 1 / 0)` is `TypeMismatch`.
- An integral exponent gives the exact power when it is representable (`2 ^ 10` is `1024`), otherwise the exact power rounded once. A negative integral exponent gives the reciprocal (`2 ^ -2` is `0.25`).
- A zero-valued base (either sign) raised to ANY exponent below zero, integral or not, is `IllegalInEval` ("zero cannot be raised to a negative exponent"). `0 ^ 0` is `1` and `0 ^ 0.5` is `0`.
- Fractional and non-finite exponents follow IEEE Decimal128. A fractional power of a negative base is NaN.

**Qualifications**
- Lean models only the integer instance: `0 ^ negative` is the same error, bases ±1 are exact, and every other negative exponent is an explicit Lean-only "fractional result" error, a documented limitation; the runtime returns the decimal.
- The accuracy machinery is not constitutional: certified correct rounding of integral powers with a 4096-digit working cap (exhaustion is `IllegalInEval`), and the exact-arithmetic path for delegated powers of a near-one base.
- Precedence: OP-01.

```katlang
0 ^ 0, 0 ^ 0.5, 2 ^ 10, 2 ^ -2, (-2) ^ 3, (-8) ^ (1 / 3), 2 ^ 10 == pow(2, 10), pow(2, -2) == Math.Pow(2, -2)
```
⇒ `S[1, 0, 1024, 0.25, -8, NaN, true, true]`

`0 ^ -1`, `0 ^ -0.5`, `pow(0, -1)` and `Math.Pow(0, -2.5)` are `IllegalInEval`, as is the planned-loop step `S(s) = s ^ -1` / `S(0).repeat(2)`.

### OP-10 — A numeric literal denotes the nearest Decimal128 value with its written quantum; an out-of-range magnitude is a front-end error

*Open: Q-56, whether silent literal underflow (B below) is stated as an accepted exception.*
*C#-only by design.*

- A number literal (lexical form: SYN-02) parses directly to Decimal128 and keeps its written quantum (`1.50` stays `1.50`).
- A literal with more than 34 significant digits is rounded half-even, with no diagnostic.
- A literal whose magnitude exceeds the Decimal128 range is the front-end diagnostic `NumberLiteralTooLarge`, and the program never evaluates. Digit text that cannot be parsed (non-ASCII digits) is `InvalidNumberLiteral`.
- Literals are unsigned (SYN-02); `-0` is the negated zero, and OP-01 holds uniformly (`-2 ^ 2` is `-(2 ^ 2)`).

**Qualifications**
- An underflowing literal such as `1e-7000` is not a diagnostic: it silently becomes a zero with an extreme quantum, so `1e-7000 == 0` is `true`.
- Positive-exponent quanta are not written by `.string` (OP-14 and below): `1e3.string` is `'1000'`.

```katlang
1_000.string, 1e3.string, 1.5e-2.string, 2e30.string, 12345678901234567890123456789012345678.string, 1.50.string, (-0).string
```
⇒ `S['1000', '1000', '0.015', '2000000000000000000000000000000', '12345678901234567890123456789012350000', '1.50', '-0']`

`1e7000` is the parse failure `NumberLiteralTooLarge`. `+1` is `UnexpectedToken`. `1E3` is `UnseparatedSameLineItem`, because uppercase `E` is not an exponent (SYN-02).

### OP-11 — Every spelling of a Math member is the same function; the spellings are nevertheless distinct bindings

*C#-only by design.*

- Each Math member has one function, reachable as the qualified `Math.X`, the lower-camel prelude alias `x`, and the canonical `X` provided by `open Math`.
- The alias property's value IS the canonical member's algorithm object, a closed native wrapper. Every spelling therefore gives identical results, signatures, arity errors and domain behavior as a direct call, a dot-call fallback (`16.sqrt`) and a callback argument (`map(xs, abs)`, `map(xs, Math.Abs)`, `reduce(xs, pow, init)`).
- The alias and the canonical member remain DISTINCT property bindings: each has its own zero-argument cache entry and its own callable identity for repeated-name binding (`P(pi, Pi)` is rejected under `open Math`).
- Each spelling is shadowed independently by ordinary lookup (RES): a user `abs` shadows only the alias, a user `Math` only the qualified spelling.

**Qualifications**
- A qualified `Math.X` is the member's callable because every argumentless structural path is (DOT-09).
- `Math.cos(1)` is the dot fallback `cos(Math, 1)` and gives `ArityMismatch` (DOT).
- There is no `Math.E` and no `e`: `e` is an implicit parameter, and Euler's number is `exp(1)`.
- The library inventory is not constitutional. That Math arguments are value-role positions for implicit lifting is PAR-07.
- Lean models no Math member and no native call (FORMAL-03).

```katlang
sqrt(16) == Math.Sqrt(16), map([-1, 2], Math.Abs), map([-1, 2], abs), (-1).abs, reduce([2, 3], pow, 1)
```
⇒ `S[true, L[1, 2], L[1, 2], 1, 9]`

With `open Math` and `P(x, x) = x`, `map([-1, 2], Abs), Pi == pi, P(pi, pi)` is `S[L[1, 2], true, 3.141592653589793238462643383279503]`, while `P(pi, Pi)` is `TypeMismatch`. `abs = { x * 10 }` / `abs(2), Math.Abs(-2)` is `S[20, 2]`, and `Math = { public Abs(x) = 99 }` / `Math.Abs(-1), abs(-1)` is `S[99, 1]`.

### OP-12 — `avg` is the correctly rounded exact mean, independent of element order

*C#-only for the Decimal128 refinement (FORMAL-04); integer elements whose exact mean is an integer are shared with Lean.*

- `avg(collection)` is the exact mathematical mean of its numeric elements (exact total divided by count), rounded ONCE to Decimal128.
- Its value therefore depends only on the multiset of elements, never on their order or on intermediate rounding of a running sum.
- While every left-to-right addition is exact, the result is bit-for-bit `sum / count`, quantum and zero sign included. A NaN or infinite element gives the ordinary IEEE result.
- `sum` stays the left-to-right Decimal128 sum, which can round along the way and is order-sensitive.

**Qualifications**
- Lean's `evalAvgCounted` truncates (`avg((1, 2))` would be 1), a documented `Int` limitation. Where the exact mean of integer elements is an integer both models agree: `avg((1, 3)), avg((2, 4))` is `S[2, 3]`.
- Empty or non-numeric collections are errors (COLL).

```katlang
avg((1, 1e34, -1e34)), avg((1e34, -1e34, 1)), sum((1, 1e34, -1e34)).string, sum((1e34, -1e34, 1)).string, avg((1, 2))
```
⇒ `S[0.3333333333333333333333333333333333, 0.3333333333333333333333333333333333, '0', '1', 1.5]`

The two `avg` values agree, while the two `sum` values differ by order.

### OP-13 — `min`/`max` are IEEE minimum/maximum: they return an input element, propagate NaN, and order the two zeros by sign

*Open: Q-56, whether the failure of `min = first ∘ order` and `max = last ∘ order` on signed zeros and NaN is stated as an accepted exception.*
*C#-only for the Decimal128 refinement (FORMAL-04); the `Int` instance is shared with Lean.*

- `min(collection)` and `max(collection)` fold with IEEE 754 `minimum`/`maximum`. The result is always one of the elements, so no value or sign is manufactured; any NaN element makes the result NaN; a tie between `0` and `-0` is decided by sign in every element order: `min` returns `-0` whenever a negative zero takes part in a zero minimum, and `max` returns `0` whenever a positive zero takes part in a zero maximum.
- On every `Int` value this agrees with Lean's `evalMinCounted`/`evalMaxCounted`.
- Which of several same-signed equal values with different quanta is returned (`1` versus `1.0`, `-0` versus `-0.0`) is unspecified, and is not governed by the retained-contribution rule of repeated names (PAT-09).

**Qualifications**
- `==` and the ordering operators still treat the two zeros as one value (CMP-05).
- `order` is a different relation (COLL-06). On Decimal128 the `Int` identities `min = first ∘ order` and `max = last ∘ order` do not hold: `first(order((0, -0)))` is `0` while `min` gives `-0`, and with NaN present `max((N, 1))` is `NaN` while `last(order((2, N, 1)))` is `2`.
- The current runtime picks the first of same-signed ties for non-negative values and the last for negative ones (`min((1, 1.0))` is `1`, `min((-1, -1.0))` is `-1.0`). This is observation, not law.

```katlang
N = (1e6144 * 10) - (1e6144 * 10)
min((0, -0)), min((-0, 0)), max((0, -0)), max((-0, 0)), min((-1, -0, 0)), max((-0, -0)), min((1, N)), first(order((0, -0)))
```
⇒ `S[-0, -0, 0, 0, -1, -0, NaN, 0]`

In the planned loop, `S(s) = min((s, -0))` / `S(0).repeat(1)` is `-0`.

### OP-14 — `.string` renders a number as its canonical positional text; quantum, sign and specials are part of that string value

*C#-only for quantum, signed zero, fractions and specials (FORMAL-04); the text of an integer carrying no fractional quantum is Lean-modeled.*

- How `.string` is selected, how it demands its receiver and which kinds it accepts are DOT-08. This rule fixes the text it produces for a number.
- The text is culture-independent positional notation, never exponent notation.
- Every trailing fractional zero the quantum carries is written (`1.50` gives `'1.50'`, `0.5 + 0.5` gives `'1.0'`, `0.000` gives `'0.000'`), and the sign is written, a negative zero included (`0 * -1` gives `'-0'`, `-0.0` gives `'-0.0'`).
- Specials are spelled `NaN`, `Infinity` and `-Infinity`.
- No display setting affects the text: neither `MinDecimalPlaces` nor `MaxDecimalPlaces`, from the program or from the host (RUN-06).
- The result is a string VALUE, so quantum and sign become observable through `==`, string literal patterns, `distinct` and `contains`: `1.50.string == 1.5.string` is `false` although `1.50 == 1.5` is `true`.

**Qualifications**
- Positional notation cannot show a positive-exponent quantum, so `1e3.string == 1000.string` is `true` and a zero with a positive exponent is written `0`. The text always reparses to the same value, and to the same quantum whenever the exponent is at most zero.
- Display may round, trim and pad under `MinDecimalPlaces` and `MaxDecimalPlaces` (RUN-06); `.string` never does. The two share one canonical spelling when no display setting applies.
- `.string` is VAL-11's in-language observer of a number's representation.
- Lean `resultToString` writes `toString` of an `Int`; it agrees with the runtime on integers other than `-0` whose quantum exponent is 0 or positive. `2.50e1` and `3 - 1.0` are exact integers whose runtime text (`'25.0'`, `'2.0'`) differs from Lean's. The test encoder refuses quantum-bearing numbers, so no differential case observes the difference.

```katlang
1.50.string, (0.5 + 0.5).string, (0 * -1).string, sqrt(-1).string, ln(0).string, (2^200).string
```
⇒ `S['1.50', '1.0', '-0', 'NaN', '-Infinity', '1606938044258990275541962092341163000000000000000000000000000']`

`1.50.string == 1.5.string, 1.50 == 1.5` is `S[false, true]`. With `MaxDecimalPlaces = 2`, `(1/3).string` stays `'0.3333333333333333333333333333333333'` while the number `1/3` is displayed as `0.33`.

## ALGHO — Algorithms and the higher-order channel

Algorithms are not values: they travel on the **algorithm channel**, the CALLABLE capability a supplied cell has beside its VALUE capability (NEED-01, NEED-06). A **callable** is anything with an algorithm identity on that channel, and **projection** obtains that identity without demanding the projected computation's VALUE. An **alias** is either a **transparent reference** or a **structural forwarding carrier**, whose law FWD-03 and FWD-04 own. An **invoking slot** is a builtin position that calls its argument: the `map` transform, the `filter` predicate, the `reduce` step, or a `while`/`repeat` step. Parameter channels and shadowing belong to PAR-01, patterns to PAT, and loop steps to LOOP.

### ALG-01 — A brace block is a scope-owning algorithm in every expression position

- A brace block `{ … }` written in any expression position (a call argument, an operand, an output row, a list element, a receiver) denotes one scope-owning user algorithm.
- On the algorithm channel it always provides that algorithm, whatever its parameter, declaration or output count.
- In a value position it is demanded with zero supplied arguments. A block that accepts zero arguments yields its output. A block that has inferred parameters is `UnresolvedImplicitParams`.
- A block whose one row is a bare reference to an algorithm of any arity is a structural forwarding carrier of that algorithm (FWD-03). The channel provides the carrier itself, with its own identity and members, and an explicit call of it forwards to the target. It has no parameters of its own: its bare value read delegates to the target, and a rejected demand reports as its written target reference reports it (CALL-05). `{ Inc }` with `Inc(x)` is Inc's `ArityMismatch`, never `UnresolvedImplicitParams`.
- Declarations written inside the block are owned by the block and are never lexically visible outside it. No name lookup outside the block selects them, except through an `open` of the block (an inline `{ … }` target, or a name holding the block), which provides its public members to the opening body and its nested scopes (MOD-05, RES-02). Structural dot access is a different route: it reaches a block's declared members from outside, private ones included (DOT-01, SYN-05).
- A name that occurs only inside the block and resolves to nothing becomes the block's own implicit parameter, in first-appearance order. A name that resolves outside the block is captured, never re-parameterized: a visible property, a parameter of an enclosing owner, or a name promoted to the enclosing algorithm because it also occurs there, whatever the order (RES-07, PAR-03).

**Qualifications**
- A brace inside a string literal is text, never a block: a string is raw (SYN-15).
- Parentheses are not blocks. `(n + 1)` is computed in place with the surrounding `n`, and a surviving capture has no algorithm identity (SUP-07). A redundant group is erased, so `({…})` is `{…}` and `Apply(({y * 2}))` is `Apply({y * 2})` (SYN-06).
- A block with several rows is one value in a value position, and one argument or state slot: `S(*xs) = xs.count` / `count({1, 2, 3}), {1, 2, 3}.count, S({1, 2}).repeat(1), (1, 2, 3) == {1, 2, 3}` gives `S[3, 3, 1, true]`. In the `repeat` the block is an argument of the captured step call, one state slot (LOOP-01).
- A name free both inside a block and elsewhere in the enclosing algorithm belongs to the enclosing algorithm, whatever the order: `Apply(f) = f(1)` / `Mk = Apply({x + k}) + k` / `Mk(5)` is `11`, and so is `Apply(f) = f(1)` / `Mk = k + Apply({x + k})` / `Mk(5)`.
- A name free only inside a block becomes a block parameter, so a callback block can have more parameters than the one element it receives: `Scale = values.map{n * factor}` / `Scale([1, 2])` is `ArityMismatch`.
- A name that resolves to a property is no parameter, so the block can take no element: `x = 3` / `[1, 2].map{x * 2}` is `ArityMismatch`.

```katlang
Call0(g) = g()
Apply(f) = f(4)
Use(f) = f.X
Call0({42}), Apply({x * 10}), {1, 2}, Apply({ Sq(y) = y * y
  Sq(x) + 1 }), Use({ X = 2
  0 }), { X = 3
  0 }.X
```
⇒ `S[42, 40, S[1, 2], 17, 2, 3]`

A zero-parameter block crosses the channel, a one-parameter block is called, a block in a row position is its output, a block owns its helper `Sq`, and dot edges reach non-public members. `1, {x + 1}` is `UnresolvedImplicitParams`. `A = { Local = 5` / `  Local + 1 }` / `A, Local` is `UnresolvedImplicitParams`, while `A = { Local = 5` / `  Local + 1 }` / `A.Local, A` is `S[5, 6]`.

### ALG-02 — Algorithms are not values: only naming forms reach the algorithm channel, and no value is ever callable

- In algorithm position, only these forms yield an algorithm:
  - a name that resolves to a callable: a user property of any arity, whatever it computes; a clause family; a prelude builtin; a Math member; a host operation; or a parameter whose cell has callable identity;
  - a brace block (ALG-01);
  - an argumentless structural dot path, which is its member (DOT-09);
  - an argumentless `.Algorithm` intrinsic edge on a call reference of the current run, which is the runtime projection of the reference's captured callee (DOT-09, CR-13).
- A name that resolves to an alias yields what the alias's kind decides: a transparent reference yields its target, and a carrier yields itself, whose invocation forwards to its target (FWD-03).
- A redundantly grouped naming form is that form, because the group is erased (SYN-06): `Apply((Inc))` is `Apply(Inc)`.
- Every computed form yields no algorithm: a call result, any other dot expression (a lexical-fallback edge, an intrinsic `.string`, an argument-bearing edge), an operator or comparison, a literal, a list literal, an index or selection, a spread, or a multi-slot capture (SUP-07).
  - As a callee, a computed form is `NotAnAlgorithm`. In source, `F(1)(2)` and `R.F(1)(2)` are already parse errors.
  - As a user-call argument, a computed form binds the value channel only.
- The value domain has no algorithm kind. An algorithm therefore can never be returned by a call, stored in a list, or produced by selection. A callable read as a result is its zero-argument value demand (CALL-05), never a callable result.

**Qualifications**
- A parameter bound to a value is not callable, even if a same-named caller callable exists (PAR-01).
- A call reference is a value, not an algorithm (VAL-01). A bare value read of `R.Algorithm` is the captured callee's ordinary VALUE, never a callable result.
- A runtime reference whose target has no callable identity is no callable when passed on (FWD-04).

```katlang
Inc(x) = x + 1
Apply(f) = f(4)
Twice(f, x) = f(f(x))
Apply(Inc), Twice(Inc, 10), Twice({y * 3}, 1)
```
⇒ `S[5, 12, 9]`

`Inc(x) = x + 1` / `Apply(f) = f(4)` / `Apply(Inc(0))` is `NotAnAlgorithm`. `Inc(x) = x + 1` / `Apply(f) = f(4)` / `R(z) = Apply([Inc])` / `R(0)` is `NotAnAlgorithm`: a list literal is a computed value, and `[Inc]` is never demanded. Written at the inferring root, `Inc(x) = x + 1` / `Apply(f) = f(4)` / `Apply([Inc])` is `UnresolvedImplicitParams`: a list element is a value role, so `Inc` lifts (PAR-07). `Mk(x) = x` / `Mk(1)()` is `UnseparatedSameLineItem`, and `Inc(x) = x + 1` / `(5.Inc)()` is `NotAnAlgorithm`.

### ALG-03 — (retired: merged into SUP-07)

### ALG-04 — (retired: merged into SYN-06)

### ALG-05 — Trailing-brace call: `F{…}` is exactly `F({…})`

*C#-only by design.*

- A brace block that follows a callable target (a name, an argumentless dot edge, or a Grace name) on the same physical line is that call's complete argument list. It is ONE argument slot holding the block, whatever the block's row count: `F{e}` is `F({e})`, `R.F{e}` is `R.F({e})`, and `F{a, b}` is `F({a, b})`.
- Same-line whitespace before `{` does not matter. A newline ends the expression, so `F` newline `{e}` is two rows.
- A completed call is not a callable target, whether it was written on a name or on a dot edge (DOT-09). So `F(x){e}`, `F{e}{e2}`, `R.F(x){e}` and `R.F{e}{e2}` are parse errors (`UnseparatedSameLineItem`).

**Qualifications**
- The call gate admits only a name, an argumentless dot edge or a Grace name before `{`. A redundant group of one is erased to its content (SYN-06). `2 {x}` is the same-line separator error, not a call (SYN-07, SYN-09).

```katlang
Algo = func(9)
Algo{a + 1}, Algo {a + 1}, Algo({a + 1}), Algo{a + 1, 5}, [1, 2].map{x * 2}, [1, 2].map {x * 2}
```
⇒ `S[10, 10, 10, S[10, 5], L[2, 4], L[2, 4]]`

`Two(y) = y` / `Two(3){y + 1}` is `UnseparatedSameLineItem`. `Box = { public G(x) = x * 10 }` / `Box.G(1){2}` is `UnseparatedSameLineItem`, while `Box = { public G(x) = x * 10 }` / `Box.G{2}, Box.G(2)` is `S[20, 20]`. `K = 1` / `K` / `{2}` is `S[1, 2]`.

### ALG-06 — (retired: merged into DOT-09)

### ALG-07 — Callable identity is the written declaration plus its captured activation

- Each written user algorithm or clause family is one declaration identity. Copies of it keep that identity, and so does forwarding it through parameters.
- Two declarations with identical bodies are distinct.
- A transparent reference has no callable identity of its own: every observation of it, identity included, is its target's, at any target arity. It keeps only its own binding: declaration, exposure and written name. A carrier is a declaration with its own identity, never its target's (FWD-03).
- The identity of a callable that captures ancestor parameters also includes the captured activation.
- Callable sameness is decided by this identity, never by body equality or spelling. Three places observe it: repeated-name binding (NEED-04, PAT-09), the owner part of the property-cache key (PROP-07), and open-provider identity, where two open targets resolving to one declaration in its declaring scope are one provider (RES-03).

**Qualifications**
- An internal runtime wrapper mints a fresh identity that no program can name: the thunk of a capture (SUP-07), or the internal holder of a dot result used as a receiver. A dot expression is its member's callable or a value (DOT-09), never a wrapper.
- Captures are value-only at user calls, so they never take part in identity comparison. Clause-family binders apply the same comparison, and a successful incompatibility is a non-match, not an error (NEED-04, PAT-09).

```katlang
P(f, f) = f
A = 5
Q(g) = P(g, g)
P(A, A), Q({5})
```
⇒ `S[5, 5]`

`P(f, f) = f` / `P({5}, {5})` is `TypeMismatch`, and so is `P(f, f) = f` / `A = 5` / `B = 5` / `P(A, B)`. `P(f, f) = f` / `A(*xs) = 5` / `B = A` / `P(A, B)` is `5`: the reference is its target.

### ALG-08 — (retired: merged into RES-07)

### ALG-09 — (retired: merged into VAL-05)

### ALG-10 — Consumer-directed observation: a name resolves to one binding, and its consumer decides what to observe

- A written name resolves to a binding independently of how the binding is consumed. The consumer determines whether it transports that binding, projects its callable identity, demands its calculated value, or explicitly invokes the algorithm. A bare name is not in general shorthand for an empty-argument call.
- **CDO-R1: resolution is consumption-independent.** Resolving a written name selects the one lexically applicable binding (RES-01 to RES-09) without running its output. The consumer's role, the argument count and whether a result is demanded never change which declaration the name denotes (RES-06). Formula lifting may transform a use of the binding, by supplying the callee's required parameters by name. It never selects a different binding (PAR-07).
- **CDO-R2: CALLABLE and VALUE are distinct observations.** Projecting the callable channel obtains the algorithm identity and its lexical owner without demanding that supplied computation's VALUE. A runtime projection, such as an `.Algorithm` link or parameter-rooted member navigation, may demand other cells on its route, and such a failure keeps its kind and is never read as callable absence. Absence is a successful "no identity" outcome (NEED-06). Ordinary calculated values never acquire algorithm identity (ALG-02).
- **CDO-R3: VALUE consumers demand a value.** Arithmetic, value `==`/`!=`, root output rows, value-requiring builtin slots, selection and the other value positions demand the binding's VALUE under their established strictness, lazy-argument behavior, emitted-count boundary and property caching. This does not override source elaboration (PAR-07 lifting, PAR-04 closed lists), closed signatures, or the argument roles of user calls and callbacks: a user call's whole argument stays neutral, and an invoking slot projects CALLABLE (HO-04).
- **CDO-R4: explicit invocation is a call.** `F(args)` invokes the selected callable with precisely the supplied items, through ordinary cardinality, pattern and body rules. There is no partial application and no callee guessing. `F()` is an explicit zero-supply invocation, not a synonym for bare `F`: it executes freshly and never reads or replaces an established zero-argument entry, and an eligible successful zero-supply invocation may publish an entry only when that origin is empty (PROP-06).
- **CDO-R5: a bare VALUE demand uses actual zero-supply acceptance.** A bare value read is eligible exactly when the selected callable's ordinary binder accepts an empty supply, never because a parameter list is syntactically empty (CALL-05). A collecting-only `Only(*xs)` may be read bare, as its cached zero-supply demand. `Head(x, *rest)` cannot, and reports its ordinary minimum-cardinality rejection. Builtins and clause families keep their own rejection and dispatch rules, `tick` its invocation-required refusal (RUN-09), and formula lifting and the root clause keep their behavior (PAR-07).
- **CDO-R6: transport preserves available capabilities.** Supplying or forwarding a written reference preserves its lazy cell with its CALLABLE and VALUE capabilities, without forcing VALUE, unless an explicit spread or another existing inspecting consumer requires it (NEED-07, NEED-08). `Apply(F)` may receive `F` as a callable. `Apply(F())` receives `F`'s calculated result, which has no algorithm identity: an invoking consumer reports its absence (`NotAnAlgorithm`) without demanding it, and a VALUE consumer demands it, so an argument-requiring `F` then fails `F()`'s own arity. A value-only input is never silently converted into a callable. `meta` parameters, `R.Invoke()` and `R.Algorithm` keep their own contract (CR rules).
- **CDO-R7: written definition forms remain distinct.** An eligible open `A = F` is a transparent reference to `F` at any target arity: full target identity, members, callable routing, VALUE and cache origin. An eligible `A = { F }` is a structural forwarding carrier: its own structure and members, fresh forwarding of every explicit call, delegated bare VALUE, and no alias-owned zero-argument entry (FWD-03). `A = F + 1` is a formula whose value use may lift `F`'s required parameters by name (PAR-07). A closed `A(p) = F` is bare forwarding by matching existing binding names, while `A(p) = F(p)` is an ordinary explicit call (FWD-02). A root output row `F` is a VALUE consumer, never alias formation. A literal `A = 7`, a named reference `A = F` and an output expression that evaluates a name are three different things.
- **CDO-R8: identity, ownership and caches remain stable.** Lexical declaration and activation ownership, members, transparent references, structural carriers, open-provider identities, property publication and per-supply memoization stay distinct concepts. Resolution, transport and identity-only projection create no fresh activation, observable value effect or cache entry. A cell's at-most-once VALUE completion (NEED-02) is never the zero-argument property cache (NEED-10). Outermost publication ownership (PROP-09), publication by a zero-supply invocation (PROP-06), re-entrant reads and the host and native non-publication exclusions are unchanged.

Each consumer asks for exactly one observation of the binding the name resolved to:

| Consumer | Observation | Effects and caching |
| --- | --- | --- |
| Plain binding, parameter transport, forwarding, alias hop, collector-slice opening | transport of the cell | none (NEED-01, NEED-07, NEED-08) |
| Invoking position: a callee `f(args)` through a parameter, a `map`/`filter`/`reduce` callback, a loop step, an `R.Algorithm` callee | CALLABLE projection, then an explicit invocation | projection demands nothing of the projected cell, though a runtime route may demand others; the invocation is fresh |
| Value position: operators, value `==`/`!=`, root rows, builtin value slots, selection, `if` result | VALUE | a named zero-supply-accepting property reads or publishes its entry; a parameter reads its cell's one completed VALUE |
| Bare read of an argument-requiring callable in a value position | VALUE demand, which is that callable's ordinary rejection | unless the front end lifted it (PAR-07) |
| Explicit `F(args)`, `F()` | invocation with the written supply | fresh; an eligible zero-supply call may establish an empty entry (PROP-06) |
| `A = F`, `A = { F }`, `A = F + 1`, `A(p) = F`, `A(p) = F(p)` | formation, decided statically | no evaluation at formation |

**Qualifications**
- This rule consolidates the laws it cites. It supersedes none of them, erases none of their exceptions, and changes no syntax, operator, coercion or equality. Repeated-name matching and representative selection stay with NEED-04.
- "Fresh" describes the invocation of the selected callable, not every computation beneath it. A deconstruction target's `a()` freshly invokes its projection and reads the separately cached right-hand side (VAR-06), and a value-only runtime reference answers a zero-supply call with its cell's VALUE (FWD-04).

```katlang
F = tick()
F, F(), F + 0, F == 1, F
```
⇒ `S[1, 2, 1, true, 1]`

```katlang
F = tick()
A = F
B = { F }
C = F + 0
A(), B(), C(), F
```
⇒ `S[1, 2, 1, 1]`

`A()` is `F`'s fresh call and establishes `F`'s empty entry, `B()` forwards freshly, and the formula reads `F`'s entry.

`Bad = 1 / 0` / `Ignore(f) = 0` / `Ignore(Bad)` is `0`, while `Bad = 1 / 0` / `Read(f) = f + 1` / `Read(Bad)` is `DivisionByZero`. `Square(x) = x * x` / `Apply(f) = f(3)` / `Apply(Square)` is `9`, while `Square(x) = x * x` / `Apply(f) = f(3)` / `Apply(Square())` is `NotAnAlgorithm` and `Square(x) = x * x` / `Read(f) = f + 1` / `Read(Square())` is `ArityMismatch`. `Only(*xs) = tick()` / `Only, Only(), Only, Only(9)` is `S[1, 2, 1, 3]`, and `Head(x, *rest) = x` / `Head` is `ArityMismatch`. `Seven = 7` / `Apply0(f) = f()` / `Apply0(Seven)` is `7`, while `Apply0(f) = f()` / `Apply0(7)` is `NotAnAlgorithm`.

### HO-01 — A callable passed by name is the same callable at the receiver

- A callable passed to a user parameter `f` may be a user algorithm, a clause family, a brace block, a prelude builtin (`if` included), a Math function (canonical or lowercase), a host operation, an alias of one of these, or a parameter already bound to one of these.
- The callee may invoke it by call syntax `f(args)`, by dot fallback `a.f`, through a builtin invoking slot, or after transport to another parameter. Forwarding itself preserves the supplied cell and invokes nothing (NEED-08); the eventual invoking consumer projects and calls its CALLABLE identity.
- Each such invocation behaves exactly like the direct call of that callable with the same arguments: same result, same laziness, same error kind. In call position a parameter is read on the algorithm channel only.
- **Whole-algorithm transport.** A written reference passes the whole algorithm it denotes, not just its value. The receiver can navigate its members (`p.X`), read its output structure (`p` in a value position) and invoke it (`p(args)`), all under its original lexical ownership (RES-07). Only the invocation `p(args)` is subject to its parameter and pattern requirements, which bind as in the direct call.
- **Aliases.** Passing a transparent reference passes its target: the receiver sees the target's identity and members, and `p(args)` is the target's call. Passing a carrier passes the carrier: the receiver sees the carrier's identity and only its own declarations as members, and `p(args)` forwards the exact supply freshly to the target (FWD-03).
- A plain binding of a callable demands nothing: the parameter receives the supplied computation with its independent CALLABLE channel (NEED-01, NEED-06, NEED-08). An inspecting pattern observes its cell as NEED-04 and CALL-06 specify: a literal or structural pattern demands VALUE, and a repeated name follows NEED-04's group-aware order.
- A VALUE read of the parameter is the zero-argument VALUE demand of the written argument (CALL-05): for a named callable that accepts zero supplied arguments its ordinary cached read (NEED-10), for a written block its output, and for a callable that cannot accept zero supplied arguments the ordinary rejection of that demand. It is made at most once, at the first read (CALL-06). Each invocation is fresh.

**Qualifications**
- A value-bound parameter is not callable, and the same holds in a builtin invoking slot (HO-04): `Apply(f) = f(4)` / `Apply(7)` is `NotAnAlgorithm`.
- Transport does not make an empty call valid: `Pair(x) = x, x + 1` / `Use(p) = p()` / `Use(Pair)` is `ArityMismatch`, and `Inc(x) = x + 1` / `F(g) = g` / `F(Inc)` is `ArityMismatch`, the zero-argument demand made at the read.
- A member that depends on a parameter needs that parameter's activation, which transport alone does not supply (RES-08): `Pair(x) = { public K = x` / `  x, x + 1 }` / `Use(p) = p.K` / `Use(Pair)` is `LocalOnlyProperty`.
- A capture has no callable identity, so it passes none (SUP-07).
- A clause-family binder keeps the callable as an ordinary binder does (PAT-07): `Inc(x) = x + 1` / `App(f, 0) = 0` / `App(f, n) = f(n)` / `R(z) = App(Inc, 5)` / `R(0)` is `6`. Written at the inferring root, `App(Inc, 5)` lifts `Inc` instead, because a family argument is a value role (PAR-07).

```katlang
Fact(0) = 1
Fact(n) = n * Fact(n - 1)
Inc(x) = x + 1
Apply(f, x) = f(x)
Apply(Inc, 4), Inc(4), Apply(Fact, 4), Fact(4), Apply(count, [7, 8]), count([7, 8]), Apply(abs, -3), abs(-3), Apply({y * 2}, 4), Apply(trace, 9)
```
⇒ `S[5, 5, 24, 24, 2, 2, 3, 3, 8, 9]`, with host log `[trace(9)]`.

```katlang
B = { public W = 3
  public H(x) = x + W
  10, 20 }
Use(p) = p.W, p.H(1), p, p.count
Use(B)
```
⇒ `S[3, 4, S[10, 20], 2]`

```katlang
Lib = { public X = 1 }
A = Lib
Get(p) = p.X
F(x) = x + 1
C = { public M = 2
  F }
Nav(p) = p.M
Call(p) = p(1)
Get(A), Get(Lib), Nav(C), Call(C)
```
⇒ `S[1, 1, 2, 2]`

`Lib = { public X = 1 }` / `C = { Lib }` / `Get(p) = p.X` / `Get(C)` is `UnknownName`: a carrier inherits no member. `Pick(f) = f(true, trace(1), trace(2))` / `Pick(if), if(true, trace(1), trace(2))` is `S[1, 1]`, with host log `[trace(1), trace(1)]`: `if`'s laziness survives the channel. `Inc(x) = x + 1` / `Apply(f) = 2.f, [1, 2].map(f), Pass(f)` / `Pass(g) = g(10)` / `Apply(Inc)` is `S[3, L[2, 3], 11]`. `A = tick()` / `Twice(f) = f() + f()` / `Twice(A), A` is `S[3, 1]`: each `f()` is fresh, and the first establishes `A`'s empty entry (PROP-06).

### HO-02 — The callback law: each element is one ordinary argument, and each callback call is the ordinary call

- `map(c, F)` and `filter(c, F)` call `F(element)`, with each element of the bound collection's one-level view (COLL-03) as ONE ordinary argument.
- `reduce(c, F, initial)` calls the ordinary two-argument `F(element, accumulator)` and associates to the left: `reduce([a, b], F, i)` is `F(b, F(a, i))`. The accumulator is one argument, a deferred cell whose demand runs the preceding step, or demands `initial` for the first step (below).
- Each call binds through the ordinary binder: same arity rule, exact collector law (VAR-01), nested-pattern opening (PAT-08), repeated-name verdict (NEED-04) and failure order (PAT-10) as the direct call.
- The collection operation decides only three things: how many values it supplies (1 or 2), which invocations it makes, and what it does with the result (HO-03). `map` invokes at most once per position, when that position is first read; `filter` at most once per candidate, in source order, as far as its consumers discover (COLL-04); `reduce` invokes its last step, and an earlier step only when a later one demands its accumulator; none invokes for an empty collection. The binding rule for a supplied value is never its own.
- The callee may be a user algorithm or a block, a clause family (through ordinary dispatch), a builtin (receiving the prepared values as its ordinary arguments), a Math function, a host operation, or an alias of one of these.
- **`reduce` demand** (issue #203). `reduce` forms its supply and checks its three-argument arity like every call, then demands the collection and reads every top-level position in order before projecting the reducer or running any step (COLL-04). A failure there ends the fold. If a position yields a nested list, that list retains its own deferred positions.
  - For an EMPTY collection it demands `initial` once and returns it; the reducer is never projected.
  - For a NONEMPTY collection it projects the reducer and demands ONLY THE LAST STEP. Each invoked step is the ordinary call over its already evaluated element and one deferred accumulator.
  - A demanded accumulator is evaluated once and keeps its value or its ordinary failure. Forwarding passes it unevaluated, and reads and pattern inspections share its completion. A reducer that ignores its accumulator skips every step that only the accumulator would reach, and `initial` with them, and effects follow actual demand.
  - The accumulator is demanded through the existing binder and argument roles: a plain binder does not demand it, a pattern that inspects the accumulator demands it during binding or clause selection, and a strict builtin or a host operation demands it as its ordinary argument.
  - An accumulator is VALUE-only: it has no CALLABLE identity, it is no invocation plan (a `meta` parameter refuses it), and it retains no slice. The start is a new cell over the original `initial` computation, demanded at most once, and a demanded failure of `initial` keeps the initial-accumulator report. A written spread in the `initial` slot is supply formation and runs whether or not the slot is demanded.
  - A demanded step's failure keeps its own position and is the fold's failure; the fold adds one reduce-step frame, however many accumulators the demand crossed, which is presentation (RUN-06). A skipped step charges nothing and reaches no limit.

**Qualifications**
- Callback parameters bind values only: an element never carries an algorithm channel.
- An element is one argument whatever its value, `()` included: `Cnt(*xs) = xs.count` / `K(x) = 7` / `P(x) = true` / `filter([(), 1], P), map([()], K), map([(), 5], Cnt)` is `S[L[S[], 1], L[7], L[1, 1]]`. Inside the callee the element behaves as in the direct call: `W(x) = (x, 1).count` / `W(()), map([()], W)` is `S[2, L[2]]`.
- A callback element is opened only by the callee's own structural pattern of the element's kind (PAT-06), in an ordinary callable and a clause family alike. A sequence pattern given a list element is `TypeMismatch` in an ordinary callee and a non-match of that clause in a family, and `NoMatchingBranch` when no clause matches. `LF([a, b]) = a * b` / `LF(n) = n` / `map([[2, 3], 4], LF)` is `L[6, 4]`.
- A loop step is not a callback. A step receives the k-slot state as k supplied arguments and its rows are the next state (LOOP-02, LOOP-03), while a callback receives one element (two for `reduce`) and returns one value (HO-03). Both invoke the callable through its ordinary call, so the same families and builtins are valid in both (LOOP-08).
- *C#-only:* how a fold executes — fold continuations accounted apart from call nesting, suspended steps kept on the heap and run on the demanding thread, and the streamed route of a reducer that leads with its accumulator — is host policy (RUN-03).

```katlang
AddPair((x, y)) = x + y
Cnt(*xs) = xs.count
Acc(x, *acc) = acc
Coll(*xs) = xs
map([(1, 2), (3, 4)], AddPair), map([(10, 7), 20], Cnt), reduce([9], Acc, ((1, 2), 3)), [(1, 2)].map(Coll), filter([(1, 2), 3], {x == 3})
```
⇒ `S[L[3, 7], L[1, 1], L[S[S[1, 2], 3]], L[L[S[1, 2]]], L[3]]`

```katlang
Only(*xs) = tick() + xs.count
map([1, 2], Only), Only
```
⇒ `S[L[3, 4], 1]`: building the list invokes nothing, so the bare `Only` takes the first tick, and reading the result then invokes the callback once per position, in order.

`filter([1, 2, 3], { x + tick() * 0 > 1 }).count, tick()` is `S[2, 4]`: counting discovers every match, with one predicate call per candidate. `Pick(item, acc) = item` / `reduce([1, 2], Pick, 1 / 0)` is `2`, and so is `R(item, acc) = if(item == 1, 1 / 0, item)` / `reduce([1, 2], R, 0)`, while `R(item, (a, b)) = item` / `reduce([1, 2], R, 1 / 0)` is `DivisionByZero`: the inspecting pattern demands the start. `Pick(item, acc) = item` / `reduce([1 / 0, 2], Pick, 0)` is `DivisionByZero`, and `reduce([], 1 / 0, 7)` is `7`. With `Inc(x) = x + 1` and `Call(item, acc) = acc(item)`, `Call(1, Inc)` is `2`, while `Probe(u) = reduce([1], Call, Inc)` / `Probe(0)` is `NotAnAlgorithm`: an accumulator has no callable identity.

`Add(x, y) = x + y` / `map([(1, 2)], Add)` is `ArityMismatch`, exactly as `Add(x, y) = x + y` / `Add((1, 2))` is `ArityMismatch`. `Sub(e, acc) = acc - e` / `reduce([1, 2, 3], Sub, 100), Sub(3, Sub(2, Sub(1, 100)))` is `S[94, 94]`.

### HO-03 — A callback returns its ordinary call result: `map` stores it as one element, `reduce` passes it as the next accumulator; `filter` needs a Boolean

- **`map` and `reduce`.** Each callback invocation is the ordinary call (HO-02), and what it returns is the ordinary call result: the ONE value the call boundary delivers (VAL-06). Several written rows, or a spread row's several items, arrive as one sequence value, and `()` and `[]` are ordinary values. Every successful invocation is accepted: `map` stores the value as ONE element of its result list, and `reduce` passes it whole as the next accumulator, the last one being `reduce`'s result. No callback result is spread or opened, and no cardinality or non-empty check applies to it.
- **Failure.** A failure of the invocation (binding per HO-02, dispatch, a demanded value, `MissingOutput` for an algorithm without output rows per VAL-05, a resource limit) is the failure of the position, candidate or step that made it, raised to the consumer that demanded it: a whole read stops there, a `filter` discovery retains an ordinary failure at its frontier (COLL-04), and a demanded fold step fails the fold (HO-02). A resource limit ends the run, including reads of earlier matches (RUN-03).
- **`filter`.** A `filter` predicate result must be a Boolean (BOOL-02).
- **Unfolding.** For pure, deterministic, total computations, `map(L, F)` has the same result value as `[F(L[0]), …, F(L[n-1])]`, and `reduce([a, b], R, i)` has the same result value as `R(b, R(a, i))`. This holds for a user algorithm, a clause family (its selected clause's ordinary call, PAT-11), an alias, a builtin, a Math member and a host operation alike. The `reduce` equation also describes when one step demands the preceding step or the start as a VALUE. It assumes the same element values and VALUE-only accumulator uses (HO-02). The fold reads its collection's top-level positions first. A written argument in the nested calls can additionally carry a callable, a capturable invocation or a retained collector slice, capabilities the fold's accumulator does not carry.

**Qualifications**
- For `map` the equation compares result values only: it guarantees nothing about effect order, argument demand, random draws, resource consumption or error timing. A mapped position reads its source position before its transform runs, while an expanded ordinary call can skip an unused argument: `L = [1 / 0, 2]` / `F(x) = 0` / `map(L, F)` is `DivisionByZero`, while `[F(L[0]), F(L[1])]` is `L[0, 0]`. For `reduce` the demand of the accumulators agrees as well: `R(x, acc) = x` / `reduce([1, 2], R, 1 / 0)` and `R(2, R(1, 1 / 0))` are both `2`. The elements still differ: `Sub(x, acc) = x - acc` / `[tick(), tick()].reduce(Sub, 0), Sub(tick(), Sub(tick(), 0))` is `S[1, -1]`.
- `()` is an ordinary element and accumulator. It never means "skip this element" or "keep the previous accumulator", and `filter` is the way to omit elements.
- A callback with an unintended extra output row is valid and yields a sequence value the author did not mean, exactly as its direct call would. An error, if any, arises where that value is used: `Net(x) = x, x * 2` / `sum(map([1, 2], Net))` is `TypeMismatch`.
- `reduce`'s `initial` is a value slot whose demand is deferred (HO-04, HO-02); with an empty collection it is demanded once and is the result: `Sub(e, acc) = acc - e` / `reduce([], Sub, 7)` is `7`.
- A loop step's rows are its next state, not a call result (LOOP-03): `Step(x) = x, x` / `Step(5).repeat(1), map([5], Step)` is `S[S[5, 5], L[S[5, 5]]]`.
- A callback body whose row is a completed loop returns that loop's one value (LOOP-07), and so does its spread: `Fib(x, y) = y, x + y` / `[0, 1].map({ Fib(x, 1).repeat(2) }), [0, 1].map({ Fib(x, 1).repeat(2)* })` is `S[L[S[1, 2], S[2, 3]], L[S[1, 2], S[2, 3]]]`.

```katlang
D(x) = x, x
G(x) = D(x)
H(x) = (x, x)
Id(x) = x
R(x, acc) = x, acc
[D(1)], map([1], D), map([1], G), map([1], H), map([(), 1, [], 2], Id), reduce([1, 2], R, 0)
```
⇒ `S[L[S[1, 1]], L[S[1, 1]], L[S[1, 1]], L[S[1, 1]], L[S[], 1, L[], 2], S[2, S[1, 0]]]`

```katlang
R(x, acc) = tick() * x + acc
reduce([1, 2], R, 0)
```
⇒ `4`, and so is `R(2, R(1, 0))` in a fresh run: the step for `2` runs first, draws `1` and then demands its accumulator, exactly as the nested calls do.

`L = [tick(), tick()]` / `F(x) = tick()` / `map(L, F)` is `L[2, 4]`: each position reads its source position, then calls `F`. With the same `L` and `F`, `[F(L[0]), F(L[1])]` is `L[1, 2]`, and the elements of `L` never run. `Lib = { public V = 1 }` / `F(x) = Lib` / `map([1], F)` is `MissingOutput`: an algorithm without output is never `()`. `filter([1, 2], {x})` is `TypeMismatch`, and so is `P(x) = x > 1, x < 5` / `filter([2], P)`.

### HO-04 — Forwarding preserves the algorithm channel: invoking slots call the named callable, value slots read its value

- **Invoking slots.** An invoking slot calls the argument's callable, including when the argument is a parameter that forwards a callable. A transparent reference there is its target, and a carrier forwards each invocation to its target (FWD-03).
- Each invocation is an ordinary call, evaluated afresh. It never reads or populates the property cache, and never adds a separate value demand.
- Supplying a callable to an invoking slot evaluates nothing: an unused callback has no effect, draws nothing, cannot fail and cannot recurse. `Apply(f, xs) = map(xs, f)` therefore selects exactly the callable `map(xs, F)` selects, even when `F` also accepts zero arguments.
- **Loop steps.** A loop's step slot is a `meta` parameter. Its argument is a written invocation, captured inertly, and the callable each iteration invokes is that call's callee (CR-13). An argument that is no written invocation is the META refusal at binding (`NotAnAlgorithm`, LOOP-01).
- **Value slots.** A VALUE slot demands its supplied computation. If it names a property, PROP-05 governs its cached read. A stage first obtains its collection. `repeat` demands its count after preparing the captured supply (LOOP-01). `reduce` demands `initial` at most once, when its fold reaches the start (HO-02). Each outcome is final.
- A loop's initial state is the captured step call's own argument cells, which take that call's roles. The loop itself never demands them (LOOP-01, NEED-01). The step's patterns and rows, or the completed loop when it forms its value, demand a cell only if they read it, at most once and with a final outcome (CALL-06).
- A forwarded parameter is read the same way: the value slot demands its cell once, so a failing argument is evaluated once, its failure is reported, and the argument is never re-run (CALL-06).
- **Value-only parameters.** A cell with no callable identity has no callable to invoke. An invoking slot that receives one reports `NotAnAlgorithm` when it is invoked, exactly as a user higher-order parameter does. Nothing is evaluated to find that out: projection demands no VALUE, and an empty collection never projects its callback at all (NEED-06).

**Qualifications**
- Plain binding and forwarding demand nothing (NEED-01, NEED-08), so an invoking slot never causes an earlier VALUE read of its callable.
- An explicit `f()` through a forwarded parameter is fresh. If it finds the entry of the binding its cell names empty, it is a qualifying zero-supply invocation and establishes that entry (PROP-06). An invoking slot's own invocation never establishes an entry.
- Projection happens at the first invocation: for `map`, when a position is first read, after its source position (COLL-04). Read as the run's result, `map([trace(1), 2], 5)` is `NotAnAlgorithm` with host log `[trace(1)]`, while `map([1], 7).count` is `1`: a stage that no consumer reads projects nothing.
- A forwarded clause family returns its ordinary call result as a callback, exactly as when it is passed directly (HO-03, PAT-11).

```katlang
OnlyCount(*xs) = count(xs)
ApplyMap(f, xs) = map(xs, f)
ApplyMap(OnlyCount, [1, 2]), map([1, 2], OnlyCount), OnlyCount
```
⇒ `S[L[1, 1], L[1, 1], 0]`

```katlang
Init = tick() * 10
Step(x, acc) = x + acc
R(f, xs, i) = reduce(xs, f, i)
R(Step, [1, 2], Init), Init, reduce([1, 2], Step, Init)
```
⇒ `S[13, 10, 13]`: the value slot shares the cache, with one tick.

`OccurrenceCount = filter(values, predicate).count` / `OccurrenceCount((1, 2), {n mod 2 == 0})` is `1`. `A = tick()` / `map([], A), A` is `S[L[], 1]`, and an unused step never ticks either: `A = tick()` / `A(5).repeat(0)` is `5`. `A = tick()` / `Call0(f) = f()` / `Call0(A), Call0(A), A` is `S[1, 2, 1]`. A callback slot's invocations are fresh too: `Only(*xs) = tick() + xs.count` / `map([1, 2], Only), Only` is `S[L[3, 4], 1]`, because the bare `Only` is read first and the callback calls, made when the result is read, never read its entry. `F(0) = 10` / `F(n) = n` / `Fwd(f, xs) = map(xs, f)` / `Fwd(F, [0, 5])` is `L[10, 5]`.

`N = randomInt(1, 50)` / `S(x) = x + 1` / `S(0).repeat(N) == N` is `true`. `Step(x) = 5` / `Step(1 / 0).repeat(1)` is `5`, while `Step(x) = 5` / `Step(1 / 0).repeat(0)` is `DivisionByZero`. `Run(f) = repeat(f(0), 1)` / `Run(5)` is `NotAnAlgorithm`, at the first iteration. `Bad = trace(1) / 0` / `Add(x, y) = x + y` / `G(v) = reduce([1], Add, v)` / `G(Bad)` is `DivisionByZero` with host log `[trace(1)]`.

`A = 7` / `ApplyMap(f, xs) = map(xs, f)` / `ApplyMap(A, [1, 2])` is `ArityMismatch`: `A` has callable identity and declares no parameters. `Through(xs, f) = map(xs, f)` / `Through([1], 5)` is `NotAnAlgorithm`, and `Through(xs, f) = map(xs, f)` / `Through([], trace(1))` is `L[]` with an empty host log. `map([1, 2], 5)` is `NotAnAlgorithm`, and so are `map([1, 2], 1 / 0)`, `filter([1], 1 / 0)` and `reduce([1], 5, 7)`: the division is never evaluated. `map([], 5), filter([], 5), reduce([], 5, 7)` is `S[L[], L[], 7]`.

### HO-05 — Recursion is by name, and every call is a fresh activation whose parameters shadow inherited bindings

- **Recursion by name.** A named algorithm or clause family may call itself or its siblings by name, including mutually. Declaration order is irrelevant: the owner walk resolves the name to the declaration (RES-01, RES-10).
- **Fresh activations.** Every call, whether direct, dotted (`x.F`), through a callback, or through a forwarded parameter, is a fresh activation. Its parameters shadow every inherited binding of the same name on every channel, so an outer callback or caller binding never leaks into the recursive call (PAR-01). Its local-only properties are evaluated per activation (PROP-08).
- **Anonymous blocks.** A brace block has no name of its own. It recurses only by receiving a callable, for example itself, as an argument.
- **Depth.** Recursion depth is bounded only by host policy (RUN-03). The language guarantees no particular depth.

**Qualifications**
- Runaway recursion such as `Loop(n) = Loop(n + 1)` ends in a structured resource error (`EvaluationDepthExceeded` or `EvaluationStackExhausted`, by route), never a crash. Which limit fires, and at what depth, is host policy (RUN-03, RUN-01).
- An alias hop is no call, so it adds no activation (FWD-03).
- Recursion through loop steps is outside the depth protocol (LOOP-02, RUN-03).

```katlang
Factorial = if(n == 0, 1, Factorial(n - 1) * n)
IsEven(n) = if(n == 0, true, IsOdd(n - 1))
IsOdd(n) = if(n == 0, false, IsEven(n - 1))
Fix(f, n) = f(n, f)
Outer(n) = map([3, 4], Factorial), n
Factorial(5), map([0, 1, 2], Factorial), IsEven(10), IsOdd(7), Fix({if(k == 0, 1, k * s(k - 1, s))}, 5), Outer(100)
```
⇒ `S[120, L[1, 1, 2], true, true, 120, S[L[6, 24], 100]]`

A recursive dot call binds the current activation: `R(values) = { list = atoms(values)` / `  if(list.count <= 1, list, list.skip(1).R) }` / `R((1, 2, 3, 4))` is `L[4]`. A local belongs to its activation: `Sum(n) = { Here = n` / `  if(n == 0, 0, Here + Sum(n - 1) + Here * 0) }` / `Sum(4)` is `10`.

## COLL — Collection builtins: one collection argument, one-level view, exact-list results

The prelude has 22 builtins: `if while repeat atoms range filter map order orderDesc count contains first last distinct take skip min max sum avg reduce tick`, plus the C#-only Math surface (OP). A **collection builtin** is one of `filter map order orderDesc count contains first last distinct take skip min max sum avg reduce`; it binds one `collection` argument plus fixed **controls** (its other arguments) and reads the bound value through the **view** (COLL-03). This family also owns `atoms` and `range`, which produce collections. `if` is BOOLCMP's, `while` and `repeat` are LOOP's, and `tick` is RUN-09's. Callback binding in `map`/`filter`/`reduce` is HO-02 and HO-03, `first`/`last` as selection is SEQ, shadowing of builtin names is RES-06, dotted spelling is DOT, the value demand and property cache in value slots are CALL and PROP, and the Decimal128 specifics of `min`/`max` (OP-13) and `avg` (OP-12) are OP.

### COLL-01 — Each builtin has exactly one signature and one behavior contract; none is overloaded by the kind of its input

- Every prelude builtin is a fixed-arity callable with exactly one signature and no optional parameters:
  - `if(condition, whenTrue, whenFalse)`, `atoms(value)`, `range(start, stop)` and `tick()`;
  - the collection builtins' signatures (COLL-02), including `reduce(collection, reducer, initial)`, whose `initial` is never optional;
  - `while(meta step)` (1 argument) and `repeat(meta step, count)` (2), whose `step` is a META parameter capturing the supplied call whose arguments are the initial state (LOOP).
- No builtin is overloaded by the kind of its input. Each has one behavior and one result contract, whatever it receives:
  - a sequence, a list and a scalar are read through the same view (COLL-03), which is one interpretation of the bound value, not an overload;
  - the result kind never follows the input kind (COLL-04);
  - a string is one opaque item, never a character collection.
- Evaluation-time arity and the absence of count-based overloading are CALL-01. A builtin passed by name is the same callable at the receiver (HO-01).

**Qualifications**
- Shadowing a builtin name is RES-06's: a nearer property or parameter replaces it completely.
- `.string` is a dot-only intrinsic, not a prelude callable (DOT); `load` is a directive (MOD); Math members have their own signatures (OP).

```katlang
order((3, 1, 2)), order([3, 1, 2]), order(5), count('abc'), take('abc', 1), contains('abc', 'a'), contains(('abc', 'a'), 'a')
```
⇒ `S[L[1, 2, 3], L[1, 2, 3], L[5], 1, L['abc'], false, true]`

Bare `count` at the root and `reduce([1, 2], {x + y})` are `ArityMismatch`, each reporting its one signature; `tick(1)` is `ArityMismatch`.

### COLL-02 — A collection builtin binds exactly one `collection` argument plus fixed controls; argument boundaries are never altered before binding

| Builtins | Signature |
|---|---|
| `count`, `sum`, `avg`, `min`, `max`, `first`, `last`, `order`, `orderDesc`, `distinct` | `(collection)` |
| `take`, `skip` | `(collection, count)` |
| `contains` | `(collection, item)` |
| `map` | `(collection, mapper)` |
| `filter` | `(collection, predicate)` |
| `reduce` | `(collection, reducer, initial)` |

- Each is an ordinary fixed-arity callable. The written or dot-injected argument slots are assembled as for any call, and their number must be exactly 1 plus the number of controls.
- An unspread sequence or list is ONE argument, whatever produced it: a literal group, a property, a call or builtin result, a selection or a collecting parameter's list. Sibling arguments are never merged into one collection.
- A spread supplies ordinary argument slots subject to the same arity (SUP). To pass the items of several values as one collection, the caller re-groups them: `sum((A*, B*))`. A spread whose operand fails supplies nothing, and its failure is the call's failure, raised before the arity check (SUP-02): `Bad = 1 / 0` / `take(Bad*)` is `DivisionByZero`.
- This is where a collection builtin differs from a user collecting parameter: `G(*v) = v.sum` accepts `G(3, 4)`, but `sum(3, 4)` is an arity error.

**Qualifications**
- A dotted receiver fills `collection` as an ordinary leading argument: `A.take(2)` is `take(A, 2)` (DOT). A collecting parameter's list passed unspread is the one collection: `Q(*args) = args.sum / args.count` / `Q(1, 2, 3), Q((1, 2)*)` is `S[2, 1.5]`, while `M(*values) = map(values*, {x})` / `M(1, 2)` is an arity error (three arguments).
- `if`, `atoms` and `range` are fixed-arity with no collection view. The initial state of `while` and `repeat` is the captured step call's own supply (LOOP).
- The `collection` slot and the value controls (`contains`'s `item`, `take`/`skip`'s `count`, `reduce`'s `initial`) are value positions: each is demanded at most once through the zero-argument value-demand law (CALL), `reduce`'s `initial` only when its fold reaches the start (HO-02); a named property is read through the property cache (PROP), and a failure is final. Callback controls receive the callable, are never VALUE-demanded, and are projected only when the builtin invokes them, so an empty collection, and a `map` or `filter` stage that no consumer reads, never projects them (HO-02, COLL-04, NEED-06).
- The cardinality of the formed supply is checked before any non-spread demand, for builtins and user callables alike; each builtin then obtains its collection or retained slice (NEED-07). `skip` and `contains` read the collection's top-level positions at binding before demanding their controls. `take` validates its count before reading a position, and `reduce` defers `initial` (COLL-04, HO-02). `count(1 / 0, 2)` is `ArityMismatch`, while `take('a', 1 / 0)` is `DivisionByZero`: `'a'` is a valid one-item collection, so the count is demanded next.

```katlang
A = 1, 2
B = 3, 4
sum((A*, B*)), sum((1, 2, 3)), [1, 2, 3].sum, A.count, count(A)
```
⇒ `S[10, 6, 6, 2, 2]`

`count(1, 2, 3)`, `count([1, 2, 3]*)`, `sum(A, B)` and `take((1, 2, 3))` are `ArityMismatch`.

### COLL-03 — The bound collection is read through ONE post-binding level; `count` counts exactly those items

- After binding, a collection builtin reads the bound `collection` value through one view:
  - a sequence or list value supplies its immediate elements;
  - `()` and `[]` are empty;
  - any other value (a number, a string, a Boolean, a call reference) is a one-element collection.
- The view opens exactly one boundary and is never recursive: a nested sequence or list is a single item. `count(c)` is the number of items in the view. There is no `arity` or `length` builtin, and count is not arity (VAL).
- The view applies only to the bound collection. It is never applied to an argument before binding, to a control, or to a user parameter: a parameter receives the value whole, and only its later use as a builtin's collection is viewed.
- An argument view `R.Arguments` (a lazy, read-only view of a captured call's supply) is no collection value. As the whole collection, `count` counts the effective supplied arguments and demands none, and `first` and `last` select and demand only that argument. Every other collection builtin, and `atoms`, refuses it with `TypeMismatch`. A collection that merely contains a view is ordinary.

**Qualifications**
- A collecting parameter makes one list item per argument: `Cnt(*xs) = xs.count` / `Cnt((10, 7)), Cnt((10, 7)*), count((10, 7))` is `S[1, 2, 2]` (VAR).
- A control is one value compared whole, never viewed: `contains([(1, 2), 3], (1, 2))` is `true`, but `contains((1, 2), (1, 2))` is `false`, because the collection `(1, 2)` views as the items `1` and `2`.
- `count({})` is `MissingOutput` blamed at the argument (CALL).
- A parameter holds the value whole: `L(xs) = xs.count` / `L(range(1, 10)), L((1, 2, 3))` is `S[10, 3]`.
- `count` needs the view's cardinality only: it reads no position of a list whose cardinality is known (a literal, or a `map` or `take` over known positions), and it makes a `filter` discover every match (COLL-04): `[trace(1), trace(2)].count` is `2` with an empty host log.
- The fused `filter`→`count` pipeline reads the same view (RUN): `7.filter{x > 1}.count` is `1` and `().filter{x > 1}.count` is `0`, as on the generic path.

```katlang
count((1, [2], 3)), count([1, 2, 3]), count(7), count('abc'), count(true), count(()), count([]), count(((1, 2), (3, 4))), count(([], []))
```
⇒ `S[3, 3, 1, 1, 1, 0, 0, 2, 2]`

```katlang
G(a, b) = a + b
F(meta c) = count(c.Arguments), first(c.Arguments)
F(G(7, 1 / 0))
```
⇒ `S[2, 7]`

In the same `F`, `sum(c.Arguments)` is `TypeMismatch`.

### COLL-04 — Collection-producing builtins return one exact list. Each consumer determines which positions it needs

- `filter`, `map`, `order`, `orderDesc`, `distinct`, `take`, `skip`, `range` and `atoms` each return ONE exact list value with emitted count 1: no items give `[]`, one item gives `[item]` (never erased to the item), many give `[a, b, …]`.
- Kept elements are stored exactly: nested sequences and lists stay elements. The result kind never depends on the input kind or the item count.
- `count`, `sum`, `avg`, `min` and `max` return one number, and `contains` returns one Boolean, each with emitted count 1. `first` and `last` select one stored element (SEQ-05).
- A builtin result re-enters every receiver as ONE value. Only an explicit spread opens the list (SUP), and a list never equals a sequence (SEQ).
- **Stages** (issue #204). After obtaining the collection, `map` and `filter` can return a list without reading a source position or projecting the callback. `take` also demands and validates its count. For example, forming the sequence receiver of `(trace(1), trace(2)).map{x + 1}.first` runs both traces, even though the consumer needs only the first mapped position.
  - `map` preserves positions: position `i` of `map(c, f)` is `f` applied to position `i` of `c`, whatever `c`'s cardinality or discovery state. Its first read reads the source position, then projects `f` (on first use) and makes the ordinary callback call (HO-02, HO-03). A source known to be empty maps to `[]`.
  - `filter` discovers its matches in source order, only as far as its consumers ask. It keeps the positions accepted so far and its scan frontier, so a later discovery resumes where the last one stopped and no candidate is inspected twice. Inspecting a candidate reads its value, projects the predicate on first use and calls it. An ordinary failure is kept at the frontier: every later discovery that reaches it reports it again, while the matches before it stay readable. A predicate that needs the scan it belongs to is `DemandCycle`.
  - For an ordinary collection, `take` returns a prefix sharing its source's positions and discovery state: a count of at most `0` is `[]` and reads nothing, and a full prefix inspects no further candidate.
- **Consumers read what they need.** `count` reads the cardinality only, known for a literal and for a `map` or `take` over known positions, discovered in full for a `filter`; `first` reads position zero; `last` finds the final position and reads it; selection reads the positions it names (SEQ-05). Every other collection builtin (`sum`, `avg`, `min`, `max`, `order`, `orderDesc`, `skip`, `distinct`, `contains` and `reduce`) reads its collection's positions in order when it binds it, and `reduce` obtains every top-level element before any step (HO-02). `contains`, `distinct` and `atoms` read whole values (COLL-07, COLL-10). A position's effects, draws and failures happen when it is read, so a position that no consumer reads never runs.

**Qualifications**
- `reduce` returns its final accumulator as one value, not necessarily a list. Its callback results, like `map`'s, are ordinary call results (HO-03).
- Over a retained collector, `take` instead demands the kept cells in order when called and returns an exact list of those values (NEED-07, COLL-08).
- A stage is one list instance, so every reader of it shares its positions and verdicts: `M = [1, 2, 3].map{trace(x)}` / `M[1], M[1], M.count` is `S[2, 2, 3]` after one `trace(2)`. The other producers read their collection when they bind it, so their result holds values: `skip([trace(1), trace(2)], 1)` is `L[2]` after both traces.
- *C#-only:* a deferred step's failure is reported under the call that built its stage, followed by the frames of the consumer that demanded it, which is presentation (RUN-06); reservations, the release of a finished stage and stack-safe reads of stages stacked at run time are host policy (RUN-03).

```katlang
take((1, 2, 3), 2) == [1, 2], take((1, 2, 3), 2) == (1, 2), take(((1, 2), (3, 4)), 1), range(3, 3), filter([1, 2], {x > 5}), map((1, 2), {x * 10}), distinct(((), ())), order(5)
```
⇒ `S[true, false, L[S[1, 2]], L[3], L[], L[10, 20], L[S[]], L[5]]`

```katlang
G(*a) = a
G(take((1, 2, 3), 2)), G(take((1, 2, 3), 2)*), take((1, 2, 3), 2)*
```
⇒ `S[L[L[1, 2]], L[1, 2], 1, 2]`

`[1, 2].map{if(n == 1, 10, 1 / 0)}.first` is `10`, `count(map([1 / 0, 2], 7))` is `2`, `first(map([1 / 0], 7))` is `DivisionByZero`, and `first(map([1], 7))` is `NotAnAlgorithm`. `[1, 0].filter{1 / n > 0}.take(1)` is `L[1]`, while `.take(2)` and `.count` on the same stage are `DivisionByZero`. `[trace(1), trace(2), trace(3)].filter{x > 1}.first` is `2` after `[trace(1), trace(2)]`. `[1 / 0, 2].take(0)` is `L[]`, and `[1 / 0].take('a')` is `TypeMismatch`.

### COLL-05 — Numeric collection builtins accept only single numbers; the empty-collection policy is fixed per builtin

- `sum`, `avg`, `min`, `max`, `order` and `orderDesc` require every item of the view to be exactly one number. A Boolean, string, `()`, sequence or list item is rejected with `TypeMismatch` naming the builtin, the item's index and the item. It is never converted, flattened or skipped.
- The empty-collection policy is fixed per builtin:

| Builtins | Result for an empty collection |
|---|---|
| `count`, `sum` | `0` |
| `order`, `orderDesc`, `distinct`, `take`, `skip`, `filter`, `map` | `[]` |
| `contains` | `false` |
| `min`, `max`, `avg` | `IllegalInEval`: at least one item is required, and there is no default such as `0` or `()` |
| `first`, `last` | `BadIndex`, exactly as `()[0]` (SEQ-04) |

- An empty collection SUPPLIED as the argument (`()` or `[]`) is not an omitted argument: `count(())` is `0`, while `count()` is an arity error (COLL-02).

**Qualifications**
- `count`, `distinct`, `contains`, `first`, `last`, `take`, `skip`, `filter` and `map` accept any item kind.
- IEEE specials are numbers: with `N = sqrt(-1)`, `sum((1, N))` is `NaN` (OP).

```katlang
sum(()), sum([]), count([]), order(()), orderDesc([]), distinct(()), take([], 3), skip((), 1), contains([], 1), filter([], {x > 0}), map((), {x})
```
⇒ `S[0, 0, 0, L[], L[], L[], L[], L[], false, L[], L[]]`

`min(())`, `max([])` and `avg([])` are `IllegalInEval`; `first([])` and `last(())` are `BadIndex`; `sum((1, true))`, `sum((1, 'a'))`, `sum(((1, 2), (3, 4)))`, `order((3, [1]))`, `avg((1, ()))` and `sum(true)` are `TypeMismatch`; `sum(5)` is `5`.

### COLL-06 — Aggregates and sorts are defined over the viewed numbers: `order` is a stable ascending sort in which equal numbers tie, and `orderDesc` is its exact reverse

*Open: whether reversing equal items is intended law or a consequence of defining `orderDesc` as the reverse of `order`. No decision records it, and Q-28 deliberately left it undecided. The reverse is the current contract, pinned by spec `order-is-stable`.*

- Over the numeric items of the view (COLL-05):
  - `sum` is their total, accumulated left to right from `0`;
  - `avg` is their mean (OP-12);
  - `min` and `max` return the smallest and the largest item, always an item of the collection (OP-13);
  - `order` returns the items sorted ascending by a STABLE sort, so items that compare equal keep their written order;
  - `orderDesc` returns exactly the reverse of `order`'s result, so equal items appear in reversed written order.
- Both sorts keep duplicates and every input element with its exact representation (VAL-11): a tie never replaces or canonicalizes a representative. The arrangement never depends on the host's sort algorithm.
- The comparison relation of `order` and `orderDesc` is a total preorder on numbers (not the IEEE `totalOrder` predicate). `-Infinity` and `Infinity` take the extremes. `0` and `-0`, and equal values written with different quanta (`1`, `1.0`, `1.00`), compare equal and so keep their written order. NaN sorts before every other value: first in `order`, last in `orderDesc`.
- This relation is neither the ordering operators' (IEEE, where every comparison with NaN is `false`; CMP-05) nor `min`/`max`'s (IEEE minimum and maximum with the zero-sign rule; OP-13). So `min`/`max` are not always `first(order(…))`/`last(order(…))` on signed zeros and NaN.

**Qualifications**
- Zero sign, quantum ties and NaN exist only on the Decimal128 tier (C#-only; spec `order-is-stable`, `nan-equality-vs-ordering`). Lean models the integer shadow (`sortIntsAsc`, a stable insertion sort, and `sortIntsDesc` as its reverse), where ties and NaN are unobservable.
- The position of NaN is the comparison convention of the C# numeric type and is not a chosen language law.

```katlang
N = (1e6144 * 10) - (1e6144 * 10)
order((1.0, 1, 0.5)), orderDesc((1.0, 1)), order((0, -0)), orderDesc((0, -0)), order((1, N, -1)), orderDesc((1, N, -1))
```
⇒ `S[L[0.5, 1.0, 1], L[1, 1.0], L[0, -0], L[-0, 0], L[NaN, -1, 1], L[1, -1, NaN]]`

### COLL-07 — `distinct` and `contains` use the one structural equality of `==`, at the top level of the view

- `contains(collection, item)` is `true` if and only if some item of the view equals `item` under the same total structural equality as `==` (CMP, VAL-11). Otherwise it is `false`.
- `distinct(collection)` keeps the first occurrence of each class of equal view items, in written order, as one exact list.
- Both compare at the top level of the view only; there is no recursive search. A nested item is compared as a whole value. Items of different kinds are unequal and never an error, so a sequence never equals a list and `true` never equals `1`. Neither requires numeric items.

**Qualifications**
- Numeric equality ignores Decimal128 quantum and zero sign, so among equal but distinguishable numbers the kept representative is the first written: `distinct((1.0, 1))` is `[1.0]` and `distinct((1, 1.0))` is `[1]`.
- Both read their collection's positions in order when they bind it, and compare whole values, every position of an element and of the item included (CMP-03): `contains([[trace(1)], 2], [1])` is `true` after `[trace(1)]`.
- NaN equals NaN under `==`, so `distinct` collapses NaNs and `contains((1, N), (-3) ^ 0.5)` is `true` with `N = (-2) ^ 0.5` (C#-only, spec `nan-equality-vs-ordering`).

```katlang
distinct((1, 2, 1, (1, 2), (1, 2), [1, 2], 'a', 'a', true, true)), contains([(1, 2)], (1, 2)), contains([[1, 2]], (1, 2)), contains([1.0], 1), distinct((1.0, 1)), contains((1, 2, 3), 2), contains([1, [2]], 2), contains([true], 1)
```
⇒ `S[L[1, 2, S[1, 2], L[1, 2], 'a', true], true, false, true, L[1.0], true, false, false]`

### COLL-08 — `take`/`skip` split the view at a whole-number count and saturate at both ends

- `take(collection, n)` returns the first `n` items of the view, and `skip(collection, n)` the items after the first `n`. Both keep written order and return exact lists.
- `n` must be one whole number: a numeric value with an integral value, so `2.0` is accepted. A count that is not a number is `TypeMismatch`, and a number that is not whole is `IllegalInEval`, the same whole-number control rule as `range` and `repeat` (LOOP-05). NaN and ±Infinity have no integral value and never saturate: `take(xs, 1e6000 * 1e6000)` is `IllegalInEval`.
- Counts saturate, without host overflow (`take([1, 2, 3], 1e40), skip([1, 2, 3], 1e40)` is `S[L[1, 2, 3], L[]]`):

| Count | `take` returns | `skip` returns |
|---|---|---|
| `n` at most `0` | `[]` | all items |
| `n` at least the item count | all items | `[]` |

- So for every valid `n`, `[take(xs, n)*, skip(xs, n)*]` equals the view of `xs` as a list.

**Qualifications**
- A scalar collection is one item: `take(5, 1)` is `[5]`.
- `take` validates its count before reading an element. With an ordinary list its prefix shares the source positions (COLL-04): `[1 / 0, 2].take(0)` is `L[]`, and `L = [tick(), tick()]` / `P = L.take(1)` / `P[0], L[0], tick()` is `S[1, 1, 2]`. With a retained collector, `Prefix(*xs) = xs.take(2)` / `Prefix(10, 1 / 0)` raises `DivisionByZero` as the kept cells are demanded. With an ordinary list, `[1 / 0, 2].take(2).count` is `2`. `skip` reads all top-level positions at binding, including those it discards.
- Lean models the saturation over `Int` (`evalTakeCounted`, `evalSkipCounted`). It cannot write a fractional count, so whole-number validation is C#-only.

```katlang
Xs = [1, (2, 3), 4]
take(Xs, 2), skip(Xs, 2), take(Xs, -1), skip(Xs, -1), take(Xs, 10), skip(Xs, 10), take(Xs, 0), [take(Xs, 2)*, skip(Xs, 2)*] == Xs, take(Xs, 2.0)
```
⇒ `S[L[1, S[2, 3]], L[4], L[], L[1, S[2, 3], 4], L[1, S[2, 3], 4], L[], L[], true, L[1, S[2, 3]]]`

`take([1, 2, 3], '2')`, `take([1, 2, 3], true)` and `skip([1, 2, 3], [1])` are `TypeMismatch`; `take([1, 2, 3], 2.5)` is `IllegalInEval`.

### COLL-09 — `range(start, stop)` is the inclusive run of integers in either direction, as one exact list

- `range(start, stop)` is a fixed two-argument builtin; there is no step or transform argument. Both bounds must be whole numbers. It returns ONE exact list of every integer from `start` to `stop` inclusive, ascending when `start <= stop` and descending when `start > stop`. `range(a, a)` is `[a]`, so a range is never empty.
- A bound that is not a number is `TypeMismatch` (`range(1, 'a')`, `range(true, 3)`, `range([1], 3)`), and a non-whole number is `IllegalInEval` (`range(1.5, 3)`).
- For written (non-spread) bounds, `start` is demanded and validated before `stop` is demanded. So `range('a', 1 / 0)` is `TypeMismatch` and `stop` is never evaluated: `range(trace('a'), trace(1) / 0)` logs only `trace('a')`. A binary arithmetic operator evaluates both operands before it validates either (OP-03). A native Math or random wrapper validates its arguments the same way, one at a time (`pow('a', 1 / 0)` is `TypeMismatch`), while a collection builtin demands its collection first, then its controls (COLL-02). Spread bounds are forced before either bound is demanded (CALL-03).

**Qualifications**
- `range((1, 5))` is an arity error because it is one argument, while `B = 1, 3` / `range(B*)` is `[1, 2, 3]`, because the spread supplies two slots (SUP). `range(1, 5, 2)` is `ArityMismatch`.
- On the Decimal128 tier the elements are written in canonical integer form whatever the spelling of the bounds: `range(1.0, 3)` is `[1, 2, 3]` (C#-only, spec `range-integral-bound-quantum`). A bound beyond 1e34 in magnitude and a result beyond the collection limit are host policy (RUN); only their error kinds are visible. Lean models `inclusiveRange` over `Int`.
- A fused `range(…).filter(…).count` iterates the same integers in the same order as the generic path (RUN): `range(5, 1).filter{trace(x) > 2}.count` traces 5, 4, 3, 2, 1.

```katlang
range(1, 5), range(5, 1), range(3, 3), range(-2, 2), range(1.0, 3), range(1, 4).count, range(1, 100).sum
```
⇒ `S[L[1, 2, 3, 4, 5], L[5, 4, 3, 2, 1], L[3], L[-2, -1, 0, 1, 2], L[1, 2, 3], 4, 5050]`

### COLL-10 — `atoms` is the only recursive flattener and always returns one exact list of numbers

- `atoms(value)` takes exactly one argument. It collects every number reachable through sequence AND list boundaries, depth-first and left to right, into ONE exact list. Strings, Booleans and call references contribute nothing, and neither does an argument view nested inside the value. An argument view given as the whole argument is refused with `TypeMismatch`.
- It is the only builtin that opens values recursively: every other collection builtin opens exactly one level (COLL-03), and the spread marker opens one (SUP).
- It reads the whole value: every position of every list in it, depth-first (COLL-04). `atoms([[trace(1)], trace(2)])` is `L[1, 2]` after `[trace(1), trace(2)]`.
- The result is a list even for a single number (`atoms(7)` is `[7]`, never `7`), and `[]` when there are no numbers. Its content equals the host's numeric flattening of the same value; the two remain separate contracts.

**Qualifications**
- `atoms(1, 2)`, `atoms()` and `A = 1, 2` / `atoms(A*)` are arity errors.
- `atoms` is not a truth view and not a numeric coercion (BOOLCMP). Its output size is bounded by the host collection limit (RUN).

```katlang
atoms(7), atoms([(1, 2), [3, [4]], 5]), atoms(('a', true, 1, [2, (3)])), atoms(()), atoms([]), atoms(((1, (2, 3)), 4)), count(atoms([[1, 2], [3]])), atoms(7) == 7
```
⇒ `S[L[7], L[1, 2, 3, 4, 5], L[1, 2, 3], L[], L[], L[1, 2, 3, 4], 3, false]`

## PAT — Clause families and parameter patterns

KatLang has two pattern languages that share one surface syntax, `Name(pattern) = body`. The **family pattern language** (binders; number, string and Boolean literals; sequence patterns `(…)` and list patterns `[…]`) is used by **clause families**, which Lean calls conditional algorithms. The **ordinary parameter-pattern language** (fixed, collecting and `meta` binders; sequence and list patterns) is used by every ordinary parameter list: single-clause definitions, callbacks and loop state. Both languages share one structural kind law and one singleton rule (PAT-06), and one classification decides which language a whole clause group gets (PAT-01). A **clause** is one `Name(pattern) = body` definition, its **head** is `Name(pattern)`, and its body is a **branch** of the family.

### PAT-01 — A same-name clause group is classified as a whole: one literal-free binder/group clause is an ordinary algorithm, anything else is a clause family

*Open: whether "a written parameter list is never empty" is deliberate law, and whether the zero-arity family arm is host-only (Q-46).*

- **One group.** All clause definitions `Name(pattern) = body` with the same name in one algorithm body form one clause group, whether or not they are contiguous and whatever declarations or rows sit between them. The group is one declaration with one visibility: its clauses must agree on `public` (SYN-04).
- **Ordinary algorithm.** The group elaborates to an ordinary algorithm if and only if it has exactly one clause whose head consists only of binders (fixed `x`, collecting `*xs` or `meta x`) and nested structural patterns, sequence `(…)` or list `[…]` alike (PAT-06). That head becomes the algorithm's closed explicit parameter-pattern list (PAR-04).
- **Clause family.** Every other group is a clause family as a whole: a group of two or more clauses, or a single clause with a number, string or Boolean literal anywhere in its head. A clause is never classified on its own.
- **No empty head.** `F()` is not a clause head; it is a parse error.

**Qualifications**
- Classification is observable: adding a clause, or a literal, to a definition changes how its existing clause behaves. These aspects differ:

| Aspect | Single literal-free clause | Clause family |
| --- | --- | --- |
| Value of the wrong structural kind or length | `TypeMismatch` or `ArityMismatch` (PAT-06) | the clause does not match; `NoMatchingBranch` if none does |
| Repeated-name incompatibility | `ArityMismatch` or `TypeMismatch` (NEED-04) | the clause does not match, and the next one is tried |
| Collecting or `meta` binder | allowed | `InvalidCollectingBinding`, `InvalidMetaParameter` (PAT-04) |
| Bare zero-argument value demand | the ordinary `ArityMismatch`, unless the head accepts an empty supply (CALL-05) | `NoMatchingBranch` (PAT-11) |
| Bare callable argument in an inferring formula | neutral, stays a callable | a VALUE role, lifted (PAT-07) |

- The two kinds share the kind law and singleton rule (PAT-06), closed inputs (PAT-04, PAR-04), one argument supply whose wrong count is `ArityMismatch` before any ordinary demand (CALL-02, NEED-05), demand only by inspection and plain binders that keep both channels (PAT-07), the one-value result (VAL-06), and eligibility as a loop step (LOOP-08).

```katlang
Area((w, h)) = w * h
Kind(0) = 'zero'
B = 5
Kind(n) = 'other'
Area((2, 3)), Kind(0), Kind(B)
```
⇒ `S[6, 'zero', 'other']`

`Area` is ordinary, and `Kind` is one family even though `B` separates its clauses. `Area((w, h)) = w * h` / `Area([2, 3])` is `TypeMismatch`, while `Area((w, h)) = w * h` / `Area(0) = 0` / `Area([2, 3])` is `NoMatchingBranch`. A literal anywhere makes a single clause a family: `F((0, y)) = y` / `F((0, 5))` gives `5`, and `F((0, y)) = y` / `F([0, 5])` is `NoMatchingBranch`.

### PAT-02 — A family call selects the first matching clause in written order; no match is NoMatchingBranch

*Open: whether a reachability diagnostic should report clauses shadowed by an earlier catch-all (Q-49).*

- **First match.** A clause-family call tries its clauses in source order over one argument supply (PAT-07). It evaluates the body of exactly the first clause whose head matches; later clauses are not consulted.
- **No match.** If no clause matches a supply of an accepted count, the call fails with `NoMatchingBranch`; it never yields a default value. A count no clause head accepts is rejected before any clause is tried, as the call's cardinality `ArityMismatch` (NEED-05, PAT-03).
- **Duplicates.** Two clauses whose heads are match-equivalent are the front-end error `DuplicateBranchPattern`. Match-equivalent means structurally identical up to a consistent renaming of binders, with literals compared by value (PAT-05), structural kinds compared (PAT-06) and repeated-binder positions significant.
- **No reachability check.** No other reachability analysis exists: a clause after a catch-all is accepted and never used.

**Qualifications**
- Only inspected positions are demanded before `NoMatchingBranch` (NEED-03, NEED-04, PAT-07). Each clause inspects its patterns left to right over the same cells and stops at its first mismatch, so a slot no attempted clause inspects is never evaluated.
- Duplicate detection is structural. `F(x)`/`F(y)`, `M(a, b)`/`M(x, y)` and `F(x, x)`/`F(y, y)` are duplicates; `F(x, x)`/`F(x, y)` are distinct heads.

```katlang
Describe(0) = 'zero'
Describe(n) = if(n > 0, 'positive', 'negative')
Loose(n) = 'any'
Loose(0) = 'zero'
Describe(0), Describe(-4), Describe(7), Loose(0)
```
⇒ `S['zero', 'negative', 'positive', 'any']`

The catch-all written first in `Loose` shadows `Loose(0)`. `G(0) = 'a'` / `G(1) = 'b'` / `G(2)` is `NoMatchingBranch`. So is `G(0, 0) = 1` / `G(1, 1) = 2` / `G(5, 1 / 0)`, whose second slot is never demanded, while `G(x, 0) = 1` / `G(x, 1) = 2` / `G(5, 1 / 0)` is `DivisionByZero`.

### PAT-03 — A family has one outer call interface: every clause takes the same number of argument slots and writes the same number of output rows

*Open: whether to keep the output-row invariant (d), which counts written rows (Q-48).*

- **(a) Same pattern arity.** Every clause head of a family has the same top-level pattern arity. `F(p1, …, pn)` has arity n; the head's own parentheses are the call's parentheses, so `F((x, y))` has arity 1. A mismatch is the front-end error `BranchArityMismatch`, reported before anything runs.
- **(b) Exact slot count.** A head of arity n matches only a call supplying exactly n argument slots. Each top-level pattern consumes exactly one slot. Surplus arguments are never dropped and missing ones never defaulted, so a wrong argument count selects no clause: the call's cardinality is rejected as `ArityMismatch` before any clause is tried or any non-spread argument demanded (NEED-05). Arity therefore never distinguishes clauses.
- **(c) Ordinary supply.** The argument supply is the ordinary call supply (CALL-02, SUP). A spread `A*` supplies A's items as separate slots before any clause is tried.
- **(d) Same output-row count.** Every clause body writes the same number of top-level output rows. A mismatch is the front-end error `BranchOutputArityMismatch`.

**Qualifications**
- (d) counts written rows, not value shapes: `F(0) = 1` / `F(x) = (2, 3)` / `F(0), F(1)` gives `S[1, S[2, 3]]`.
- (d) has no runtime consumer, because a family call result is one value (VAL-06): `F(0) = 0, 0` / `F(x) = x, x` / `Coll(*xs) = xs` / `Coll(F(1))` gives `L[S[1, 1]]`.
- Nested structure may differ between clauses. `Area(('rect', w, h))` beside `Area(('sq', s))` is legal, and both heads of `M((a, b, c)) = 1` / `M(x) = 0` have arity 1: `M((a, b, c)) = 1` / `M(x) = 0` / `M((1, 2, 3)), M(5)` gives `S[1, 0]`.

```katlang
Pick(0, y) = y
Pick(x, y) = x
A = 0, 5
Pick(A*), Pick(3, 4), Pick((0, 5)*)
```
⇒ `S[5, 3, 5]`

`Pick(0, y) = y` / `Pick(x, y) = x` / `Pick(1, 2, 3)` is `ArityMismatch`, and so is `Pick(0, y) = y` / `Pick(x, y) = x` / `Pick(7)`. `F(0) = 1` / `F(x, y) = 2` is `BranchArityMismatch`. `F(0) = 1` / `F(x) = 2, 3` is `BranchOutputArityMismatch`.

### PAT-04 — A clause head is the complete input specification of its branch

*Open: whether the rejection of collecting bindings in families is permanent (Q-47).*

- **Binders are the only inputs.** The binders of a family clause's pattern are the only parameters of that branch. Any other free name in a branch body must resolve through ordinary lexical, property, open or prelude lookup.
- **Closed at the front end.** A free name that does not resolve is the front-end error `UndeclaredIdentifier`. It is reported for every clause, whether or not that clause is ever selected. A branch never acquires implicit parameters, and the front end never lifts a hidden argument into a branch.
- **The branch's own level is closed to Grace.** The branch's own level infers nothing, so a Grace marker in its head patterns or in any row the branch writes (its output rows and its deconstruction right-hand sides, through every transparent construct) is `InvalidGraceMarker` (PAR-06).
- **Family binders.** Collecting bindings (`*xs`, at any depth, as in `K((a, *r))`) are rejected in family heads (`InvalidCollectingBinding`), and so are `meta` parameters (CR-1): `F(0) = 0` / `F(meta x) = 1` and the single literal-bearing clause `F(meta x, 0) = 1` are `InvalidMetaParameter`.
- **Nested owners are ordinary.** An algorithm written inside a branch body (a brace block in any position, a property, a nested family's nested owners, at any depth) is an owner of its own. One that infers its own signature infers it and may use Grace (PAR-06). Its inferred parameters are supplied by whoever calls it; none is ever added to the branch, and a branch binder seen from it is an enclosing parameter.
- **Otherwise an ordinary body.** Apart from these rules a branch body is an ordinary scope-owning body. It sees sibling and ancestor properties and has its own local definitions, opens and nested clause families. A nested family binds its own binders. Branch-local definitions do not leak to sibling branches or outside the family.

**Qualifications**
- Every written list is closed: `G(n) = n + z` is `UndeclaredIdentifier` too (PAR-04).
- A callee parameter that a binder of the same name does not supply gets nothing. With `A = x + 1`, the formula branch `F(0) = A + 0` keeps `A` as its zero-argument demand, which fails with the ordinary arity error at run time (NEED-05), and the lone row `F(0) = A` is bare forwarding, the front-end `UnforwardableParameter` (FWD-02). A binder of that name does supply it: `A = n + 1` / `F(0) = 0` / `F(n) = A` / `F(4)` gives `5`.
- A branch-local member reached from outside is an accessibility failure (DOT-01, RES-08): `F(0) = { P = 10` / `P }` / `F.P` is `LocalOnlyProperty`.
- A definition body written as one brace block is the branch body: `G(0) = 0` / `G(k) = { y - ~x }` reports `UndeclaredIdentifier` and `InvalidGraceMarker`, while `G(k) = { { y - ~x } }` holds a nested owner.
- A load-bearing branch is one deferred compilation unit (MOD-10): its elaboration errors, these and its own-level Grace verdict included, are reported when the unit is selected.

```katlang
Rate = 10
Tax(0) = 0
Tax(amount) = amount * Rate / 100
Tax(0), Tax(250)
```
⇒ `S[0, 25]`

```katlang
Outer(n) = {
  Inner(0) = 100
  Inner(m) = m + n
  Inner(n)
}
Outer(4)
```
⇒ `8`

```katlang
Apply(f) = f(1, 10)
F(0) = Apply({ y - ~x })
F(0)
```
⇒ `9`

The named spelling agrees: `Apply(f) = f(1, 10)` / `F(0) = { B = y - ~x` / `Apply(B) }` / `F(0)` gives `9`. `F(0) = 0` / `F(n) = n + z` / `F(0)` is `UndeclaredIdentifier` even though only the first clause is selected. `Apply(f) = f(1, 10)` / `F(0) = 0` / `F(n) = Apply({ x - ~n })` is `InvalidGraceMarker`, and so is `F(0) = 0` / `F(n) = { a, b = (~n, 1)` / `a + b }`.

### PAT-05 — A literal pattern matches only an equal value of its own kind

- **Numbers.** A number literal pattern, optionally with a leading `-`, matches only a number equal to it under `==` (VAL-11), whatever either Decimal128 representation: `F(1.5)` matches `1.50` and `3 / 2`, `F(0)` matches `-0` and `0.0`, and two `==`-equal literals are one clause head (PAT-02). The literal binds nothing.
- **Strings.** A string literal pattern matches only a string with exactly the same characters: ordinal and case-sensitive. A double-quoted run in a clause head or a parameter pattern, at any depth, is `UnsupportedDoubleQuotedString`, never a pattern (SYN-15).
- **Booleans.** `true`/`false` in a head are Boolean literal patterns and match only that Boolean.
- **No cross-kind match.** A literal never matches a value of another kind: `1` matches neither `true`, `'1'` nor `[1]`. No coercion is applied.
- **Binders.** A binder matches any value.
- **No expressions.** Patterns use the pattern grammar, not general expression syntax: a pattern is a binder, a collecting binder where VAR-02 allows one, a number (optionally with a leading `-`), string or Boolean literal, or a structural pattern, which may be empty. An arithmetic expression, a call or any other expression is not a pattern: `F(1 + 1) = 2`, `F(x + 1) = x`, `F([1 + 1]) = 1` and `F(f(1)) = 1` are rejected at the first token the pattern grammar cannot take.
- **Classification.** A literal anywhere in a head makes its group a family (PAT-01).

**Qualifications**
- The decimal and signed-zero cases of the number clause are a reviewed C#-only instance of the value rule. Lean has integer literal patterns only, so `F(1.5)` beside `F(1.50)` being `DuplicateBranchPattern` is C#-only too (FORMAL-04).
- Inside a structural pattern, literals are matched element-wise.
- The empty patterns `()` and `[]` are valid, distinct structural patterns, each matching only the empty value of its own kind (PAT-06): `F(()) = 1` / `F(x) = 2` / `F(()), F([])` gives `S[1, 2]`.

```katlang
Kind(true) = 'bool'
Kind(1) = 'one'
Kind('1') = 'text'
Kind(x) = 'other'
Kind(true), Kind(1), Kind('1'), Kind(false), Kind(2)
```
⇒ `S['bool', 'one', 'text', 'other', 'other']`

`F(1.5) = 'y'` / `F(x) = 'n'` / `F(1.50), F(3 / 2), F(1.25)` gives `S['y', 'y', 'n']`. `F(0) = 'y'` / `F(x) = 'n'` / `F(-0), F(0.0), F(true), F('0')` gives `S['y', 'y', 'n', 'n']`. `F(1) = 'y'` / `F(x) = 'n'` / `F(1.0), F((1)), F([1])` gives `S['y', 'y', 'n']`. `F(-1) = 'y'` / `F(x) = 'n'` / `F(0 - 1)` gives `'y'`. `F('a') = 0` / `F(x) = 1` / `F('a'), F('A')` gives `S[0, 1]`.

### PAT-06 — Structural pattern delimiters select the value kind they destructure: a parenthesized pattern matches sequence values only, a bracketed pattern list values only, and a one-item sequence pattern is invalid

This rule owns the structural kind law for both pattern languages (PAT-01).

- **Two structural kinds.** A parenthesized pattern `(p1, …, pn)` is a sequence pattern and a bracketed pattern `[p1, …, pn]` is a list pattern. A sequence pattern matches sequence values only; a list pattern matches list values only. Neither structurally matches the other kind, and neither treats a scalar (number, string, Boolean) as a one-item structure.
- **Whole values.** A bare binder `x` is the only pattern that takes a value whole, whatever its kind.
- **Length.** A pattern without a collector matches exactly its number of elements. A pattern with a collector (`(x, *rest)`, `[*xs]`; ordinary language only, PAT-04) matches at least its fixed ones, and the collector collects the rest as one exact list (VAR-01).
- **Empties.** `()` matches the empty sequence only and `[]` the empty list only.
- **Singleton rule.** A sequence pattern with exactly one non-collecting item (`(x)`, `((x))`, `(([x]))`, `(((x, y)))`, `(((true)))`), at any depth, in a parameter list or a clause head, is invalid source: the front end rejects it (`SingletonSequencePattern`) and never normalizes it to `x`. KatLang has no one-item sequence value (`(7)` is `7`, VAL-03), so the pattern describes a boundary no value has. The collector-only `(*xs)` is not a singleton: in the ordinary language it is valid and matches every sequence, `()` included, while a family head admits no collector at all (`InvalidCollectingBinding`, PAT-04). Lists have the one-element pattern `[x]` because a one-element list is a value (SEQ-01).
- **Nesting.** Every level is checked against its own delimiter: `F(([x, y], z))` takes a sequence whose first element is a two-element list, and `G([(x, y), z])` a list whose first element is a pair.
- **Outer arity is not structural shape.** Every top-level pattern consumes one argument whatever it destructures (PAT-08), so `F((x, y))` and `F([x, y])` are one-parameter callables.
- **Failures use existing categories.** In the ordinary language a value of the wrong kind fails the binding with `TypeMismatch` naming the written pattern and the value received, and a value of the right kind with the wrong number of elements is the group's `ArityMismatch`. In the family language neither is raised: the clause does not match, and a call no clause matches is `NoMatchingBranch` (PAT-02).
- **Equivalence.** Duplicate-clause detection (PAT-02) compares kinds: `F((a, b))` and `F([a, b])` are different heads, as are `F(())` and `F([])`.

**Qualifications**
- A host-built tree carrying a singleton sequence pattern is `IllegalInEval` before evaluation (FORMAL-08). The whole-value spelling is `F(x)`; the one-element-list spelling is `F([x])`.
- Assignment deconstruction is not a written pattern. `x, *y, z = RHS` is the unpacking receiver (VAR-05): it opens a lone sequence or list right-hand side and treats a scalar as one item. It is not subject to this rule, and there is no bracketed deconstruction target.

```katlang
Kind([]) = 0
Kind([x]) = 1
Kind(()) = 10
Kind(xs) = 2
Kind([]), Kind([5]), Kind(()), Kind((5, 6)), Kind(5)
```
⇒ `S[0, 1, 10, 2, 2]`

List patterns distinguish list cardinalities in a family, and `()` and `[]` are different heads.

```katlang
Only([x]) = x
ListSum([x, y]) = x + y
S = 2, 3
Only([7]), Only([[1, 2]]), ListSum([S*])
```
⇒ `S[7, L[1, 2], 5]`

`PairSum((x, y)) = x + y` / `PairSum([2, 3])` is `TypeMismatch`, and so is `PairSum((x, y)) = x + y` / `PairSum(7)`. `F(([x, y], z)) = x + y + z` / `F(((1, 2), 3))` is `TypeMismatch`, and `F(([x, y], z)) = x + y + z` / `F(([1, 2], 3))` gives `6`. `P((x, *rest)) = x` / `P(())` is `ArityMismatch`, and so is `Only([x]) = x` / `Only([1, 2])`. In a family the same mismatches only reject the clause: `Area(('rect', w, h)) = w * h` / `Area(other) = 0` / `Area(['rect', 2, 3]), Area(('rect', 2, 3))` gives `S[0, 6]`. `F((x)) = x` is `SingletonSequencePattern`, and so is `F(0) = 0` / `F((x)) = x`.

### PAT-07 — A clause family demands only what its patterns inspect, and its binders keep both channels of their cells

A clause-family call forms its supply like every call (CALL-02): explicit spreads are opened, every other argument stays a suspended computation, and the family's cardinality is checked before any of them is demanded (NEED-05). Then:

- **Ordered inspection.** The clauses are tried in written order (PAT-02), each against the same supply cells (NEED-04). A clause head is inspected left to right, recursively in written order: a literal pattern demands its argument's VALUE and compares it (PAT-05), a structural pattern demands its argument's value and checks its kind and shape (PAT-06, PAT-08), leaving a list's positions unread until a field inspects them (NEED-04), each occurrence of a repeated name follows NEED-04 (PAT-09), and a plain binder whose name does not repeat demands nothing.
- **Selective demand.** A family therefore demands exactly what the inspected patterns need and, after selection, what the selected body reads. An argument that no inspected pattern and no selected body demands is never evaluated, so it cannot fail, run an effect or draw. A cell demanded during one clause attempt keeps its completed outcome for the later attempts.
- **Mismatch versus failure.** A literal, kind, shape or repeated-name incompatibility is a non-match, and the next clause is tried. A failure raised while a required pattern demands or projects its argument aborts dispatch with that failure and is never a non-match. No matching clause is `NoMatchingBranch` (PAT-02).
- **Both channels.** A successful clause binds each plain binder to its cell with both channels (NEED-04), so a family receives callables. A binder still shadows same-named outer bindings on every channel, and calling a binder whose argument has no callable identity is `NotAnAlgorithm`.
- **Elaboration role.** For formula lifting a family's arguments remain VALUE positions (PAR-07, NEED-05), so an inferring formula still lifts a bare callable written there into a call, and that call's result, a value, reaches the binder. Only an argument that is not lifted, such as one under a closed list, reaches the binder as a callable.

**Qualifications**
- Passing a family as an argument to an ordinary callee is unaffected (PAT-11).
- Turning a one-clause definition into a family makes none of its uninspected arguments strict and removes no callable identity at run time.

```katlang
Ten = 10
F(x, 0) = x
F(x, y) = y
F(Ten, 0), F({ 3 }, 0), F(0, trace(8))
```
⇒ `S[10, 3, 8]`

The literal `0` demands each call's second argument, and no pattern demands the first. In `F(0, trace(8))` the first clause's literal demands `trace(8)` once and the second clause reuses that outcome, so the host log holds one `trace(8)`.

```katlang
Inc(x) = x + 1
App(f, 0) = 0
App(f, n) = f(n)
R(z) = App(Inc, 5)
R(0)
```
⇒ `6`

Written at the inferring root the same call lifts `Inc`: `Inc(x) = x + 1` / `App(f, 0) = 0` / `App(f, n) = f(n)` / `App(Inc, 5)` is `UnresolvedImplicitParams`, and `Inc(x) = x + 1` / `App(f, 0) = 0` / `App(f, n) = f(n)` / `R = App(Inc, 5)` / `R(7)` is `NotAnAlgorithm`.

- Unused failing argument: `F(0, y) = 'zero'` / `F(x, y) = y` / `F(0, 1 / 0)` gives `'zero'`. A failure an inspecting pattern demands aborts dispatch: `F(0, y) = 'zero'` / `F(x, y) = y` / `F(1 / 0, 2)` is `DivisionByZero`.
- A list argument is read by kind and cardinality first: `P([a]) = 1` / `P(x) = 2` / `P([1 / 0, 2])` gives `2`, and so does `P(0) = 1` / `P(x) = 2` / `P([1 / 0])`, whose literal rejects the list by kind without reading it.
- Output-less argument: `F(x, 0) = 1` / `F(x, y) = 2` / `F({ }, 0)` gives `1`, because the binder `x` never demands the block.
- Binder shadowing: `f(x) = x + 1` / `F(f, 0) = f(2)` / `F(f, n) = n` / `F(7, 0)` is `NotAnAlgorithm`.
- Demand order: `F(0, y) = 'zero'` / `F(x, y) = y` / `F(trace(0), trace(1))` gives `'zero'` after `[trace(0)]`, and `F(0, y) = 'zero'` / `F(x, y) = y` / `F(trace(5), trace(1))` gives `1` after `[trace(5), trace(1)]`. `F((a, b), 0) = a` / `F(x, y) = y` / `F(trace((1, 2)), 5)` gives `5` after `[trace(S[1, 2])]`. `F(0) = 1` / `F(1) = 2` / `F(trace(5))` is `NoMatchingBranch` after one `trace(5)`. `F(0) = 1` / `F(1) = 2` / `F(trace(1), trace(2))` is `ArityMismatch` with no host event.

### PAT-08 — An ordinary structural parameter pattern consumes one argument and opens that argument's value exactly one level, through its own kind

- **Where it applies.** Every ordinary parameter-pattern list: a single literal-free clause head, callback binding, loop-state binding, and the zero-argument demand's empty supply. The deconstruction helper binds through the unpacking receiver instead (VAR-05).
- **One slot, opened once.** A structural pattern, a sequence pattern `(p1, …, pn)` or a list pattern `[p1, …, pn]`, consumes exactly one supplied argument slot. It binds its items against that slot's VALUE, opened once, and only if that value has the pattern's own kind (PAT-06):
  - a sequence pattern opens a sequence value to its immediate elements, `()` to zero;
  - a list pattern opens a list value to its positions, `[]` to zero, without reading them: its names bind the original positions, read when used (SEQ-02);
  - any other value is the pattern's kind mismatch (PAT-06), never a one-item supply.
- **Ordinary binder inside.** The opened items are bound by the ordinary prefix/collector/suffix binder. A nested `*rest` collects exactly the remaining opened items as one list (VAR-01, VAR-02). A nested pattern opens its own item once more, again through its own kind.
- **Call-shape syntax.** Pattern delimiters never create a runtime value boundary, and no pattern is ever unwrapped (a one-item sequence pattern is invalid, PAT-06). How the argument was written (`F(S)`, `F((S))`, `F({S})`, `F((S*))`) never matters; only its value does (SYN).
- **Arity.** For arity purposes a structural pattern counts as one required slot whatever it contains, and a nested collector never lowers the outer minimum (CALL-05): even `P((*xs))` and `P([*xs])` need one supplied value.
- **Only openers.** Structural patterns (and deconstruction, VAR-05) are the only binders that open an argument. Without one, a sequence or list argument stays one value.

**Qualifications**
- A structural pattern is strict: `Bad = 1 / 0` / `P((a, b)) = 1` / `P(Bad)` is `DivisionByZero`. An unused fixed binder would not demand it (CALL-06). A list pattern is strict in its argument's VALUE, not in its elements: `P([a, b]) = b` / `P([1 / 0, 2])` is `2`, while `P([a, b]) = a` / `P([1 / 0])` is `ArityMismatch`, because the cardinality is checked before any field.
- Callbacks bind the same way (HO-01): `P((x, *rest)) = (x, rest)` / `map([(7, 8), (1, 2)], P)` gives `L[S[7, L[8]], S[1, L[2]]]`, and `P((x, *rest)) = (x, rest)` / `map([7], P)` is `TypeMismatch`.
- In a clause family the same written pattern follows the same kind law and only rejects the clause (PAT-06).

```katlang
PairSum((x, y)) = x + y
S = 2, 3
PairSum((2, 3)), PairSum(S), PairSum((S)), PairSum({ S }), PairSum((S*))
```
⇒ `S[5, 5, 5, 5, 5]`

```katlang
Split((x, *rest)) = x, rest
LSplit([x, *rest]) = x, rest
Split((1, 2, 3)), Split((1, (2, 3))), LSplit([1, 2, 3]), LSplit([1])
```
⇒ `S[S[1, L[2, 3]], S[1, L[S[2, 3]]], S[1, L[2, 3]], S[1, L[]]]`

`Split((x, *rest)) = x, rest` / `Split(7)` is `TypeMismatch`. `Only([x]) = x` / `Only([1, 2])` is the list pattern's `ArityMismatch`.

### PAT-09 — A repeated name is a compatibility constraint over independently supplied arguments, never a merge or a rebinding

*Open: repeated-parameter interpretation, `Same(x, x)` and structural equivalence are deferred with the NEED-04 design area. This rule restates NEED-04 by reference and settles nothing.*

- NEED-04 owns repeated names: the order at each occurrence, the comparison, and which contribution is bound. Every occurrence of a repeated name is an inspecting pattern, including its first.
- The binding is one original contribution, never a splice of one contribution's identity with another's VALUE.
- In an ordinary binder an incompatibility is a binding error. In a family it is a non-match, and an executed CALLABLE or VALUE failure stays the dispatch's failure (PAT-07).

**Qualifications**
- Repeated collecting names and repeated `meta` binders stay invalid. Fixed repeated names beside collectors use the same group state (VAR-02, CR-1).
- Duplicate-clause detection reads repeated-binder positions (PAT-02).

### PAT-10 — A pattern list is inspected in written order after its cardinality check, and the first failure or conflict that inspection meets is reported

When an ordinary pattern list could fail for more than one reason, the reported failure is the first one met in this order, in every execution path (NEED-04, NEED-05):

1. **The cardinality check** of the list, before any non-spread argument is demanded. Explicit spreads have already run during supply formation (CALL-02).
2. **Ordered inspection.** The patterns are visited left to right, recursively in written order (a nested group's patterns before the next pattern of its level). With a collector, the fixed prefix and suffix are allocated from both ends (VAR-02) and visited in written order, prefix, collector, suffix, and binding the collector demands none of its slice (NEED-07). At each visit:
   - a plain binder whose name does not repeat demands nothing;
   - a `meta` binder demands nothing either: it reifies its supplied cell's invocation plan into the bound reference, evaluating nothing, and an argument outside the capture domain fails there with `NotAnAlgorithm` (CR-2), so an earlier inspecting pattern's failure wins;
   - a literal and a structural pattern demand their argument's VALUE when visited, so a failing argument fails there, as its own failure;
   - a structural pattern then checks its kind and length (PAT-06, PAT-08);
   - each occurrence of a repeated name, the first included, projects its cell's CALLABLE first and demands VALUE only as NEED-04 requires (PAT-09).
3. **The first failure or conflict ends the binding.** Later patterns are not visited, and their arguments are not demanded.

A clause family uses the same traversal, but an incompatibility there is a non-match and the next clause is tried; a failure raised by a demand or a projection aborts dispatch (PAT-07).

**Qualifications**
- Reading a collector materializes its slice: `P(x, *r, (a, b)) = r` / `P(trace(1), trace(2), trace((3, 4)))` gives `L[2]` after `[trace(S[3, 4]), trace(2)]`.
- Which contribution a successful repeated name binds, and what permuting its contributions preserves, is NEED-04's. Failure category and blame follow this order, so they may change under permutation when different incompatibilities coexist.

```katlang
Bad = 1 / 0
P(x, x, (a, b)) = a
P(1, 2, Bad)
```
⇒ `ArityMismatch`

The second `x` conflicts as soon as it is visited, so `(a, b)` is never inspected and `Bad` is never evaluated.

- Cardinality first: `P((a, b)) = a` / `P(1 / 0, 2)` is `ArityMismatch`. Explicit spreads come earlier still: `P(x) = x` / `P(1, (1 / 0)*)` is `DivisionByZero`.
- Plain binders are silent: `P(x, y, (a, b)) = a` / `P(trace(1), trace(2), trace((3, 4)))` gives `3` after `[trace(S[3, 4])]`.
- Depth first, and the first failure stops: `P((a, (b, c)), (d, e)) = a` / `P((1, 2), 1 / 0)` is `TypeMismatch`, and `P((a, b), (c, d)) = a` / `P((1, 2, 3), 1 / 0)` is `ArityMismatch`.
- A `meta` binder keeps its written place: `F((a, b), meta m) = a` / `F(1 / 0, 5)` is `DivisionByZero`, and `F(a, meta m) = a` / `F(1 / 0, 5)` is `NotAnAlgorithm`.
- Families use the same order: `F(0, 0) = 1` / `F(x, y) = 2` / `F(1, 1 / 0)` gives `2`, because the first literal rejects the clause before the second demands `1 / 0`.

### PAT-11 — A clause family is an ordinary callable: it can be passed, called back and dot-called, its call result is one value, and a zero-argument value demand of it is NoMatchingBranch

- **Algorithm channel.** A family name denotes one callable on the algorithm channel. It can be:
  - passed to an ordinary callee and invoked there;
  - used as a `map`/`filter`/`reduce` callback, where each invocation binds the element (and, for `reduce`, the accumulator) as ordinary arguments through ordinary family dispatch and returns its ordinary call result (HO-02, HO-03);
  - reached by dot fallback: `5.Fact` is `Fact(5)` (DOT-03).
- **One value.** A family call result, direct or as a `map`/`reduce` callback (HO-03), crosses the call value boundary and is one value (VAL-06).
- **Zero-argument demand.** A family that reaches a run-time zero-argument value demand is accepted only through a clause of top-level arity 0 (CALL-05). No source clause has a zero-arity head, so the demand is rejected before any dispatch, as `NoMatchingBranch`. Such a demand is a bare root row (the root clause of PAR-07), a value slot under a closed parameter list or in a clause branch whose bindings do not supply the family's parameter names (NEED-05, PAR-07), or a parameter or collected item bound to the family and read as a value.
- **Formula lifting.** In an inferring formula a bare family in a VALUE role is not demanded but lifted (PAR-07): a nameable family becomes a call that forwards its binder names (at the root, an unresolved implicit parameter), and an unnameable one is `UnliftableClauseFamily`.
- **Explicit call.** `Fact()` is an ordinary call supplying zero slots, which no clause head accepts: the cardinality `ArityMismatch` (NEED-05).
- **A collector slot.** A family supplied to a collecting parameter is collected like any argument (VAR-03): collecting it demands nothing, re-spreading the slice keeps it callable, and reading the collected list is the family's zero-argument demand, so `NoMatchingBranch`.
- **Not an open provider.** A family is not a valid `open` provider (`IllegalInOpen`, MOD-04).
- **A loop step.** A family is a valid `repeat`/`while` step: each iteration dispatches its clauses over the current state exactly as the ordinary call, and the selected clause's rows are the next state (LOOP-08). A state no clause matches is the ordinary `NoMatchingBranch`, never loop termination.

**Qualifications**
- An unused fixed parameter never demands the family's value (CALL-06): `Fam(0) = 0` / `Fam(n) = n` / `K(x) = 7` / `K(Fam)` gives `7`.
- Aliases of a family and bare forwarding to one, unnameable families included, are FWD-02's and FWD-03's.
- A callback element is one argument, matched by the family's patterns under the kind law (HO-02, PAT-06): `Swap((0, b)) = (b, 0)` / `Swap((a, b)) = (b, a)` / `map([(1, 2)], Swap)` gives `L[S[2, 1]]`, and `Swap((0, b)) = (b, 0)` / `Swap((a, b)) = (b, a)` / `map([[1, 2]], Swap)` is `NoMatchingBranch`.

```katlang
Fact(0) = 1
Fact(n) = n * Fact(n - 1)
IsZero(0) = true
IsZero(n) = false
map([0, 3, 5], Fact), filter([0, 1, 0], IsZero), 5.Fact
```
⇒ `S[L[1, 6, 120], L[0, 0], 120]`

Zero-argument demand:

- `Fam(0) = 0` / `Fam(n) = n` / `Fam` is `NoMatchingBranch`, and `Fam(0) = 0` / `Fam(n) = n` / `Fam()` is `ArityMismatch`.
- Under a closed list: `Fam(0) = 0` / `Fam(n) = n` / `K(z) = count(Fam)` / `K(0)` is `NoMatchingBranch`, and `Fam(0) = 0` / `Fam(n) = n` / `K(z) = Fam + 0` / `K(1)` is `NoMatchingBranch`.
- In a clause branch: `Fam(0) = 0` / `Fam(n) = n` / `G(0) = count(Fam)` / `G(1) = 1` / `G(0)` is `NoMatchingBranch`.
- A closed list or branch whose bindings supply every parameter name forwards them: `Fam(0) = 0` / `Fam(n) = n + 1` / `K(n) = Fam + 0` / `K(4)` gives `5`. One that supplies only some does not: `Fam(0, y) = y` / `Fam(x, y) = x` / `K(x) = Fam + 0` / `K(1)` is `NoMatchingBranch`.
- Through a parameter, even at the root: `Fam(0) = 0` / `Fam(n) = n` / `F(x) = x + 1` / `F(Fam)` is `NoMatchingBranch`, and `Fam(0) = 0` / `Fam(n) = n` / `P((x, y)) = x` / `P(Fam)` is `NoMatchingBranch`.
- Lifted at the root: `Fam(0) = 0` / `Fam(n) = n` / `count(Fam)` is `UnresolvedImplicitParams`, and `Fam(0) = 0` / `Fam(1) = 1` / `count(Fam)` is `UnliftableClauseFamily`.

Collector slot:

- `Fam(0) = 0` / `Fam(n) = n` / `Coll(*xs) = xs` / `Coll(Fam)` is `NoMatchingBranch`.
- `Fam(0) = 0` / `Fam(n) = n` / `Ignore(*xs) = 1` / `Ignore(Fam)` gives `1`.
- `Fam(0) = 100` / `Fam(n) = n + 1` / `Apply(f) = f(9)` / `Fwd(*fs) = Apply(fs*)` / `Fwd(Fam)` gives `10`.

Results and steps:

- `Tag(0) = 'z'` / `Tag(n) = 'n'` / `Apply(f, x) = f(x)` / `Apply(Tag, 0)` gives `'z'`, and `Add(0, y) = y` / `Add(x, y) = x + y` / `reduce([1, 2, 3], Add, 0)` gives `6`.
- `Pair(0) = (0, 0)` / `Pair(n) = (n, n)` / `C(*xs) = xs.count` / `C(Pair(1))` gives `1`.
- `F(0) = 1, 2` / `F(n) = n, n` / `map([0, 3], F)` gives `L[S[1, 2], S[3, 3]]`.
- `Step(0) = 0, false` / `Step(n) = n - 1, true` / `Step(3).while` gives `0`, and `Step(1) = 0, true` / `Step(0) = 5, true` / `Step(3).while` is `NoMatchingBranch`.

## LOOP — `repeat` and `while`: stepping an explicit multi-slot state

`repeat` and `while` are ordinary prelude builtins (resolution and shadowing: RES, CALL-01) of fixed arity: `while(meta step)` and `repeat(meta step, count)` (a builtin may declare a `meta` parameter: REF CR-17). The argument bound to `meta step` is the **step call**, a written invocation such as `Step(0)`: its callee is the **step** and its supplied arguments are the **initial state**. A **state** is an ordered list of **slots**, each holding one value; it is neither a value boundary nor a callback element. Each iteration invokes the step on the current state, and the step's emitted **row supply** is the next state. The planned-loop optimizer is C#-only and bound by the execution-strategy transparency law (RUN).

### LOOP-01 — The initial state is one state slot per supplied argument of the captured step call

- The forms are `while(meta step)` and `repeat(meta step, count)`: exactly one and two supplied arguments. The count is checked against the argument count after spread expansion of the outer call and before any demand; a mismatch is `ArityMismatch` against the registry signature. The pre-META spellings `while(step, s1, …)` and `repeat(step, count, s1, …)` are therefore arity failures.
- The `meta step` argument must be a written invocation with an argument list: a call through a name, parameter, member, module, grouped path or extension, or a rebuilt projection (`Box.Step(0).while`, `Math.Abs(-3).repeat(2)`, `op.Algorithm(op.Arguments*).while`). The binder captures it inertly: the step is the call's callee, and the initial state is the call's own supply (REF CR-9). Anything else is refused when the loop binds it, with nothing evaluated, before the count and whatever the count: a value, a bare callable or member path (`while(S)`, `S.repeat(2)`, `Box.Step.while`), a property read, an existing reference, a block. The refusal is `NotAnAlgorithm`, framed `while binding meta parameter 'step'` (REF CR-2).
- Each effective supplied cell of the step call is one slot. Zero cells are the ordinary empty state: `Z = false` / `Z().while` is `()`, and `C(*xs) = xs*` / `C().repeat(3)` is `()`.
- Each non-spread argument is exactly one slot holding its value, whatever it is (a number, string, Boolean, sequence, list, `()`, a block, a property or call result). A loop never opens an initial argument. A spread argument `v*` of the step call supplies its items, one level (SUP-02); it is opened when the captured supply is prepared, after the capture and, for `repeat`, before the count is demanded.
- Slots are supplied, not demanded (NEED-01). The loop never demands an initial slot: the step demands what its patterns inspect and its rows read (NEED-03, NEED-04), the completed loop demands what remains of its final state left to right (LOOP-07), and a slot nothing reads is never evaluated, a failing one included. A demanded slot reads its value through the zero-argument value-demand law (CALL-05).
- A slot written as a callable keeps its CALLABLE identity (NEED-06), so the first iteration's step may invoke it. Every later state is the step's rows, which carry values only.

**Qualifications**
- A property read recovers no call: `Start = Step(0)` / `Start.while` is the META refusal.
- `Step(a, b).repeat(n)` is `repeat(Step(a, b), n)` through the ordinary extension fallback (DOT-03); a structural member named `repeat` would win (DOT-01). `Algo(1, 2, 0).while` is `while(Algo(1, 2, 0))`. Redundant parentheses are erased first: `S(((1, 2))).repeat(1)` is `S((1, 2)).repeat(1)`.
- A step that needs a state fails through its own binding when the state is empty: `Inc().repeat(1)` is the loop-state `ArityMismatch`.
- A spread in the step call is opened before earlier non-spread slots and before the count. `S(a, b) = a, b` / `S(trace(2), trace(3)*).repeat(trace(1))` logs `trace(3)`, `trace(1)`, `trace(2)`; without the `*` the order is 1, 2, 3.
- A step row that reads a callable slot as a value demands its zero-argument value: `Inc(x) = x + 1` / `T(f, y) = f, y` / `K(z) = T(Inc, z).repeat(1)` / `K(0)` is `ArityMismatch`.

```katlang
Step(*xs) = xs.count
Pair = 1, 2
Step((1, 2)).repeat(1), Step(1, 2).repeat(1), Step(Pair).repeat(1), Step(Pair*).repeat(1), Step({1, 2}).repeat(1), Step([1, 2]).repeat(1), Step(()).repeat(1), Step([]).repeat(1)
```
⇒ `S[1, 2, 1, 2, 1, 1, 1, 1]`

The collecting step counts its slots: two only for `1, 2` and for `Pair*`.

```katlang
Inc(x) = x + 1
S(g, y) = g(y), y
K(z) = S(Inc, z).repeat(1)
K(0), S(Inc, 0)
```
⇒ `S[S[1, 0], S[1, 0]]`

With `.repeat(2)` the second iteration is `NotAnAlgorithm`: the state is then `S`'s rows, which carry no callable. `S(f) = f()` / `S(5).repeat(1)` is `NotAnAlgorithm`: a value slot has no callable (PAR-01).

`K(a, b) = 7, b` / `K(1 / 0, 2).repeat(1)` is `S[7, 2]` and `K(a, b) = 7, 8` / `K(trace(1), trace(2)).repeat(1)` logs nothing. The step decides the demand order: `S(a, b) = b, a` / `S(trace(1), trace(2)).repeat(1)` logs `trace(2)`, `trace(1)`; with `.repeat(0)` the completed loop demands left to right, `trace(1)`, `trace(2)`.

### LOOP-02 — Each iteration invokes the step on the current state as the ordinary call

- Each iteration invokes the step exactly once, as a fresh activation (HO-05), supplying the current state slots. The slots are established items: nothing reopens or re-counts them before binding.
- The step binds that supply exactly as the direct call `Step(s1, …, sk)` binds k supplied items, through its own ordinary machinery (LOOP-08):
  - fixed parameters bind positionally;
  - one collecting parameter collects an exact list (VAR-01);
  - a structural pattern opens its slot's value one level, of its own kind only (PAT-06): `S([a, b]) = [b, a]` / `S([3, 4]).repeat(1)` is `L[4, 3]`;
  - repeated names are compatibility constraints (PAT-09, NEED-04), following the failure order of PAT-10. Only an initial slot can carry CALLABLE identity.
- A user step's supplied-cardinality mismatch is the loop-state `ArityMismatch`. Failures during pattern inspection keep the ordinary binder's error: a wrong structural kind is `TypeMismatch`, unequal repeated-name values are `ArityMismatch` ("repeated parameter 'x' requires equal arguments"), and two different callable identities are `TypeMismatch`. A clause family dispatches its clauses over the same supply (a successful mismatch tries the next clause; none matching is `NoMatchingBranch`), and a builtin binds it through its argument roles.
- From the second iteration on the bindings are the step's rows, which carry values only (NEED-06). The step's parameter names shadow every inherited binding on every channel (PAR-01, HO-05), so a same-named outer callback or caller binding is never visible inside the step.
- The step body is evaluated in its lexical environment, so captured parent values read as usual (RES-07). A step-local property that reads the state belongs to the iteration's activation and is re-evaluated each iteration; a self-contained one is evaluated once per run (PROP-08).
- For every callable, slot assembly, binding and dispatch of `Step(a1, …, ak).repeat(1)` are those of the direct call `Step(a1, …, ak)`.

**Qualifications**
- The equivalence covers binding. For `repeat`, one iteration also equals the direct call in value and emitted count (LOOP-07).
- A step is not a callback. A step receives k slots and may return any number of slots (HO-02, HO-03).
- Inferred parameters are in first-occurrence order (PAR-05): `Step = b, a` has parameters `(b, a)` and is the identity; write `Step(a, b) = b, a` or `Step = b, ~a` to swap.

```katlang
Head((x, *rest)) = x
Same(x, x) = x + 1, x + 1
Mixed(first, *middle, last) = first + 1, middle*, last + 1
Head((4, 5)).repeat(1), Head((4, 5)), Same(1, 1).repeat(2), Mixed(0, 5, 5, 10).repeat(2)
```
⇒ `S[4, 4, S[3, 3], S[2, 5, 5, 12]]`

`Same(1, 2).repeat(1)` is `ArityMismatch`, exactly like the direct call `Same(1, 2)`.

```katlang
Twice = {
  Step = n * 2
  Step(x).repeat(1)
}
G = n + Twice(n + 1)
map([3], G), G(3)
```
⇒ `S[L[11], 11]`

The step binds its own `n = 4`; reading the callback's `n = 3` would give 9.

`A = tick()` / `S(x) = { T = x + tick() ⏎ x + 1 + A - A + T - T }` / `S(0).repeat(3), A` gives `S[3, 1]`: `A` is read once per run, `T` once per iteration.

### LOOP-03 — The step's emitted row supply becomes the next state; patterns bind, they never produce

- One iteration forms each required output row at most once, all under the bindings of the state that entered the iteration. The new state replaces the old only after every row is formed. A `repeat` iteration forms the rows left to right; a `while` round forms them in the order of LOOP-06.
- The step's rows — a user step's or block's own, or the selected clause's of a family step (LOOP-08) — form the next state as an item supply (VAL-07), not as the call's one value:
  - each non-spread row supplies exactly one slot, its value: `()` and every call, property, selection and loop result included (a completed loop is one value, LOOP-07);
  - each spread row supplies its spread items (SUP-02), possibly none;
  - a builtin step has no written rows: its one result value is one non-spread row, `()` and lists included, exactly the row of its wrapper `W(p…) = builtin(p…)`.
- Patterns bind; they never produce. The step binds the incoming state through NEED-04's ordinary inspection (repeated names compared at each later occurrence, collectors sliced, structural patterns opened), and that is the whole effect of its patterns (LOOP-02). A repeated-name conflict on a later iteration is NEED-04's ordinary `ArityMismatch`, exactly as for the direct call. The category or identity of the expression that produced a row never adds or removes slots. A structured value stays one slot only when the step writes it as one value: a capture `(h*, next)` or a list `[h*, next]`.
- The next state may differ from the previous one in slot count, including zero slots, and in value kind. The next iteration binds whatever state results.

**Qualifications**
- A `repeat` iteration runs row effects in written order. `S(a, b) = trace(b), trace(a)` / `S(1, 2).repeat(2)` logs `trace(2)`, `trace(1)`, `trace(1)`, `trace(2)`.
- A single parenthesized row is one slot: `S(x) = (x + 1, x < 3)` as a `while` step has the pair as its flag, a `TypeMismatch` (LOOP-06). `G(a, b) = (b, a + b)` produces one slot holding a sequence, so `G(0, 1).repeat(2)` is `ArityMismatch`, where `Fib(a, b) = b, a + b` produces two slots.
- Builtin steps: `repeat(take([1, 2, 3], 2), 1)` is `L[1, 2]`, one slot, so `repeat(take([1, 2, 3], 2), 2)` is `take`'s own `ArityMismatch`. `while(first([()]))` is `TypeMismatch`: the `()` result is one slot, hence the flag, like its wrapper `Fi(c) = first(c)`.

```katlang
A = (1, 2), 9
E(x, y) = (), y + 1
Sel(x, y) = A[0], y + 1
Spr(x, y) = (x, y)*, 7
Fib(a, b) = b, a + b
Nest(x) = Fib(0, 1).repeat(1), x
E(0, 0).repeat(1), Sel(0, 0).repeat(1), Spr(3, 4).repeat(1), Nest(5).repeat(1)
```
⇒ `S[S[S[], 1], S[S[1, 2], 1], S[3, 4, 7], S[S[1, 1], 5]]`

The `()` row, the selected pair and the nested loop row are one slot each; the spread row is two. With `Nest(x) = { Fib(0, 1).repeat(1)*, x }`, `Nest(5).repeat(1)` is `S[1, 1, 5]`.

Patterns bind, rows produce:
- `Dup(x, x) = { x + 1, x + 1 }` and `Dup(x, x) = { (x + 1, x + 1)* }` both give `Dup(1, 1).repeat(2)` as `S[3, 3]`. With diverging rows `x + 1, x + 2`, `Dup(1, 1).repeat(1)` is `S[2, 3]` and `Dup(1, 1).repeat(2)` is `ArityMismatch`, the repeated-name failure of the next binding (NEED-04), like the direct call `Dup(2, 3)`.
- `Step((a, b)) = (b, a + b)` / `Step((0, 1)).repeat(3)` is `S[2, 3]`: one sequence value is one slot, re-bound by `(a, b)`. `Step2((a, b)) = { (b, a + b)* }` supplies two items: `Step2((0, 1)).repeat(1)` is `S[1, 1]`, and `Step2((0, 1)).repeat(3)` is `ArityMismatch` (1 state value expected, 2 found).
- Histories: `P((*h), n) = (h*), n + 1` / `P((1, 2), 0).repeat(2)` is `S[S[1, 2], 2]`; `Grow([*h], n) = [h*, n], n + 1` / `Grow([], 0).repeat(3)[0]` is `L[0, 1, 2]`. Without the capture, `P((*h), n) = h*, n + 1` supplies the history's items: `P((1, 2), 0).repeat(1)` is `S[1, 2, 1]`, and `.repeat(2)` is `ArityMismatch`.
- Kind and size changes: `Grow(*h) = h*, h.count` / `Grow(0).repeat(3)` is `S[0, 1, 2, 3]`; `B = {[x]}` / `B(1).repeat(2)` is `L[L[1]]`; `Drop(*xs) = { ()* }` / `Drop(1).repeat(2)` is `()`: zero slots, still bound by the collecting step. A brace block is named to be a step (`repeat({[x]}, 2)` is the META refusal).

### LOOP-04 — (retired: merged into LOOP-03)

### LOOP-05 — `repeat` invokes the step exactly `count` times, and `count` is a non-negative whole number

*C#-only by design: the rejection of a non-integral count (Decimal128 tier; Lean's count is an `Int`).*

*Formal evidence (Constitution catch-up, 2026-11-15; task "Widen finite-loop correspondence (E-15)", `20742ba8`, landed on `main` @ `9ec6bf3b`): the repeat driver is Lean-modeled (`lean/KatLang.lean`, `.repeatBuiltin`; `lean/KatLangArityLaws/FiniteLoopCorrespondence.lean`, `repeatDriver_zero`, `repeatDriver_succ`, `repeat_trace_iff`). Only non-integral count rejection is C#-only, as the index and summary now state explicitly. The conditional correspondence and its remaining premises stay in `docs/design/formal-correspondence-ledger.md`, E-14 and E-15; no question is closed here.*

- The count is a value slot. It is demanded once, through the zero-argument value-demand law (CALL-05), before any non-spread initial slot is demanded. A spread written in the step call was already opened when `repeat` prepared the captured supply, after the inert capture and before the count is demanded: `Inc([1][5]*).repeat(1 / 0)` is `BadIndex`, and `Inc(1 / 0).repeat(-1)` is the count's `IllegalInEval` with the non-spread cell unevaluated.
- Its value must be a whole number:
  - a value that is not a number (a string, Boolean, sequence, list or `()`) is `TypeMismatch` "Expected a number";
  - a non-integral number is `IllegalInEval` "Repeat count must be an integer";
  - a negative number is `IllegalInEval` "Repeat count must be >= 0";
  - a whole number written with a fractional quantum, such as `2.0`, is accepted.
- `repeat(Step(s…), n)` invokes the step exactly n times, each time on the state the previous invocation produced (LOOP-02, LOOP-03), and returns the final state (LOOP-07).
- `n = 0` returns the initial state unchanged. The step is never projected, bound or invoked, so its validity is never checked (LOOP-08). The `meta step` argument itself is still bound first, so a non-invocation is the META refusal whatever the count.

**Qualifications**
- Counts above `long.MaxValue` saturate: host policy.

```katlang
S(x) = trace(x) + 1
repeat(S(0), 3)
```
⇒ `3`

The host logs `trace(0)`, `trace(1)`, `trace(2)`.

```katlang
Run(f, s) = repeat(f(s), 0)
count(5).repeat(0), Run(1 / 0, 5)
```
⇒ `S[5, 5]`

A value can stand in the step position only through a parameter, and zero iterations never project it. Written directly, `repeat(1 / 0, 0)` is the META refusal. A family that would not match is never projected either: `F(0) = 1` / `repeat(F(5), 0)` is `5`.

With `S(x) = x + 1`: `repeat(S(0), -1)` and `repeat(S(0), 2.5)` are `IllegalInEval`; `repeat(S(0), true)`, `repeat(S(0), [1])` and `repeat(S(0), ())` are `TypeMismatch`; `repeat(S(0), 2.0)` is `2`. The count is demanded as soon as the captured supply is prepared, while a non-spread initial cell stays suspended: `repeat(S(trace(0)), trace(2))` is `2`, logging `trace(2)` then `trace(0)`.

### LOOP-06 — `while` reads its continuation flag first: the last effective output item is a Boolean flag, and `false` returns the state that entered the round

- Every round charges one loop step, binds the current state to the step through its ordinary invocation (LOOP-02, LOOP-08) and enters the step body once: every row formed in the round shares that one activation, its parameter cells and its local-property caches.
- Flag discovery runs right to left. The round forms the step's output rows from the last row backwards, each a complete ordinary formation (LOOP-03's row rule), until a row supplies at least one item. That row's last item is the continuation flag: the last effective output item, not necessarily the last written row. A trailing spread row that supplies nothing is formed (effects included) and passed over: `Tail(n) = ()` / `Step(n) = n + 1, n < 2, Tail(n)*` reads its flag from `n < 2`.
- The flag must be a Boolean (BOOL-02). Any other value is `TypeMismatch` naming "while continuation flag (the step's last output)": a number, string, sequence (a parenthesized row holding a pair included), list or `()`. The error is positioned at the written row that supplied the flag, falling back to the enclosing span for a spanless host-built row or an atomic builtin step. There is no numeric truth. No row supplying any item is `ArityMismatch` "a while step must output at least its continuation flag"; a step with no written output is `MissingOutput`.
- `false` stops. The loop returns the state that entered the round, without forming the remaining earlier rows: they are never evaluated, so their effects do not happen and their errors are not reported. On the first round this is the initial state, still lazy until the loop's final materialization (LOOP-07).
- `true` continues. The remaining earlier rows are formed left to right, each at most once, and the next state is the complete supply in written order without its last item. A supply of exactly one item is both the flag and the next state. The next round's binding checks the new state's arity.
- Protection is row-granular. Each row is one ordinary value: a call or spread inside a row runs its own rows left to right before any of its items exists. A flag produced inside the same row as the transition (`Step(x) = Pack(x)*`, a builtin, host or wrapper step) gets no early exit, and whatever the flag row itself needs (a shared local property, a division it reads) is computed first by ordinary call-by-need.
- Only `while` reads its rows this way. Ordinary calls and `repeat` form every row left to right (LOOP-03); the order belongs to the `while` receiver, not to a callable kind (LOOP-08).

**Qualifications**
- The flag row's failure, or its non-Boolean value, is reported before any earlier row is formed.
- The flag row's effects, host calls, random draws and lazy initial-cell demands precede the transition rows'; on the stopping round the transition rows do not happen. Writing the flag to read a local that holds the transition forces the transition first.
- "While the condition holds" is exact when the flag is computed from the step's inputs. A flag computed from a candidate tests the candidate, and the returned state is still the one that entered the round.
- A flag that never becomes `false` runs until a host limit (RUN).
- A flag written as a capture that normalizes to a Boolean, such as `(x < 3, ()*)`, `([x < 3]*)` or `((x < 3))`, is accepted (BOOL-02).
- A step whose last written row is a spread is read by the generic condition-first reader; the planned loop evaluates a plain last row's flag first. Both are strategy-neutral.

```katlang
S(i, acc) = i + 1, acc + i, i < 5
while(S(0, 0))
```
⇒ `S[5, 10]`

At state `(5, 10)` the flag `5 < 5` is `false`, so the loop returns `(5, 10)` without forming `i + 1` or `acc + i`.

```katlang
Step(x) = 10 / (x - 1), x > 1
Step(1).while
```
⇒ `1`

`S(x) = trace(x) + 1, x < 0` / `while(S(5))` is `5` with nothing logged. `S(x) = trace(x + 1), trace(x < 3)` / `S(2).while` is `3` and logs `trace(true)`, `trace(3)`, `trace(false)`: the flag first. `S(x) = 1 / 0, trace(false)` / `S(1).while` is `1`.

What the flag needs still runs: `Step(x) = 10 / (x - 1), 10 / (x - 1) > 0` / `Step(1).while` is `DivisionByZero`, as is the same step with a shared local `Q = 10 / (x - 1)`; `Pack(x) = 10 / (x - 1), x > 1` / `Step(x) = Pack(x)*` / `Step(1).while` is `DivisionByZero`.

Flag failures: `S(x) = x + 1, 1`, `S(x) = 1 / 0, 5` and `S(x) = x + 1, 'a'` are `TypeMismatch`, the second before `1 / 0` is formed. `S(x) = x < 3` fails on its second iteration, when its state `true` reaches `x < 3`. `S(x) = { ()* }` is `ArityMismatch`.

The state may change kind: `S(x) = if(x == true, 0, true), x != 0` / `S(true).while` is `0`.

### LOOP-07 — The loop result is ONE value: the canonical capture of the final state's slots, one item at every receiver

- `while` and `repeat` return one value: the canonical capture of the final state's slots (VAL-03) — `()` for zero slots, the slot itself for one, a sequence for several — with emitted count `Result.valueCount`, like every other builtin and call result (VAL-06).
- The count of `()` is 0, including a completed zero-slot loop. A non-spread row receiver contributes that value as one visible item; an explicit `*` opens it into zero items. The loop has no special count exception (VAL-06 with VAL-07).
- A loop result written as a row — at the root, in a body, a capture or a list, in a loop step, or as a callback body — is one item like any other non-spread row (VAL-07, SUP-01, LOOP-03). A `map`/`reduce` callback returns its ordinary call result (HO-03), so `N(x) = ()` / `E(x) = repeat(N(x), 1)` / `map([1], E)` is `L[S[]]`. The slot count is not observable outside the loop.
- Only an explicit spread `repeat(…)*` supplies the final value's items (SUP-02).
- For a `repeat` step, one iteration equals the direct call in value and emitted count: `Step(a…).repeat(1)` and `Step(a…)` are the same counted result, whatever the step's head.
- Iterating is not nesting calls. `S(s…).repeat(2)` equals `S(S(s…))` when the first iteration supplies exactly one item, whatever its value (`Pair(x) = (x, x)`, a list row `W(x) = [x, x]`, a `()` row), and equals `S(S(s…)*)` when it supplies zero or several items (`Fib(a, b) = b, a + b`). For one item that is not a sequence, a list or `()`, both spellings agree.

**Qualifications**
- `count(repeat(…))` counts the elements of the one bound value through the post-binding collection view (COLL); it equals the slot count only because the final state is a sequence.
- A lone loop row is one display row like any value (RUN).

```katlang
Fib(a, b) = b, a + b
Coll(*xs) = xs
X = repeat(Fib(0, 1), 3)
repeat(Fib(0, 1), 3).Coll, repeat(Fib(0, 1), 3)*.Coll, count(repeat(Fib(0, 1), 3)), X.Coll, repeat(Fib(0, 1), 3)[0]
```
⇒ `S[L[S[2, 3]], L[2, 3], 2, L[S[2, 3]], 2]`

`Fibonacci(a, b) = b, a + b` / `Fibonacci(0, 1).repeat(10)` is the one row `(55, 89)`; with a trailing `*` it is the two rows `55` and `89`; `Fibonacci(0, 1).repeat(10), 7` is `S[S[55, 89], 7]`.

A nested loop as a step row is one slot: `Two(a, b) = repeat(Fibonacci(a, b), 2)` / `Two(0, 1).repeat(3)` is `ArityMismatch`, like its helper form `Inner(a, b) = repeat(Fibonacci(a, b), 2)` / `Two(a, b) = Inner(a, b)`; the spread forms `Two(a, b) = { repeat(Fibonacci(a, b), 2)* }` and `Two(a, b) = { Inner(a, b)* }` give `S[8, 13]`. In a callback body, `[0, 1].map({ repeat(Fib(x, 1), 2) })` with `Fib(x, y) = y, x + y` is `L[S[1, 2], S[2, 3]]`, like the helper `H(x) = repeat(Fib(x, 1), 2)`.

The slot count stays inside the loop: `P1(p) = (p[0] + 10, p[1] + 10)` / `repeat(P1((10, 20)), 1)` (one slot holding a pair) and `P2(a, b) = a + 10, b + 10` / `repeat(P2(10, 20), 1)` (two slots) are both `S[20, 30]`, and `==` gives `true`.

```katlang
Pair(x) = (x, x)
Fib(a, b) = b, a + b
repeat(Pair(1), 2) == Pair(Pair(1)), repeat(Fib(0, 1), 2) == Fib(Fib(0, 1)*), repeat(Fib(0, 1), 1) == Fib(0, 1)
```
⇒ `S[true, true, true]`

The mismatched nestings `Pair(Pair(1)*)` and `Fib(Fib(0, 1))` are `ArityMismatch`.

### LOOP-08 — A loop step is an ordinary callable invoked over the current state supply

*Open: whether loop-step invocations should charge dynamic depth (Q-39). Today an iteration charges one loop step and no depth.*

- The step is the canonical callee cell of the step call (REF CR-13): its route's callee, which is the written callee (a parameter callee is that parameter's own cell), an argumentless member path, an `.Algorithm` link or an extension's lexical fallback. It is projected, never value-demanded, and never read through the zero-argument law or the property cache (HO-04, PROP-05). It is projected when the first iteration needs it, so a zero-iteration `repeat` never projects it or checks its validity (LOOP-05). Projection follows the ordinary resolution of the written slot: owner walk, prelude, opens, structural dot paths (DOT-09), aliases normalized to their target (FWD-03), and parameters that forward a callable (HO-04).
- Each iteration invokes the projected callable as the ordinary call whose supplied arguments are the current state slots, in order. The slots are an already formed supply (LOOP-01, LOOP-03): the loop never reopens, re-counts or demands them. Cardinality, parameter and pattern binding (NEED-04), clause-family dispatch (clause order, inspecting patterns, non-match versus failure), builtin argument roles, demand, effects, random draws, cancellation and errors are those of the direct call `Step(s1, …, sk)` with the same supply. The loop adds only the iteration protocol.
- The invocation's row supply is the next state (LOOP-03): a user algorithm's or block's rows, the selected clause's rows of a family, or an alias's target's rows. A builtin supplies its one result value as one non-spread row. `while` reads its flag condition first (LOOP-06): that order belongs to the `while` receiver, not to the callable, so every callable kind stays eligible and its binding and dispatch are unchanged.
- Every callable is a valid step: user algorithms and blocks, clause families, prelude builtins (`if`, `map`, `while` and `repeat` included), Math functions, host operations, aliases of any of these, opened, qualified and dotted members, and forwarded callables. Validity never depends on the callable's category or representation, its number of clauses, the spelling that reached it, or whether the loop planner optimizes it.
- A captured call whose callee has no CALLABLE identity is `NotAnAlgorithm` ("The repeat step is not callable"), raised by CALLABLE projection alone when an iteration needs it, never by demanding VALUE. A genuinely zero-parameter callable supplied a non-empty state is callable but cannot bind the supply: the loop-state `ArityMismatch` "the loop found no step parameter to bind it to".
- Eligible is not successful. A failing invocation fails with its ordinary failure under the step's own call frame inside the loop's: a family non-match is `NoMatchingBranch`, never loop termination (only `while`'s `false` flag ends a loop), and a wrong state arity is the callee's ordinary `ArityMismatch`.

**Qualifications**
- An intrinsic-shaped invocation such as `5.string().repeat(1)` is captured, but loop setup refuses it: `NotAnAlgorithm` "The captured expression is not a callable invocation" (REF).
- A builtin's callback slot can invoke only a state slot that carries CALLABLE identity, an initial slot written as a callable: `repeat(map([1, 2], { x + 1 }), 1)` is `L[2, 3]`, `repeat(map([1, 2], 5), 1)` is `map`'s own `NotAnAlgorithm`, and `repeat(map([1, 2], { x + 1 }), 2)` is `map`'s own `ArityMismatch` at iteration 2, since results carry no callable identity.
- Builtins keep their argument roles: `repeat(if(false, 1 / 0, 2), 1)` is `2`.
- Loops are steps like any builtin: with `Step = { x + 1 }`, `repeat(repeat(Step(0), 2), 1)` is `2` (the inner call's original argument cell `Step(0)` is the outer `meta step`), a second iteration is `repeat`'s own `ArityMismatch`, and `while(repeat(Step(0), 1))` is a `TypeMismatch` flag.
- The loop planner plans eligible user steps only; a family or builtin step runs generically with identical values, effects and budgets on every strategy (RUN). Eligibility never consults it.

```katlang
Step(0) = 0
Step(n) = n - 1
repeat(Step(3), 2), Step(3).repeat(5), Step(Step(3))
```
⇒ `S[1, 0, 1]`

Each iteration is the ordinary family call.

```katlang
Countdown(0) = 0, false
Countdown(n) = n - 1, true
Countdown(3).while
```
⇒ `0`

A family is a `while` step with a base case, and the selected clause's last row is the flag.

```katlang
C(c) = count(c)
repeat(count([1, 2]), 1), repeat(C([1, 2]), 1), count([1, 2]).repeat(1)
```
⇒ `S[2, 2, 2]`

A builtin step is its one-row wrapper.

- Multi-slot family: `Gcd(a, 0) = a, 0, false` / `Gcd(a, b) = b, a mod b, true` / `Gcd(48, 18).while[0]` is `6`.
- Spellings: with `Inc = { x + 1 }` and `Swap = { b, a }`, `repeat(abs(-3), 2), repeat(Math.Abs(-4), 1), repeat(Inc(0), 3), repeat(Swap(5, 6), 1)` is `S[3, 4, 3, S[5, 6]]`. A brace block is not a callable reference, so it is named to be a step; `{ x + 1 }(0)` is `UnseparatedSameLineItem` (SYN-07A). A block reaches a loop unnamed through a parameter: `Apply(f, x) = repeat(f(x), 1)` / `Apply({x * 2}, 21)` is `42`.
- Opened and qualified: `open Lib` / `Lib = { public Step(x) = x + 1 }` / `repeat(Step(0), 2)` is `2`; `open Math` / `repeat(Abs(-4), 1)` is `4`; with a family member `Lib.Step`, `repeat(Lib.Step(3), 2), Lib.Step(3).repeat(2)` is `S[1, 1]`, while the bare path `repeat(Lib.Step, 2)` is the META refusal.
- Aliases and forwarding: with the family `Step` above, `A = Step` / `repeat(A(3), 2)` is `1`, and `Run(f, *s) = repeat(f(s*), 2)` / `Run(Step, 3)` is `1`. `Loop(g) = while(g(0))` / `Loop(SumWhile)` with `SumWhile(x) = x + 1, x < 2` is `2`.
- Failures: `F(0) = 1` / `F(1) = 2` / `repeat(F(5), 1)` is `NoMatchingBranch` exactly as `F(5)`; `repeat(Step(1, 2), 1)` and `repeat(take([1, 2]), 1)` are the callee's `ArityMismatch`; `Run(f) = repeat(f(0), 1)` / `Run(5)` is `NotAnAlgorithm`; `Z = 5` / `repeat(Z(0), 1)` is the loop-state `ArityMismatch`. The step's call frame names the expression its supply cell retains, which for a transported cell is the argument originally written for it.
- A step as a forwarded reference: `W(step) = while(step)` forwards the original call, so `W(S(0))` loops; `W(meta step) = while(step)` hands on a captured reference, which the META binder refuses (REF CR-4).

## SYN — Syntax and layout: vocabulary, rows, delimiters, separators, lines, and markers

This section fixes how source text becomes a program: the reserved vocabulary and literals, comments and physical lines, declarations and output rows, the three delimiters and grouping, separators and line continuation, line-anchored declaration heads, the star roles and marker attachment, and strings. Lean has no lexer or parser and sees only the elaborated AST, so these rules are C#-only by design: the C# parser is the sole implementation, and the constitution states the grammar's reading of valid programs. A **slot** is one item of an expression list, a **row** is an output slot of an algorithm body, and a **physical line** ends at a line feed. Two meta-rules govern the rest: parsing never consults meaning (SYN-13), and recovery from malformed text gives that text no meaning (SYN-14). Recovery shapes, diagnostic wording and spans are tooling and outside this section.

### SYN-01 — Exactly ten words are reserved; every other identifier-shaped word is an ordinary name, and names are exact

*C#-only by design.*

- Exactly ten spellings are keywords, never identifiers: `div mod and or xor not public open true false`. Reservation is exact and case-sensitive, so `True`, `Open` and `NOT` are ordinary identifiers.
- `true` and `false` can never be declared, shadowed, used as a parameter, or inferred as an implicit parameter. In a clause head they are literal patterns (PAT).
- Every other word is an ordinary name: every builtin (`if`, `count`, `sum`, `map`, …), `tick`, `load`, `Output`/`output`, `self`, `when`, `empty`, `content`, `spread` and `string`. Its meaning comes only from name resolution (RES; the prelude is shadowable), never from the lexer or the parser.
- An identifier is a maximal run that starts with `_` or a letter and continues with `_`, letters or digits. It is classified whole: a keyword spelling is always the keyword. Characters are classified per UTF-16 code unit, so surrogate pairs and combining marks are not identifier characters.
- Two identifiers are the same name if and only if their UTF-16 code units are identical: comparison is case-sensitive and ordinal, with no normalization. `Rate` and `rate` are different names, and a user `IF` never shadows the prelude `if`. No casing convention decides inference, visibility or kind.

**Qualifications**
- A few spellings are recognized by the implementation without being keywords: the call `load(...)` during load elaboration (MOD-07), the dot intrinsics `.string`, `.Invoke`, `.Arguments` and `.Algorithm` (DOT-08), the root's own `MinDecimalPlaces` and `MaxDecimalPlaces` properties, which the engine reads after output (RUN-06), and the contextual modifier `meta`. Everywhere else these are ordinary names: `load = 5` / `load` is `5`.
- `meta` modifies a parameter only when it is directly followed on the same line by another pattern item: `Capture(meta operation) = operation`. `F(meta)`, `F(meta, x)` and `meta = 3` keep the ordinary name, and a misplaced modifier is `InvalidMetaParameter` (PAR-01).
- Case-insensitive matching exists only in the near-miss suggestions of diagnostics.

```katlang
True = 1
self = 2
empty = 3
Open = 4
when = 5
π2 = 6
True + self + empty + Open + when + π2, not false
```
⇒ `S[21, true]`

- `true = 1` and `not = 1` are `UnexpectedToken`; `x = !true` is `UnexpectedCharacter` (`!` is not a token; write `not`).
- `F(true) = 1` / `F(false) = 0` / `F(true), F(false)` gives `S[1, 0]`: the reserved literals are patterns, not binders.
- `K = X + y` / `K(2, 3)` gives `5`: casing never decides inference.
- `rate = 1` / `Rate = 2` / `IF(x) = x * 100` / `rate, Rate, IF(3), if(true, 4, 5)` gives `S[1, 2, 300, 4]`.
- Nothing is normalized: `ﬁ = 1` / `fi = 2` / `ﬁ, fi` (the U+FB01 ligature is a letter) gives `S[1, 2]`.
- `F(MaxDecimalPlaces) = MaxDecimalPlaces + 1` / `F(1)` is `2`: a parameter with that name is ordinary.

### SYN-02 — Literal forms: unsigned decimal numbers, raw single-quoted strings, and the two Boolean keywords

*C#-only by design.*

- A number literal is ASCII digits with `_` allowed only between digits, an optional `.digits` fraction, and an optional lower-case exponent `e` with an optional sign and digits. It never starts or ends with `.`, and `E` is not an exponent marker.
- A literal never carries a sign: `-2` is prefix minus applied to `2` (OP). The numeric value a literal denotes (Decimal128, rounding, out-of-range rejection) belongs to OP.
- A string literal is raw single-quoted text, `'…'`, with no escape mechanism and nothing evaluated inside it: it cannot contain `'`, CR or LF (SYN-15). It is one `StringLiteral` token carrying the text. A `"` never starts a literal: it is `UnsupportedDoubleQuotedString` (SYN-15).
- The only Boolean literals are the keywords `true` and `false`.
- Lexing is greedy and maximal: a literal never absorbs a following letter, and what it cannot absorb starts a new token.

```katlang
1_000, 1.5e-2, 'it is', true, -2, 0.1 + 0.2
```
⇒ `S[1000, 0.015, 'it is', true, -2, 0.3]`

- `1E3` is `UnseparatedSameLineItem` (the literal `1`, then the name `E3`). `.5` and `1.` are `UnexpectedToken`. `'it''s'` is two strings, `UnseparatedSameLineItem`: no literal holds an apostrophe.
- `1__0, 1_0.0_1` gives `S[10, 10.01]`: several underscores may separate digits. `1e7000` is `NumberLiteralTooLarge`.
- `'a # not a comment', 'x' == 'x'` gives `S['a # not a comment', true]`.
- With `x = 5`, `-x ^ 2` is `-25`: minus applies to the power because literals and names are unsigned.

### SYN-03 — `#` comments are invisible to the grammar, and a physical line ends only at a line feed

*C#-only by design.*

- A `#` outside a string literal starts a comment that runs to the next CR, LF or end of input; no whitespace is needed before it. `//` is not a comment: it is two division tokens, so `1 // 2` is `UnexpectedToken`. A `#` in the text of a string literal is text, and so is one inside a rejected double-quoted run, which the lexer never interprets (SYN-15).
- Comments are invisible to every grammar decision: continuation, slot separation, declaration-head lookahead and star classification. Adding or removing a comment never changes the parse, and the newline that ends a comment keeps its full row and continuation meaning.
- A physical line break is LF alone. `\r\n` breaks the line through its `\n`; a lone `\r` is whitespace that separates no rows. Backslash is no continuation. Every line rule in this section (SYN-07, SYN-08, SYN-10, SYN-11) is stated over these physical lines.

```katlang
# a leading comment
A = 5 # five
A # the next line is a new row, not A - 1
-1
value=6#7
value
```
⇒ `S[5, -1, 6]`

- Without the comments the same program gives the same rows.
- `A = 5 -  # comment` newline `1` / `A` gives `4`: a trailing operator still continues past a comment. `1 # comment` newline `+ 2` gives `3`.
- `Foo(x) # comment` newline `= x` is `UnexpectedToken`: a comment cannot help a head span lines (SYN-10).
- `A = 1\rB = 2\rA + B` (CR-only line endings) is `UnseparatedSameLineItem`, because it is one physical line. The same text with `\r\n` gives `3`.

### SYN-04 — An algorithm body is a set of declarations plus an ordered list of output rows; there is no output keyword

- Every item of a body, the root included, is a declaration or an output row. The declaration forms are exactly `open …` (MOD), `[public] Name = body`, the clause `[public] Name(pattern) = body` (PAT), and a flat deconstruction `x, *y, z = body` or `*xs = body` (VAR).
- Every other item is an output row and contributes to the algorithm's output in written order (VAL-07).
- Rows and declarations interleave freely. Declaration order is unobservable (RES-10). The positional rules are the placement of `open` (MOD-01), the written order of a clause family's clauses, which is its selection order (PAT-02), and the row position of a deconstruction's right-hand side, which can reorder inferred parameters (RES-10).
- `=` only ends a declaration head; it is never an expression operator. Equality is `==` (CMP), and `A = x = 1` is malformed.
- There is no output keyword: `Output` and `output` are ordinary names.
- `public` prefixes only a property or clause definition, on the same line as the name, and a same-name clause family must be uniformly public or private. It never applies to `open`, a deconstruction or a row. Its only meaning is visibility to `open`: which names an `open` provides and which steps a dotted `open` target may take (RES-08, MOD-03, MOD-05). It affects neither exposure (RES-08, PROP-08) nor structural access.

```katlang
Total = Price * Count
Output = 5
Total
Price = 3
Output + output
output = 1
Count = 2
```
⇒ `S[6, 6]`

- These are parse failures: `A = x = 1` (`UnexpectedToken`; `x == 1` is an expression row, failing later as `UnresolvedImplicitParams`); `Algo(x, y) = { Prop = 7 }` (`ExplicitParametersRequireOutput`, a Lean-modeled constraint, VAL-05); `Rate = 5` / `Rate = 6` (`DuplicateProperty`, PROP-01); `public x, y = 1, 2` and `public 1` (`UnexpectedToken`); `X = { public open M … }` (`InvalidOpenDeclaration`); a clause family with a `public` first clause and a private second one (`ClauseVisibilityMismatch`).
- `open Lib` / `Lib = { public A = 1 ⏎ B = 2 ⏎ public F(0) = 10 ⏎ public F(n) = n + A ⏎ 0 }` / `A, F(0), F(5), Lib.B` gives `S[1, 10, 6, 2]`: structural access `Lib.B` reaches a private member (DOT-01).
- `F(n) = n` / `F(0) = 100` / `G(0) = 100` / `G(n) = n` / `F(0), G(0)` gives `S[0, 100]`: clause order is selection order.
- A program with no rows (`A = 1` / `B = 2`) has no program output. The engine reports it as no output and the raw evaluator as `MissingOutput`; that difference is host layering (VAL-05, RUN), not syntax.

### SYN-05 — Only a brace block (and the root) creates a scope; parentheses group and capture, brackets build lists, and indentation means nothing

- `( … )` groups an expression, captures several slots or a lone spread into one value (SUP-06), and delimits call arguments. `[ … ]` constructs one list (SEQ-02) or, on the same physical line after a completed receiver expression, delimits that receiver's selector list (SEQ-05). `{ … }` is an algorithm with its own lexical scope (ALGHO).
- A brace inside a string literal is text, never that brace: a string is raw (SYN-15).
- Only `{ … }` and the program root may contain declarations. `open`, property and clause definitions, and deconstructions inside `( … )` (a group or an argument list) or `[ … ]` are parse errors.
- A brace block's declarations, its `open` included, never leak outward, and a brace block is legal in any expression position.
- The three empties differ: `()` is the empty sequence value, `[]` the empty list, and `{}` an algorithm with no output, which is not a value (VAL-04, VAL-05).
- In a parameter list or clause head, `( … )` is a sequence pattern and `[ … ]` a list pattern (PAT-06); neither delimiter groups inside a pattern. `[` is contextual: it begins a list pattern there, a selector list after a same-line receiver expression (SEQ-05), and a list expression everywhere else.
- A definition whose entire body is one brace block (after redundant-group erasure) is that block, so its members are the definition's members.
- Indentation and blank lines never create or close a scope.

```katlang
A = 10
X = { A = 1
  A + 1 }
Outer(v) = v + Inner
  Inner = 100
X
{ A = 5
  A * 2 }
A, Inner, Outer(1)
(), [], [()]
```
⇒ `S[2, 10, 10, 100, 101, S[], L[], L[S[]]]`

The block-local `A` values (1 and 5) never leak, and the indented `Inner` is a root property, so the root can read it.

- `(A = 1)`, `F(x = 1)` and `(open Math)` are `DeclarationInParentheses`; `[A = 1]` is `UnexpectedToken`.
- `{}` and `X = {}` / `X` are `MissingOutput` errors.
- `Y(x) = 99` / `X = { Y = 1 ⏎ 0 }` / `Z = ({ Y = 2 ⏎ 0 })` / `W = { Y = 3 ⏎ 0 }, 5` / `X.Y, Z.Y, W.Y` gives `S[1, 2, 99]`. `Z` is the block, because its redundant group is erased (SYN-06). `W` has two slots, so it has no member `Y`, and `W.Y` is the extension call `Y(W)` (DOT-01).
- `X = { A = 1 ⏎ A }` / `X.A` is `1`: structural access reaches a non-public block member.
- `Twice(f) = f(f(1))` / `Twice({ x * 3 })` is `9`: a block in argument position.

### SYN-06 — Parentheses group syntax: a one-slot, non-spread group IS its content, so `E ≡ (E) ≡ ((E))` everywhere

*C#-only by design.*

- A parenthesized group with no declarations, exactly one slot, and a slot that is not a spread elaborates to the very node inside it, whatever that node's kind: a name, a call, a dot edge, a selection, a list, a block, a capture, `()`, or a graced name.
- No observer can tell the grouped spelling from the bare one: value, emitted count, normalization, every binding form, storage, caching and value demand, selection, dot receiver, spread, callable target, algorithm identity on the higher-order channel, open target, evaluation count and order, error kind, and every execution strategy.
- Parentheses never create, remove or change algorithm identity, at any nesting depth: `Apply((F))` ≡ `Apply(F)`, `(F)(x)` ≡ `F(x)`, `({…})` ≡ `{…}`, and `map(xs, (F))` ≡ `map(xs, F)`.
- Only a group whose parentheses do something survives, as a capture: several slots `(a, b)`, or a lone spread `(A*)` (SUP-06, SUP-07).
- Pattern parentheses are different. In a parameter pattern, parentheses are a sequence pattern, never grouping: `F((x))` is the invalid one-item sequence pattern, not `F(x)`, and `(…)` / `[…]` select the value kind they destructure (PAT-06). Grouping applies to call arguments (`F((A))` is `F(A)`), never to patterns.

**Qualifications**
- A grouped dotted callee erases to the dot node, so `(Box.G)(2)` is a call on the argumentless edge `Box.G` while `Box.G(2)` attaches the arguments to the edge. A structural path carries its member's identity in callee position (DOT-09), so both are the member call. On a structural miss the grouped callee is a computed value, and calling it is `NotAnAlgorithm`. `(Box.V)()` is fresh, like `Box.V()`.
- The only residue of a group is its source span, which serves diagnostics only.

```katlang
A = (1, 2)
Coll(*xs) = xs
F(x) = x * 10
Coll(A), Coll((A)), Coll(((A))), Coll((A*)), Coll(A*)
(F)(3), ((7)), (()), ((1, 2)), (A).count
```
⇒ `S[L[S[1, 2]], L[S[1, 2]], L[S[1, 2]], L[S[1, 2]], L[1, 2], 30, 7, S[], S[1, 2], 2]`

`(A*)` is a real capture (one value); only the unparenthesized `A*` supplies two items.

```katlang
T = tick()
(T), ((T)), T, (T).count, count((T)), (T)()
```
⇒ `S[1, 1, 1, 1, 1, 2]`

Every grouped read is the one cached read; only the explicit call `(T)()` evaluates afresh (PROP-06).

- With `Obj = { public V = 7 ⏎ 0 }` and a lexical `V = 99`, `Obj.V, (Obj).V, ((Obj)).V` gives `S[7, 7, 7]`.
- With `Inc(x) = x + 1` and `Apply(f) = f(10)`, `Apply((Inc)), Apply(Inc), Apply(((Inc))), (Inc)(1), map([1, 2], (Inc)), Apply(({ y * 2 })), Apply({ y * 2 })` gives `S[11, 11, 11, 2, L[2, 3], 20, 20]`.
- A capture has no algorithm identity (SUP-07): with `Dec(x) = x - 1`, `G(z) = Apply((Inc, Dec))` / `G(0)` is `NotAnAlgorithm`, and at the root, where the capture's elements are value positions, formula lifting makes the root `Apply((Inc, Dec))` fail as `UnresolvedImplicitParams`.
- `K = y - ((~x))` / `K(1, 2)` is `1`, the same as `y - ~x`.
- With `F((x, y)) = x + y` and `A = (1, 2)`, `F(A), F((A)), F(((1, 2))), F({ A })` gives `S[3, 3, 3, 3]`.
- `Step(x) = (x) + ((1)), ((x)) < 3` / `Step(0).while` is `3`.
- `Box = { public G(x) = x * 10 ⏎ 0 }` / `(Box.G)(2), Box.G(2)` gives `S[20, 20]`; `Inc(x) = x + 1` / `(5.Inc)()` is `NotAnAlgorithm`.

### SYN-07 — On one physical line only a comma separates slots; a newline separates slots only where a list is open across lines; `;` is not KatLang syntax

*C#-only by design.*

- In every expression list (root and body rows, groups, argument lists, list literals, definition bodies), `,` is the explicit slot separator.
- Whitespace never separates. Two complete expressions on one physical line without a comma are `UnseparatedSameLineItem`. A same-line `[` after a completed expression is no second expression but that expression's postfix selection (SEQ-02, SEQ-05): `A [1]` is one expression.
- A physical newline separates slots only in the contexts that stay open across lines: root output, a brace body, and an open `(`, `[` or argument list. An independent next-line expression or declaration ends a simple definition body or an open target list; continuation grammar crosses LF under SYN-08. A newline is never a separator inside a parameter-pattern list.
- A comma separates slots within its owning expression list. A trailing comma keeps the list open onto the next line, but a trailing comma before a closer is an error. A leading comma continues the owning expression list across LF, simple property, clause and deconstruction bodies included: `P = 1` newline `, 2` has two slots. Pattern lists and the open-target list keep their own separators. After the slot a comma introduced, ordinary grammar priority applies again: an independent next-line item ends a simple definition body.
- `;` is never a separator, joiner or continuation (`UnsupportedSemicolon`).
- An expression that continues (for example `1 -2`) is one slot, never two.

```katlang
F(x) = x
P = 1,
  2
Q = 3
4
P
Q, F(1 -2)
[5,
 6
 7]
```
⇒ `S[4, S[1, 2], 3, -1, L[5, 6, 7]]`

`P = 1,` continues across the newline, so `P` is the pair; `F(1 -2)` is the one argument `1 - 2`; inside the open `[`, a comma and a newline both separate.

- These are parse failures: `1 2`, `F(1 2)`, `2(3)`, `2 (3)`, `A[0](1)`, `x = 3 y = 4` and `1E3` (`UnseparatedSameLineItem`; `A[1]` and `A [1]` are selections); `1; 2` (`UnsupportedSemicolon`); `(3,)` (`UnexpectedToken`); `F(a` newline `b) = a + b` (`UnexpectedToken`, plus `UndeclaredIdentifier` from the front end: a pattern list has no newline separator).
- `P = 1` newline `2` / `P` gives rows `S[2, 1]`: the body ended at the newline. `2` newline `(3)` gives `S[2, 3]`.
- `F(a, b) = a - b` / `F(10` newline `3)` is `7`: a newline inside an open argument list.
- `P = 1` newline `, 2` / `P` gives `S[1, 2]`, as `P = 1, 2` does.
- A comma is also required between a spread slot and a following item on the same line, because `A* B` multiplies (SYN-11).

### SYN-08 — Grammar role has priority across physical newlines

*C#-only by design.*

- The canonical newline rule: "Newlines separate complete expressions by default. An incomplete expression continues when valid syntax permits it, without consuming a new declaration. Otherwise, an independent expression or declaration begins a new construct. Syntax that cannot stand alone but can legally continue the preceding expression attaches backward. All decisions are syntactic, never based on evaluated values." No indentation, value, type, arity or resolution participates.
- A dot continues member chains. A comma continues only its expression-list grammar, simple definition, clause and deconstruction bodies included; independent next-line slots still end those bodies.
- Unary minus requires direct attachment (OP-01): `10` newline `-2` is two rows, while `10` newline `- 2` is subtraction. A detached unary minus without a left operand is a syntax error. A negative literal pattern sign likewise requires direct attachment: `F(-2)` is valid, `F(- 2)` is a syntax error. `not`, Grace, and group, block and list openers keep independent expression roles; calls and selection stay same-line.
- Binary `+`, `-`, `*`, `/`, `div`, `mod`, `^`, the comparisons and `and`/`or`/`xor` continue according to grammar role, with the ordinary precedence and a single comparison chain. A collecting declaration on a star-led line remains a declaration.
- A line-final star is classified by attachment first (SYN-11): an attached `A*` completes the expression, a detached `A *` is incomplete multiplication, including before EOF, a later-line closer or a declaration. Missing operands are diagnosed; declarations and closers keep their owners (SYN-10).
- Comments, reported characters and blank lines are transparent to significant-token lookup but cannot reconstruct direct attachment.

**Qualifications**
- Design note: a complete line ends by default, and a continuing token announces itself on its own line; the previous line alone does not always settle whether an expression has ended.
- The canonical role table is `docs/design/language-rules/syntax.md` § Lexical identity and physical lines.

```katlang
10
+ 2
```
⇒ `12`

```katlang
10
-2
```
⇒ `S[10, -2]`

- `10` newline `- 2` gives `8`; `10` newline `* 2` gives `20`; `10 -2, 10- 2, 10 - 2, 10-2` gives `S[8, 8, 8, 8]`; `A` newline `.string` with `A = 2` is `'2'`.
- `Data = [10, 20]` / `Data` newline `[0]` gives `S[L[10, 20], L[0]]`: a later-line `[` begins a new list.
- `1 +` newline `Good = 41` / `Good` reports the dangling operator and preserves `Good`.
- `F(-2) = 1` / `F(n) = n` / `F(-2), F(5)` gives `S[1, 5]`.

### SYN-09 — A call is written only as a same-line `(` or `{` after a callable name or argumentless dot edge; juxtaposition never calls and never multiplies

*C#-only by design.*
*Open: whether "a written parameter list is never empty" (R5 below) is deliberate law, and whether a zero-arity family arm is host-only (Q-46).*

- A `(` or `{` on the same physical line directly after a callable target starts that target's argument list; whitespace between them is allowed. The callable targets are a name, a graced name, an argumentless dot edge (a member reference), and a redundantly grouped one of these (SYN-06).
- Nothing else is callable in syntax. After a number, a call result (a dot call with arguments included), an operator expression, a selection (`A[0](1)`), a list, a capture or a block, a same-line `(` or `{` is an unseparated item (SYN-07): never a call, never implicit multiplication.
- `F { e }` passes exactly one brace-algorithm argument: `F{e}` is `F({e})` (ALGHO).
- `A` (a property read) and `A()` (an explicit zero-argument call) are distinct forms (PROP-06).
- A written parameter list is never empty: `F() = …` is malformed.

```katlang
F(x) = x * 2
Sub(a, b) = a - b
F (3), F{ 4 }, (F)(5), 10.Sub (4)
F {
  6 }
```
⇒ `S[6, 8, 10, 6, 12]`

- `Mk(1)()`, `F(1)(2)` and `(1 + 2)(3)` are `UnseparatedSameLineItem`: a call result is not callable in syntax. `2(3)` is the same error. `F() = 1` is `UnexpectedToken`.
- `A = 3` / `A(), A` gives `S[3, 3]`.
- With `Mk(k) = k + 1` and `a = 1`, `a.Mk()` gives `2` and `a.Mk()()` is `UnseparatedSameLineItem`, like `Mk(1)()`: an argument-bearing dot result is not callable in syntax (DOT-09).
- `(Box.G)(2)` is a call on the argumentless edge `Box.G`, so it is the member call `Box.G(2)` (SYN-06, DOT-09).

### SYN-10 — Declarations are line-anchored: each begins a line, its head never spans lines, and a head is never an operand

*C#-only by design.*

- A declaration begins a physical line, or is the first item directly after the `{` that opens a body.
- Heads are line-local. A simple property head or deconstruction head is written on one line. A clause head's name and `(` share a line, and its `)` and `=` share a line; only the pattern list inside the open parentheses may span lines. `public` shares its name's line. A newline, comment, blank line or indentation never assembles a head after the fact.
- Once a head is recognized, its body after `=` may begin on the next line.
- A head is never an operand: a line that ends incomplete never takes the next line's declaration head as its missing operand, slot, member or body. The head stays a declaration.

**Qualifications**
- This is a recovery-side rule: it changes no valid declaration semantics. The detached `A *` newline `B = 5` reports the dangling multiplication and preserves `B`; the attached `A*` newline `B = 5` is a completed spread row followed by the declaration (SYN-11).

```katlang
Add(a,
    b) = a + b
A =
  5
x, y = 1, 2
Add(A, x + y)
```
⇒ `8`

The pattern list spans lines inside the open head, and `A`'s body begins on the line after `=`.

- Split heads are `UnexpectedToken` (the stray `=`): `A` newline `= 1`; `Foo` newline `(x) = x + 1`; `Foo(x)` newline `= x + 1`; `x, y` newline `= 1, 2`; `Lib = { public` newline `A = 1 }`.
- A declaration after content on the same line is `UnseparatedSameLineItem`: `1 P = 3` and `x = 3 y = 4`.
- A dangling line before a declaration is `UnexpectedToken` at the dangling token, and the declaration survives: `1 +` newline `Other = 2`, and `A =` newline `B = 1`.
- `A = 1 +` newline `B` newline `B = 2` / `A` gives `3`: the next line `B` is not a head (no `=` follows on that line), so it is the operand.

### SYN-11 — Star roles are syntactic; a line-final star is classified by attachment

*C#-only by design.*

- The star has four roles. Prefix attached `*name` is the collect marker in binding positions, infix `*` is multiplication, directly attached postfix `expr*` is spread when explicit same-line syntax closes it or when it is the final significant token of its physical line, and a `*` directly attached to a declaration head's name or to its parameter list's `)`, before the `=`, is the declaration's output-spreading marker (`A* = x, y`, `A(x, y)* = x, y`). No spread VALUE semantics are introduced here (SUP; the marker's elaboration is SUP-08).
- A marked head stays line-local (SYN-10): `Name*` and `=` share a line, and a clause head's `)`, `*` and `=` share a line. `A*` newline `= 1` is a spread row and a stray `=`, a parse error, never a marked declaration. Declaration recognition sees the marked heads through the same lookahead, so a marked declaration is never taken as an operand: `X = 2 *` newline `A* = 3` reports the missing operand and keeps the declaration `A`.
- When `*` follows a completed expression and is the final significant token of its physical line (EOF, a later-line token, closer or declaration next; comments and blank lines change nothing), attachment decides: an attached `expr*` is the spread marker and completes the expression, while a detached `expr *` is multiplication and leaves it incomplete. The canonical newline rule (SYN-08) then applies unchanged.
- Attachment is exact source adjacency. A reported character between operand and star leaves it detached. Nothing about values, names, types or arity participates, and there is no evaluate-then-fall-back reading.
- With a same-line follower the classification is spacing-independent: a same-line operand multiplies (`A*B`, `A* B`, `A *B`, `A * B`, `A*[0]`), while an explicit same-line comma, closing delimiter, fluent dot or further spread layer permits spread: `F(A*)`, `[A*]`, `Data[Indexes*]`, `A*, B`, `A*.F`, `(A**)`. For a same-line-closed spread classification precedes attachment: `F(A *)` is `InvalidSpreadMarker`. Prefix collect and Grace keep their own attachment rules (SYN-12).
- A leading star continues multiplication under SYN-08 unless it starts a collecting declaration.
- After a completed spread, syntax that cannot stand alone still attaches backward: `A*` newline `.F` is the fluent `F(A*)`, and `A*` newline `+ B` is `MisplacedSpread`.
- A root-final bare `Values*` is valid. A capture or brace creates one value and does not preserve root row cardinality: `X = (A*)` and `X = { A* }` are explicit closures.

```katlang
A = 3
B = 10
A*
B
```
⇒ `S[3, 10]`

```katlang
A = 3
B = 10
A *
B
```
⇒ `30`

- `A = 1, 2, 3` newline `A*` emits three rows. `A**` at EOF is two spread layers. `X = A*` newline `X` is the spread definition and the row `X`. `7*` at EOF spreads the scalar `7`; `7 *` at EOF is a missing operand.
- `A*` newline `B = 5` keeps the declaration, while `A *` newline `B = 5` reports the missing operand and preserves it.
- `A*` newline `-2` is two rows, and `A *` newline `-2` is `A * -2`. `A` newline `* B` multiplies.
- With `A = 3` and `B = 2`, `A*B, A* B, A *B, A * B` gives `S[6, 6, 6, 6]`.

### SYN-12 — Markers and special prefix roles require attachment; binary operators retain ordinary spacing

*C#-only by design.*

- The markers are the collect marker `*name`, the spread marker `expr*`, the declaration's output-spreading marker `Name*` / `Name(…)*` (SYN-11, SUP-08), and Grace `~name`/`name~`.
- Attachment is exact source adjacency: each marker must touch the syntax it modifies, and any whitespace, comment or newline breaks attachment.
- A detached marker is a parse error (`InvalidCollectMarker`, `InvalidSpreadMarker`, `InvalidGraceMarker`, `DetachedOutputSpreadMarker`), never a reinterpretation as another operation.
- Attachment is checked after classification, except for a line-final star: a star with a same-line follower is classified without attachment, a line-final star by attachment (SYN-11).
- A collect marker attaches to exactly one binding name (`**x` is an error), and a declaration takes exactly one output-spreading marker (`A** = 1` is `RepeatedOutputSpreadMarker`). Grace attaches to a bare name occurrence only, so `(a)~`, `f(x)~` and `5~` are errors. The weights and eligibility of Grace belong to PAR-06 (see also DOT-06).
- Binary operators, `.` and the selection bracket `[` accept any same-line spacing.

**Qualifications**
- Because a line-final star is classified by attachment, a formatter must preserve its attachment; it cannot replace a classified marker with another valid operation.

```katlang
Coll(*xs) = xs
K = a - ~b
A = (1, 2)
N = 3
Coll(A*), K(10, 3), N * 2, N*2
```
⇒ `S[L[1, 2], -7, 6, 6]`

`~b` moves `b` first, so `K(10, 3)` is `3 - 10`.

- These are parse failures: `Coll(A *)` (`InvalidSpreadMarker`); `F(* xs) = xs` and `F(**xs) = xs` (`InvalidCollectMarker`); `K = a - ~ b` and `K = (a)~ - b` (`InvalidGraceMarker`, the latter with the eligibility message); `A * = 1` (`DetachedOutputSpreadMarker`).
- `K = a~ - b` / `K(10, 3)` gives `-7`.
- A line-final Grace marker after a call is rejected, never moved to the next row: `Q = {` / `b` / `F(1)~` / `a` / `}` / `F(z) = z` / `Q(10, 20)` is `InvalidGraceMarker` (the one-name eligibility rule).
- Comments neither manufacture nor destroy attachment: `A*# comment` at EOF is an attached line-final spread, while `A *# comment` leaves a multiplication without its operand.
- With `Sub(a, b) = a - b` and `A = 10`, `A . Sub(1), A .Sub(2), A. Sub(3)` gives `S[9, 8, 7]`; with `A = (10, 20)`, `A [1], A[0]` gives `S[20, 10]`.

### SYN-13 — The grammar never consults meaning: no parse depends on arity, values, types, name resolution, or callee spelling, except MOD-07's `load(...)` open-target form check

*C#-only by design.*

- Every parse decision is made from tokens and their physical lines alone: slot separation, continuation, star classification, call formation, declaration recognition and redundant-group erasure.
- No parse decision looks at the arity of any callable, runtime values, inferred types, what a name resolves to, or a callee's spelling.
- Consequently a wrong-arity call to anything, builtins included, parses and fails at evaluation (`ArityMismatch` for every callee category, a clause family included, CALL-04; `NoMatchingBranch` is a family's verdict for an accepted count that no clause matches, PAT-02); a builtin's name may be a user property or parameter without the parser noticing; and a spread argument's item count is known only at evaluation.

**Qualifications**
- Two spellings are read by the parser, both by token and line alone. The `load(...)` directive (MOD-07): the open-target form check admits a written `load(...)` call as a surface open form, so `open Load('u')` is a parse-time `BadOpenForm` while `open load('u')` is left to load elaboration. That check decides only whether an open target is a valid form. And the contextual modifier `meta` (SYN-01), which modifies the next pattern item on the same line.
- The dot intrinsics `.string`, `.Invoke`, `.Arguments` and `.Algorithm` (DOT-08) and the reads of the root `MinDecimalPlaces` and `MaxDecimalPlaces` (RUN-06) are evaluator and engine decisions, not parse decisions.
- Declaration recognition is purely syntactic lookahead: `Name =`, `Name(…) =`, either with an output-spreading marker before the `=` (`Name* =`, `Name(…)* =`), a binding-pattern head, `open`, `public`.

```katlang
T = true, 10, 20
Twice(if) = if(if(1))
if(T*), true.if(10, 20), Twice({ x + 3 })
```
⇒ `S[10, 10, 7]`

The spread expands to three arguments at evaluation, and the parameter named `if` is an ordinary callable.

- These are evaluation errors, not parse failures: `if(true, 2)` is `ArityMismatch` (the builtin's arity is checked on the resolved identity, RES); `F(a, b) = a + b` / `F(1 -2)` is `ArityMismatch` (the text is one argument whatever `F` expects).
- A clause family reports a wrong count as `ArityMismatch`, never a parse error: `Fam(0) = 0` / `Fam(n) = n` / `Fam(1, 2)` (too many) and `Fam(0, y) = 0` / `Fam(n, y) = n` / `Fam(5)` (too few).

### SYN-14 — Recovery is not grammar: recovery trees, stand-ins, delimiter repairs and clause-head confinement give malformed text no meaning

*C#-only by design.*

- A lexical or syntactic error makes the parser build a recovery tree for diagnostics and editor analysis only.
- Recovery decisions are not grammar and never give malformed text a meaning. They include reported characters standing in for a missing piece, delimiter-ownership repairs, separator stand-ins and clause-head confinement.
- What a program means is decided by the grammar's reading of valid source (SYN-01 to SYN-13). A recovered tree that happens to look like a valid program is still not that program.
- That no source with a front-end error (lexical, syntactic, load or elaboration) is ever evaluated is RUN-04; this rule is its grammar-side reason.

**Qualifications**
- Recovery shapes, diagnostic multiplicity and wording are tooling, outside this law. The gate and its host-API caveats belong to RUN-04.

```katlang
A @= 1
A, tick()
```
⇒ `UnexpectedCharacter`

The recovery tree contains the declaration `A = 1`, but the program has no value and `tick` is never called. Likewise `X = { A = (1, 2]` newline `Later = 5 }` / `X.Later, tick()` is `UnexpectedToken`: the delimiter repair keeps `Later` inside `X` for the editor, and the program still has no value.

### SYN-15 — A string has one spelling, raw single-quoted text; a double quote is the targeted front-end error `UnsupportedDoubleQuotedString`

*C#-only by design.*

- A string literal is raw single-quoted text, `'…'`: its text is exactly the code units between the quotes, on one physical line, with no escapes and nothing evaluated inside it. `'a\nb'` keeps its backslash, `'{x}'` is the text `{x}`, `'C:\temp'` is that path, and `'say "hi"'` holds two double quotes.
- A string cannot contain `'`, a line feed or a carriage return: a line feed ends it, and so does a lone carriage return. There is no prefix form, no verbatim form and no multiline string. An unclosed `'` is one `StringLiteral` token to the line end with one diagnostic, `UnterminatedStringLiteral`, so the next line lexes independently.
- Double-quoted strings and string interpolation are not KatLang syntax, and nothing replaces them: no escape, no doubled brace, no hole, no concatenation, no `format` or `print` builtin, no other quotation and no implicit conversion of a value to text (VAL-02).
- A `"` outside a comment or a single-quoted string is `UnsupportedDoubleQuotedString`. The lexer scans from the quote to the next `"` on the same physical line, or to the end of that line when there is none, and never consumes the line break. It interprets nothing inside the run: no backslash, no brace, no `#`. It emits one recovery `StringLiteral` token carrying the undecoded text, and exactly one diagnostic over the whole run: both quotes when it is closed, to the line boundary when it is not. An unclosed run is that diagnostic alone, never also `UnterminatedStringLiteral`.
- Recovery cannot authorize acquisition. A string token rejected by the lexer keeps its text for analysis but can never be an `open` or `load` URL: an unterminated single-quoted string and every rejected double-quoted run cause no downloader invocation for that directive, even when the diagnostic-list cap omitted the lexical error's report. Other valid imports keep their ordinary schedule (MOD-07, RUN-04).
- A program holding a double-quoted run has a front-end error and is never evaluated (RUN-04). Later declarations are still parsed as written, and a clause head holding a rejected run is a recovered head, compared with no other clause (SYN-14).

**Qualifications**
- The rule is per run, so one malformed line may report more than once: `"a \"b\" c"` is the run `"a \"`, the code `b\` and the run `" c"`.
- The rejection is a recovery rule, not a supported spelling: the recovered text is never a string value, a pattern, an open target or a URL.

```katlang
'{x}', 'C:\new', 'say "hi"', 'a' == 'a', 'a # not a comment'
```
⇒ `S['{x}', 'C:\new', 'say "hi"', true, 'a # not a comment']`

- These are front-end failures, each `UnsupportedDoubleQuotedString`: `"abc"`; `x = 1` / `"Total: {x}"`; `A = "abc` newline `A, 5` (unclosed: one diagnostic, and the next line parses as written); `F("a") = 1` / `F('a')`.
- `A = 'abc` newline `A` is `UnterminatedStringLiteral`.
- `'it''s'` is two strings, `UnseparatedSameLineItem` (SYN-02): no literal holds an apostrophe.

## RUN — Runtime transparency, evaluation outcome, host policy, and seeded randomness

A **route** is one way the C# runtime executes a program: generic or optimized, synchronous or async twin, plain or counted, engine or low-level evaluator. A **run** is one top-level evaluation with its own state (RUN-02), and its **observation** is what every route must agree on (RUN-01). A **resource limit** is host protection that can stop a run and never redefines it (RUN-03). A **demand point** is a place where written code may go unevaluated (RUN-08). Lean models almost none of this machinery: RUN-07, RUN-08 and RUN-09 restate what its evaluator fixes, and RUN-02 is partly modeled.

### RUN-01 — The meaning of a program is independent of the execution route

*Open: the layering of `NoProgramOutput` and `MissingOutput` in exception 3 (Q-41).*
*C#-only by design.*

- Fix the program, the host-operation configuration, the seed and the limits. Every execution route must then produce the same observation. The routes are:
  - the synchronous generic evaluator, which is the oracle;
  - the optimized strategies: planned `while`/`repeat` loops, fused `filter`→`count`, and direct-range fusion;
  - the async twin family, whether it completes inline or genuinely suspends;
  - plain `Evaluator.Run` and counted `Evaluator.RunCounted`;
  - `KatLangEngine.Run` and `KatLangEngine.RunAsync`.
- The observation is the value, the emitted count, the error kind (RUN-07 (d)), the sequence of host-operation invocations (count, order and arguments), the sequence of random draws (RAND-01), and the number of times each property body is evaluated.
- **Representation sharing is not a route.** When one immutable expression node occurs at several positions, each occurrence is evaluated separately under its own lexical context. It has the same value, effects (host calls, random draws), evaluation counts, charges and resource verdicts as structurally identical clones. The shared-node cases are host-built DAG ASTs and the front end's shared implicit-argument bundles.
- No value cache and no semantic identity is keyed on expression-node reference identity. Semantic identity comes only from declaration and activation identity (ALG-07, PROP-07). The one spliced module of MOD-09 shares a cache entry because it is one declaration, not because its nodes are shared. A memo keyed on nodes or on a deconstruction group may hold planning facts or a pure re-bind of an already cached value, never an effectful result.
- **Module-loading configuration does not change meaning either.** A downloader (`RunOptions.DownloadCode`, the CLI's `--allow-loading`) together with its load policy makes module loading available. It is a capability, not part of the program's meaning.
  - With host operations, seed and limits held fixed, a program without a `load` directive elaborates to the same semantic structure and gives the same observation with or without a downloader, on supported entry points and subject to the exceptions below.
  - In a program that does load, module elaboration preserves every non-directive boundary (MOD-07). Actual imported declarations may change surrounding binding, signatures and results; that is the effect of loading source, not of merely configuring the capability.
  - The downloader and policy determine whether acquisition succeeds and what module source is supplied (MOD-11), and the configuration determines which entry points are supported (exception 4). No equivalence between different host-operation configurations or different downloaded source is asserted.
- The zero-argument property cache is not a route. It is language semantics (PROP-04 to PROP-09), and every route applies that one cache law. In an effect-free program, caching is unobservable.

**Permitted exceptions.** There are exactly four:

1. **Plan and fusion hit counts** differ between optimized and generic runs by definition. The budget counters (steps, peak depth, materialized items and string units) are the same on every strategy (RUN-03), and the twin's equal the generic ones.
2. **Resource limits.** Whether a resource limit stops a run, which verdict fires and where may depend on the route. The host-stack backstop differs in both directions: the twin's larger frames usually reach it earlier when it does not suspend, so a run that completes on the synchronous routes can stop with `EvaluationStackExhausted` on the twin, while a twin that genuinely suspends before descending resumes on a fresh stack and can complete where the synchronous routes stop. This is host policy (RUN-03). It never depends on which limits are configured, and it never licenses a route-dependent success value: every encountered resource limit is terminal for the run, so resource-limit differences may stop a route or change its resource verdict, but never change the value of a route that succeeds.
3. **Post-evaluation host projections** exist only on the engine: the reads of the root's own `MinDecimalPlaces` and `MaxDecimalPlaces` source settings with their validation and pair checks (RUN-06), the bounded host-atom projection, and mapping `MissingOutput` to `NoProgramOutput`.
4. **Sync entry points refuse some trees and configurations.** A synchronous low-level entry point rejects a tree carrying deferred module regions with `InvalidOperationException` (MOD-10). The synchronous source entry points (`KatLangEngine.Run`, `Parser.Parse(source, options)`) likewise reject a downloader-configured options object before parsing. Both are refusals: no route ever runs the program with a different meaning.

**Qualifications**
- Diagnostic detail is an implementation requirement, not constitutional. Routes are also required to agree on the error's message, payload, span and context frames, and the parity suites pin that. Wording and spans are nevertheless presentation.
- Accounting is strategy-neutral. Planned loops and fused pipelines charge exactly what the generic strategies charge: one step per iteration and per invocation, the generic expression-work checkpoints, the generic composition's item reservations and the same string units. Every limit verdict is therefore strategy-independent while the optimizations stay enabled under any limits (RUN-03).
- The twin always pins the generic strategies.
- The nearest look-alike is `A` versus `A()`. That is no route difference: `A()` is a different call shape with different semantics (PROP-06). Programs that differ only in spelling are other rules' laws: `(E)` and `E` (SYN-06), `x.F` and `F(x)` (DOT-03).
- Opt-in passive observation of root properties is a host read of the entries the run already published. It evaluates, charges and draws nothing and observes no cancellation, so it changes no observation. Absence of an entry proves nothing. For a published list, the snapshot uses a concrete form the run built, a completed one-level read, or the memoized values of all positions once cardinality has settled. It applies the same test to nested lists. An unsettled, unread, failed or cyclic part withholds the whole observation, as does a call reference or its argument view (CR-6, CR-12): `Whole = [1 + 1, 2]` / `Whole` observes `L[2, 2]`, while `Part = [1 + 1, 1 / 0]` / `Part.count` withholds `Part` (SEQ-02).
- Lean terms are trees, so the sharing clause has no Lean counterpart. The plain/counted route is FORMAL-05.

```katlang
A = tock()
Step(i, acc) = i + 1, acc + trace(i) + A
P(x) = traceA(x) > 2
repeat(Step(0, 0), 3), count(filter(range(1, 5), P)), A, A()
```
⇒ `S[S[3, 6], 3, 1, 2]`, with host log `[trace(0), tock#1, trace(1), trace(2), traceA(1), traceA(2), traceA(3), traceA(4), traceA(5), tock#2]` on every route.

Each occurrence of a shared argument bundle draws and traces on its own:

```katlang
G = randomInt(0, 1000) + trace(a)
H = G, G, G
H(1)
```
⇒ `S[700, 293, 63]`, with three `trace(1)` events, exactly like the written form `H(a) = G(a), G(a), G(a)`.

Load-free source keeps every written boundary, with or without a downloader: `X(a) = 100` / `A = { { public X = 1` / `5 } }` / `A.X, A` is `S[100, 5]`. The written inner block owns `X`, so `A.X` falls back to `X(a)`.

### RUN-02 — The run is the unit of evaluation state

- Each evaluation run starts from fresh run-scoped state:
  - an empty zero-argument property cache;
  - fresh activation and binding contexts;
  - a fresh budget;
  - a fresh random stream (RAND-01);
  - a `tick()` counter at zero (RUN-09).
- That state is shared by everything inside the run: nested calls, callbacks, loop frames, suspension and resumption, and the engine's `MinDecimalPlaces` and `MaxDecimalPlaces` reads. It never outlives the run.
- That includes the invocation plans call references denote. Run results and host-operation arguments refuse any value containing a reference or argument view (`TypeMismatch`). In C#, a reference used by another run or after its own run ended is `IllegalInEval`; serial Lean has no cross-run channel.
- An observation depends only on the program and its options. It never depends on earlier, concurrent, interleaved, suspended or nested runs, even when they share a parsed tree, an options object, a host-operation configuration or a limits instance.
- For a fixed program, options (including the seed) and host-operation behaviour, every run that completes, with a value or with an ordinary failure, yields the identical observation.
- The only nondeterminism is an unseeded random stream (RAND-02), host operations' own results, and whether the machine-dependent host-stack backstop stops a run. That outcome can differ between processes, threads, routes, builds, runtimes and JIT states, even between two runs in one process as its code tiers up, but never because of which limits are configured (RUN-03).
- A run that a resource limit stops fails with that limit. It never completes with a different observation (RUN-03).

**Qualifications**
- Within a run, sharing is intended. `A` is one entry for the whole run, across all activations, when it is exported (PROP-08).
- Run-scoped memos that add no semantics, such as the deconstruction shared-bind cache, are not part of this rule. The hoisted source itself is an ordinary cached property (PROP-04).
- A module loader instance's module cache is persistent per-instance state. A deferred module region's materialized body is memoized on the region for the lifetime of the elaborated tree, and is shared by concurrent and later runs of that parse. A failed materialization is never cached, and download attempts stay charged to the loader's source-processing budget. That is front-end source acquisition and host admission (MOD-10, MOD-11), not evaluation state.
- Unseeded runs are deliberately not reproducible (RAND-02).

```katlang
A = tock()
R = randomInt(0, 1000)
A, A, R, R, randomInt(0, 1000)
```
⇒ `S[1, 1, 699, 699, 292]`, with one `tock` event. Evaluating the same source again invokes the host again for `A` and restarts the seeded stream at `699`: no cache entry crosses runs.

### RUN-03 — Runtime protection is host policy: it may stop a run, never redefine it

*Open: whether loop-step invocations should charge dynamic depth (Q-39). A loop step is outside the depth protocol today, so recursion routed through loop steps is bounded only by the host-stack backstop.*
*Open: whether the engine should fail a successfully evaluated run on its host-atom projection bound, and whether host-returned collections should be charged against the cumulative budgets (Q-40).*
*Open: cancellation precedence in `KatLangEngine.Run` (Q-41).*
*Open: whether Lean's incomplete outcome stays a constructor of `Error` (Q-82). It is no resource limit and no language error, and no C# kind corresponds to it.*

- **An encountered resource-limit failure is terminal for the run. A configured limit may prevent a result, but it must not redefine the value of a run that succeeds.** Runtime resource protection is host policy; it does not change the language's value rules.
- **Terminal.** Once any evaluation that actually occurs reaches a resource limit, the run ends with that failure. Nothing is evaluated after it: no later argument, callee body, loop iteration, output row, random draw or host operation.
- **Never postponed or absorbed.** No construct can defer, absorb or replace it: not a binding that is never read afterwards, a supplied computation's memo, forwarding, a builtin's arity verdict, an earlier ordinary failure, or a consumer's choice. A demanded cell that reaches a limit stores it as its terminal completion and the run retains that error, so the cell never restarts and no later semantic work runs: no further evaluation, memo read, CALLABLE projection, random draw or host operation (NEED-02, NEED-09).
- **Ordinary failures differ.** An ordinary failure is the completed outcome of the computation that raised it (NEED-02, CALL-06) and fails only the demands that reach it, while a reached limit is terminal for the whole run. Neither is ever a recoverable argument value or a clause mismatch, and neither enters the success-only property cache (NEED-10). Both end the run once evaluation that actually occurs raises them, and a supplied computation that is never demanded runs nothing and reaches neither (RUN-08).
- **No new eagerness.** Code that the language never evaluates (the demand points of RUN-08) reaches no limit. A limit is never a reason to evaluate anything.
- **The limit law.** Hold all other semantic inputs fixed: the program, KatLang version, seed, host-operation behaviour, supplied module source and entry point. A run that completes under a configured evaluator limit, with a value or with an ordinary failure, is exactly the run without that limit. Raising a limit may therefore turn a resource-limit failure into that run, never one success into another. Absorption of a limit may never replace the unlimited evaluation's ordinary failure or divergence with a success. An actually encountered limit ends evaluation; a computation that would fail ordinarily but was never demanded does not change that. This is a semantic reference, not the default configuration: default runs still have always-active limits. Lean supplies that reference only for the semantics it models (FORMAL-03, FORMAL-04); it does not model seeded draws, host operations or the full Decimal128 tier.
- **Scope.** The canonical classifier is `IsResourceLimit`, which reads through context wrappers.
  - Its seven evaluator kinds cover dynamic depth (`EvaluationDepthExceeded`), steps (`EvaluationStepLimitExceeded`), host-stack exhaustion (`EvaluationStackExhausted`), per-collection size (`CollectionSizeLimitExceeded`), cumulative materialized items (`MaterializationLimitExceeded`), per-string length (`StringSizeLimitExceeded`) and cumulative string units (`StringMaterializationLimitExceeded`).
  - Its other two kinds belong to different phases. AST depth (`AstDepthLimitExceeded`) rejects the tree before evaluation, and a selected deferred unit's materialized body before the evaluator descends into it, at the run's effective limit less the placeholder's weighted prefix, as a terminal run verdict (MOD-10). Display overflow (`DisplayLengthLimitExceeded`) is rendering state after evaluation and leaves an existing success and its value intact; the terminal law does not turn it into an evaluation failure.
  - No source form grows a string: its producers are string literals, `.string` and the host (VAL-02). Every string a run creates is reserved once against the per-string and cumulative string limits, identically on every strategy, and a host operation's returned strings are admitted against the per-string limit before use.
- **Transient item supplies** add no kind. An expanded argument, selector, loop-row or accumulator supply is bounded by the per-collection limit before it retains its expansion.
  - An overflowing supply retains nothing more but still forms, count-only, to its end. Later explicit spreads evaluate in written order with their effects, a failure one of them raises is reported instead, and ordinary slots stay undemanded.
  - The refusal comes there: for a list, capture, group or join through its own reservation (the error the unbounded accumulator reached), and for a call, selection or loop-row supply before any binding. A call, selection or loop round whose expanded supply exceeds the limit is therefore refused at the end of formation and never reaches an arity verdict, an ignored collector or the collector's own refusal.
- **Host-returned values** add no kind. A host return is admitted against the per-collection and per-string limits before any consumer sees it (RUN-05). Both this refusal and a transient supply's are terminal like every other.
- **Structural work.** Evaluator-owned equality and hashing charge the run's structural-work budget and observe cancellation: `contains`/`distinct`, every `==`/`!=` link, repeated-name VALUE compatibility and literal-string pattern matching.
  - String payload counts, and a large payload is charged before its one uninterruptible native compare or hash.
  - A refused required comparison returns the retained resource error directly, never inequality, a repeated-name arity verdict or a clause non-match, and no later clause, demand or effect runs.
  - Unit counts depend on reference sharing. Completed value and hash semantics and demand order do not.
  - Comparison memos belong to one builtin operation, one comparison link or one binder activation, never another run. The public host comparer stays context-free, and Lean has no corresponding cost model.
  - Host-boundary walks follow the same policy. Admitting a host return's nested structure and the per-call host-argument call-reference scan are charged structural work. The once-per-run result-export scan charges nothing, because a successful run never fails for having had its result inspected, and it only observes cancellation.
- **Source admission.** Source-size and acquisition limits are host admission policy, applied when the language's source-processing contract requires a source unit, before its contents are used.
  - A deferred unit is processed only when an operation requires its compilation, including required identity information. Refusal stops that operation and its run, while an undemanded deferred computation performs no source work, and no admission event exists for it.
  - These refusals stay outside `IsResourceLimit`, which keeps its evaluator, preflight and rendering meaning. A reached required-source failure cannot be bypassed, turned into an alternative successful value or treated as branch or pattern non-match.
  - Initial or eager refusal is `ParseFailure`. Required deferred refusal is `EvalFailure` carrying the underlying diagnostic and import provenance, before the body executes.
- **Static-structure admission.** Static structure analysis, signature selection included (PAR-08), runs inside a deterministic per-operation resource envelope that a host may only lower. Machine or GC memory never changes it. Exhausting it is the front-end error `StaticStructureLimitExceeded`: a resource refusal, never an inference rule and never `SelfDependentInferredParameters`. It stays outside `IsResourceLimit`, and no partial completion is published.
- **Further host-protection guarantees.**
  - A limit never crashes the process and never becomes a KatLang value.
  - **Limits observe a run; they never choose how it runs.** No configured evaluation limit selects an execution strategy. The strategy comes from the program, the requested optimizations and the route, and the route from genuine host capability (an async-capable cache, an asynchronous host operation, a deferred module region), never from `EvaluationLimits`. A limit is a check, never a switch, and writing a limit's default value is the same as leaving it unset.
  - Every strategy performs the same logical accounting for every semantic budget: steps (the bulk expression-work checkpoints included), depth, materialized items and string units. A limit that is reached therefore gives the same verdict, at the same point, on every strategy. Configuring, raising or removing a limit that a run does not reach changes nothing about that run on the same host: not its value, effects, random draws, budget accounting, strategy, or whether it completes.
  - Budgets are per run. A rejected enter or reservation mutates no counter. Depth is released exactly once. Steps, items and string units are cumulative.
  - A materialized sequence or list accounts for its own immediate slots. A capture or exact list built from a completed supply reserves those slots before constructing its result. Lists with deferred positions follow the reservation points below. A nested constructed value occupies one independently reserved parent item, so nesting never transfers, suppresses or duplicates a child's reservation. A canonical capture of zero or one item reserves nothing, an exact list reserves its immediate length (one included), redundant grouping creates no boundary, and completed child reservations stay charged when a later slot fails or cancellation interrupts.
  - **Lists evaluated on demand** (C#-only accounting). A list of known cardinality reserves its positions when it is built. A `filter` scan reserves its accepted positions at completion. A stage over discovered positions reserves them when it first builds a concrete form. An executed callback is charged its invocation and its work when its position is read, and an unread element incurs no evaluation charge. Building a known-size list can still reach its reservation limit. Whole-value reads keep explicit frames and observe cancellation. A result that keeps building lists while it is read whole is bounded like recursion: `F(x) = [x].map(F)` / `F(1)` is `EvaluationDepthExceeded`, while `F(1).count` is `1`.
  - **Folds** (C#-only accounting). A `reduce` step suspended while its accumulator is evaluated is a fold continuation, accounted apart from call nesting: every step runs at the depth the fold began at, so a fold over any admitted collection stays within `MaxDepth` exactly when one step does, while recursion inside a reducer still counts. A reducer that leads with its accumulator (`acc + x`) takes a streamed route, chosen from the reducer's structure alone, with the same values, effects, ordinary failures and total charges; it charges a step's expression work when that step's body runs instead of on the way down, so a `MaxSteps` budget that runs out inside such a fold stops after more completed steps than the nested order would, with the same verdict at the same consumed total on every strategy.
  - **Semantic limits are deterministic; the host stack is an environmental backstop.** Only the error kind belongs to the language; the thresholds are host configuration. Under a given configuration, the verdict and failure point of the depth, step, per-collection, cumulative item, per-string and cumulative string limits follow from the program and the logical accounting above, identically on every route and strategy, unless the host-stack backstop stops the run first.
  - **Host-stack headroom is not semantic.** Whether and where `EvaluationStackExhausted` fires depends on the thread and its stack size, the build, the runtime and its JIT state (which changes within one process as code tiers up), the platform, the route and suspension (a suspended twin resumes on another stack). Routes may therefore disagree on whether a run stops and, when the backstop pre-empts a semantic limit on one route, on which verdict fires (RUN-01 exception 2), never on the value of a run that completes. Its firing depth is never promised, and it never depends on which limits are configured.
- **Host cancellation is not an error.** A requested cancellation throws `OperationCanceledException` with the supplied token. Inside the C# async evaluation boundary, `EvalError.HostTermination` carries the retained exception to the entry point, which rethrows it. KatLang code cannot observe cancellation as a value or a binding verdict. A supplied computation interrupted by cancellation completes as cancelled and is never restarted: a later demand of it rethrows the same cancellation (NEED-02, NEED-09). An uncancelled token changes nothing.

**Qualifications**
- The verdict kind and the depth at which the host-stack backstop fires depend on the route and the machine. Here `A = A.string` / `A` gives `EvaluationDepthExceeded` on the synchronous route and `EvaluationStackExhausted` on the async twin, and `F(x) = if(x < 40, F(x + 1), x)` / `F(0)` gives `40` on the synchronous route and can stop with `EvaluationStackExhausted` on a non-suspending twin. Absolute thresholds are never promised.
- The engine additionally bounds its host-atom projection after a successful evaluation (RUN-06).
- Source-processing limits are not among the nine kinds. Per-source and aggregate length, module count, import depth and module-elaboration stack protection stay host and source policy, under the source-admission law above.

```katlang
range(1, 200000).count
```
⇒ `CollectionSizeLimitExceeded` on every route.

A limit is reached only by evaluation that occurs:

```katlang
Deep(n) = if(n == 0, 0, 1 + Deep(n - 1))
G(x, y) = y
G({Deep(1000) + randomInt(0, 1000)}, randomInt(0, 1000))
```
⇒ `699`: `G` never demands `x`, so its computation never runs and reaches no limit, and `y` draws the stream's first word. With `G(x, y) = x + y` and a `trace` around each draw, `x` is demanded first, its limit ends the run after `[trace(699)]`, and `y` never runs. An ordinary failure in the same position stays undemanded too: `G(x, y) = y` / `G({1 / 0 + randomInt(0, 1000)}, randomInt(0, 1000))` is `699`.

### RUN-04 — A source with any front-end error is never evaluated, and recovery gives malformed text no meaning

*Open: whether this law should reach the low-level `Evaluator.Run*` API over an erroneous `ParseResult.Root` (Q-41).*
*C#-only by design.*

- At the source-level entry points (`KatLangEngine.Run`/`RunAsync` and everything built on them), any error diagnostic from source processing stops the program before evaluation. That covers lexing, parsing, load elaboration, loaded-module source and every elaboration pass.
- When such an error exists:
  - there is no evaluation, no host-operation call, no random draw, no budget charge and no evaluation-cancellation check;
  - the outcome is a `ParseFailure`, which exposes no root;
  - a front-end error inside a property or function that would never be demanded still rejects the whole program.
- **Deferred compilation units.** A load-bearing clause branch is one deferred compilation unit (MOD-10) and the one scheduled exception. Its written text is parsed with the program, so a parse error there blocks entry like any other. The rest of the unit is elaborated only when the branch is selected, and any front-end error found then stops that evaluation before the branch body runs (`EvalFailure`, MOD-11). A branch that is never selected cannot fail after parsing.
- Within every unit that is elaborated, no front-end error is exempt because the declaration it concerns is never demanded or because of where it is written, open targets included (MOD-06).
- **Recovery gives no meaning.** A lexical or syntactic error makes the parser build a recovery tree for diagnostics and editor analysis only. It is never run, neither to obtain more diagnostics nor to obtain a partial value. No recovery decision gives malformed text a meaning. The recovery decisions include:
  - reported characters standing in for a missing piece;
  - delimiter-ownership repairs;
  - separator stand-ins;
  - clause-head confinement.
- **Elaboration recovery gives no meaning either.** An elaboration pass that installs a recovery shape after a front-end error (for example the recovered signature of an invalid inferred signature) installs it only beside that reported error, so the shape never reaches evaluation.

**Qualifications**
- Evaluation-time failures of a front-end-clean program are governed by VAL-10 and RUN-07: the first demanded failure ends the run with no partial output, and undemanded code may contain failures.
- The evaluator's pre-evaluation gate. A static-validity violation that the front end misses reaches this gate. It is then reported as an `EvalFailure`, not a `ParseFailure`, but still before any evaluation: no host call and no step. For parsed source the gate meets only what the front end cannot judge. It never descends into a deferred region's placeholder, whose provisional body is judged when it materializes. This also qualifies PROP-02: an undemanded declaration can fail the run (VAL-05, RUN-07 (e)).
- Module acquisition is front-end processing, not evaluation. With a downloader configured, the loader still fetches and parses the modules of a source that already has a syntax error, so their diagnostics can be reported too.
- Missing modules, unavailable or refused, are a front-end error state (MOD-11).
- The low-level evaluator runs any AST. `Evaluator.Run*` evaluates a host-built AST as-is, and `Parser.Parse(src).Root` of an erroneous source is an elaborated recovery tree that will evaluate if handed to it. The host must check `ParseResult.HasErrors`.
- A bare `load` that no binding provides is the front-end error `UnboundLoadReference` (MOD-07), so it never reaches evaluation.
- Recovery shapes, diagnostic multiplicity and wording are not part of this law (SYN-14).

```katlang
trace(1), randomInt(0, 10)
X = 1 2
```
⇒ `UnseparatedSameLineItem`, with an empty host log: `trace(1)` never runs.

The same holds for an error in code that would never run:

```katlang
F(x) = { x = 1
x }
trace(5), tock()
```
⇒ `ParameterPropertyCollision`, with an empty host log.

Recovery is never evaluated: `A @= 1` / `A, tock()` is `UnexpectedCharacter`, and `X = { A = (1, 2]` / `Later = 5 }` / `X.Later, tock()` is `UnexpectedToken`, both with an empty host log.

### RUN-05 — Host operations are ordinary prelude members; each executed call invokes the host exactly once

*C#-only by design.*

- A configured host operation enters a program only as one ambient prelude property, a wrapper around its native call. Every language rule applies to it unchanged:
  - lookup, with the prelude outermost (RES-01, RES-06), so any nearer property or parameter with the same name shadows it completely;
  - arity (a wrong count is `ArityMismatch`);
  - use as a callback or loop step;
  - the zero-argument cache law: bare `op` is read once per run, while `op()` is fresh (PROP-04, PROP-06).
- After its arguments succeed and pass the host boundary, the wrapper invokes the delegate exactly once. Suspension never replays it. Its arguments are the ordinary bound parameter values: callback-bound values, never same-named ambient values.
- An argument is read whole where the operation is called, in argument order: every position of a list evaluated on demand is read, depth first, before the host is invoked, so the host never receives such a list, and a failure, limit or cancellation reached there is the call's. `trace([trace(1)].map{x + 1})` is `L[2]` after `[trace(1), trace(L[2])]`.
- An argument containing a call reference or argument view at any depth is refused with `TypeMismatch`, and the host is never invoked with it.
- A successful return enters the program as a canonical KatLang value, normalized and admitted before any consumer or the cache sees it. Every collection it contains, at any depth, must fit the per-collection limit by its immediate item count, and every string the per-string limit, or the run ends with that terminal resource failure (RUN-03). Admission is a size check, never a cumulative materialization charge.
- The public entry rethrows the original host exception. Inside the async evaluation boundary, the terminal marker carries it to that entry (RUN-03).
- Without a configuration, the same name is just an unresolved name and becomes an implicit parameter. A program references an operation whenever the operation's spelling occurs in it as a free name, even if the author meant an implicit parameter: the configuration then captures that name, and the program's meaning changes. Only a configuration whose names do not occur freely in the source is outcome-neutral.

**Qualifications**
- A host operation names no binding for publication, so `op()` never establishes the entry (PROP-06): `tock(), tock` is `S[1, 2]`.
- `A = tock` is a transparent reference to the operation (FWD-03). A bare `A` is the operation's own cached read, and `A()` is the operation's fresh call: `A = tock` / `A, A()` is `S[1, 2]`, and `A = tock` / `A(), A` is `S[1, 2]`. `A = tock()` is a property with its own entry: `A = tock()` / `A(), A` is `S[1, 1]`.
- Outcome neutrality of an unused configuration is pinned only for names that do not occur in the source. The same capture-by-spelling effect applies to every C#-only prelude member (Math aliases, `random`), which is why FORMAL-03's conservative extension holds only for elaborated core programs.
- A configured asynchronous operation routes even a program that never calls it through the async twin. That is accepted route variability (RUN-01 exception 2): it can turn the one success into a resource failure, never into another success.
- Host-returned values are the host's responsibility. They are outside seeded reproducibility, and KatLang cannot bound what the delegate allocates before returning. The cumulative materialization budgets count what evaluation constructs, so they never charge a return (Q-40, RUN-03).
- The async and sync restrictions are host routing, not language. Sync entry points reject async configurations with `InvalidOperationException` before evaluating, and async operations are awaited at one site.
- Operation naming rules (a valid identifier, not a reserved prelude name such as `tick`) are API policy.

```katlang
tock, tock(), tock, map([1, 2, 3], traceA)
```
⇒ `S[1, 2, 1, L[1, 2, 3]]`, with host log `[tock#1, tock#2, traceA(1), traceA(2), traceA(3)]`.

A nearer binding shadows an operation completely:

```katlang
F(tock) = tock + 1
G = { tock = 5
tock * 2 }
F(10), G, tock
```
⇒ `S[11, 10, 1]`, with host log `[tock#1]`.

`trace()` and `trace(1, 2)` are `ArityMismatch`. Capture by spelling: `F = tock + 1` / `F(5)` is `ArityMismatch`, because `tock` is the prelude operation and `F` has no parameter, while `F = tocks + 1` / `F(5)` is `6`, because `tocks` is an implicit parameter.

### RUN-06 — Presentation is not meaning: display settings change only rendered text

*C#-only by design.*

- Rendering a finished result never changes semantic values, Decimal128 representations (VAL-11), `.string` text (OP-14), program output cardinality, errors, effects, random draws or any other previously determined program behavior. This covers the decimal-places settings below and the output formatters.
- **Decimal places.** A run has two independent presentation settings: `MinDecimalPlaces`, the fewest digits shown after the decimal point, and `MaxDecimalPlaces`, the most. Each is one integer from 0 through 99.
  - Each setting has two origins. The program root's own property of that name is the source setting. A host-configured value (`RunOptions.MinDecimalPlaces` / `RunOptions.MaxDecimalPlaces`, the CLI's `--min-decimal-places` / `--max-decimal-places`, a host application's display setting) is the host setting.
  - Each setting composes only with its counterpart of the same name: an absent one imposes nothing, one present one is effective, and when both are present the effective value is their minimum. Neither origin overrides the other.
  - Neither setting supplies a value for the other. A setting that no origin sets stays absent: a minimum alone never rounds, and a maximum alone never pads. A fixed number of places is both settings at the same value.
  - Absence is structural. A host value of `null` ("off") is no host setting: never zero places, and never a reason to ignore the source setting. An explicit `0` from either origin is a real setting.
- **Consistency.** An effective minimum above the effective maximum is an error. It is never repaired by clamping, swapping or dropping a value, and it is reported where it arises:
  - CLI options inconsistent with each other are a usage error at command-line parsing, before the source is read;
  - a host pair inconsistent in `RunOptions` is a host argument exception where the run begins, before parsing or evaluation, never a source diagnostic;
  - a source pair inconsistent with itself is `IllegalInEval`, whatever the host settings are: a host setting never excuses an invalid source configuration;
  - an effective pair inconsistent only across origins is `IllegalInEval`.
  - Both `IllegalInEval` reports name the two values and the origin of each (the program or the host). They are positioned at the program's `MinDecimalPlaces` declaration when the minimum is the program's, otherwise at its `MaxDecimalPlaces` declaration.
- **Obtaining the source settings is evaluation; rendering is not.** The source settings are an engine-level host presentation convention, not core evaluator semantics.
  - After the program output has succeeded, `KatLangEngine` reads the root's own `MinDecimalPlaces` and then its `MaxDecimalPlaces`, each with the ordinary cached VALUE access, which is a zero-supply demand of that property, in the same run: same cache, budget, random stream, host operations and cancellation token (RUN-02). It does so whatever the host settings are, and whatever order the program declares the two in.
  - Those reads are themselves evaluation. They may consume steps and random state, perform effects, observe cancellation or fail. When the first read fails, the second is not attempted.
  - Both values are then validated, the minimum first. A failing read, or a value that is not one integer from 0 through 99, fails the engine run with that error even when a host setting is stricter; a value is never clamped. The source pair is checked before composition, and the effective pair after it.
  - Raw `Evaluator.Run*` performs neither read and neither check (RUN-01 exception 3).
  - The rendering step itself is inert.
- **The display rule.** With no setting from any origin, a number is displayed canonically, with its stored digits (`2.5000` shows `2.5000`). A non-finite value always keeps its canonical spelling. Otherwise the value is rounded to the maximum when one is present (midpoints away from zero), written with the fewest fractional digits that represent it exactly, and padded with zeros to the minimum. It has no decimal point when it has no fractional digits, and it keeps its sign, also for a zero and for a value that rounds to zero. So once any setting is present the text depends on the numeric value, never on its stored quantum: `MinDecimalPlaces = 0` and `MaxDecimalPlaces = 99` are not "no setting", and integers are padded.
- The host settings are host configuration: never evaluated, never injected as source, no binding, no step, no draw, no effect.

**Qualifications**
- `MinDecimalPlaces` and `MaxDecimalPlaces` are otherwise ordinary identifiers. A nested or opened one does not count, and reading one undeclared makes an implicit parameter. The engine's read of them is one of three spelling-selected behaviours (RES-06). No other spelling is a setting: a root `DisplayDecimals` is an ordinary property with no display effect.
- Only the engine evaluates them. `MaxDecimalPlaces = 1 / 0` / `5` is `DivisionByZero` on the engine, while the low-level evaluator returns 5. Likewise `MaxDecimalPlaces = 100` / `5`, `MinDecimalPlaces = 'a'` / `5` and `MinDecimalPlaces = 3` / `MaxDecimalPlaces = 1` / `5` are `IllegalInEval` on the engine only.
- The 0 to 99 range is a validity bound, never a clamp. The display text is presentation; `.string` text is OP-14's and reads no setting.
- Order: output rows; then, only if the output succeeded, the read of `MinDecimalPlaces` and then of `MaxDecimalPlaces`; then the validation of each value; then the source-pair check; then the composition with the host settings; then the effective-pair check; then rendering when the host asks. An output failure is never masked by a setting, and a setting failure follows the output's effects.
- Cache: each read is the ordinary cached zero-argument read. It reuses an entry established by an earlier read or by an owning successful zero-supply call such as `MaxDecimalPlaces()` (PROP-06). Explicit calls stay fresh and never replace an established entry.
- Scope: only the root's own declaration is a setting. Nested, opened, inline-opened, member, module, module-root and parameter declarations are ordinary bindings. A root declaration that is an alias reads its target (FWD-03). A declaration that cannot accept zero supplied arguments fails the run with its ordinary rejection: `MaxDecimalPlaces(x) = x` / `5` is `ArityMismatch`.
- The engine's bounded host-atom projection can fail a successfully evaluated run (Q-40, RUN-03): `L = range(1, 60000)` / `[L, L].count, [L, L]` is `CollectionSizeLimitExceeded` on the engine, while the low-level evaluator succeeds.

```katlang
MaxDecimalPlaces = 2
X = 1.555
X, X * 2 == 3.11
```
⇒ `S[1.555, true]`. The engine displays `1.56` and `true`: the comparison uses the unrounded value.

```katlang
MaxDecimalPlaces = trace(1)
A = trace(10)
A / 3, A
```
⇒ `S[3.333333333333333333333333333333333, 10]`, with host log `[trace(10), trace(1)]`, and the engine displays `3.3` and `10`. The output rows run first, and `MaxDecimalPlaces` is read afterwards. The low-level evaluator logs only `trace(10)`.

- `MinDecimalPlaces = 2` / `1.5, 10, 1.234567` displays `1.50`, `10.00` and `1.234567`: a minimum alone pads and never rounds. `MaxDecimalPlaces = 4` / `10, 1.234567, 2.5000` displays `10`, `1.2346` and `2.5`: a maximum alone rounds and never pads. With both set to 2, `1.234567, 10, 2.5000` displays `1.23`, `10.00` and `2.50`.
- `MaxDecimalPlaces = tick()` / `MinDecimalPlaces = tick()` / `tick()` displays `1.00`: the output takes the first tick, the minimum is read next (2) and the maximum last (3), whatever the declaration order.
- With `MaxDecimalPlaces = 7` / `1 / 3`, no host setting shows `0.3333333`, a host maximum of 5 shows `0.33333`, and a host maximum of 10 shows `0.3333333`.
- `MinDecimalPlaces = 4` / `5` run with a host maximum of 2 is `IllegalInEval`: the minimum is the program's and the maximum the host's.

### RUN-07 — A run yields its output or exactly one error: errors are not values, cannot be caught, and end the run; the outcome is the first RAISED failure in the evaluation order the rules fix

*Open: whether to unify the error category of an unresolved bare root name (Q-42): `A = x + 1` / `A` is `ArityMismatch`, while `A = x + 1` / `A + 0` is `UnresolvedImplicitParams`.*

- **(a) One value or one error.** Evaluating a demanded expression gives a value or fails with one error. No value kind represents an error, and no construct inspects, catches, defaults or retries one (VAL-10).
- **(b) Propagation.** A failure in a demanded subevaluation fails every enclosing evaluation up to the run, and later work is not started. This covers operators (OP-03), comparison chains (CMP-02), selection (SEQ-05), supply slots (SUP-01), user-call arguments (CALL-02), callback invocations (HO-02, COLL-04: the read that meets the failure invokes no later position), loop iterations (LOOP-03: later iterations do not run) and root rows (VAL-07: later rows are not evaluated, and no partial output is produced from the completed ones).
- **(c) No place defers a failure.** A supplied computation is evaluated only when demanded (NEED-01 to NEED-03), and a demanded failure is raised at once and propagates under (b). A list position is such a computation (SEQ-02). A demanded computation keeps its completed failure for any later demand of it, which reports the same failure and never re-derives it (CALL-06, NEED-02). A failed spread is raised during supply formation (SUP-02). A resource-limit failure is never deferred: wherever evaluation reaches it, it ends the run at once (RUN-03).
  - A failure's kind is rewritten at exactly one place: a spread reports its operand's own `MissingOutput` as `SpreadMissingOutput`, while a nested one keeps its kind (SUP-02). Context frames wrap an error without changing its kind.
  - Lookups that fail inside resolution (an argument with no algorithm channel, a receiver that is not a structural provider, the implicit-parameter promotion test) are resolution decisions, not failures of evaluated source.
- **(d) The error's category is part of meaning.** The observable category is FORMAL-06's granularity: the innermost error, with the arity family collapsed for Lean parity. Changing a category is a Lean and C# change. Wording, span and context frames are presentation for Lean parity. FORMAL-06 stays category-only, with selected shared structured fields compared separately. All of them must still agree across C# routes, as an implementation requirement (RUN-01).
- **(e) Static versus dynamic errors.** Static errors reject the program whether or not anything is demanded, with RUN-04's one scheduled exception for a load-bearing clause branch (MOD-10, MOD-11). The static errors are:
  - the RUN-04 front-end families, reported as `ParseFailure`: `DuplicateProperty` (PROP-01), `DuplicateBranchPattern`, `BranchArityMismatch` and `BranchOutputArityMismatch` (PAT-02, PAT-03), `ExplicitParametersRequireOutput` for written and inferred parameters (VAL-05), `ParameterPropertyCollision` (RES-05), `UnresolvedOpenTarget`, `OpenTargetIsParameter` and `IllegalInOpen` (MOD-03, MOD-04), `AmbiguousOpen` for a written name occurrence (RES-03) and `UndeclaredIdentifier` (PAR-04); and every other front-end error (RUN-04), among them `UnforwardableParameter` and `UnforwardableCallable` (FWD-02), `UnliftableClauseFamily` (PAR-07), `InvalidCollectingBinding` (VAR-02), `SingletonSequencePattern` (PAT-06), `SelfDependentInferredParameters` (PAR-08), `UnboundLoadReference` (MOD-07) and `StaticStructureLimitExceeded` (RUN-03);
  - the evaluator's pre-evaluation gate, reported as `EvalFailure` before any row: `ExplicitParametersRequireOutput` and branch-arity violations of host-built trees, and, as `IllegalInEval`, a singleton sequence pattern, more than one collecting capture per pattern level, a repeated name that includes a collector, a collecting clause-family binder (C#-only: Lean clause binders never collect), a misplaced `meta` parameter or a `meta` clause-family binder (Lean checks parameter lists only), an alias target that is neither a static path nor a runtime row, and an alias cycle. The gate never descends into a deferred region's provisional placeholder body, while an attached complete host-built parent scope is validated before evaluation;
  - the root `UnresolvedImplicitParams` check, which runs before any row (PAR-03).
- Every other evaluation-error kind is dynamic and is raised only when reached. `AmbiguousOpen` is also raised at run time for a lookup the front end cannot decide (a MAY-selected dot fallback, a host-built tree).
- **(f) The evaluation-error taxonomy.** An evaluation error names the first semantic contract the executed operation cannot satisfy, in that operation's ordinary evaluation order, never the helper that noticed the failure. One contract is reported alike on every route and in every spelling: written call, dot call, alias, forwarded parameter.
  - Missing CALLABLE capability is `NotAnAlgorithm` in every invoking position: a user higher-order parameter, a `map` transform, a `filter` predicate, a `reduce` reducer, a `while` or `repeat` step, and an invoking slot reached through a builtin used as a step. CALLABLE projection raises it only when an invocation is required, never by demanding VALUE (NEED-06), and an unused invoking slot is never projected. A slot that has callable identity keeps its callable's binder and dispatch verdicts, and there is no value-to-thunk fallback.
  - A present VALUE of the wrong kind is `TypeMismatch`: every non-number operand of unary `-`, a Math argument, a selector, a `range` bound, a `repeat`, `take` or `skip` count that is not a number, a non-numeric element of `sum`, `avg`, `min`, `max`, `order` or `orderDesc`, every Boolean position, and a structural pattern given the other kind.
  - Supply or output cardinality is `ArityMismatch`: a call or builtin given the wrong number of arguments, a right-kind structural pattern of the wrong length, a `while` step that emits no slot, a zero-parameter callable given an item, and a zero-argument VALUE demand of a callable that requires arguments, in every spelling, a named or inline alias included. A `map` transform or `reduce` step returning `()` or several rows is no cardinality failure (HO-03).
  - A selection naming no position is `BadIndex`, `first` and `last` of an empty collection included.
  - A zero divisor is `DivisionByZero`.
  - Any other domain failure of a valid-kind value is `IllegalInEval`: a non-whole count or bound, a negative `repeat` count, an invalid random interval (RAND-03), `0 ^ -1`, an empty `min`, `max` or `avg`.
  - No matching family clause is `NoMatchingBranch` (PAT-02).
  - An algorithm read as a value without output is `MissingOutput` (VAL-05).
  - A cyclic active dependency is `DemandCycle` (NEED-09). Fresh recursion is not a cycle and obeys ordinary limits.
  - NEED-04's repeated-name categories are that binder rule's own.
- **(g) A run hands out only concrete values.** A list evaluated on demand exists only inside its run (SEQ-02). The run assembles its output row by row (VAL-07) and then reads it whole, left to right and depth first, while the run is still active. A named top-level property that the engine reads after the output (the root's `MinDecimalPlaces` and `MaxDecimalPlaces`, RUN-06) is read whole as it is read, and a host-operation argument where the operation is called (RUN-05). A failure, a resource limit or a cancellation reached in such a read is the run's outcome: `[1, 1 / 0]` is `DivisionByZero`, and `L = [tick()]` / `L, tick()` is `S[L[2], 1]`. The run-result boundary then refuses a call reference or argument view anywhere in the materialized value (CR-6, CR-12). Formatting receives the finished result (RUN-06).

**Qualifications**
- Which of several possible failures is reported is decided by each construct's own order: supplied arguments in the order they are first demanded (CALL-02), cardinality before any VALUE demand for every callee (CALL-03), written-order pattern inspection after the cardinality check (PAT-10), comparison chains (CMP-02).
- Host exceptions and host cancellation are not KatLang errors. They propagate to the host (RUN-05, RUN-03).
- Whether and which resource-limit error fires is route-dependent (RUN-01 exception 2).
- A demanded computation's completion is final, and only demanded work can fail. A failed property evaluation is never stored in the property cache (PROP-09), a separate memo domain from the cell's completed outcome (NEED-10). Since the failure ends the run, neither is read again.
- The category rule does not settle every assignment. The doubtful choices stay open with their owners (Q-42).

```katlang
A = trace(1) / 0
Ok = trace(2)
if(false, A, Ok), trace(3), 1 / 0, trace(4)
```
⇒ `DivisionByZero`, with host log `[trace(2), trace(3)]`: the undemanded failure is harmless, the demanded one is not, the completed rows are discarded and the last row never runs.

Later work never starts: `map([1, 2, 3], {trace(x) / (x - 2)})` is `DivisionByZero` with host log `[trace(1), trace(2)]`, and `S(x) = x + 1 + 0 * (1 / (2 - trace(x)))` / `repeat(S(0), 5), trace(9)` is `DivisionByZero` with host log `[trace(0), trace(1.0), trace(2.0)]`.

Demand order decides the failure: `F(a, b) = a` / `F(1 / trace(0), trace(2))` is `DivisionByZero` with host log `[trace(0)]`, `count(1 / trace(0), trace(2))` is `ArityMismatch` with an empty host log, and `P(x, x, (a, b)) = a` / `P(1, 2, 1 / 0)` is `ArityMismatch` with the division never run.

A completed outcome is final: `Twice(x) = x + trace(x)` / `Twice(trace(1) / 0)` is `DivisionByZero` with one `trace(1)`.

Static checks precede every row: `trace(1)` / `F = { a, b = x, 1 }` / `trace(2)` is `ExplicitParametersRequireOutput` with an empty host log, although `F` is never demanded. `trace(1), x + 1` is `UnresolvedImplicitParams` with an empty host log, while `trace(1), {z}` reaches the same error after `trace(1)`, at the block's value demand.

The taxonomy, one witness each: `map([1, 2], 1 / 0)` is `NotAnAlgorithm`, with the division never evaluated; `[1, 2]['x']` is `TypeMismatch`; `Add(x, y) = x + y` / `Add((1, 2))` is `ArityMismatch`; `first(())` is `BadIndex`; `5 mod (1 - 1)` is `DivisionByZero`; `0 ^ -1` is `IllegalInEval`; `F(0) = 1` / `F(2)` is `NoMatchingBranch`; `X = { Y = 1 }` / `X` is `MissingOutput`; `A = B.Algorithm` / `B = A` / `A` is `DemandCycle`.

### RUN-08 — Evaluation is strict except at a closed set of demand points, and "exactly once" has enumerated exceptions

- A demanded expression evaluates its subexpressions eagerly, in the orders fixed by OP-03, BOOL-04, CMP-02, SEQ-05 and the consuming construct, except at the demand points below. A supplied call argument is not such a subexpression: it is a computation of the caller that runs only when demanded (CALL-02). Neither is an ordinary list element: it is a position that runs only when read (SEQ-02).
- Written code may go unevaluated only at these points, and nowhere else:
  - a supplied argument computation of any call (a user callee, a clause family, a builtin, a Math, random or host wrapper, a dot-call receiver), until its VALUE is first demanded; one never demanded is never evaluated (CALL-02, CALL-03, CALL-06, NEED-01, NEED-03). Binding it to a plain parameter, transporting or forwarding it, collecting it, re-spreading a known collector slice, transporting it through an argument-view spread, capturing it as a `meta` parameter's call reference and projecting its callable identity evaluate nothing. A runtime projection (a reference's `.Algorithm` link, or navigation through a parameter whose cell is a runtime projection) may demand the VALUE of other cells on its callee route, never the projected cell's own (NEED-01, NEED-06, NEED-07, NEED-08);
  - a property body, until it is demanded; a cache hit re-runs nothing (PROP-02, PROP-04);
  - a deconstruction right-hand side, until one of its targets is demanded (VAR-06);
  - the unselected branch of builtin `if` (BOOL-05);
  - the right operand of an `and` whose left operand is `false`, and of an `or` whose left operand is `true` (BOOL-04);
  - a list position that no consumer reads: an ordinary element of a list literal, a `map` position, a `filter` candidate beyond the scan's frontier, and a position outside a `take` prefix (SEQ-02, COLL-04);
  - a `reduce` step that no later step demands, together with the `initial` behind it (HO-02);
  - builtin slots after an earlier failure in that builtin's required order of demands and validations (CALL-03, COLL-02);
  - invoking slots, which are never value-demanded: a callback is invoked only for the positions, candidates and fold steps a consumer demands (HO-02, HO-04), and a loop step once per iteration (LOOP-05, LOOP-06, LOOP-08); supplying one evaluates nothing, so an unused callback has no effect;
  - the step of a zero-count `repeat` (LOOP-05);
  - the earlier transition rows of a condition-first `while` round whose discovered flag is false (LOOP-06). Discovery still reads rows right to left to find the last effective item, so trailing empty rows and dependencies needed by the flag may run;
  - the ordinary selectors of a postfix selection after its first failure: once the receiver is in hand, each ordinary selector is a supplied computation demanded only when the selection reaches it, left to right, so the selection stops at its first failure (SEQ-05);
  - unselected clause bodies (PAT-02), and the arguments a clause family's patterns do not inspect (NEED-04);
  - deferred module branches, whose modules are fetched and elaborated only when selected (MOD-10);
  - `open` providers, which opening neither activates nor evaluates (MOD-04);
  - structural dot navigation, which evaluates nothing (DOT-02);
  - the receiver of the `.string` intrinsic (and, on the same template, of the call-reference intrinsics `Invoke` and `Arguments`, whose argument-list check precedes the receiver demand), which is demanded only once its written argument list, if any, has formed a supply of zero items. A supply of one or more items is rejected with `ArityMismatch` before the receiver or any non-spread argument is demanded (DOT-08, NEED-05). The call-reference intrinsics refuse their argument form before demanding the receiver too: bare `R.Invoke` is `IllegalInEval`, `R.Invoke(args)` forms its list like `.string` and rejects one or more items with `ArityMismatch`, and any argument list on `R.Arguments`, `R.Arguments()` included, is `IllegalInEval` with nothing formed.
- No other place leaves a failure unraised. A computation is either never evaluated (above) or, once demanded, raises its failure at once, keeps it for any later demand without re-evaluating, and ends the run (VAL-10, RUN-07 (c), CALL-06, NEED-02). A reached resource-limit failure ends the run; its terminal completion cannot restart work or be recovered as an argument value (RUN-03, NEED-09).
- Everything else is strict:
  - both operands of every binary arithmetic operator and of `xor`, the operand of unary minus, and the left operand of `and` and `or` (OP-03, BOOL-04);
  - every comparison operand, eagerly past a `false` link (CMP-02);
  - capture and row slots (SUP-01, SUP-06, VAL-07), and the spread slots of a list literal, formed when it is built (SEQ-02);
  - an arbitrary explicit spread in every call and every selector list (SEQ-05), the `.string` intrinsic's written argument list included (DOT-08): its operand is evaluated while the supply is formed, and its failure is raised there, before any arity check or binding (SUP-02, CALL-02, CALL-03, NEED-07);
  - inspecting patterns: a literal and a structural pattern demand their argument when visited (PAT-07), a list pattern reading its kind and cardinality and a field only when it inspects one (NEED-04), and the occurrences of a repeated name are inspected as NEED-04 states (PAT-09);
  - a collector's VALUE, which demands every collected computation, left to right (VAR-03, NEED-07);
  - the positions of a collection bound by any collection builtin other than `count`, `first`, `last`, `take`, `map` and `filter`, which the builtin reads in order when it binds the collection, `reduce` before any step (COLL-04, HO-02);
  - the whole-value reads: equality, `contains`, `distinct`, a repeated name's agreement and `atoms` (CMP-03, COLL-07, COLL-10, NEED-04), the run's output, the engine's named top-level reads, and a host-operation argument (RUN-07, RUN-05).
- No optimizer, route or future builtin may add a deferral point or evaluate a computation that was not demanded: either would be a language change, not an optimization (RUN-01, NEED-03).
- "Each evaluated subexpression is evaluated once per evaluation of its parent" has exactly these exceptions:
  - an explicit call: `A()`, `f()` on a parameter, `R.Invoke()`, which executes the captured call afresh over the same memoized argument cells, and `R.Algorithm(args)`, a fresh ordinary call of the captured callee with exactly `args`. Each of these is fresh (PROP-06, NEED-06). The one call that is not is a zero-supply call through a runtime alias whose target has no callable identity: it answers with the alias's binding-cell VALUE and never reruns the row (FWD-04);
  - one callback invocation per newly computed mapped position, newly inspected filter candidate or demanded fold step, and one loop-step invocation per iteration.
- A written call argument is no such exception: within one call a slot is evaluated at most once, and reading its parameter never evaluates it again (CALL-06). Nor is a list position: it is evaluated at most once per list instance (SEQ-02).
- A failed property and a failed deconstruction right-hand side are never cached (PROP-09, VAR-06). Since a demanded failure ends the run, neither is read again in that run.

**Qualifications**
- Invoking a callable is not a value demand: an invoking slot receives the algorithm and calls it per position, candidate, step or iteration. Whether a bare name in a VALUE slot is read through the cache is PROP-05's rule.
- An arbitrary spread slot of any call is evaluated, and the level it opens read, while the supply is formed, before the arity check: in `if(true, Risky*)`, `Risky` is evaluated before the condition is demanded.
- PROP-02 names some of these points. This rule is the complete list and supersedes it.
- Static validation is not evaluation: static errors in undemanded code still reject the program (NEED-05, RUN-07 (e)).
- Supplied arguments run in the order they are first demanded, after every call's spread-first formation (CALL-02, CALL-03, NEED-03).

```katlang
Bad = trace(1) / 0
Unused = trace(2)
F(x, y) = x
S(x) = trace(x)
F(3, trace(4)), if(true, 5, trace(6)), repeat(S(7), 0)
```
⇒ `S[3, 5, 7]`, with an empty host log. `Bad` and `Unused` never run, nor do the unread argument, the unselected branch and the zero-count step.

The later demand points, each pinned on its own: `false and tick() == 1, true or tick() == 1, tick()` is `S[false, true, 1]` (BOOL-04); `[trace(1), trace(2)].first` is `1` after `[trace(1)]`, and `[1, 2, 3].map{trace(x)}.last` is `3` after `[trace(3)]` (SEQ-02, COLL-04); `Pick(item, acc) = item` / `reduce([1, 2], Pick, 1 / 0)` is `2` (HO-02).

```katlang
Bad = trace(1) / 0
I(f) = 0
A = trace(2)
I(Bad), I(Bad), A, A, A()
```
⇒ `S[0, 0, 2, 2, 2]`, with host log `[trace(2), trace(2)]`. Neither call demands `Bad`, and the successful `A` runs once for both bare reads and once more for `A()`.

Further points, each with the host log shown:
- `Bad = trace(1) / 0` / `F(v) = v` / `F(Bad)` is `DivisionByZero` with `[trace(1)]`: reading `v` demands the slot once.
- `p, q = trace(1), trace(2)` / `p` is `1` with `[trace(1), trace(2)]`: demanding a target evaluates the whole right-hand side, while a list right-hand side keeps its positions: `a, b = [trace(1), 1 / 0]` / `a` is `1` with `[trace(1)]` (VAR-05).
- `p, q = trace(1) / 0, 2` / `q` is `DivisionByZero` with `[trace(1)]`.
- `F(x, y) = y, x` / `F(trace(randomInt(0, 1000)), randomInt(0, 1000))` is `S[699, 292]` with `[trace(292)]`: `y` is demanded first and draws first.
- `open M` / `M = { public A = trace(1)` / `public B = 2 }` / `B` is `2` with an empty log.
- `3 < 2 < trace(1), 3 < trace(2)` is `S[false, false]` with both traces.
- `(trace(1)).string(2)` is `ArityMismatch` with an empty log.
- `Ign(x) = 0` / `G(z) = Ign(Undeclared)` / `G(1)` is `UndeclaredIdentifier`, `F(q) = q` / `A(p) = F` / `5` is `UnforwardableParameter`, and `Ign(x) = 0` / `Ign({ X = 1` / `X = 2` / `3 })` is `DuplicateProperty`, all before anything runs.

### RUN-09 — `tick()` counts actual executions: one counter per run, advanced only when the primitive executes

- `tick` is an ordinary zero-arity prelude builtin. A nearer binding named `tick` shadows it completely (RES-06). It adds no syntax, value kind or cache of its own.
- Each run owns one counter that starts at zero (RUN-02). Every actual execution of the primitive advances it by exactly one and returns the new value as one number with emitted count 1. Nested calls, callbacks, aliases, call references and every evaluation context of the run share it. A separately started run has its own.
- The counter advances only when dispatch reaches the primitive, after the route's ordinary arity, step, depth, cancellation and terminal-state checks. Parsing, elaboration, static structure resolution, callable identity inspection, editor analysis and optimization never execute it. No optimizer folds, merges, hoists, removes or duplicates a demanded `tick()`.
- There is no reset, read, naming, timestamp or configuration API. The counter is independent of steps, depth, item and string budgets, property-cache statistics, time and the random stream. It resets only by starting a new run. A later failure rolls nothing back.
- `tick()` is the only executing form, and it accepts exactly zero effective supplied arguments. A surplus argument is the ordinary `ArityMismatch` before any argument is demanded (`tick(1 / 0)`). An explicit spread is formed first (CALL-03), so `tick(trace(5)*)` traces and then rejects. An extension call supplies its receiver, so `5.tick` is `tick(5)`.
- A bare `tick` is the builtin's CALLABLE identity. Obtaining or transporting it executes nothing: `T = tick` and `Apply(tick)` run no primitive until a call does.
- A bare VALUE demand of `tick` is `IllegalInEval`, invocation required, never an arity report. A bare `tick` is never lifted, because its signature requires nothing (PAR-07), so the refusal is a runtime demand in every value position, through an alias too.
- The largest value is 2^63 − 1. At that limit a call fails with `IllegalInEval` and the counter does not move: it never wraps, rounds or saturates into a duplicate value. This is a domain failure, not a resource limit.
- `tick` composes with the existing CALL, VALUE and cell machinery. An undemanded argument and an unselected branch run nothing, one supplied `tick()` demanded twice runs once (NEED-02), `A = tick()` is an ordinary property (PROP-04, PROP-06), aliases and carriers keep their targets' behavior (FWD-03), and `R.Invoke()` is a fresh execution of the captured call.

**Qualifications**
- `tick` is a reserved prelude name: a host operation cannot take it (RUN-05). Host counters use another name.
- In C#, concurrent demands of one run, if any, still return distinct values. No new ordering guarantee is introduced for them.
- The Lean laws are serial. C# routes, suspension and cancellation rest on C# evidence.

```katlang
A = tick()
A(), A, A(), A
```
⇒ `S[1, 1, 2, 1]`: declaring `A` ticks nothing, the first `A()` establishes the entry, and the second is a fresh execution that leaves the entry alone.

Sharing and freshness: `A = tick()` / `A + A` is `2`, `A = tick()` / `A() + A()` is `3`, and `A = tick()` / `A, A(), A` is `S[1, 2, 1]`. One cell runs once: `Twice(x) = x + x` / `Twice(tick())` is `2`. Nothing undemanded runs: `Ign(x) = 0` / `Ign(tick()), if(false, tick(), 0), tick()` is `S[0, 0, 1]`.

Forms: `tick` is `IllegalInEval`; `T = tick` / `T(), T()` is `S[1, 2]`; `tick(1 / 0)` is `ArityMismatch`; `5.tick` is `ArityMismatch`; `F(tick) = tick` / `F(7)` is `7`.

### RAND-01 — One run-scoped random stream, consumed exactly where evaluation executes a random call

*C#-only by design.*

- `random`/`Math.Random` and `randomInt`/`Math.RandomInt`, in every spelling, draw from one mutable stream owned by the run (RUN-02). It is never static, never on configuration objects, and never duplicated or reset by nested calls, callbacks, loops, suspension, or the engine's `MinDecimalPlaces` and `MaxDecimalPlaces` reads.
- Which random calls execute, and in what order, is decided entirely by the ordinary evaluation rules:
  - supply formation, which evaluates a call's explicit spreads first, and then the order in which supplied arguments are first demanded, for every callee alike; an argument nothing demands never draws (CALL-02, CALL-03, NEED-03, NEED-07);
  - the strictness law and its demand points (RUN-08), including lazy `if` branches (BOOL-05), the skipped right operand of `and` and `or` (BOOL-04), unread list positions (SEQ-02) and undemanded `reduce` steps (HO-02);
  - the zero-argument property cache: a cache hit draws nothing, while `R()` draws afresh (PROP-04, PROP-06);
  - the order in which list positions, `filter` candidates and `reduce` accumulators are demanded (COLL-04, HO-02), and loop iteration order;
  - output rows before the read of `MinDecimalPlaces`, and that read before the read of `MaxDecimalPlaces` (RUN-06).
- Every execution route that completes without a resource-limit failure (RUN-01) must therefore consume the same draws in the same order. A route stopped by a limit may have executed only an initial part of that draw sequence. Optimizers are never disabled because a seed is present.
- A resource limit can end a run before later draws occur, but it never changes which draws a successful run makes: a limit the run reaches is terminal, so it is never absorbed into a success that consumed a different part of the stream (RUN-03). Where a limit fires may still depend on the route (RUN-01 exception 2).

**Qualifications**
- Draw order follows evaluation order, which is not always written order. Every callee forms its supply the same way, and a demanded failing argument never draws again when its parameter is read (CALL-06): the slot's one evaluation consumed its draws, and every read reuses its outcome.
- One module, one draw: with one canonical URL `r`, `A = load(r)` / `C = { public B = load(r) }` / `A.R, C.B.R` reads one module binding and makes one draw (MOD-09).

```katlang
R = randomInt(0, 1000)
S(x) = x + randomInt(0, 10), x < 20
P(x) = randomInt(0, 2) == 1
R, R, R(), S(0).while, count(filter(range(1, 8), P)), if(false, R(), randomInt(0, 1000))
```
⇒ `S[699, 699, 292, 22, 6, 19]` on every route. Replacing the `if` row with a bare `randomInt(0, 1000)` still ends in `19`: the unselected `R()` drew nothing.

An empty entry is established by a zero-supply call: `R = randomInt(0, 1000)` / `R(), R, R(), R` is `S[699, 699, 292, 699]`.

Draw order, with the first two words `699` and `292`:
- `if(randomInt(0, 1000) >= 0, randomInt(0, 1000)*, 0)` is `699`: the spread slot draws first, at supply formation, and the condition draws next.
- `F(c, a, b) = if(c, a, b)` / `F(randomInt(0, 1000) >= 0, randomInt(0, 1000)*, 0)` is `699`, and without the spread `F(c, a, b) = if(c, a, b)` / `F(randomInt(0, 1000) >= 0, randomInt(0, 1000), 0)` is `292`: `c` is demanded first.
- `F(x, y) = y * 10000 + x` / `F(randomInt(0, 1000), randomInt(0, 1000))` is `6990292`: `y` draws first.
- `Ignore(x) = 0` / `Ignore(randomInt(0, 1000)), randomInt(0, 1000)` is `S[0, 699]`: the unused argument draws nothing.
- `F(x) = x + x` / `F({1 / (trace(randomInt(0, 2)) - 1)})` is `DivisionByZero` with host log `[trace(1)]`: the one evaluation made one draw, and its failure is final.

### RAND-02 — A seed is host configuration: it reproduces the stream, never memoizes, and has no source syntax

*C#-only by design.*

- The only ways to seed a run are host configuration: `RunOptions.RandomSeed`, the `Evaluator.Run*` `randomSeed` overloads, and CLI `--random-seed`.
- A seed names a stream. Every `long` is valid, and distinct seeds are distinct streams. For a given KatLang version the same program, seed and executed path must produce the same values on every platform.
- A seed never decides which calls execute (RAND-01) and never memoizes results. A second call draws the next word, and removing an earlier random call generally changes every later value.
- There is no seeding syntax. A source property named `RandomSeed` is an ordinary property that seeds nothing.
- An unseeded run is nondeterministic: it takes its entropy once at run start. Parsing ignores the seed.
- The exact stream is not promised across KatLang versions.
- A limit never shifts the stream of a successful run. A limit the run reaches ends it (RUN-03), so a seeded run that succeeds made exactly the draws of the same run under no limit. Whether and where a limit stops a run is not part of this guarantee (RUN-03, RUN-01 exception 2).

**Qualifications**
- Stream positions do not depend on how an argument is spelled or how often a callee reads its parameter (CALL-06).
- Host-operation results are outside the guarantee.
- The stream is not cryptographically secure. The generator and its constants, composition and entropy source are internal contract, not language.

`randomInt(0, 1000), randomInt(0, 1000)` is `S[699, 292]`: the second call draws the next word. `RandomSeed = 7` / `randomInt(0, 1000), randomInt(0, 1000)` is `S[699, 292]` too: the declared property seeds nothing. A different host seed gives a different, equally reproducible stream.

```katlang
Pair(x) = x, x
Pair(randomInt(0, 1000)), Pair({ randomInt(0, 1000) })
```
⇒ `S[S[699, 699], S[292, 292]]`: each spelling draws one word, however often the callee reads its parameter.

### RAND-03 — `random`/`randomInt` draw uniformly from a half-open interval, and validation precedes every draw

*C#-only by design.*

- The two random operations are two-argument calls. There is no zero-argument random member.
- `random(start, end)` / `Math.Random` draws a unit fraction `u` uniformly from the lattice `{k·10^-34 | 0 ≤ k < 10^34}` and returns `start + u·(end − start)` in Decimal128 arithmetic. A result that rounds up to `end` folds back to `start`, so every result lies in `[start, end)`. Both bounds must be finite, `start < end`, and the range must be finite.
- `randomInt(start, end)` / `Math.RandomInt` returns a uniform whole number in `[start, end)`. The bounds must be whole numbers with `start < end`.
- A call with invalid bounds fails with `IllegalInEval` before consuming any word of the stream. Every valid call consumes at least one word, even when its interval has one member.
- The lowercase alias and the canonical `Math.` member are the same operation on the same stream (OP-11).

**Qualifications**
- `Math.Rand`, the removed zero-argument form, is just an unresolved member (`Math.Rand` is `UnresolvedImplicitParams`). A random value that is read repeatedly is spelled as a user property `R = random(0, 1)`, which the cache makes one draw per run (RAND-01).
- The `|bound| ≤ 1e34` restriction for `randomInt` (`randomInt(0, 1e35)` is `IllegalInEval`) is a representability limit of Decimal128 integers. It is policy, not a law of the interval.
- The sampling algorithms are internal.
- Random calls are Math-wrapper user callables (C#-only prelude wrappers, not Lean builtins). When the native runs, it demands its arguments in parameter order and checks each before demanding the next (CALL-03): `randomInt('a', 1/0)` is `TypeMismatch` and the division never runs, and `randomInt(trace('a'), trace(1))` is `TypeMismatch` with host log `[trace('a')]`.

`F(x, y) = y` / `F({randomInt(5, 1)}, randomInt(0, 1000))` is `699`, like `F(x, y) = y` / `F({1}, randomInt(0, 1000))`: `x` is never demanded, so the invalid call never executes (NEED-03). `F(x, y) = y` / `F({randomInt(0, 5)}, randomInt(0, 1000))` is `699` too: the valid call is never demanded either. When the callee demands `x` first, `G(x, y) = x * 0 + y` / `G({randomInt(0, 5)}, randomInt(0, 1000))` is `292`, because `randomInt(0, 5)` drew the first word, and `G(x, y) = x * 0 + y` / `G({randomInt(5, 1)}, randomInt(0, 1000))` is `IllegalInEval`, which ends the run.

`randomInt(5, 1)`, `randomInt(1.5, 3)` and `random(1, 1)` are `IllegalInEval`.

```katlang
randomInt(0, 1), randomInt(-3, -2), Math.RandomInt(0, 1000), randomInt(0, 1000)
```
⇒ `S[0, -3, 62, 708]`: the one-member intervals still consumed the two words `699` and `292` would have used.

## FORMAL — Lean/C# correspondence: authority, model coverage, and what is proved

KatLang has two implementations of one meaning. The Lean model `lean/KatLang.lean` is the normative semantics of the constructs it models. The C# implementation in `dotnet/src/KatLang/` adds what the model deliberately leaves out. This family states which side decides what, the observation on which they must agree, how strong the evidence for that agreement is, and the domain of trees over which every law here is stated. The per-construct laws are owned by the other families.

### FORMAL-01 — `lean/KatLang.lean` is the normative semantics of every construct it models

- For every construct the Lean model represents (FORMAL-02), the meaning of a program is what `lean/KatLang.lean` computes on its elaborated core AST. That meaning is the observation of FORMAL-06, and the C# implementation must produce the same observation.
- If the two disagree, the Lean model decides, unless the model itself is changed first and explicitly. If Lean is silent or ambiguous about a behavior, that behavior is undecided and must be clarified before C# fixes it.
- An observable change to a modeled construct is made in Lean and C# together.
- Every other artifact is subordinate: `CoreArityAlgebra.lean`, the prose documents, `AGENTS.md` and the tutorial. When one of them disagrees with `KatLang.lean`, the artifact is wrong.

**Qualifications**
- Authority covers the modeled fragment only. C#-only constructs are normative through the hand-written expectations in [the canonical conformance corpus](../../conformance/features/) and through the design rules in `docs/design/language-rules/`, never through tutorial prose (FORMAL-03, FORMAL-04).
- Lean exercises its authority over the tree the C# front end produces, which is the source-reachable elaborated core (FORMAL-08). Front-end decisions are not checked by the Lean evaluator (FORMAL-02).
- Agreement is checked executably on bounded corpora, not proved (FORMAL-07). The corpora differ in what their guards mean. A `LanguageSpecCases` guard pins a hand-written expectation, so it checks both engines against intent. A `SemanticExplorerCases` guard pins an observation recorded from C#, so it checks agreement, not intent, and a change applied to both engines is re-pinned silently. A `SemanticGeneratedCases` guard checks Lean on each included SEM-2B case's identity-prelude members (the base, `alpha-rename` and, when present, `declaration-reorder` sources with `trace(x) = x` and `wait(x) = x` prepended) against the generator's constructed expectation, each transformation member also against the base member's observation; the host-operation programs, host events, async and optimizer paths stay C# evidence. A `FrontEndDecisionCases` guard pins a DECISION recorded from the C# front end (an owner selection, a parameter-or-resolve verdict, an open head, a family lifting signature, a slot role) against a Lean specification function, so it checks agreement on that decision, not evaluation and not intent. *(Added 2026-11-15, front-end decision differential.)*

### FORMAL-02 — Lean models the elaborated core; surface syntax and front-end elaboration are C#-only, and both sides run the same elaborated program

- The Lean model's domain is the post-elaboration core:
  - the 18 `Expr` constructors, `sequenceConstruct` being internal only;
  - six value kinds: `Int` atom, string, Boolean, sequence, list, and the call reference with its argument-view facet;
  - four algorithm kinds: user, conditional (clause family), builtin, and alias, a transparent reference or a structural forwarding carrier (FWD-03);
  - the 22 prelude builtins;
  - parameter and branch patterns, and the semantic error kinds;
  - run state: need cells with their invocation plans, routes and canonical callee and receiver cells, the zero-argument property cache and its active owners, runtime-alias binding cells, binding-context and lexical-activation identities, and declaration identities. A list position evaluated on demand is a need cell (`Result.deferred`), and a `filter` result is a list whose positions are discovered through verdict cells (`Result.pendingList`); neither is a seventh value kind.
- Strings are modeled: exact equality only, no ordering or arithmetic, string literal patterns, and `.string` on canonical integer atoms. The string spelling and the rejection of a double quote are C#-only surface syntax (SYN-15): Lean has no lexer.
- C#-only: lexing, parsing, layout, redundant-grouping erasure, recovery, and the front-end passes (implicit-parameter inference and its order, signature selection, Grace, forwarding and lifting, exposure classification, clause grouping, deconstruction lowering, load elaboration, every static diagnostic). Lean evaluates their output.
- The Lean program of every differential case is derived mechanically from the C#-elaborated AST. It is never hand-authored, and derivation fails loudly on anything the model does not represent. A Lean/C# comparison therefore always runs the same program on both sides. A surface law (SYN) is pinned only as C# behavior plus the core AST it elaborates to.

**Qualifications**
- Lean holds partial models of some front-end decisions: owner selection and open-head elaboration, clause grouping, formula lifting and forwarding specifications, and signature validity. Descriptive load prose with structural predicates exists, without a complete executable load elaborator. `KatLangArityLaws/SignatureCompletion*.lean` is a separate reference kernel of signature selection (FORMAL-07). The derived EVALUATION corpora bypass all of these, because they encode C#'s tree. Conformance checks exist for the owner walk (`OwnershipConformanceTests`), on a finite corpus for the signature selector (`SignatureCompletionBridgeTests`), and — on the parser-accepted programs of the explorer and LanguageSpec corpora — for owner selection, the parameter-or-resolve verdict, open-head elaboration, clause-family lifting signatures and the lifting role table (`FrontEndDecisionCases`, generated by `FrontEndDecisionLeanArtifactTests`; formal-correspondence ledger FD-1..FD-5). *(Front-end decision differential, 2026-11-15; formerly "Conformance checks exist only for the owner walk … and … the signature selector".)* Implicit-parameter promotion, clause grouping, forwarding sources, alias formation and exposure classification have no such check.
- Some errors C# reports statically are also checked by Lean:
  - Before evaluation, with the same whole-program verdict: `explicitParamsRequireOutput`, `branchArityMismatch`, `branchOutputArityMismatch`, and the `illegalInEval` refusals of a singleton sequence pattern, more than one collector at a pattern level, a repeated name that includes a collector, a misplaced `meta` parameter, and an alias target that is neither a static path nor a runtime row, or that closes a cycle. C#'s refusal of a collecting or `meta` clause-family binder has no Lean counterpart, because Lean clause binders carry no kind.
  - Only when the construct is evaluated: `duplicateProperty`, `duplicateBranchPattern`, `badOpenForm`, `illegalInOpen`, and `OpenTargetIsParameter` as a run-time `badOpenForm`. For an algorithm never evaluated the C# front end is strictly stronger, and such programs are parse-level, outside the correspondence.
- A front-end mistake that yields a well-formed but wrong core tree is accepted by both evaluators. Only hand-written canonical expectations, the ownership table or — for the decisions the front-end decision differential covers (ledger FD-1..FD-5) — a `FrontEndDecisionCases` guard can catch it. *(Front-end decision differential, 2026-11-15; formerly "Only hand-written canonical expectations or the ownership table can catch it".)*
- C# has two `Expr` variants Lean lacks: `Grace`, stripped by elaboration, and `NativeCall`, the body of Math and host wrappers (FORMAL-03). The encoder refuses both.

### FORMAL-03 — Everything outside the Lean model is C#-only by design and must extend the modeled core conservatively

*C#-only by design.*

- These have no Lean counterpart by design:
  - Language-visible surface: the `Math` module, its native bodies and lowercase prelude aliases; `random`/`randomInt` and the seeded stream; public host operations; `MinDecimalPlaces`, `MaxDecimalPlaces` and all output formatting; the Decimal128 numeric tier (FORMAL-04), including the `.string` text of every number that is not a canonical integer.
  - Execution and tooling machinery: optimized loops and fused pipelines; the async twin; budgets, limits, stack protection and cancellation; module transport, admission, deferred loading and missing-module analysis; diagnostic codes, wording, spans and context frames; editor semantics and the public API.
- Every such construct enters the language only through Lean-modeled mechanisms: an ordinary prelude or root binding that is resolved, shadowed, bound, cached and demanded by the modeled rules. It must not change the meaning (value, structure, emitted count, semantic error kind) of any ELABORATED core program made of modeled constructs.
- For the C#-only execution strategies, the generic synchronous C# evaluator is the executable oracle, and that evaluator is itself checked against Lean (RUN-01).
- When a C#-only feature makes a modeled rule observable for the first time, the rule belongs in the Lean model.

**Qualifications**
- C#-only constructs are normative through their hand-written canonical cases and the design rules, not through tutorial prose. These are the parse-level LanguageSpec cases and the C#-only cases carrying a `LeanExclusionReason`.
- Resource-limit outcomes fall outside this law, because they are not part of the shared observation (FORMAL-06). Their route dependence is RUN-03's.
- **Source-level capture by the prelude.** The conservative-extension guarantee holds for elaborated core programs only. A C#-only prelude member is an ordinary prelude binding, so its spelling stops being a free name and is captured away from implicit-parameter promotion (RES-04). Adding a prelude member or configuring a host operation therefore changes the source-level meaning of every program that uses that spelling as a free name, and the Lean correspondence cannot see this, because it compares elaborated trees. `F = sign + 1` / `G = signs + 1` / `G(5), F(5)` is `S[6, 2]`: the alias `sign` is resolved and lifted, while the free name `signs` becomes an implicit parameter.
- Modeled rules that C#-only features rely on include the property cache, ownership-first lookup and the parameter channels.

```katlang
abs(x) = 100
abs(-3), Math.Abs(-3)
```
⇒ `S[100, 3]`

### FORMAL-04 — Numerics are two-tier: Lean's `Int` laws bind C# on the common exact integer subdomain, and Decimal128-only behavior has no Lean witness

- Lean models numbers as unbounded `Int`; C# computes in IEEE 754 Decimal128 (OP-05). This rule is the single statement of how the two numeric models correspond and how a numeric change is routed.
- The **shared tier** is the common exact integer subdomain: operands and results that are integers, exactly representable in Decimal128, and carried in canonical integer representation (no fractional digits, not `-0`). There the Lean-modeled laws are normative for C#. They cover:
  - exact in-range integer `+`, `-`, `*` and unary minus;
  - `div` and `mod` truncating toward zero, with `div` exact wherever the truncated quotient is representable (`x == y * (x div y) + (x mod y)`; OP-08);
  - the comparisons on integer values, and structural equality;
  - Boolean-only condition consumption (BOOL-02);
  - the evaluated-zero divisor error (OP-06), and the zero-base negative-exponent error at its integer instance (OP-09);
  - non-negative integer powers, and the exact reciprocals of the bases `1` and `-1`, while the result stays exact and finite.
- Everything else is the **Decimal128 tier**:
  - 34-digit precision and range, including rounding or overflow of integral operands, and a `div` quotient beyond 34 digits rounded toward zero;
  - fractional values and the quantum, including exactly integral values that carry one (`1.0`, `2.50e1`, `3 - 1.0`);
  - non-exact `/`, and the decimal `avg` mean (OP-12);
  - negative powers of every base other than `0`, `1` and `-1` (`2 ^ -1` is `0.5`), fractional exponents, and integer powers whose exact value exceeds 34 digits;
  - NaN, ±Infinity, signed zero, overflow, gradual underflow, and the IEEE ordering of these specials as opposed to structural equality;
  - transcendental Math;
  - the `.string` and display text of every number that is not a canonical integer.
- **Routing.** A change to a shared-tier law is made in Lean and C# together, with Lean-comparable LanguageSpec coverage. The Decimal128 tier is C#-normative: it is pinned by C#-only canonical cases with a `LeanExclusionReason` and must never be given a fabricated Lean encoding.
- Where Lean's `Int` core answers differently inside that tier, the Lean answer is a documented model limitation, never the runtime contract: for example the truncating `7 / 2 = 3` and the `illegalInEval` "cannot represent" error for `2 ^ -1`. This is the explicit numeric scoping of FORMAL-01's "Lean decides".
- **Tier membership** is decided by the values' exact integrality AND their canonical integer representation, never by how the source is spelled:
  - Integer literals do not keep a program in the shared tier once an operation rounds, overflows or produces a fraction.
  - An exactly integral value with a non-canonical quantum is Decimal128 tier for every observer that sees representation: `.string`, display, the neutral differential observation (FORMAL-06), and the representative that `distinct` or a repeated-name binding keeps.
  - For value-only observers, such as `==` against the canonical integer, that value still obeys the `Int` laws.

**Qualifications**
- The encoder refuses fractional, non-finite, negative-zero and quantum-bearing number literals, so a Decimal128-tier literal cannot enter the Lean-guarded partition. It cannot refuse a RESULT that leaves the tier (a quotient, an overflow, `-0` from unary minus); such cases rely on the reviewed exclusion list in `SEMANTIC-ALIGNMENT.md`.

```katlang
-7 div 2, -7 mod 2, 2 ^ 10, 3 < 5
7 / 2, avg((1, 2)), 0.1 + 0.2 == 0.3, (1e40 div 7).string
```
⇒ `S[-3, -1, 1024, true, 3.5, 1.5, true, '1428571428571428571428571428571428000000']`

The first row is shared tier. The second is Decimal128 tier.

### FORMAL-05 — Counted evaluation is the one meaning of an expression; plain evaluation is its value projection

- Every expression has exactly one semantic definition: its counted evaluation, which yields a value with its emitted count (VAL-08 (c)): `valueCount` at every value boundary, the number of supplied items for a spread, and the number of emitted items for row accumulation.
- The plain value of an expression is, by definition, the value component of its counted result. A value therefore never depends on whether a consumer reads it through the plain view or the counted view. The emitted count is part of the meaning, not an implementation detail.
- C# must preserve this. There is no independent plain evaluator body. Counted code may read a plain projection only for strictly smaller work at a value boundary, never for the same node.

**Qualifications**
- In Lean this holds by construction: `evalCounted` matches every `Expr` constructor with no default arm, and `eval e = (evalCounted e).fst` is a kernel theorem (`eval_is_counted_projection`).
- The slot-view family returns item lists and has no plain/counted pair. In C#, the root decoration pair and the opens-free direct lookup are listed exceptions (`SEMANTIC-ALIGNMENT.md` § Known gaps).
- Taken literally, the law is about internal architecture. Its user-visible content is "one meaning per expression, of which the count is a part".

```katlang
F(x) = x, x
[F(1), F(1)*], count((F(1), F(1)*))
```
⇒ `S[L[S[1, 1], 1, 1], 3]`

### FORMAL-06 — Lean/C# agreement is defined on the neutral observation: structure, emitted count, and innermost error kind

- The observation on which the two implementations must agree, and so the content of "language semantics" for correspondence, is:
  - success or failure;
  - on success, the raw value structure (atoms, strings, Booleans, sequences, lists, the empty sequence) and the root emitted count;
  - on failure, the innermost semantic error category. Context frames are discarded, and the arity kinds collapse into one `arity` category.
- Outside this observation, and never required to match Lean: diagnostic wording, source spans, context frames, notes and suggestions, structured public codes; resource-limit outcomes, whose kind may even differ between C# paths; operational counters; display text.
- Evaluation effects are semantic but are not part of this observation. The property-cache and evaluation-count laws are Lean-modeled and pinned on each side separately. The order of host-operation calls and random draws is C#-only (RUN, PROP).
- **Constitutional status of error kinds, one policy for every family.**
  1. Invariance is constitutional. Lean and C# must agree on the error category of every failing program in this observation, and every C# route must agree on the error kind of every failing program (RUN-01). Resource-limit verdicts are excluded from both (RUN-03).
  2. A specific category is constitutional only where a rule commits to it explicitly: for example `TypeMismatch` in a truth position (BOOL-02) and for a non-numeric ordering operand (CMP-04), `DivisionByZero` (OP-06), `NoMatchingBranch` (PAT-02), `AmbiguousOpen` (RES-03), `MissingOutput` and `SpreadMissingOutput` (VAL-05), and the evaluation-error taxonomy of RUN-07. NEED-04's repeated-name categories are that binder rule's own. Lazy and unused roles are not validated until execution demands their semantic role.
  3. Elsewhere only the verdict "fails" is constitutional. The current category is Current semantics: the corpora pin it, and it may change through a coordinated Lean, C# and canonical-case change without a constitutional amendment.

**Qualifications**
- The public-failure checks distinguish success, dynamic failure and parse rejection, and shared payload guards exist for reviewed fields. Exact messages and frames, host limits and universal demand traces stay outside this observation.
- The category collapse also hides C#-only arity variants (`EvalError.VariadicArityMismatch` maps to `arity`).
- A non-terminating program has no Lean result: the Lean evaluator has no budget, and its internal incomplete outcome is never a compiled run's result. In C# such a run ends in a resource-limit error whose kind depends on the path. That outcome lies outside the correspondence (RUN-03).

```katlang
Add(x, y) = x + y
Add((1, 2))
```
⇒ `ArityMismatch`

### FORMAL-07 — Proofs cover total helpers and operation-level laws of the fuel-indexed evaluator core; whole-program evaluation is checked executably on bounded corpora

- `docs/design/formal-correspondence-ledger.md` is the one status of every proof claim. This rule states the classes of evidence; the ledger states the instances, with their premises. A law's status may claim only the strength it actually has.
- A Lean theorem is about Lean. There is no machine-checked bridge from any C# source to any Lean term: no extraction, no formal C# semantics, no translator. Every claim that reaches C# is therefore tested correspondence over a trusted boundary, and universal agreement of the two evaluators is open.
- The classes of evidence are:
  1. **Production Lean:** a kernel theorem about the definitions of `lean/KatLang.lean`, with its production instance discharged. These include the production bridge of the total fuel-indexed core, the public-run bridge over the total identification, validation and wiring prefix of `runResultM`, whole-run heap discipline, the address invariant (also for the public run from every entry state that satisfies it), cache survival, and Model-C binder laws over production runs. The admitted set of that validation is characterized: it returns `ok` exactly on a declarative predicate over the identified tree (`validate_ok_iff`). No `partial` definition and no opaque printer remains in `lean/KatLang.lean`; the public-run results stay parametric only in core's layout `Std.Format.pretty` that `reprStr` runs, and read incompletion through one predicate (Q-82).
  2. **Conditional:** a kernel theorem whose named premises are not all discharged for production. Repeated-name and supply-correspondence laws hold under completed/Ready and identity-domain premises, or over Ready supplies; a suspended argument and its Ready value are not equivalent, by design. Since lazy collections (formal ledger row E-24), the repeated-name model and the heap-renaming simulation are stated over CONCRETE observations and values, because a lazy value's positions are heap addresses, and the finite-loop one-round theorems assume that a step's rows are not bare list positions (`PlainRows`). The invariant that no evaluator result is a bare deferred item, which would discharge `PlainRows`, and the lazy extension of the simulation are open.
  3. **Reference kernel:** a theorem about `KatLangArityLaws/SignatureCompletion*.lean`, a model of the equation system signature selection receives. It is about that model, never about `KatLang.lean` or C#. AST-to-equation extraction is unmodeled.
  4. **Executably checked:** `#guard`s that run the Lean evaluator, and generated C#/Lean differential corpora over the same derived programs. This is bounded validation, not verification.
  5. **C# tests only:** C#-only behavior, checked only by C# tests and C#-only canonical cases (FORMAL-03, FORMAL-04).
  6. **Source inspection:** what is established only by reading. **Open:** well specified and unproved.
- Scope limits on what a theorem establishes:
  - Theorems over the Lean SPECIFICATION functions of C#-only front-end passes, which the evaluator never calls, prove that specification, not the C# passes that decide the elaborated program.
  - A theorem of the isolated `CoreArityAlgebra` proves a law of that non-authoritative extraction. One refinement theorem connects its binder to production, and it covers ALLOCATION only: not the binder's result, no repeated names, no structural or literal patterns, no VALUE demand. A universal law proved in the algebra is not thereby a law of the production binder.
  - E-24 (vii) proves divergence for the Lean core whole read of `F(1)` when `F(x) = [x].map(F)`. From the prelude context and empty heap, this call exhausts every fuel and its production evaluation never completes (`LazyCollectionBoundaries.recursiveMap_wholeRead_production`).
- The Lean sources use no escape hatch: no `sorry`, `admit`, user `axiom` or `native_decide`. The theorem dependency audits report only `propext`, `Quot.sound` and `Classical.choice`. A successful `lake build` shows that the checked development builds, and nothing more about correspondence. `#eval` output and `-- EXPECTED:` comments are not verification.

**Qualifications**
- "Lean-modeled" never means "proved correct". Evaluator-level laws that ordinary programs depend on may be only executably checked on finite inputs.
- Evidence labels in `docs/design/language-rules/` and in dated reports are history unless the ledger confirms them. Where they differ, the ledger is current.

### FORMAL-08 — The constitution is stated over the source-reachable elaborated core; host-built shapes outside it are not constitutional

- Every tree produced by a successful parse and front-end elaboration of source satisfies:
  - (a) no `Expr.SequenceConstruct`;
  - (b) no surviving `Expr.Grace`;
  - (c) `Expr.Param` appears only as elaboration output, never from the parser;
  - (d) no `Expr.NativeCall`, which exists only as the body of a prelude Math member or configured host operation;
  - (e) a parenthesized group survives only as a `Capture` of at least two slots or of one spread slot; `()` is `EmptySequence`; no `Capture` carries declarations; and a `Capture` that elaboration synthesizes has the same two shapes (FWD-02);
  - (f) every `EmptySequence` has depth 0;
  - (g) every `Comparison` has at least one link;
  - (h) a `SequenceSpread` appears only as a whole slot or as the operand of another spread; the lowered fluent leading argument of `A*.F(…)` counts as a whole slot, and `(A*)` is the spread slot of a capture;
  - (i) a `Call`'s function is `Resolve`, `Param` or an ARGUMENTLESS `DotCall` (SYN-09, DOT-09), with one exception: the synthesized assignment-deconstruction helper call, whose callee is an `AlgorithmExpr`;
  - (j) every `DotCall` fallback is exactly `Resolve` or `Param` with the member's own name;
  - (k) no unresolved `load`;
  - (l) at most one collector per pattern level;
  - (m) `Algorithm.Conditional` comes only from clause-group elaboration, and never as a single-clause family whose head is an ordinary binder pattern, which elaborates to `Algorithm.User`;
  - (n) no parameter or branch pattern contains a one-item sequence pattern (PAT-06);
  - (o) the unpacking receiver appears only as the one parameter of a synthesized deconstruction helper (VAR-05);
  - (p) a `meta` capture is only a plain, fixed name written once at the top level of an ordinary explicit parameter list, never inside a structural pattern and never a clause-family binder (CR-1).
- Every law in the other families is a law over such trees. The behavior of `Evaluator.Run*` and of the Lean model on host-built shapes outside this core is evaluator or model totality. Lean guards and defensive-branch tests pin it, but it is not constitutional. Examples: `SequenceConstruct` joins; a single-row or empty `capture`; a capture or number callee; a zero-link comparison chain; a surviving Grace, which is `IllegalInEval`; a hand-built single-branch conditional with an ordinary binder head; an unpacking receiver written by a host outside a deconstruction helper.
- A host-built tree that violates (l) or (n), or that nests a `meta` capture in a structural pattern or repeats its name, is refused before evaluation as `IllegalInEval`, never given a meaning. In C# only, so is a `meta` clause-family binder.

**Qualifications**
- The rule concerns successful elaborations. A result with diagnostics may keep recovery shapes or a refused `load` kept as written, and such a result is never evaluated (RUN-04).
- Clauses (a), (b), (j), (k), (l) and (n), and the placement part of (p), have dedicated checkers, in Lean and C# or in C# alone. The others hold by construction and are pinned by inspecting their construction sites. Lean's `postElabInvariant` states only (j) and (k); it admits `sequenceConstruct` because the Lean model's `Expr` must represent internal nodes.

```katlang
x, y = 1, 2
((x)), (y), 1 < 2 < 3
```
⇒ `S[1, 2, true]`

`F(*a, *b) = a` is `InvalidCollectingBinding`. `(A = 1)` is `DeclarationInParentheses`. `{ x + 1 }(2)` and `(1, 2)(3)` are `UnseparatedSameLineItem`: a block or capture is never a written callee.
