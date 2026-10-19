# Q-68 — current Lean guard audit and closeout (2026-10-20)

Q-68 (FORM-05; X-11) asked whether weak Lean guards — assertions that accept "some error" or
discard the structure they claim to test — should be tightened or removed. This document is the
**replacement completion basis** for Q-68: a fresh, source-grounded inventory of the current
handwritten Lean executable guards, the disposition of every candidate, the strengthened guards
and the controls that show they discriminate.

**Provenance.** The original FORM-05 inventory of "about 18 'some error' guards" was not available
to the S4 formal-evidence closeout (2026-10-18), and the owner has directed that it be replaced by a
current audit rather than recovered. It was **not reconstructed** here, and none of its unnamed
entries are invented. Its named historical candidates (`Conditionals` `test22`–`test24`, the former
`redundantParensAroundListCanonicalize`, the former `reduceVariadicAccumulatorStateFlattens`, and the
X-11 empty-policy guard) were settled by S4 and are re-checked below as anchors. This is executable
guard/evidence closeout, not universal evaluator refinement: it changes no language semantics and
no production code.

Detailed, reproducible evidence (ignored, local): `artifacts/validation/q68-current-guard-audit/`.

## 1. Baseline

- Checkout `D:\Projects\katlangnet`, branch `main`, HEAD `2908ddaa` ("Prove scoped S6a repeated-name
  laws for nested and mixed heads"), version 0.8.248; clean working tree and index at the start.
  The brief's inspected snapshot `ea59e22a` is two commits older; neither later commit touches the
  S4 anchor guards. 28 stashes and 13 worktrees (primary + 12 under `.claude/worktrees/`) were
  present and were not touched.
- S4 (`experimental/features/formal-evidence-closeout-s4-report.md`, evidence in
  `artifacts/validation/formal-evidence-closeout-s4/reviewer/`) strengthened 23 guards / 25
  accept-any-error arms and kept three deliberate broad assertions. All of its anchors are present
  in the current source with their strong assertions (§ 5). S4's validation is historical evidence;
  every check reported in § 7 was executed for this audit.

## 2. Scope and census

**Handwritten guard modules** (every tracked file built by the `CoreTests` and `KatLangArityLaws`
Lake targets, plus the other handwritten Lean files):

| Set | Files | `#guard` commands (baseline → final) |
| --- | --- | --- |
| `lean/CoreTests.lean` + `lean/CoreTests/*.lean` (incl. `Common.lean` helpers) | 48 | 2,272 → 2,273 |
| `lean/KatLangArityLaws.lean` + `lean/KatLangArityLaws/*.lean` | 26 | 468 → 472 |
| `AstDemo`, `CoreArityAlgebra`, `CoreArityAlgebraProofs` | 3 | 0 (theorems / `#eval` demos only) |
| **Total handwritten** | **77** (58 contain guards) | **2,740 → 2,745** |

**Generated corpora** are listed separately and were not edited: `lean/LanguageSpecCases.lean`
(420 guards) and `lean/SemanticExplorerCases.lean` (2,976 guards). Their freshness is owned by
`LanguageSpecArtifactsTests` / `SemanticExplorerLeanArtifactTests` (regeneration flags only), and
their observation policy is FORMAL-06's neutral `obs` (raw structure, root count, innermost
category) plus Q-67's reviewed payload guards. Q-67's Comparable / Partial / CategoryOnly / HostOnly
policies are unchanged; every precise payload added here is a Lean-only guard.

**Selection method** (`census.py`, a one-off discovery script — not a lint framework). Each file is
split into top-level commands; a candidate is a `#guard`, or a Boolean helper definition a guard
calls, whose text matches a weak-observation pattern: `.error _ => true`, `| _ => true`,
`.ok _ => true`, `.isError/.isOk/.toBool`, `.isSome/.isNone/== none`, the broad helpers
`innermostIsAny{Type,Arity}Mismatch` / `innermostIsBad{Arity,Index}`, or the flattening observers
`runFlat`/`expectFlat`/`hostAtoms` near a structure word. Search is discovery only. Three
supplementary manual searches covered what the patterns miss: negated success (`#guard !…`,
`== false`), constructor payload wildcards (`.error (.ctor _)`), and a local `isError` helper.

**Flattening, decided by instrumentation instead of by eye.** The 441 flat-observer hits were not
triaged by keyword. A scratch copy of every module that calls `runFlat` (24 modules, 511 call
sites) replaced each call with one that also reports, through `dbgTrace`, the STRUCTURED result of
the same program. 424 traces were lossless (an atom, or a non-empty sequence of atoms — the flat
projection loses nothing **for that current result**), 58 were error paths, and 118 traces at
**114 distinct sites hid structure** (a list kind, a nested list/sequence, or an empty element).
These are discovery labels, not proofs that the assertions are adequate. A fixture can reduce
its input to counts before `runFlat`: the resulting scalar observation still cannot establish
preservation of nested structure. Review checked observers and fixtures beyond these labels (§ 9).

| Census measure | Count |
| --- | --- |
| Baseline candidate units (pattern hits) | 590 (441 flat-observer, 121 broad helper, 33 Option, 5 ok-wildcard, 4 error-wildcard, 2 any-wildcard, 1 `isError`-style; a unit may carry several flags) |
| Supplementary manual candidates | 22 sites (+1 flat call site discovered by instrumentation) |
| Initial implementation inventory | 613 rows (`candidate-dispositions.tsv`, retained as history) |
| **Final reviewed inventory** | **618 rows** (`reviewer/candidate-records.json`, `reviewer/candidate-dispositions-reviewed.tsv`): five new sites and four corrected initial dispositions |
| Strengthened rows | **29 rows covering 38 assertion sites**, plus the new payload sweep; ten guard commands strengthened in review, one overlapping an initial strengthened row (§ 9) |
| Deliberately broad, with rationale | **178 rows**, including S4's three exceptions and the builtin acceptance classifier |
| Already strong | **411 rows** |
| Supplementary failure census | **983 failure-related `#guard` commands**, including exact assertions, Boolean/String observers, tuple/heap/error patterns and local predicate dependencies (`reviewer/failure-guard-review.json`); an over-approximation including equivalence and success controls |
| Shared observers inspected separately | **10 units**, including imported TypeMismatch helpers, taxonomy String observers, partial member/ambiguity observers and the lossy `finalHeap` fallback (`reviewer/shared-observers.json`) |

A guard count and an assertion-arm count differ; these overlapping inventories must not be added.
One helper row can stand for several guards
(`fcTwoRowPredicateRejected` serves two), and one `#guard` can hold several arms.

## 3. Initial review classes and their decision rules

Every row was reviewed against its stated claim, its actual input and route, and a wrong outcome
the assertion must reject. Expectations come from the accepted rules (Q-27 builtin minimums,
Model-C collection, NEED-04 identity, LOOP-CF1, alias-cycle validation) and were then corroborated
by Lean probes (`probes/*.log`); the current result was never taken as its own oracle. The initial
classification below had genuine omissions; § 9 and the final reviewed inventory supersede those
dispositions. Current-result shape instrumentation did not itself establish assertion strength.

| Class | Rows | Decision |
| --- | --- | --- |
| Exact arity count available, constructor-only asserted (`innermostIsAnyArityMismatch`, `badArity ∨ any arity`) | 5 | **Strengthened** to the exact `arityMismatch expected actual`. |
| Boolean-required rejection asserted as "some TypeMismatch" where the comment names that rejection | 6 | **Strengthened** with the existing `innermostIsBooleanRequired role description` (`booleanRequiredMessage` is the repository's one structured message family); another TypeMismatch would have passed. |
| Accept-any-error via negated success or a local `isError` | 2 negated successes + 9 `isError` uses (1 row) | **Strengthened** to the exact innermost error. |
| Payload wildcard whose payload is a stable, pinned contract | 1 | **Strengthened** (`ModelC` callable-identity message). |
| Flat observation whose claim is the erased structure | 4 | **Strengthened** to structured `Result` equality. |
| Option success that discards the rebuilt value | 1 | **Strengthened** (`CountC` row compared by `reprStr`). |
| Payload-less constructors (`badArity`, `badIndex`, `missingOutput`, `divByZero`) | 49 | Already strong: the constructor is the maximal observation; the competing outcome in each case is a different constructor or success. Repeated-name `badArity` frames are pinned exactly in `NestedRepeatedNameGuards` (`valueConflict`). |
| `TypeMismatch` constructor only | 59, plus the supplementary `Strings` / `SupplyCorrespondenceGuards` wildcards | Deliberately broad: Q-67 classifies TypeMismatch as **CategoryOnly** (`DifferentialErrorContracts`), its payload being prose; every order/precedence guard in the class (`CollectionBuiltins` mirrored spreads, `VariadicSelection` selectors, `Strings` interpolation holes, `BuiltinArgumentRoles` spreads, `LoopConditionFirst` `Tr`/`Nb1`) races it against a `divByZero` or arity competitor, so the constructor discriminates. |
| Option presence/absence (`isSome`, `isNone`, `== none`) | 31 | Already strong: absence/presence of a callable projection, a forwarding row or a cache key component is the stated observation, paired with exact heap/event checks. |
| Flat observation, current result lossless | 312 initially; 310 retained | Value/order or numerical-count claims, with structural evidence separate. Review strengthened nested-collector and internal-empty-join claims; current scalar results alone were insufficient. |
| Flat observation, lossy but claim is values/counts | 101 initially; 99 retained | Retained claims concern element values, order or receiver cardinality. Empty/spread emitted-count claims were strengthened. Builtin result kinds remain pinned by generated raw `obs` and structured siblings (`ValueBoundary`, `SelectionValueBoundary`, `OutputBundle`, `sequenceBuiltinDotCall*SequenceValueSweep`). |
| No `runFlat` executed for the unit | 9 | Open-list or helper mention only. |

## 4. Initial strengthening (20 rows, 29 sites) and the new sweep

| Site (file / declaration) | Claim | Before | After (corroborated by probe) |
| --- | --- | --- | --- |
| `AliasForwarding` `A_repeat(Inc)` | an alias keeps `repeat`'s own minimum | any arity | `arityMismatch 3 1` |
| `AliasForwarding` `CountC` bare-forwarding row | a nameable target forwards by its own names | `.toOption.isSome` | row is `CountC(collection)` |
| `ForwardingBindings` `fwdReportSuperseded` | the superseded helper read with no arguments | any arity | `arityMismatch 2 0` |
| `LoopConditionFirst` `Ar` | the next round's binder checks a one-slot state | any arity | `arityMismatch 2 1` |
| `LoopConditionFirst` `Nb2` | the flag row's non-Boolean value is reported first | any TypeMismatch | Boolean-required while flag, `numeric value 5` |
| `LoopSteps` `take` as a `repeat` step | a builtin's list result is ONE state slot | any arity | `arityMismatch 2 1` |
| `LoopSteps` `first` / `Fi` as `while` steps (2) | a `()` result is one slot, so the flag needs a Boolean | any TypeMismatch | Boolean-required while flag, `a sequence value with 0 sequence elements: ()` |
| `ValueDemand` `sum` zero-supply | the builtin's own arity error, the one `sum()` reports | `badArity ∨ any arity` | `arityMismatch 1 0` |
| `FamilyCallbackCardinality` two-row predicates (2) | a two-row predicate is the Boolean-required error | any TypeMismatch | Boolean-required filter predicate, `(true, true)` |
| `CallbackResultBoundary` § 9 filter | same | any TypeMismatch | same |
| `ModuleUnits` two module declarations | two declarations are two callables | `!evaluatesTo … 5` (any failure) | callable-identity TypeMismatch |
| `ModuleUnits` inline alias chain | the inline text is a static alias cycle | `!validates` (any failure) | `illegalInEval aliasCycleMessage` |
| `ModelC` `differentCallablePairStopsBeforeTheLaterFailure` | identity conflict stops before the later failure | `.typeMismatch _` | exact identity message |
| `InvocationPlanGuards` `arityBeforeDemand` | wrong cardinality before any demand | `isError` ×2 | `arityMismatch 1 2` ×2 |
| `InvocationPlanGuards` `failingSpreadIsSticky`, `failingValueThenMeta`, `recoveredFailureThenMeta` | the original VALUE failure is sticky / recoverable | `isError` ×5 | `divByZero` ×5 |
| `InvocationPlanGuards` `readyAndUnsupportedStayOrdinary` | Ready and unsupported cells are refused by META | `isError` ×2 | `notAnAlgorithm "meta: not a supplied call computation"` ×2 |
| `Conditionals` `uniformBranchOutputArityPasses` | both branches emit TWO top-level outputs | flat `[1, 2, 7, 7]` | `((1, 2), (7, 7))` |
| `ValueDemand` `map(…, Collect)` | a collecting callback receives one input per element | flat `[1, 2]` | `[[1], [2]]` |
| `ValueDemand` `map(…, Only)` | each element is collected | flat `[1, 2]` | `[[1], [2]]` |
| `CollectingParameters` `variadicScaleMatchesBuiltinMap` | the variadic scale and `map` produce the same items | flat equality | the two results are the same list `[10, 20, 30]` |

**New companion sweep.** `ParityGuards.builtinArityParityHolds` classifies a rejection by
constructor only (it must, so that an accepted count can never be mislabelled). The new
`builtinArityRejectionCarriesMinimum` pins the payload of every rejected count `0..6` for all 21
swept builtins: `arityMismatch (minimum) (supplied)`, with the minimums written out independently
of `builtinMinimumArity` (`builtinWrittenMinimumArity`). This is the Lean side of Q-27's payload
hygiene, already pinned in C# by `IfBuiltinArityPayloadTests`.

**New helper.** `InvocationPlanGuards.failsAs` (innermost error through context frames, compared by
`reprStr`) replaces the accept-any-error `isError`; four self-guards show it accepts a framed match
and rejects success, another constructor and another payload. `CoreTests.Common` is unchanged.

No guard was removed. The initial implementation preserved fixture inputs. Review replaces the
unused-reference capture fixture with an actual reference read (§ 9).

## 5. Deliberately broad assertions (retained) and S4 anchors

S4's three exceptions are reviewed and retained:

1. **`ModelC` six-permutation repeated-conflict matrix** — establishes unsatisfiability for every
   permutation; the order-dependent innermost constructors are pinned separately by the two guards
   just above it (callable-identity TypeMismatch; repeated `badArity`).
2. **`ModelC.valueFailureDoesNotEraseCallableIdentity`** — the subject is CALLABLE survival after a
   VALUE failure and no extra binding context; the precise VALUE error is not the property.
3. **`HigherOrderCalls.callbackParamCollisionFailsCleanly`** — a termination regression: a
   structured failure instead of a loop is the whole claim.

Other retained broad sites, each with its reason: `ModelC` `if`/`Choose` selector (agreement, or
both TypeMismatch with deliberately different messages); `SupplyCorrespondenceGuards` non-vacuity
checks (existence of successes, non-matches and errors); `GraceMovement.singleMoverHolds`
(vacuous outside its single-mover domain by design); `BinderGuards` / `WhileRoundGuards`
category predicates (the subject is the exact demand-event trace; failures are injected by the
guard or category companions of exact Lean/C# pins); `Numerics` fractional power (`illegalInEval`
whose payload is a Lean-core-only limitation message; the competing outcome is silent
truncation); `OutputBundle` capture open targets (`badOpenForm` whose payload is a rendered form
description such as `capture: (inline#0)`); `Strings` `test43`–`test45` (CategoryOnly
TypeMismatch against success); the `ParityGuards` acceptance classifier (now with the payload
sweep).

**S4 anchors (unchanged, re-built green):** `Conditionals.test22/23/24` (`arityMismatch 3 2`,
numeric conditions keep cardinality-before-demand), `test36` (`noMatchingBranch "Sign"`);
`HigherOrderCalls.test14d` (unknown `length`) and the three failing `dotCallBoundary*16a` routes
(arity 2/1); `DotCallSemantics.flatFixedCallStillDoesNotAutoSpread` (2/1), `test4` (ambiguous open
`G`), `test5a` (structural member 1/0); the collecting-suffix guard and
`ForwardingBindings.uflNestedValueFormerly` (1/0); `OutputBundle.captureReceiverDoesNotExposeStructuralMembers`
(unknown `V`, direct-member control succeeds);
`SequenceBuiltinRegressions.reduceCollectingAccumulatorCollectsTheOneAccumulatorValue` (exact
nested accumulator, C# twin); `ParityGuards.builtinEmptyPolicyFailuresAreNotArityErrors` (real
`()`/`[]`, per-builtin `badIndex` / domain `illegalInEval`). The removed
`redundantParensAroundListCanonicalize` stays removed; its note in `ListValues.lean` names the
surviving parser-derived evidence (`RedundantParenthesesTransparencyTests`,
`SemanticExplorerTests.DerivedLeanPrograms_MirrorParserParenthesisNormalization`, the
`parentheses-group-syntax` spec case) and `listKeepsVisibleEmptyElement` for list shape.

## 6. Discriminating controls

All controls are scratch copies under `controls/`; the candidate source is never edited.
`run-control.sh` applies one `sed` edit, refuses an edit that changed nothing, compiles with
`lake env lean` and records the exit code and every error line.

- **25 negative controls** (`controls-summary.txt`): 21 wrong expectations (count, role,
  description, message, constructor, flat-instead-of-nested shape, list-instead-of-sequence kind,
  wrong builtin minimum) and 4 altered routes (`Nb2` → `Nb1`'s operator TypeMismatch; `take` with
  one round so no second call; one module declaration instead of two; `F(bad)` with an accepted
  count so `bad` is demanded). Every control exits 1 with errors **only** at the intended guard
  lines (two lines where one helper serves two guards). These show assertion sensitivity; they are
  not production mutants, and no production mutation campaign was warranted.
- **Contrast guards** (`GuardContrasts.lean`, compiles green): each former observer accepts the
  wrong observation its replacement rejects — `innermostIsAnyArityMismatch` accepts arity 2/2,
  `badArity ∨ any arity` accepts `badArity`, `innermostIsAnyTypeMismatch` accepts the operator
  TypeMismatch, `hostAtoms` identifies `[[1], [2]]` with `[1, 2]` and two two-value rows with one
  four-value row, and a negated success accepts `unknownName`.
- **Helper self-tests** for `failsAs` are part of the built `InvocationPlanGuards` module.

Every executed control must complete within its isolated process timeout. A timeout, crash or
elaboration error is not an assertion rejection. No evaluator fuel or runtime limit is changed.

## 7. Implementer validation (preceding stage)

Level **V1**: Lean test/guard precision inside the `CoreTests` and `KatLangArityLaws` dependency
closure, plus documentation; no evaluator, parser, `Result`, shared helper (`CoreTests.Common`),
generator, public API or production code changed, so no V3 trigger is engaged. Executed serially;
logs and exit codes are in `artifacts/validation/q68-current-guard-audit/validation/`. These are
the implementer's results, not independent verification of the reviewer fixes:

1. `lake build CoreTests` (exit 0) and `lake build KatLangArityLaws` (exit 0) on the final
   candidate; the development build of the same sources rebuilt all 13 edited modules, and every
   guard passed.
2. `dotnet build tests/KatLang.Tests` (exit 0, 0 warnings), then one filtered `--no-build` run of
   the C# tests that read the edited Lean files or scan Lean source — `LeanCoreTestsCompositionTests`
   (3), `MaintainedDocumentationConsistencyTests` (124), `ReduceInitialReportAlignmentTests` (45) —
   plus `IfBuiltinArityPayloadTests` (7), the C# twin of the new payload sweep: 179 passed, 0 failed,
   0 skipped (TRX recorded); no `KATLANG_REGENERATE_*` flag was set.
3. The 25 scratch negative controls (each exit 1 at the intended guard only), `GuardContrasts.lean`
   (exit 0), and S4's reviewer `GuardControls.lean` recompiled against the current modules (exit 0,
   `negatives-ok`, `reviewer-controls-ok`).
4. `git diff --check` (exit 0). The tracked/untracked candidate state was identical before and
   after the validation stream.

Not run: the other five canonical Lean targets and the full .NET suite (V3 only); no generated
artifact was regenerated.

## 8. Closure and remaining limits

Q-68 is **closed** against this newly completed current guard inventory, following the owner's
direction to replace the unavailable historical FORM-05 inventory. Every current candidate is
strengthened, already strong, or justified by its intended assertion scope; no substantive
in-scope weakness is left unexplained and no runtime defect was found. The historical list was not
reconstructed.

Limits: the census covers handwritten guards in the built Lean targets; generated corpora are
governed by their own freshness/observation tests. Discovery plus fixture/observer inspection bound
the review. The supplementary failure census includes exact assertions and String/tuple observers
missed by the initial weak-pattern search. Remaining success-only assertions outside the selection
were not all individually reviewed. The source manifest, full source units, 618 final candidate
records, 983 overlapping failure-related commands and ten shared-observer dispositions make this
boundary reproducible.
Q-68's closure does not establish whole-run heap/cache/callback refinement, and Q-66, R3′, R4,
R6, CF-4 and R7 keep their evidence-supported statuses.

## 9. Independent review and repairs (2026-10-20)

The reviewer verified all 14 incoming pending-file hashes against handoff candidate
`6BAA616E215EA350052566F6B774A5AB0A66BDBE77350E220D15547B42345646`, inspected the complete diff,
fixtures and assertion helpers, and expanded discovery to failures hidden by named predicates,
String observations, heap tuples and error-to-sentinel conversions. The source manifest corrects
the CoreTests file count (48, including its root). No production or shared `CoreTests.Common`
code changed.

| Site | Actual fixture and required observation | Contract / wrong outcome rejected | Reviewer control |
| --- | --- | --- | --- |
| `CollectingParameters.variadicPreservesNestedSequenceValues` | `Arg = (1,2), (3,4)`; `Arg.Collect` must be `[ ((1,2), (3,4)) ]`, retaining count 1 / atoms 4 | Exact collector law; `[ (1,2,3,4) ]` also has one item and four atoms | N26 wrong nested shape; R27 collapsed fixture |
| `Conditionals.uniformBranchOutputArityPasses` | `F(0)=1,2; F(x)=x,x`; root rows `F(0),F(7)` have the nested value and actual emitted count 2 | Value boundaries / root row count; retain `runResult` whole-program validation **and** the lower-level `runCountedProgram` count | N28 wrong count; W19 wrong shape |
| `ModelC.failedCompletionDoesNoFurtherWork` | Catch two demands of a call dividing by zero; require DivByZero, identical full outcomes and unchanged binding-context count | NEED-02; equality of two successes passed the former check | N29 wrong constructor; R30 successful fixture |
| `OutputSemantics.explicitEmptyProducesZeroValues` | Raw `()` has `CountedResult (sequenceValue [], 0)` and an empty host projection | Value boundaries; flattened atoms do not establish emitted count | N31 count 1 |
| `OutputSemantics.spreadEmptyJoinContributesNoItems` | Internal join of spread 1, non-spread `()`, spread 2 has `sequenceValue [1,2]`, emitted count 1 (one constructed value with two items) | Internal sequence-join/value-boundary law; reject an inserted visible empty item | N32 hidden empty element |
| `OutputSemantics.spreadOfEmptyContributesNoItems` | `()*` has empty sequence value and emitted count 0 | Spread law; flat `[]` alone cannot establish zero emitted items | N33 count 1 |
| `CallReferenceGuards` capture inertness | Compare `R == R` for `R=Capture(Sq(5))`; require successful `true`, no `x*x` and no supplied `5` cells | META capture is inert; old fixture never read R, and `finalHeap` returned an empty heap on errors | R34 failed capture route |
| `CallReferenceGuards` adapter call | `Again(meta op)=op(3)` applied to `Sq(5)` fails as `notAnAlgorithm "param(op)"` | META adapters have no CALLABLE; reject another callee's failure | N35 wrong callee |
| `ArgumentViewGuards` view construction | Equality of `R.Arguments` for `Capture(Add(Sq(5),Sq(6)))` succeeds as `true`, without a `Sq(5)` preparation cell | S2 view construction is inert; failed runs converted to empty heaps must not pass | R36 refused capture route |
| `AlgorithmProjectionGuards` computed argument | `Ap(if(true,R.Algorithm,0),8)` fails as `notAnAlgorithm "param(f)"` | Result boundary / independent CALLABLE projection; reject an unrelated callee failure | N37 wrong callee |

Contracts are `docs/design/language-rules/call-by-need.md` (NEED-02, result boundary, META and
argument views), `sequences-lists-and-calls.md` (value boundaries, spread, collectors), and
`AGENTS.md`'s internal sequence-join rule. Exact source/fixture references are in each final record.

The four remaining zero-cell observations using `finalHeap` have successful-value or positive-cell
companions for the exact fixture. The helper remains a lossy convenience, never independent
evidence of success. CategoryOnly / Partial / Comparable / HostOnly policies are unchanged; the
two new callee payload checks are Lean-only precision. S4's three broad exceptions remain unchanged.

Final evidence is under `artifacts/validation/q68-current-guard-audit/reviewer/`:

- `source-manifest.json` and `sources/` fix the census to reviewed bytes. Candidate records contain
  source identities, assertion/input units, fixture references, contract sources, dispositions,
  required observations and wrong outcomes. `failure-guard-review.json` and `shared-observers.json`
  cover the supplementary observer inspection. Search misses are not counted as verified successes.
- `validate.py` is the serial **V1** plan: affected `CoreTests` and `KatLangArityLaws` builds;
  fresh test-project build and focused .NET tests (Lean-reading/documentation fixtures, builtin
  payload, differential observations, generated-artifact freshness/fidelity, parser grouping and
  the reduce-accumulator twin); S4 controls; original and reviewer contrast guards; all 25 original
  controls reconstructed against final source and 12 new controls. `validation.json` records actual
  exit codes, TRX discovery/execution counts, commands, expected assertion locations and logs.
  Negative controls must fail only at the intended assertions. Other failures, timeouts and
  unavailable checks block closure. This is assertion sensitivity, not production mutation testing.
  The first development build rejected the reviewer's initial internal-join count 2; the model's
  documented one-constructed-value count 1 corrected that expectation before the final run
  (`reviewer/development/first-count-check.*`). This was a test expectation error, not a runtime defect.
- Frozen snapshots include HEAD, branch, index/worktree diffs, pending hashes, stashes, worktrees
  and all six live Constitution records. External/local six-record backups and byte-exact reversal
  checks precede the dated Constitution review correction. Earlier S4 and implementer evidence
  remain historical; independent final results are in the reviewer report.

V1 stays appropriate: isolated test precision using existing helpers, with no language, evaluator,
generator, API or shared test-helper change. The other five Lean targets and full .NET suite remain
outside this plan. Final Q-68 status is **CLOSED against the replacement current inventory**, with
review repairs and required final checks recorded; the historical FORM-05 list was not reconstructed.
