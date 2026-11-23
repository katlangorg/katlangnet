# Differential observations (Q-67)

FORMAL-06 is unchanged: successful observations are `ok raw=... n=...`;
failures are `err CATEGORY`. Raw structure, root emitted count and the
innermost semantic category remain the neutral correspondence contract.
Finite generated corpora are bounded evidence, not an evaluator refinement proof.

## Routes and observations

| Route | Before Q-67 | Supplementary evidence |
| --- | --- | --- |
| C# plain / counted | Success/failure, exact value; failure category | Selected structured fields on every failed observation, including internal ASTs |
| Public sync engine | Value/count/display on direct success; skipped direct failures | Every surface case executes the engine; parse diagnostic codes, dynamic failure phase, category and shared payload; root output absence remains NoProgramOutput |
| Lean plain / counted | Same value, counted root count, category; internally cross-checked | Separate `errorObs` cross-checks supported payloads on both routes |
| Explorer generated expectations | C#-observed neutral expectations | Additional payload guards derived from the same C# observation; ordinary successful cases incur no extra runs |
| Canonical specification | Handwritten value/count/category/display | Ten independently handwritten payload expectations checked by C# and generated Lean guards |
| Generic / optimized / forced async | Corpus value/count/category and accounting equivalence | Existing corpus suites also compare shared payloads, with no extra executions |
| Public async | Existing API and route suites | Canonical payload cases additionally check exact failure phase/category/payload against the direct evaluator |
| Effects | Independent C# exact event logs and Lean heap guards | Missing ordinary-failure root/callback/loop terminality witnesses added on six routes |
| Resources | C# host policy, separate bounded-limit suites | Unchanged; no Lean budget or cross-strategy stack-depth requirement |

`MetamorphicErrorDetail`, shared as source between the tests and standalone fuzz
target, owns the C# category and supplementary field policy. `DifferentialErrors`
maps it to the existing Q-67 records without changing their contract.
Five generated observation artifacts use both `LeanObsTemplate.SharedDefinitions`
and `AppendErrorGuard`: `lean/LanguageSpecCases.lean` (`LanguageSpecLeanArtifactTests`),
`lean/SemanticExplorerCases.lean` (`SemanticExplorerLeanArtifactTests`),
`lean/CoreTests/HostParentDifferential.lean` (`HostParentDifferentialTests`),
`lean/CoreTests/SemanticGeneratedCases.lean` (`SemanticGeneratedLeanArtifactTests`) and
`lean/CoreTests/ModuleDifferential.lean` (`ModuleDifferentialTests`, § Module programs). `obs`
retains its original contract; `errorObs` is separate. Only the host-parent
artifact also emits the KL-07 `structural` guards (§ Lean `kl-struct-v1`
exporter). On supported failures, `errorObs` runs the plain and counted Lean
evaluators again. Each `structural` guard on a host-parent success runs the plain
evaluator once. The first four artifacts also emit the KL-06 cache observation
(`CacheObservationDefinitions`): the host-parent artifact guards it on every
case, the other three on a four-case pilot each (§ Cache publications). The
hand-maintained `lean/CoreTests/PlannedLoopPublications.lean` embeds the same
definitions for the F01 loop cases (`PlannedLoopPublicationTests` checks its text).
A sixth generated artifact, `lean/CoreTests/PlannedLoopTempFamily.lean`
(`PlannedLoopTempFamilyTests`, § Planned-loop temp family), emits the shared and
cache definitions and adds its own tick observation; it has no failing case, so
it emits no `errorObs` guard.
The public engine adds one run only on failures and parse rejections where it
was previously skipped. Q-67 changed no production evaluator code and no
normal-run overhead. The F01 decision of 2026-11-21 added one production hook,
the planned loop's publication report (§ Cache publications).

## Complete constructor policy

SEM-2A adds supplementary metamorphic observations without changing FORMAL-06's
neutral text, Q-67's constructor policy, seed decoding or replay fingerprints.
In-process structural comparisons use `Result.ValueComparer`. Durable comparisons
require canonical `kl-struct-v1` identities: an ASCII, length-framed post-order
table with distinct number/Boolean/string/sequence/list tags, child counts and
references to earlier nodes. Definitions are interned by content so sharing does
not affect identity. Numbers follow Decimal128.Equals equality classes (quantum
and zero sign ignored, NaN reflexive); strings escape exact UTF-16 code units,
including unpaired surrogates. Legacy-only successes cannot establish structural
equality and raise a harness error. The decoder validates lengths before allocating.

Real structure-projecting surfaces retain ordinary completed values and their
versioned identities. Legacy neutral text is omitted, never truncated, beyond
4,000,000 UTF-16 units; typed equality remains available. Structural diagnostics
are bounded escaped previews and are never compared. Root emitted counts remain
a separate facet. No run-local references or evaluator state are retained.

The declared `StrictSameSource` error policy compares the supported Q-67 fields
of innermost errors only when both failing surfaces expose `StructuredError`.
Optimizer parity, entry-point parity and same-source budget laws declare it;
cross-source transformations retain the normalized policy. A public surface
without structured errors records that strict comparison was not exercised.
Missing claimed structural/error data is a harness defect rather than equality
of two absent fields. The host-parent corpus uses the Lean-side `kl-struct-v1`
exporter for successful values (KL-07 pilot, § Lean `kl-struct-v1` exporter
below). The other three generated corpora retain their existing value, count
and error observations.

“Partial” means a Lean field or a public C# field (a rendered description or
name) is deliberately excluded, so only the named fields are shared; C#-internal
diagnostic metadata (signatures, provenance, blame flags) has no Lean
counterpart and never makes a policy partial. A constructor tag is also
checked for comparable/partial cases. In particular `badArity`, ordinary
counted arity, branch input arity and branch output arity stay distinct.

| Lean Error | C# EvalError | Neutral category | Policy; shared fields | Excluded fields / reason |
| --- | --- | --- | --- | --- |
| arityMismatch | ArityMismatch | arity | Comparable: expected, actual | Diagnostic signature, accepted-arity facts and implicit provenance |
| arityMismatch | VariadicArityMismatch | arity | Partial: expected minimum, actual | Callee display name; minimum/count normalization is the binder's existing contract |
| badArity | BadArity | arity | Comparable: distinct fieldless tag | No count payload exists |
| branchArityMismatch | BranchArityMismatch | arity | Partial: distinct tag, expected, actual | Rendered algorithm path/name |
| branchOutputArityMismatch | BranchOutputArityMismatch | arity | Partial: distinct tag, expected, actual | Rendered algorithm path/name |
| unknownName | UnknownName | unknownName | Comparable: name | None |
| unknownProperty | UnknownProperty | unknownProperty | Partial: property name | Rendered object description |
| notPublicProperty | NotPublicProperty | notPublicProperty | Partial: property name | Rendered object description |
| localOnlyProperty | LocalOnlyProperty | localOnlyProperty | Partial: property name, exposure kind | Object description; Lean embeds required names in exposure, C# has optional diagnostic RequiredParameters; no new ordering/availability contract imposed |
| ambiguousOpen | AmbiguousOpen | ambiguousOpen | Partial: name | Rendered provider descriptions |
| duplicateProperty | DuplicateProperty | duplicateProperty | Comparable: name | None |
| unresolvedImplicitParams | UnresolvedImplicitParams | unresolvedImplicitParams | Comparable: ordered parameter names | Implicit diagnostic provenance |
| typeMismatch | TypeMismatch | type | Category-only | Human message |
| noMatchingBranch | NoMatchingBranch | branch | Category-only | Rendered/synthesized algorithm name |
| notAnAlgorithm | NotAnAlgorithm | notAnAlgorithm | Category-only | Human description |
| illegalInOpen | IllegalInOpen | illegalInOpen | Category-only | Human reason |
| badOpenForm | BadOpenForm | badOpenForm | Category-only | Human reason |
| illegalInEval | IllegalInEval | illegalInEval | Category-only | Human reason |
| badIndex | BadIndex | index | Comparable: fieldless | Neither model carries the rejected index |
| divByZero | DivByZero | div0 | Comparable: fieldless | None |
| demandCycle | DemandCycle | demandCycle | Comparable: fieldless | No heap address is public semantics |
| duplicateBranchPattern | DuplicateBranchPattern | duplicateBranchPattern | Comparable: fieldless | None |
| explicitParamsRequireOutput | ExplicitParametersRequireOutput | explicitParamsRequireOutput | Comparable: fieldless | None |
| missingOutput | MissingOutput | missingOutput | Comparable: fieldless | C#-internal selected-member blame flag (diagnostic metadata, like ArityMismatch's signature) |
| spreadMissingOutput | SpreadMissingOutput | spreadMissingOutput | Comparable: fieldless | None |
| withContext | WithContext | Inner category | Strip wrapper and classify inner | Diagnostic frames, text, spans |
| None | EvaluationDepthExceeded | evaluationDepthExceeded | Host-only | Limit |
| None | EvaluationStepLimitExceeded | evaluationStepLimitExceeded | Host-only | Limit |
| None | EvaluationStackExhausted | evaluationStackExhausted | Host-only | Host stack policy |
| None | CollectionSizeLimitExceeded | collectionSizeLimitExceeded | Host-only | Limit, requested size |
| None | MaterializationLimitExceeded | materializationLimitExceeded | Host-only | Limit |
| None | StringSizeLimitExceeded | stringSizeLimitExceeded | Host-only | Limit, requested size |
| None | StringMaterializationLimitExceeded | stringMaterializationLimitExceeded | Host-only | Limit |
| None | DisplayLengthLimitExceeded | displayLengthLimitExceeded | Host-only | Limit |
| None | AstDepthLimitExceeded | astDepthLimitExceeded | Host-only | Limit |
| None | AstCycleDetected | astCycleDetected | Host-only | Malformed host graph |
| None | ModuleRegionMaterializationFailed | moduleRegionMaterializationFailed | Host-only | Source diagnostics/import provenance |

The fixed/variadic correspondence follows `Evaluator.NeedCallArityError` and
Lean `needCardinalityGate`: both count mandatory top-level supplied slots,
not flattened captures. Branch counts follow the two validation gates.
Ordered names follow `Algorithm.params`; exposure kinds follow the existing
`LeanAstEncoder.EncodeExposure` mapping. Messages and paths have deliberately
different representations and are not normalized into invented semantic fields.
Twenty-eight independent constructor-projection goldens check every shared field and all category-only decisions in both languages, including constructors absent from validated-source executions. These are projections of error values, not evaluator runs or handwritten source translations. All 37 C# variants have a reviewed policy pin; `DifferentialErrors.Observe`
names every variant with no catch-all arm, so a new C# variant fails the test
build (`CS8509`) until it is classified. Lean's projection has no wildcard, so
new constructors require a deliberate decision. Independent policy tests reject
payload downgrades.

## Lean `kl-struct-v1` exporter (KL-07 pilot)

The neutral text writes strings between unescaped quotes, so the list of the two
strings `a` and `b` and the list of the one host-built string `a', 'b` both read
`L['a', 'b']`, although `Result.ValueComparer` tells them apart (KL-07). Only
host-built strings can collide: a source literal cannot hold the quote, and
`.string` on a number cannot produce one (STR-03). On 2026-11-18 the owner chose
a Lean exporter of the existing `kl-struct-v1` format, introduced one corpus at a
time, over escaping quotes in the neutral text. The neutral text (FORMAL-06) is
unchanged.

**Exporter.** `lean/CoreTests/StructuralIdentity.lean`
(`StructuralIdentity.encode : Result → Option String`) is maintained test code;
`lean/KatLang.lean` does not use it. It renders a completed Lean value as text
byte-identical to `MetamorphicStructuralIdentity.Encode` on their shared
domain. A Lean atom is an `Int`, written as its Decimal128 equality class: `0`,
or `[-]<coefficient>e<exponent>` with trailing coefficient zeros moved into the
exponent, so Lean `1200` and C# `1200` / `1200.00` all read `12e2`. A Lean string
is a sequence of Unicode scalar values: a scalar outside the BMP contributes its
UTF-16 surrogate pair, and the length counts UTF-16 code units. Definitions are
interned by their text, with ids in left-to-right post-order of first completion,
so sharing never shows. A value holding a call reference or argument view has no
identity (`none`), just as the C# encoder refuses one.

**Evidence.**

- *Hand-reviewed examples.* The module's guards pin hand-written texts for:
  the quote collision (both lists), `()` against `[]`, Booleans, numbers and
  strings side by side, a backslash, printable ASCII, a line feed and a tab, BMP
  and non-BMP characters, nested lists and sequences, equal subtrees with
  different sharing, repeated values, negative integers, zero, an integer with
  trailing decimal zeros, and multi-digit ids. Boundary checks on the helpers
  cover the printable range, DEL and the end of the BMP.
  `StructuralIdentityExamples` holds the same examples as C#-built values with
  the same texts. `StructuralIdentityExporterTests` checks that the C# encoder
  gives each text, including the C#-only fractional class (`1.5` and `1.50` read
  `15e-1`); that two examples have equal texts exactly when their values are
  equal; and that the Lean module guards exactly the texts of the 25
  Lean-comparable examples.
- *Cross-check against the C# encoder.* The generated
  `lean/CoreTests/HostParentDifferential.lean` writes each Lean-comparable
  example as a Lean literal and guards that the exporter's text equals the C#
  encoder's text of the C# value. On each successful host-parent case (82 of 113),
  a `structural` guard compares the exporter's text of the Lean plain run's value
  with the C# encoder's text of the typed C# value. `HostParentDifferentialHarness.Observe`
  encodes `counted.Value.Value` directly: rebuilding the value from neutral text
  would lose the distinction under test. The `obs` (value and emitted count),
  `errorObs` and cache guards are unchanged, including KL-06's failed-run guards.
  No C#/Lean disagreement was found.

**Where it is used.** Only in the host-parent corpus. Structural guards are not
emitted for `LanguageSpecCases.lean`, `SemanticExplorerCases.lean` or
`CoreTests/SemanticGeneratedCases.lean`.

**KL-07 acceptance.** HP-17a and HP-17b put the two-string list and the
one-string list in a host property that is read through an opened block. Both
observe `ok raw=L['a', 'b'] n=1`, but their identities are
`kl-struct-v1:3:t1:at1:bl2:0,1,;` and `kl-struct-v1:2:t6:a', 'bl1:0,;`.
`HostParentDifferentialCorpus.NeutralCollisionPairs` declares the pair, and the
generated artifact guards that neither Lean value has the other case's
identity. On 2026-11-20 each program was substituted for the other in a scratch
copy of the artifact. Each copy failed exactly two guards, both on the
substituted case: its structural pin and its cross guard. Its neutral `obs` guard
and its cache guards still passed.

**Coverage claim.** The exporter establishes structural equality of completed
values that both engines can represent. It does not cover:

- Decimal128 representation (the spelling `1.0` against `1.00`): neutral text
  and C#-side checks keep that;
- unpaired UTF-16 surrogates: a Lean `String` cannot hold them, see the Lean
  string boundary in `tests/KatLang.Tests/LeanAstEncoder.cs` (`Quote`);
- host-visible object identity (as in KL-01): the format deliberately gives
  equal subtrees the same text, whatever their CLR identity.

**Measurements** (2026-11-20; Lean 4.35.0 and Lake 5.0.0; Windows 11 with 20
logical processors). The baseline is the landed KL-06 output at `36986d89`.
Rebuild command, from `lean/`: delete the build outputs of
`CoreTests.HostParentDifferential` under `.lake/build` (`.olean`, `.ilean`,
`.trace`, their hashes, and the IR `.c`, `.c.hash` and `.setup.json`), then run
`lake build CoreTests.HostParentDifferential`. Every dependency (`KatLang`, plus
`CoreTests.StructuralIdentity` for the pilot) stays built and cached, which is
the situation after a change to the artifact alone. Three runs were made on each
side. A supplementary run elaborated scratch copies of both files with
`lake env lean`, interleaved over four rounds.

| | Baseline | Pilot | Delta |
| --- | --- | --- | --- |
| Generated file | 166,029 bytes | 176,933 bytes | +10,904 (+6.6%) |
| Cases (successful) | 111 (80) | 113 (82) | +2 (+2) |
| `#guard` lines | 435 | 552 | +117: 82 structural, 25 examples, 2 KL-07 cross guards, 8 for HP-17a/b |
| Module rebuild, wall-clock median | 9.62 s | 10.97 s | +1.35 s (+14%) |
| Module rebuild, Lake-reported median | 8.7 s | 9.9 s | +1.2 s |
| Interleaved scratch elaboration, median | 8.78 s | 10.01 s | +1.24 s (+14%) |
| New exporter module (11,166 bytes), built once | — | 0.8 s (Lake) | +0.8 s |

The dependent `KatLangArityLaws/MayCaptureCallsCorpus.lean` gains two gate
guards (HP-17a/b). It imports the host-parent module but evaluates no structural
guard. The target rebuild and the exporter's first build together suggest an
estimated 2 s of extra work on this machine. The Lean CI job has a 30-minute
timeout.

**Estimates for the other three corpora (not migrated).** These are estimates,
not a migration. One structural guard was added after each successful `obs` guard
in scratch copies outside the tree. The expected text was derived from the
neutral raw text, which is unambiguous in these source-built corpora; the same
derivation reproduced all 80 C# identities of the host-parent baseline exactly.
Each copy was elaborated with `lake env lean` against the built oleans, over two
alternating rounds; the table gives the mean. A real migration would add the C#
generator changes and possibly an example section, and Lake's C emission adds a
little to elaboration time. The scratch guards call a longer function name, so the
byte estimates run about 2 bytes per guard high. Every added guard passed in all three copies.

| Corpus | Successful cases | File before | Estimated added bytes | Elaboration before | Estimated delta |
| --- | --- | --- | --- | --- | --- |
| `LanguageSpecCases.lean` | 369 | 318,639 | +39,239 (+12%) | 10.1 s | +2.4 s (+24%) |
| `CoreTests/SemanticGeneratedCases.lean` | 481 | 663,676 | +64,531 (+10%) | 19.0 s | +3.6 s (+19%) |
| `SemanticExplorerCases.lean` | 2,041 | 1,042,737 | +173,195 (+17%) | 32.0 s | +10.2 s (+32%) |
| All three | 2,891 | 2,025,052 | about +277 KB | 61.2 s | about +16 s |

Extending the exporter to these corpora is a separate owner decision, to be made
on these measurements. In any later migration, the language specification's
hand-written expectations stay an independent oracle. Logs and scratch tools are
in `artifacts/validation/kl-struct-lean-pilot/`.

## Cache publications (KL-06 and its pilots)

The zero-argument property cache is observable semantics, and what a run
PUBLISHED is a final-state observation that the neutral text does not carry.
KL-06 compared it on the host-parent corpus only, on success and on failure. On
2026-11-20 the observation was extended to one small pilot in each of the three
source corpora. Their neutral, payload and count guards are unchanged.

**Observation.** C#: `ZeroArgPublicationObserver` runs the program on three
cache-recording routes — generic, optimized and the genuinely suspending async
twin — over the run-scoped publication law. The two synchronous routes compare
entry counts per binding name. The async route checks the total and that all
access used the async interface. All three check that every owner was released. Lean:
`publicationsOf`, `publications`, `cacheEntries` and `cacheTotal`, one text
(`LeanObsTemplate.CacheObservationDefinitions`) emitted into the four cache-observing artifacts;
each cache guard runs its program once.

**What a publication is (F01, owner decision Option A, 2026-11-21).** A
publication is counted when a zero-argument property first establishes a
reusable value in its owning invocation. Each loop round is a fresh invocation
of the step, so each round that successfully establishes a step property's value
publishes it once, whether the property is local-only or exported.

- *The finding.* The planned loop keeps the value of a planned step property in
  the round's frame slot and never asks the property cache. The optimized route
  therefore reported no publication for it, while the generic route and Lean
  reported one per round. The values agreed, so no neutral guard could see it:
  `Step(n, total) = { Next = n + 1 ⏎ Next, total + Next }` /
  `Step(0, 0).repeat(3)` is `S[3, 6]` on every route, with `Next` published
  three times by generic C# and Lean and never by optimized C#. Since the
  inner-property lifetime rule the same holds for an exported step property
  (`T = 5`).
- *The decision.* The frame storage stays. A successful store of a frame slot
  counts as a successful store of the cache does, under the property's own
  binding name, when the slot is first established in a round. A later read in
  the round adds nothing. A qualifying zero-supply call `T()` that finds the
  slot empty establishes it; a later `T()` still executes fresh and adds
  nothing. An undemanded property and a calculation that fails before it
  establishes its value publish nothing. A later ordinary failure keeps what
  was published.
- *The mechanism.* `LoopRunFrame.EstablishTempSlot` is the one place a slot is
  stored. Both callers reach it only for an empty slot and only after the
  property's calculation succeeded. It reports the store to the run's
  `IPlannedLoopPublicationObserver`, with the declared binding: an alias step
  property shares its target's slot, so its target is reported, as on the
  generic route. Only a harness cache implements the interface (the recorder of
  `ZeroArgPublicationObserver`), so an ordinary run pays one null check per
  established slot, and the cache's own counters still count its own store
  only. The count comes from actual stores: after a handover the planned rounds
  are frame-slot stores and the generic rounds are cache stores, and the round
  that handed over is never evaluated again. The async route pins the generic
  strategies, so it has no frame slot.
- *Lean.* The model is unchanged. A round binds a fresh context, so its entries
  already had their own keys.
- *Pins.* `PlannedLoopPublicationTests` holds 17 source programs with
  hand-written expectations and `lean/CoreTests/PlannedLoopPublications.lean`
  the encoding of the same elaborated programs with their neutral and cache
  guards (hand-maintained; the C# class checks the module text). The module
  embeds the shared observation definitions and the five state guards verbatim.

| Case | Result | Published |
| --- | --- | --- |
| Local-only property read twice per round (the F01 witness) | `S[3, 6]` | `Next=3` |
| Exported constant property | `15` | `T=3` |
| Two properties, one reading the other | `39` | `A=3 B=3` |
| Call, then read; read, then call; two calls | `926` each | `A=3` each |
| Exported property called, then read | `252` | `E=3` |
| Alias property | `14` | `A=3`, `B=0` |
| `while` (the condition row establishes the slot) | `2` | `Next=3` |
| `while`, a state row reads `T = n * 2` (the original F01 demand witness) | `S[3, 6]` | `T=3` |
| Its twin, `acc + n * 2` written in place of `acc + T` | `S[3, 6]` | `T=0` |
| Undemanded property | `6` | `Unused=0` |
| Calculation fails in the first round | `err div0` | `Bad=0` |
| Calculation fails in the second round | `err div0` | `T=1` |
| Failure in a round after its publication | `err div0` | `T=2` |
| Failure after the loop | `err div0` | `T=3` |
| Handover to the generic strategy after one planned round | `S[S[], 3]` | `T=3` (1 frame slot, 2 cache stores) |

For every case the C# test reads the planner diagnostics of the very run it
compares: the loop was entered planned, every row and step property is a plan,
and the expected entries came from frame slots. It also requires the generic
publication order and the generic step, checkpoint, depth and materialization
counts of the optimized route, and that an unobserved optimized run has the
observed run's result and counts while its cache stores nothing for a planned
property. Without the report all 13 cases that then published failed with "generic and
optimized routes published different cache entries" (measured 2026-11-21 before
the report was added). The pilots, the census numbers and the corpus guards
below are unchanged by this decision; widening them stays a separate decision.

The demand witness and its twin (added 2026-11-22) run four planned rounds each:
a round reads its condition row first, so the round whose verdict is false forms
no state row and does not demand `T`. They give the same value, so only the
publication guards tell them apart, on the generic and optimized routes and in
Lean. The physical insertions into the run cache stay route-specific: three on
the generic route for the witness, none on the optimized route, whose frame
slots hold the witness's three values, and none for the twin
(`OptimizedRoute_KeepsItsFrameStorage_AndObservingItChangesNoResultOrCharge`).

**Three states, never written alike.**

| State | C# | Lean | Guard |
| --- | --- | --- | --- |
| No observation | no expectation (`CachePublicationState.NotObserved`) | an unselected program has no observation expression; if an observed run is incomplete or still has an active owner, the observer returns `none` | no program guard for an unselected case; an observed case requires `some` |
| Completed, empty cache | total 0 | `some []` | `cacheTotal … == some 0`, plus `cacheEntries … "N" == some 0` for a watched name |
| Completed, with entries | total n > 0 | `some cache` | one `cacheEntries` guard per name and one `cacheTotal` guard |

A run completes in success or in failure: a failed run keeps what its successful
owners published before the failure, and a failed owner publishes nothing. Five
hand-written guards on `publicationsOf` in each artifact pin the states on
synthetic outcomes and states (no evaluator run): an incomplete outcome and an
active owner give `none`; an empty state gives `some 0` after success and after
failure; a failed outcome over a one-entry state gives `some 1`.

**Host-parent corpus.** Every one of its 113 cases keeps its cache guards (196
named, 8 of them on the 31 failing cases; HP-16a–c are the failed-run witnesses).
Its three coverage floors had fallen behind the corpus (102 comparable, 96
pre-wired, 181 named guards on successes) and are now the current counts: 113,
103 and 188. (Since EXPORTED-DETACHED, November 2026, the corpus has the HP-18
family: 134 cases, 224 named guards, 24 of them on the 46 failing cases, and
floors 134, 124 and 200.) `CoverageDropControl_LosingOneUnitOfAMetricFailsTheRatchet` takes
one unit of exactly one metric away in memory — HP-16a removed; HP-02f run on a
parent-free program; HP-10g no longer watching its unpublished `Large` — and
requires the ratchet to report that metric alone. Against the old floors all
three controls failed (each drop was absorbed), so a control also fails whenever
a floor is stale. KL-04's absent-versus-empty exact-owner pair (HP-05j/k) reaches
Lean through `LeanAstEncoder`; `lean/CoreTests/NameOwnership.lean` now pins the
same pair on hand-written terms (`unownedCapturedMember`): absent depths are
refused, an explicitly empty list is accepted, and a listed requirement that no
owner satisfies is refused with or without a depth, both at `memberAccessible?`
and through the structural read `Box.L`.

**Pilots.** Four existing cases per corpus, one per class. No corpus case was
added, so no program text and no other artifact changed.

| Corpus | Success with entries | Success, empty cache | Failure after a publication | Failure before any (control) |
| --- | --- | --- | --- | --- |
| `SemanticExplorerCases.lean` | `special__listSpreadConcat`: `A=1 B=1` | `root__p12`: nothing | `indexBig__p12`: `err index`, `x=1` | `special__repeatedNameFailedThenValue`: `err div0`, `Bad=0` |
| `LanguageSpecCases.lean` | `property-value-boundary`: `Coordinates=1` | `expanded-map-calls-may-skip-indexed-arguments`: `L=0` | `index-out-of-range`: `err index`, `x=1` | `if-spread-builds-values-before-branch-selection`: `err div0`, `Risky=0` |
| `CoreTests/SemanticGeneratedCases.lean` | `sem2b/v2/sys/cache/0`: `v1=1` | `sem2b/v2/sys/cache/2`: nothing | `sem2b/v2/sys/select-fail/3`: `err index`, `v1=1` | `sem2b/v2/sys/cache-fail/0`: `err div0`, `v1=0` |

A name at zero is watched and unpublished. Where the expectation comes from
follows each corpus's own oracle:

- *Language specification.* `SpecCase.ExpectedCachePublications` is hand-written
  on the canonical case. `LanguageSpecRunnerTests.Case_MatchesCanonicalCachePublications`
  requires it of C#; the generated guards require it of Lean.
- *Semantic explorer and SEM-2C.* A reviewed table in the artifact test
  (`CachePublicationPilot`). Generation observes the case and refuses a table
  entry C# does not meet, so a guard never pins an unreviewed number.
- *SEM-2C transformation members.* An alpha-rename renames the entries, so each
  pilot case's member (four alpha-rename members; none of the four cases has a
  reorder member) guards its published TOTAL, which C# requires to equal the
  base member's.

`CachePublicationPilotTests` pins the exact guard lines by hand, that each pilot
covers the four classes, that no other program of an artifact has a cache
guard, and that the C# observer rejects a wrong expectation.

**Census (2026-11-20, scratch run, not part of the suite).** Every
Lean-comparable program of the three corpora was observed on the C# routes and by
a scratch Lean file importing the built corpus modules.

| Corpus | Programs | Success with entries | Success, empty | Failure with entries | Failure, empty | Entries |
| --- | --- | --- | --- | --- | --- | --- |
| Semantic explorer (surface and internal-node) | 2,570 | 834 | 1,207 | 154 | 375 | 1,171 |
| Language specification | 477 | 151 | 218 | 13 | 95 | 242 |
| SEM-2C base members | 264 | 105 | 82 | 28 | 49 | 194 |
| SEM-2C transformation members | 414 | 191 | 103 | 52 | 68 | 363 |
| All | 3,725 | 1,281 | 1,610 | 247 | 587 | 1,970 |

C# and Lean published the same entries under the same names on all 3,725
programs, and each C# route gave the corpus's own neutral observation. The 19
internal-node programs declare no property and publish nothing. Every member of
the 264 SEM-2C cases published as many entries as its base member. The names
include the front end's hoisted deconstruction source (`$deconstruct$0`), which
both sides publish under that name. The census is evidence that a full
migration would pass today; it is not a migration, and nothing in the suite
re-runs it.

**Coverage after the pilots.** Guarded programs: host-parent 113 of 113; semantic
explorer 4 of 2,570; language specification 4 of 477; SEM-2C 4 of 264 base
members by name plus 4 of 414 members by total. Every other program of the three
source corpora has no cache observation.

**Mutation sensitivity (2026-11-20).** Lean side, on scratch copies outside the
tree, elaborated with `lake env lean`. For each source corpus the copy holds the
artifact's header and shared definitions and its pilot cases (plus the one
program a substitution needs); the host-parent artifact was mutated whole. Every
unmutated copy elaborated with no failing guard. The cells count failing
`#guard`s.

| Mutant | Explorer | Specification | SEM-2C | Host-parent |
| --- | --- | --- | --- | --- |
| The entry kept after the failure is guarded at 0 | 1 | 1 | 1 | — |
| The pre-publication control's total is guarded at 1 | 1 | 1 | 1 | — |
| The empty success's total is guarded at 1 | 1 | 1 | 1 | — |
| The failure-after-publication case runs another corpus program with the same neutral observation that publishes nothing | 2 | 2 | 2 | — |
| `publicationsOf` reports an empty cache for a failed run | 3 | 3 | 4 | 7 |
| `publicationsOf` reports an empty cache where it has no observation | 2 | 2 | 2 | 2 |
| `publicationsOf` reports no observation for a failed run | 6 | 6 | 8 | 41 |

- A wrong number fails exactly the guard that holds it; the case's other guards
  still pass.
- The substituted program (`special__firstEmpty`, `list-index-out-of-range`,
  `sem2b/v2/seed/5EED2B000004/8`: each `err index` with an empty cache) fails
  the case's named and total cache guards while its `obs` and `errorObs` guards
  still pass: the neutral observation cannot see the difference.
- An observer that drops a failed run's entries fails the one-entry state guard
  and the cache guards of every failure that follows a publication (in SEM-2C
  also the member's total; in the host-parent artifact HP-14i, HP-16a and
  HP-16c).
- An observer that writes a missing observation as an empty cache fails only the
  two `isNone` state guards. No run of a corpus program reaches that state, so
  those hand-written guards are what keeps `none` apart from `some 0`.
- An observer with no observation on failure fails both failure state guards and
  every cache guard of a failing case (host-parent: 31 totals and 8 named).

C# side: `PilotCase_CacheObserverRejectsWrongReviewedExpectations` gives each of
the 12 pilot cases a wrong reviewed expectation — an entry under a name the run
never published, one entry too many, an empty cache for a run that published
(with and without the watched names) — and another neutral observation. For
every nonempty pilot it also moves a publication to another name while keeping
the total fixed. Each check requires the observer to identify the corpus and
case. The explorer and SEM-2C use the observer during generation. The
specification checks C# in its runner and emits its hand-written oracle directly.
`FailedRun_KeepsWhatWasPublishedBeforeTheFailure_AndNothingAfter` observes one
program text with its two rows swapped (`X`, then `1 / 0`; `1 / 0`, then `X`).
The host-parent coverage-drop controls are described above.

Model mutants: two mutants of the Lean model's `memberAccessible?` were built in
scratch workspaces outside the tree (`KatLang`, then `CoreTests.NameOwnership`
and `CoreTests.HostParentDifferential`; about 40 s each). Treating an explicitly
empty exact-owner list as absent fails exactly one guard of
`NameOwnership.lean`, the new `unownedCapturedMemberIsAccepted (some [])`, and
the four generated guards of HP-05k: until now only that encoder-derived case
told the two apart. Treating absent depths as an empty list fails
`unownedCapturedMemberIsRefused none`, nine older guards of that module and the
fifteen generated guards of HP-05d, e, h, i and j.

Three mutants of the Lean model's publication law
(`evalZeroArgPropertyAccessCounted`) were built the same way against the four
regenerated artifacts:

| Model mutant | Explorer | Specification | SEM-2C | Host-parent |
| --- | --- | --- | --- | --- |
| A successful owner stores no entry | 5 | did not finish | 6 | 100 or more |
| A failed owner stores an entry | 2 | 2 | 3 | 17 |
| A failed owner stays active (Lean then has no observation: `none`) | 2 | 2 | 3 | 18 |

In the explorer and SEM-2C artifacts every failing guard is a pilot cache
guard: none of their neutral, payload or count guards (2,917 and 829 before the
pilots) fails under any of the three mutants. Under the first mutant the
specification module stopped in Lean's interpreter with a deep-recursion error
before reporting a guard. Its log leaves the case and its termination behaviour
undetermined. The host-parent module stopped at Lean's limit of 100 errors (cache guards,
and five `obs` and five `structural` guards). Under the other two, the failing
guards of the three source corpora are exactly the pre-publication controls'
(named and total, and the SEM-2C member's total); the host-parent failures are
cache guards of failing cases. No mutant of the C# evaluator was built: the
shared checkout's production code was left untouched, so on the C# side the
evidence is the reviewed expectations, the route agreement and the census.

A separate review exercised the 16 selected source programs and HP-16a–c,
using their generated definitions and guards together in a small Lean module.
Every guard passed against the current model. The same successful-owner mutant
failed four specification guards in this module, the named and total guards
on `Coordinates` and `x`. Across the 19 programs, suppressing a successful
publication failed 19 cache guards, publishing on failure failed 12, and
leaving a failed owner active failed 13. All their result and error guards
continued to pass. Replacing just the expected name after publication in
each of the four corpora failed exactly those four named guards. The correct
totals still passed.

**Cost (2026-11-20; Lean 4.35.0 and Lake 5.0.0; Windows 11 with 20 logical
processors, under other load that day: absolute times are about twice those of
the KL-07 table above).**

| Artifact | Bytes before | Bytes after | `#guard` lines | Added guards |
| --- | --- | --- | --- | --- |
| `CoreTests/HostParentDifferential.lean` | 176,933 | 178,246 (+1,313) | 552 → 557 | 5 state guards (`publicationsOf` split out of `publications`; its 113 cases unchanged) |
| `LanguageSpecCases.lean` | 318,639 | 322,825 (+4,186) | 521 → 535 | 5 state, 8 on the pilot cases, 1 count |
| `CoreTests/SemanticGeneratedCases.lean` | 663,676 | 667,901 (+4,225) | 829 → 846 | 5 state, 7 on the pilot cases, 4 member totals, 1 count |
| `SemanticExplorerCases.lean` | 1,042,737 | 1,046,592 (+3,855) | 2,917 → 2,931 | 5 state, 8 on the pilot cases, 1 count |

- *Regeneration.* One flagged `dotnet test --no-build` run per artifact, wall
  clock including test-host start: host-parent 12–17 s, language specification
  14–18 s (it also rewrites the two prompt blocks, which did not change), SEM-2C
  23–26 s, semantic explorer 26–40 s. The cache observer runs three routes per
  selected program, including the four SEM-2C alpha-rename members. The
  specification runs those routes in its C# runner. Each artifact was generated twice and the two generations
  were byte-identical. An incremental build of the test project took 49–76 s.
- *Lean elaboration.* Baseline and regenerated copies were elaborated with
  `lake env lean` outside the build directory, interleaved over three rounds.
  Medians, baseline → pilot: host-parent 23.5 → 20.6 s, language specification
  18.6 → 17.3 s, SEM-2C 31.5 → 31.5 s, semantic explorer 49.0 → 47.8 s. Rounds
  differed by up to 2× with the machine's load. The SEM-2C timing used an
  earlier 667,913-byte pilot with the same guard count. These measurements
  cannot establish a marginal cost for the final pilots.
- *Dependents.* No program text changed, so
  `KatLangArityLaws/MayCaptureCallsCorpus.lean` was not regenerated; it imports
  the corpus modules and is rebuilt with them.
- *Real builds.* `lake build` of the four affected targets, one at a time,
  rebuilt `CoreTests.NameOwnership` (17 s), `CoreTests.HostParentDifferential`
  and `CoreTests.SemanticGeneratedCases` (34 s each, side by side),
  `SemanticExplorerCases` (46 s), `LanguageSpecCases` (13 s) and
  `KatLangArityLaws.MayCaptureCallsCorpus` (20 s, Lake-reported): 122 s of wall
  clock for `CoreTests`, `SemanticExplorerCases`, `LanguageSpecCases` and
  `KatLangArityLaws` together.

**Estimate for a full migration (not done).** Scratch copies outside the tree
added, for each previously unguarded program, one `cacheEntries` guard per
published name and one `cacheTotal` guard, with the numbers of the C# census.
The existing pilots, including the four SEM-2C total-only member guards, were retained. The pilot
copies and these copies were elaborated in two alternating rounds (means below).
All 5,652 added guards passed.

| Corpus | Programs | Added guards | Bytes | Elaboration |
| --- | --- | --- | --- | --- |
| `LanguageSpecCases.lean` | 477 | 705 | 322,825 → 372,710 (+15%) | 15.0 → 21.1 s (+41%) |
| `CoreTests/SemanticGeneratedCases.lean` | 678 | 1,213 | 667,901 → 766,310 (+15%) | 31.1 → 47.7 s (+53%) |
| `SemanticExplorerCases.lean` | 2,570 | 3,734 | 1,046,592 → 1,253,421 (+20%) | 56.8 → 82.6 s (+45%) |
| All three | 3,725 | 5,652 | +355,123 | 102.9 → 151.4 s (+47%) |

Every cache guard is its own evaluation. The 5,652 added guards cover the
3,709 programs outside the pilots. An alternative with one whole name-and-count
guard per program would take 3,725 evaluations across the complete corpus. The SEM-2C copy would be within 5% of that
artifact's 800,000-byte cap. A real migration would also add the expectations'
review: observed and reviewed tables for the explorer and SEM-2C, and
hand-written expectations for the specification, whose canonical oracle must
stay independent of observation.

**Not covered.** The pilots do not observe the cache on the public engine, on
the host-operation programs of SEM-2B, or under cancellation. They compare entry
counts per binding name, not the cached values (the neutral guard holds the
value a program returns) and not cache keys: two bindings of one name in
different scopes are two entries under that name, as in the host-parent corpus.
The same limits hold for the F01 loop cases. The census above predates the F01
decision and the inner-property lifetime rule, and its scratch tools are not in
the tree. Its C# half was repeated on 2026-11-21 with the publication report in
place (a scratch test, not kept): 2,551 explorer surface programs, 541
specification programs, 264 SEM-2C base members and 414 transformation members.
None of those 3,770 runs established a planned frame slot, and the C# routes
agreed on their publication observations. The explorer and SEM-2C entry totals equal the
table's (1,171, 194 and 363); the specification has grown to 541 programs with
392 entries. The Lean half was not repeated for unguarded programs. The five
further language-specification cases proposed in the 2026-11-21 widening report
are not added either.
Extending the observation to all 3,725 programs is a separate owner decision, to
be made on the census and the cost above. Logs, the census tables and the
scratch tools are in `artifacts/validation/kl-cache-pilots/`.

## Planned-loop temp family (F01 follow-up)

The follow-up of § 7 of the 2026-11-20 C#/Lean differential bug hunt, on the
contract of F01 Option A above: a small deterministic generator family of
`repeat` and `while` steps (`PlannedLoopTempFamily`, checked by
`PlannedLoopTempFamilyTests`, Lean half in the generated
`lean/CoreTests/PlannedLoopTempFamily.lean`, flag
`KATLANG_REGENERATE_PLANNED_LOOP_TEMP_FAMILY`). It is separate from SEM-2B and
from the hand-written F01 table. The plan-retention gate differential (E-21)
checks all 36 programs against their encoded trees.

**The family.** Every step `Step(n, acc)` declares the same four temps:

- `T = n * 2`, the F01 anchor: pure, plannable and local-only, read k times in
  every state-forming round.
- `F = n * 10 + tick()`, the fallback temp: the planner cannot plan the
  `tick()` call.
- `K = 7`, exported and self-contained. A `while` step's continuation row
  `n + K <= R + 7` reads it once more in every round, the false round included.
- `U = n + 100`, declared and never demanded.

The rows are `n + 1`, `acc + (T + K)×k` (each group with `+ F` on the fallback
path) and, for `while`, the continuation row. Each case runs its loop in two
activations (two root rows, initial accumulators 0 and 100) at activation depth
0 (the step at the root), 1 (inside `Run(b)`) or 2 (inside `Outer(c)` around
`Run(b)`). Depth, the round count R ∈ {1, 2, 3} and the reuse k ∈ {1, 2, 3}
follow the L9 orthogonal array (each pair of levels of two factors exactly once)
for each loop kind and path: 36 cases.

- *Planned path.* F is undemanded, so every row is planned: T and K live in
  frame slots, F's refusal is recorded and U is planned and never read.
- *Fallback path.* The accumulator row reads F, which has no plan. The planner
  withdraws every temp plan ("local properties require the shared generic cache
  in a partially planned loop"), and the accumulator and continuation rows run
  generically inside the optimized loop, through the run's cache.

**Expectations.** `PlannedLoopTempFamily.Predict` simulates the arithmetic and
the reads in evaluation order (a `while` round's continuation row first) under
the approved reading. A round publishes each temp it demands once, later reads
in the round reuse that value, an undemanded temp does no work, and `tick()`
advances once per establishment of F. That gives the neutral observation, the
four per-name counts (zeros are watched), the tick count and the optimized
route's frame-slot split (the planned path's T and K, nothing on the fallback
path). Nothing is copied from a run.

**What the approved route policy compares.**

| Observation | Routes | Compared with |
| --- | --- | --- |
| Neutral observation (value, root emitted count) | generic, optimized, suspending async; each ordinary and with retained invocation plans (`InvocationPlanTestSeam`) | the constructed one |
| Value, host-call log | both engines, the engine's async twin, generic, optimized, forced twin (`SixRouteAgreement`) | the constructed value; no host call |
| Final `tick()` output in a second run with that row appended | the same six routes | constructed tick count plus one; no host call |
| Publications per binding name | generic and optimized, both passes | each other and the constructed counts |
| Publication total | suspending async | generic |
| `tick()` count (run budget) | generic, optimized, suspending async | the constructed count |
| `obs`, `cacheEntries` for the four names, `cacheTotal`, `tickTotal` | Lean | the constructed values |

Route-specific observations, never compared with Lean, are:

- the storage split on the optimized route: frame slots against the constructed
  split, and the run cache's own store count (all publications on the generic
  route, the rest on the optimized one);
- the planner's path, read from the observed optimized run's diagnostics in
  both passes: one plan build and execution per activation, the plan identity,
  every temp's and row's plan or refusal, and the number of generic row
  evaluations;
- the publication order and the operational counters (steps, checkpoints, peak
  depth, materialized items), between generic and optimized and between the two
  passes.

The async cache reports only the publication total. The public engines expose
ticks through the extra output row and have no cache observer. The supplementary
readout run is C#-only. Lean checks the original program. The whole family is in the
shared domain: the tick counter is modeled language state, and Lean's
`tickTotal` reads the final `EvalState.tickCounter` under `publicationsOf`'s
completion rule (four hand-written state guards).

**Telling the readings apart** (`Readings_AreToldApartExactlyWhereTheVariedDimensionsReachThem`).

| Rejected reading | Told in | Changes the value in |
| --- | --- | --- |
| The exported temp keeps one run entry | every case (two activations) | no case |
| One entry per loop execution | R ≥ 2 or `while` | R ≥ 2 |
| Keyed by the outermost invoked owner | depth ≥ 1 and (R ≥ 2 or `while`) | depth ≥ 1 and R ≥ 2 |
| Every read evaluates and publishes | k ≥ 2 or `while` | fallback path, k ≥ 2 |
| Demanded temps never publish | every case | no case |

So each dimension is needed: without depth ≥ 1 the outermost-owner key is the
round itself, without R ≥ 2 or a `while` a loop's memo is the round's, and
without k ≥ 2 or the `while` row's extra read a temp is read once per round.
Where the value does not change, only the publication guards tell the reading.

**Negative controls.** `PerturbedRecorder_IsRejectedExactlyWhereTheFamilyCanTellIt`
puts a perturbed `ZeroArgPublicationObserver.PublicationRecorder` on the two
synchronous cache-recording routes. The async route keeps the reference cache.
For each perturbation the test pins, case by case, the requirement of the
policy that rejects it. It also pins where the constructed expectations alone
reject it, with no route compared with another.

| Perturbation | Rejected by the policy | Rejecting requirement | Constructed expectations alone |
| --- | --- | --- | --- |
| Planned slot reports dropped (the observer before F01) | the 18 planned cases | per name | the same 18 |
| Run-wide key (one entry per binding and run) | all 36 | per name; async total on the fallback path | all 36 |
| T's and K's slots reported under each other's names | the 18 planned cases | per name for `while`, order for `repeat` | the 9 planned `while` cases |
| Every read evaluates afresh | the 30 with k ≥ 2 or `while` | per name; async total on the fallback path | the same 30 |
| Every reuse counted as a publication | the same 30 | the same | the same 30 |

The unperturbed recorder is rejected nowhere. On the fallback path both
synchronous routes share the perturbation, so their per-name comparison cannot
see it. The async reference route's total or the constructed expectations
reject it there.

**Lean model mutants (2026-11-21, scratch copies outside the tree, not in the
suite).** Each copy holds the model and this module and was built with `lake
build CoreTests.PlannedLoopTempFamily`. The unmutated copy passed every guard.

| Mutant of `KatLang.lean` | Failing case guards (of 252) |
| --- | --- |
| The cache key loses its binding context and environment (one entry per binding and run) | 174: T, K and the total in all 36 cases; F and the tick count in the 18 fallback cases; `obs` in 30 (the six one-round planned cases keep their value) |
| The key's property name is wrong (`binding.name ++ "'"`) | 90: exactly the T and K name guards of every case and the F guards of the fallback cases; `obs`, totals and tick counts pass |
| Every read misses (`lookup []`) | 24: `obs` and `tickTotal` of the 12 fallback cases with k ≥ 2. Every cache guard passes, because Lean's `insert` keeps one entry per key, so only the tick effect shows the evaluation count |

The first mutant reached Lean's 100-error limit under `lake build`, so its
count comes from `lake env lean -DmaxErrors=5000`. Logs are in
`artifacts/validation/plt-probe/lean-mutants/`.

**Cost (2026-11-21).** The module is 80,747 bytes with 262 guards: seven per
case (`obs`, four names, the total and the tick count), the five cache-state and
four tick-state guards, and one count guard. `lake build CoreTests` built it in
10 s, and the model alone builds in 14–15 s in a scratch copy. The C# class (82
tests) runs in about 2 s.

**Not covered.** The family does not cover explicit temp calls (`T()`), alias
temps, failing temps or handovers (the F01 table covers them). It also leaves
out host operations, cancellation and resource limits.

## Module programs (MODULE-DIFF-1 pilot)

The pilot uses ten named programs drawn from `ModuleIdentityTests` and
`ModuleHygieneTests`. The fixtures in `ModuleDifferentialCorpus` specify the
expected values, emitted counts, error payloads, diagnostic positions and requested
URLs. `ModuleRouteAgreement.Modules` serves six fixed files in memory and raises a
local error for a missing URL. Each parse and engine run gets a fresh downloader.

| Fixtures | Hand-written expectation |
| --- | --- |
| `same_url`, `nested_first`, `distinct_url` | A direct holder and a nested import of the same canonical URL read one cached tick. Both declaration orders yield `(1, 1, 2)`, including a fresh explicit call. Giving the direct holder identical bytes under a distinct URL yields `(1, 2, 3)`. |
| `module_shadow`, `inline_shadow` | A module reads the prelude's `sum` and returns 3. The same body written inline reads the caller's `sum` and returns 999. |
| `one_provider`, `two_providers`, `written_ambiguity` | A receiver-decided fallback returns 10 with one provider. Two providers give a runtime `ambiguousOpen` naming `F`. Writing the ambiguous name directly gives a C# front-end diagnostic at the name. |
| `missing_module`, `selected_branch` | A missing file gives a positioned `LoadFetchFailed` after one request. A deferred branch fetches nothing during parsing, fetches once when selected, and returns 1. |

**Compared with Lean.** Seven admitted programs have a FORMAL-06 `obs` guard over the
encoded tree and the fixture's expected observation. The runtime ambiguity also has
a Q-67 `errorObs` guard. Both sides check plain and counted evaluation. C# checks
the public asynchronous engine against the same values, counts and error details.
The dependent E-21 artifact checks the plan-retention gate on those seven trees.

**C# only.** Each fixture runs with the in-memory files supplied in both orders.
Each order must meet the same per-URL request counts and pinned outcome. The
encoded trees must also match for a given source. Parser and public-engine
diagnostics are checked by code and span. The deferred branch runs on the public
engine and on both asynchronous evaluator routes. A refused parse or a tree
admitted with a deferred region has no Lean evaluator guard. The encoder itself
refuses the deferred tree as evaluator evidence, and the harness requires exactly
that refusal. Any other encoder refusal fails the test.

Lean consumes the tree the C# front end elaborated. The pilot covers numeric and
sequence results and the provider error above. It measures neither downloader
request order nor cache-entry counts, structural keys, host events, scheduling,
cancellation, resource limits, or editor behavior.

## Demand, effects and model boundaries

ModelCProductionTests, ArgumentDemandOrderTests, ModelCPropagationTests and
NeedCellTests already independently assert unused/required computations,
spread formation, cardinality precedence, first demand order, single flight,
sticky failures, projections and cache separation. FailureTerminalityWitnessTests
adds exact six-route logs for root rows, map/filter/reduce and repeat/while,
no partial successful value, and two independently failing demanded cells.

Lean CoreTests/ModelC already observes suspended/completed cells, unchanged
work on repeated successful/failed demands, shared clause attempts, slice
transport, callable projection and the separate property cache. These are
bounded one-sided heap witnesses, not shared universal operational traces.
Host operations remain C#-only. R3 (October 2026) adds kernel theorems for the
Lean BINDER's boundary event schedule (`KatLangArityLaws/BinderTrace.lean`,
`FamilyDispatch.lean`, `BinderCorrespondence.lean`): they are binder-level laws over the Lean model, not a
shared universal operational trace of the evaluator, and say nothing about C#.

The explorer's eleven exclusions remain exactly the existing parse/front-end
cases; its nineteen internal-node cases stay same-AST comparable. Its
collection invariants already use independent structural expectations. The
canonical specification's twenty-two numeric/native exclusions already have
handwritten intent expectations and exact-ID ratchets. No case is newly excluded.

Both generator prompts retain their generated canonical-example block (161
examples of the then 448-case specification when Q-67 landed in `091ddca4`,
2026-10-15; the block header records the current count and is verified by
`LanguageSpecArtifactsGeneratorPromptTests`). Twenty
selected handwritten result claims (ten per prompt) now use the existing TutorialCorpus grammar
and TutorialResultSweepTests assertion, with exact first-row inventories.
This includes the corrected `Many` counts and the decimal Order claim.

The prompts' other examples are indented rows annotated with `# result`
comments, a convention the tutorial grammar does not read (independent review,
2026-10-15: before it, the text prompt's dozens of concrete annotated rows, such
as `Values[1]  # 20`, could be edited with no test failing). Every such row
outside a fence is now classified by its verbatim text in
`PromptFile_AnnotatedExampleRowsExecuteOrAreExempt`: 86 of the 104 distinct
rows execute in their example's context with the annotated display, evaluation
error or front-end rejection, and 18 carry an explicit exemption (network module
loads and rejected load forms, metavariable illustrations, definition
annotations whose claims follow in prose). An unclassified or stale row fails
the census. Claims written inside prose sentences remain outside mechanical
verification, as in the tutorial. The untracked LLM generator harness is an
experimental generation/validity tool, not a result oracle.

Final execution counts, runtime measurements, mutations and Constitution
preservation are recorded in `artifacts/validation/q67-differential-observations/`.

## Generated grammar-aware cases (SEM-2B)

The SEM-2B generator (`fuzz/README.md` § Grammar-aware semantic testing) judges
every generated case with these same observations — SEM-2A's typed structural
value and `kl-struct-v1` identity, the root emitted count as its own facet, the
`MetamorphicErrorDetail` strict policy between profiles of one source — plus an
exact host-event log from a deterministic fixture. Its expectations are
constructed by the generator, not observed from a run. Their confidence comes
from C# profile parity (generic, optimized, asynchronous twin, public sync and
async engines, a fresh re-run) together with those independent constructed
anchors.

Since SEM-2C every valid generated case also has a per-case Lean guard in
`lean/CoreTests/SemanticGeneratedCases.lean` (`SemanticGeneratedLeanArtifactTests`).
The guarded program is the case's IDENTITY-PRELUDE member — the base source
with `trace(x) = x` and `wait(x) = x` prepended in place of the host operations
Lean does not model — encoded from its real elaborated AST. C# checks that
member against the constructed expectation, and the guard pins its FORMAL-06
neutral observation (plus the Q-67 `errorObs` payload where shared). The
case's transformation members (`alpha-rename` always, `declaration-reorder`
when the root has two or more declarations) are guarded the same way with the
identity prelude; C# also checks the SEM-2B runner's member relation
(SemanticEqual to the base, `Normalized` errors: equal neutral text), and each
member guard pins the BASE member's neutral text. The guards do NOT observe the
host-operation programs in Lean (their relation to the identity-prelude members
is C# evidence), host events, async suspension or cancellation, or optimizer
paths.

The named tick block (`sys/tick/…`, 23 cases since 2026-11-21) observes
evaluation order through `tick()` rather than host events. The counter is
language state Lean models, and its values are part of the result. These
guards therefore check, on Lean, the order inside `map`, `filter` and
`reduce` callbacks, `repeat` and `while` rows, and selectors. They also check
member reads through transparent references and forwarding carriers, and the
per-activation lifetime of two nested parameterized owners' local properties.
The block's three fault shapes trace their ticks: which ticks ran before the
fault is C# host-event evidence, and Lean checks the error kind. Each shape's
named rejected reading (`fuzz/README.md` § Families and interactions) is a C#
control of the anchor's sensitivity. It is not a Lean mutation test.
