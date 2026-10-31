# B3: one static-structure resolver for the M4★ front end, with A1

Current isolated candidate (2026-10-30): Q1–Q7 are the consolidated production structural
authority for detection, resolution, editor analysis and exposure. The independent acceptance
review accepted the architecture and the earlier exhaustive V3 evidence, with three integration
blockers F1–F3. Their corrections pass fresh validation on the final frozen executable source.
V3 passes under the explicitly approved exhaustive 44-batch procedure in both modes; the canonical
core attempts timed out and remain INCOMPLETE. The final Gate D/B3-2★ verdict, including the
independent read-only delta review, is recorded in
`experimental/features/alias-unify-1-b32-final-corrections-2026-10-30.md`.

The approved V3 procedure first attempts canonical ordinary and forced full-host validation.
After a 900-second timeout without unresolved correctness failures, the owner-approved 44-batch
fallback preserves all original 42,325 core cases, 542 whole collections and deferred theory rows
in both modes, plus added regressions, solution builds, CLI/API, all seven Lean targets and
generated/specification checks. Each host retains 900-second/6-GiB bounds and exact identity and
fingerprint verification. Cross-class co-residency, process-state lifetime and contention differ
between batches; that residual limitation remains explicit. This approval is scoped to this
candidate, not a general validation-policy change.

Q8 requirement equations, processing order and MAY→MUST refinement, and Q9 pending/completed
publication remain in place. B3-5★ is separate future work, including the inherited Round-14
items; B2 is not adopted and X-04 remains an owner decision.

## 1. Owner decisions (2026-10-27)

- **A1.** Reject statically detected self-dependent implicit-parameter inference with a deterministic compile-time
  diagnostic.
  - Preserve ownership-first name resolution.
  - Classification must not depend on declaration order or expression traversal order.
  - Reject as little as possible, and keep resource bounds.
- **B3.** Replace the structural reasoning that parameter detection and alias resolution each duplicate with one
  authoritative, demand-driven, memoised computation.
  - Preserve M4★, OD-B–OD-E and NEED-04.
  - Remove inconsistent structural verdicts, fragile sibling-processing dependencies and host-stack-depth
    amplification.
  - Preserve non-alias behavior, diagnostic order, lazy evaluation and resource guarantees.
- **B2 is a fallback only.** No narrowing of M4★ semantics without explicit owner approval. If B3 meets a fundamental
  obstacle, document it and stop for a decision.

Background: `artifacts/validation/alias-unify-1-impl/handoff/owner-decision-brief.md` and `status-handoff.md`
(git-ignored).

## 2. Why B3

Since M4★, static structure depends on inference, and inference depends on static structure:

- structure means alias status (OD-C/OD-D), `open` providers and receiver members;
- inference means which free names are inputs, and whether a dot edge's fallback is certain (Q-75).

Before B3-2★, the front end computed these in two places:

- the parameter detector (`ParameterDetector` / `ElaboratedScopeLookup`, with the input "decider");
- implicit-argument resolution (`ImplicitArgumentResolver`), whose static chases, miss refinement and alias formation
  run in the order fixed by a static sibling-order channel (`PropertyDependencyGraph`, `SiblingOrderLookup`), with
  on-demand processing (`PropertyLoop.EnsureOnDemand`) as the fallback.

Fourteen review rounds found those superseded authorities disagreeing:

- the navigated-body defect;
- reads the channel cannot order, which nest on the host stack until `DemandDepthBudget` refuses;
- answers that depend on declaration order;
- the self-dependent class (owner question (b)), which has no consistent or affordable answer.

B3 computes every structural fact once, by demand, in one engine. Both passes, and the editor, read the same answer.

## 3. The engine (stage B3-0)

`StaticQueryEngine<TKey, TValue>` solves pure equations over a pointed information order. One engine serves one
front-end operation; keys preserve declaration/body identity. This is an implementation protocol, not an additional
language rule. It does not decide X-04 sibling lifting cycles.

**Ordinary equations.** `reader.Read(k)` always returns the current lower bound, initially `Initial(k)`, and subscribes
the running query to changes of that key. `Complete(value)` publishes its ordinary equation's answer. Every strict
change must satisfy the definition's `IsRefinement`; equality is supplied separately. Computations are deterministic
and monotone. Reading Unknown permits a definite answer only when all refinements agree (branch agreement).

**Reference equations.** `return reader.Follow(k)` declares that this query's entire equation is one definite
reference step to k. It does not return a context-dependent cycle Boolean. There is at most one successor, and once
declared it can never be withdrawn or rewired. Ordinary guards must establish that successor conclusively first.
With an Unknown guard, read alternatives ordinarily and apply branch agreement; do not speculate a path edge.
A definition may move from an ordinary Unknown answer to a confirmed path once its guard is decided.

The definition supplies one `PathCycleValue`, the OD-D refusal verdict. Consumers interpret refusal at the queried
body's own identity. Union-find representatives are graph bookkeeping only, never algorithm identities or open
provider identities. Acyclic paths transport the exact terminal answer; brace/carrier boundaries are explicit
terminal equations under M4★, not reference edges.

**Graph cycle classification.** Confirmed reference edges form a growing functional graph (outdegree at most one).
Each weak component is either an open tree with one sink or a closed component with one directed cycle. A new edge
from that sink closes a directed cycle exactly when its endpoints are already in the same weak component. Disjoint
sets with size merging and iterative path halving detect this independently of evaluation ancestry. Linked member
lists seed refusal once per newly cyclic entry, including new tails into an already closed component. Ordinary
dependencies never participate in this cycle test.

Thus A follows C, C follows A, and A also reads B which follows C: all three are refused even if the irrelevant B
read runs first. Conversely A follows B and B *ordinarily reads* A has no pure reference cycle and remains Unknown
without another deciding fact. A1 later rejects unresolved inference decisions; it does not relabel every dependency
cycle as OD-D refusal.

**Fixed point and finality.** An iterative FIFO worklist computes newly reached equations and propagates changes to
every ordinary reader and reference predecessor. Queue membership is deduplicated; independent discoveries are
batched. Ordinary subscriptions are replaced on recomputation, so obsolete branches leave no stale dependencies.
Values stay in place; there are no provisional result owners, chase frames, suspension recipes or invalidation logs.
No new key becomes final until the entire worklist is quiescent. The resulting reachable closure is cached; later
demand roots can add incoming edges but cannot alter an already final closure under the purity contract.

Starting at bottom and applying monotone equations fairly computes their least information fixed point, with
refusal seeds exactly for confirmed path cycles. This justifies scheduling independence *under the definition
contract*. Runtime checks reject observed non-refinements and unstable successors; they cannot prove arbitrary
callbacks pure, globally monotone or sound on unobserved alternatives. Real Q1–Q7 definitions must establish those
properties, including stable identity and stratum, at B3-2★. Independent synchronous whole-graph/path-walk oracles
test the protocol using different algorithms; they are not a proof of the unfinished real queries.

**Limits and cost.** `MaxEvaluations` bounds worklist events plus explicitly charged local certificate and adapter work;
`MaxReads` bounds all reader calls (including duplicates),
`MaxEntries` bounds engine discovery and admitted auxiliary live records, and `MaxRefinements` bounds strict changes per key. Reaching a bound
raises `StaticQueryLimitExceededException`. Cancellation is checked before/after callbacks and throughout engine,
subscription, component and propagation loops; its original token is retained. Reader failures are sticky even if
a callback catches them. Any failed/cancelled solve permanently faults the engine; no partial facts are usable.
Production consumers must supply finite operation-scaled limits and map bound failures to the existing resource diagnostic.
The default limits are for the unconsumed foundation, not production resource policy.

For V keys, maximum refinement height H and E distinct observed dependency edges, worklist events are O(V + H E),
reference analysis is O(V α(V)), and resident graph space is O(V + E). Each entry is classified cyclic at most once.
Total work also includes R, the reader/subscription work across callback reruns, plus the callbacks' own bounded
work. R can be quadratic: a wide callback may rescan its inputs as a chain refines one fact at a time. FIFO removes
the simpler independent-input rescan pathology, but does not prove universal FE-1 linearity. Allocation churn is
O(R), even with linear resident space. B3-2★ must use bounded fan-in/shared aggregates or demonstrate equivalent
bounds on its actual equations; use the read limit as a terminal resource bound, not a substitute for that analysis.
The engine uses no host recursion. Callbacks must cooperate with cancellation and remain bounded between reads.
Statistics expose events, computations, reads, value changes, path edges/cycles, queue peak, entries and live
ordinary dependencies for regression and complexity checks.

**Gate C private integration (2026-10-29).** Closed namespace observers use a second FIFO queue, run only
when ordinary work is quiescent; an observer that unlocks ordinary work yields to that work before the next
observer. This coalesces intermediate closures without changing initial facts, refinement order, `Follow`
equations or language identity. It is not a richer identity domain or a solution to Q8/X-04.

The production admission policy is deterministic for equivalent source, configured resource policy and
compilation phase. `SourceProcessingLimits.MaxStaticStructureBytes` may lower the fixed 1-GiB ceiling;
values must be positive, larger requests clamp to the ceiling, and null selects that ceiling. No GC
or machine-memory report changes it. Source admission bounds distinct nodes at envelope/32 and edge
work at envelope/8. For F = admitted distinct nodes + edges, limits remain 16,384 + 1,024F work,
65,536 + 4,096F reads, four refinements, and min(envelope/1,024, 4,096 + 128F) entries.
Multiplications saturate safely before overflow. Source parser/engine entries inherit RunOptions'
immutable source policy, including eager and deferred modules; standalone host semantic analysis
accepts the same policy through its additive Build overload. Each admission is an operation, not
a mutable process-wide budget. The default 1-GiB envelope allows 1,048,576 entries and 16,777,216
ledger slots; operation-scaled limits can be tighter. This retains the measured conservative
1-KiB entry and 64-byte metadata accounting, with ample room above the 1,000/2,000-property
witnesses; it is not a total-process heap guarantee. Hosts needing less memory set lower limits.
A numeric, token-free ledger enforces the same envelope in conservative 64-byte bookkeeping
slots (`MaxStorageUnits`): entries, actual subscriptions, the maximum read buffer, certificate-local graphs
and simultaneous temporary sets, input indexes, contextual adapters, completed projection and snapshot work.
Slot counts are a conservative accounting policy, not a byte-exact heap theorem; source/runtime/editor work
has separate policies. Arithmetic clamps before multiplication to prevent Int64 overflow. Resource refusal
is `StaticStructureLimitExceeded`, never A1. A failed solve/active publication invalidates unsealed facts, cached provider reads and future export.
Successful sealing releases the producer ledger; later producer cancellation/fault cannot invalidate immutable
completed facts or previous continuations. Cancelling an independent export discards that copy and does not
poison its source solve. No failed solve, cancelled copy or unfinished unit can export a continuation.

Frozen state shares immutable syntax/member indexes and persistent maps. New syntax graphs are completed
before export so a failed later unit cannot add unrecorded lazy storage to a previous snapshot. Retained
admission counts unique frozen entries and completed projections, excluding discarded operation-local
wrappers; it is distinct from cumulative allocation/work. Copies contain no producer engine or token.
Measured provider/name and contextual-body products can still require quadratic numbers of logical facts;
Gate C establishes finite enforcement and the measured families, not universal FE-1 linearity. See
`experimental/features/alias-unify-1-b32-gate-c-2026-10-29.md`. The superseded structural authorities are deleted; final Gate D acceptance follows the current gates above.

## 4. Query catalog (stages B3-1 to B3-5)

The stratum (OD-D's lower, final and formation readings) is part of a key. A lower stratum never reads a higher one;
the definitions assert this.

| Query | Value | Reads | Replaces |
| --- | --- | --- | --- |
| Q1 `Binding(scope, name, stratum)` | A declaration, a parameter (written or inferred) of an owner, an opened member with its provider identity, ambiguous, unbound, or Unknown | `IsInput` of each owner on the walk (inputs are owner-walk parameters), `OpenProviders` | The detector's and resolver's lookups (`ElaboratedScopeLookup` owner walk, `DirectDeclaration`, `StaticOpenedDeclaration`, `MayInferParameter`, `IsInferredByAnEnclosingBody`) |
| Q2 `OpenProviders(level, stratum)` | Ordered provider list (Q-19 identity) | `TargetWalk` of reference targets (OD-C) | `GetResolvedOpenProviders(stratum)`, `StaticOpenProvider`, `StaticChaseMemos.OpenProviderOf` |
| Q3 `TargetWalk(body, stratum)` | A static algorithm, a carrier, a runtime reference, not static, refused (OD-D), or Unknown | Ordinary `Binding`/`Members` reads; conclusive next walk via `Follow` (§ 3) | `ChaseStaticStructure`, `StaticReferenceStructure`, `StaticCycleCheck`, `StaticStructureMemo` / `StaticChaseMemos.Structures`, `AliasStructureCell`, `SuspendChase` / `TakeSuspendedChase` |
| Q4 `Members(structure)` | Declared members (any visibility), branch-only marks | — | `TryLookupProperty`, `DeclaredMember` |
| Q5 `MissSelection(edge)` | Never / MAY / MUST | The receiver's `TargetWalk` / `Members`; whether a link body keeps an input (`Signature`) | Detection's stamp and the resolver's refinement (`MissSelectionOf`, `ReadReceiver`, `ReadDeclaration`, `CertainMissDecidesALift`, `StaticFallbackCalleeKind`, `ProvisionalMiss`, `CertainFallbackReports`) |
| Q6 `IsInput(body, name)` | Yes / No / Unknown | `Binding`, `MissSelection` of the edges whose fallback is the name | The decider (`InputDecider`, `InferredInputDecisions`, `AgreesWith`, repeated passes, tentative forget/settle, `SuspendWalk` / `TakeSuspendedWalk`) |
| Q7 `Inputs(body)` | Ordered inputs (first semantic occurrence plus Grace movement) | `IsInput` of each candidate | The detector's collection order |
| Q8 `Signature(body)` | The processed signature: inputs plus the parameters formula lifting adds | `Inputs`, the role classifier (`FormulaLiftingRoles`, kept), `Signature` of callees through aliases | Processing order and its repairs (`PropertyLoop`, `SiblingOrderLookup.RefinedMiss` / `OwnedMemberSibling` / `OpenedSiblingProvider`, soft preferences, `EnsureOnDemand`, `ProcessedFormOnDemand`, `DemandDepthBudget` nesting) |
| Q9 `AliasTarget(body)` | Reference(target), carrier(target), runtime, or no alias | `TargetWalk` (formation stratum), `Signature` | `TryCompleteLoneCalleeRow`, `RuntimeAliasRow`, `AliasTargetCell` / `PendingTargetOn` |

**Consumers (production Q1–Q7, future Q8/Q9 consolidation at B3-5★).**

- The detector rewrites names from Q1/Q7 and stamps Q5.
- The resolver reads Q1–Q7 while preserving Q8 lifting/forwarding, processing order and Q9 alias publication. Removing the Q8/Q9 processing order is future B3-5★ scope.
- Exposure, the editor model and the provenance finalizer read the same answers.

**Queries never report.** Diagnostics stay with the passes, at their current sites and in their walk order, so report
order is preserved wherever answers are unchanged.

## 5. A1 inside the model

- **Unknown means self-dependent.** A decision `IsInput(body, name)` is left Unknown by the least fixed point exactly
  when it depends on itself through no well-founded reasoning. Examples: `x` is an input iff `y` is not and vice versa
  (two consistent answers); `m` iff `n` and `n` iff not `m` (none); the positive loop `a` iff `a`.
- **Rejection.** A body with any Unknown decision gets exactly one diagnostic.
  - Production diagnostic: `DiagnosticCode.SelfDependentInferredParameters` and the corresponding public
    `KatLangErrorCode` member (both already appended in the API baseline).
  - It is placed at the body's definition name and lists the undecided names in first-occurrence order.
  - Diagnostic form: "The parameters inferred for 'P' depend on themselves: whether 'x' is a parameter depends on the
    answer itself. Declare P's parameters explicitly, or remove the dependency."
  - The body publishes no inference, and dependent lifts are suppressed. The operation is already rejected, so this
    avoids cascading errors.
- **Diagnostic recovery after A1 (F4, 2026-10-31).** A1 stays a rejection: the unit (the eager program or one deferred
  branch) is never forwarded, exposure-settled, frozen or published, and is never evaluated.
  - Independent errors are still reported where the detected tree alone establishes them: the parameter/property
    collision rule runs over the detected tree, after detection's own reports
    (`ParameterPropertyCollisionValidator.ValidateAfterSelfDependentInference`, from `FrontEndPipeline` and
    `DeferredModuleRegion.CompileLoadedBody`). A detected signature holds the written parameters and the inputs Q6
    decided Yes; an undecided input is absent and forwarding only appends, so every collision found holds for any
    completion. A collision only an undecided input or a forwarded parameter could cause is not reported, and the
    walk records no completed bindings on deferred regions.
  - Deliberately suppressed, because they read signatures, targets or forwarding outcomes the undecided inputs
    leave open: implicit-argument resolution and its reports (`UnforwardableParameter`, `UnforwardableCallable`,
    `UnliftableClauseFamily`, …), the `open` provider rule (`UnresolvedOpenTarget`, `IllegalInOpen`, …), the
    inferred-parameter output rule (its message lists the completed signature) and exposure settlement.
  - Recovered reports use the same bag (budget, prefix law, marker) and the same phase order as an ordinary run; a
    provisional elaboration still withholds them.
  - Editor tooling inspects the erroneous, non-evaluable detected tree; its sealed completed facts keep the
    A1-affected entries unavailable (`A1DiagnosticRecoveryTests`).
- **Order independence.** The least fixed point is unique, and path-step returns are structural facts.
- **Minimal rejection.** Branch agreement decides any decision whose answer does not actually depend on the unknown.
  For example, `a` iff (`a` or true) is decided Yes.
- **Escape hatch.** An explicit parameter list makes the body closed, so it infers nothing.
- **Expected outcomes for the witnesses** (owner-decision brief § A.3):
  - A.3.1 (two answers), A.3.2 (no answer) and A.3.3 (one answer reachable only through a self-read): rejected.
  - Every body whose decisions do not read themselves keeps its current signature.

## 6. Preserved guarantees

| Guarantee | How B3 keeps it |
| --- | --- |
| Ownership-first lookup | Q1 is the one implementation of the six ordered rules: owner walk (written and inferred parameters, properties, prelude), then opens per level. Identity never depends on spelling. |
| M4★, OD-B–OD-E | Encoded once, in Q3/Q9. NEED-04, the evaluator and Lean are untouched: this is front-end only. |
| Non-alias behavior and report order | Passes keep their walks and report sites; differential runs over the saved probe corpora at every stage. |
| Laziness | Front-end only; no runtime change. |
| Resource bounds | One memo per operation; module units once per operation (Q-32); iterative worklist/graph loops; finite operation-scaled work/read/entry/refinement bounds and cancellation. Actual query callback and fan-in costs must satisfy § 3. |
| Deferred units | A deferred branch runs with its own engine, which reads the eager operation's final answers for keys outside the unit. |

## 7. Stages and exit criteria

Each stage switches one whole capability and deletes the mechanism it replaces in the same stage, so the front end is
never partly on two models for one capability.

| Stage | Work | Exit criteria |
| --- | --- | --- |
| **B3-0** (done) | Engine core | Least fixed point over random three-valued circuits in every demand order; deep chains without host recursion; models of the A1, OD-D and navigated-body witnesses; limits |
| **B3-1** | Key model and AST adapters: scope and level identities shared by detector, resolver and editor; module and deferred units | Unit tests on identity and sharing (DAG, module splices) |
| **B3-2** | Q1–Q4. The detector's static chases and the resolver's static reads switch to them, and their memos and suspension machinery are deleted. | Navigated-body witnesses (`probe-cases-r9h.txt`): `strata0-get` = 42, `strata0-ambiguous` = static `AmbiguousOpen`. All alias and ownership suites pass. |
| **B3-3** | Q6–Q7 plus the A1 diagnostic. The decider is deleted. | A.3.x witnesses rejected in every order. HEAD signatures for every non-self-dependent body (differential over all saved probe corpora). |
| **B3-4** | Q5. The resolver refinement and deferred checks are deleted where subsumed. | Round-12/13 refinement witnesses |
| **B3-5** | Q8–Q9. Processing order, the channel's repairs, soft preferences, on-demand processing and demand nesting are deleted. | Round-14 witnesses: no `AstDepthLimitExceeded` on the K = 40 chains, order-independent results. Rounds 12–13 witnesses. |
| **B3-6** | Editor and exposure consumers; `AGENTS.md`, `ownership-and-lookup.md`, `SEMANTIC-ALIGNMENT.md`; spec cases; A1 public code and the API baseline | Editor suites, spec artifacts |
| **B3-7** | Mutation runs, differential tests within the suite, full V3 (one ordinary `-Phase DotNet`, one `-Phase Lean`; local execution only when requested) | All green |

## 9. Stage soundness (B3-1, 2026-10-28)

### 9.1 Identity: implemented and tested (`src/KatLang/StaticKeys.cs`, `StaticKeyTests`)

- **One key per written body across passes.** Every written `User`/`Conditional` body keeps its `DeclarationIdentity`
  through detection and resolution: the passes rewrite with `with`, and alias formation passes the written body's
  identity on to the `Algorithm.Alias`. No provenance map is needed.
- **Scope keys.** `StaticScopeKey` interns the declaration chain that `OpenProviderIdentity` already compares.
  - The detector's levels (`ElaboratedPropertyScope`), the resolver's chains (`DeclaringOwners`) and its levels
    (`ResolverLevel`) map to the same key.
  - Key equality is exactly provider-identity equality; an exhaustive pairwise test checks this.
  - A loaded module has one key wherever it is held.
  - A body shared by two contexts (a host DAG) has one key per context.
- **Deferred units.** Their runs build levels on the eager chain, so the same rule gives the same keys. B3-2★ tests
  this on real deferred branches.
- **Query keys.** `StaticQueryKey` gives one key type for every query family. Scopes and expression nodes compare by
  reference: an `Expr` record's own equality is structural, so two equal edges written twice are two questions.

### 9.2 The Q1/Q3/Q5/Q6 cycle

The reads between queries:

| Query | Reads | Why |
| --- | --- | --- |
| Q6 `IsInput(b, n)` | Q1 `Binding(b, n)` | Whether `n` is unbound after the owner walk and the opens |
| Q6 | Q5 | For the edges whose fallback name is `n` |
| Q5 | Q3 / Q4 | The receiver's structure: a navigated body, a reference's target, a runtime row |
| Q3 | Q1 | Row heads and path steps |
| Q3 | Q6 | A head naming an input of the body or of an enclosing body is a runtime reference, and a navigated body's own input stops a walk (the navigated-body defect) |
| Q1 | Q6 | Inferred inputs are owner-walk parameters, so an enclosing body's input shadows a nested body's opens |
| Q1 | Q2 | `open` providers |
| Q2 | Q3 | OD-C: a static reference opens its target |

So **{Q1, Q2, Q3, Q5, Q6} is one strongly connected capability**; Q4 and Q7 hang off it. Consequences:

1. **The planned B3-2 (Q1–Q4 without Q6) is unsound.** Its Q1/Q3 would have to read input decisions from the old
   decider, whose answers come from the old chases. That is two authorities for one fact, which recreates the
   detector/resolver disagreement. **B3-2 and B3-3 are therefore one stage, B3-2★ (static structure and inference).**
   - It covers Q1–Q7 and A1.
   - In one step it switches all of parameter detection's static chases and input decisions, and the resolver's static
     structural reads: alias formation's OD-D verdicts and static targets (`TryCompleteLoneCalleeRow`,
     `IsCyclicReferenceChase`), its open providers, and the structure half of its miss refinement.
   - The decider and both chase implementations are deleted in the same stage.
   - Acceptance is the union of the old B3-2 and B3-3 criteria.
2. **A1 belongs to this SCC's fixed point.**
   - A body is rejected exactly when one of its input decisions stays Unknown.
   - A pure path return is an OD-D refusal, a definite answer.
   - A dependency cycle that no input decision reads cannot reject anything.
3. **Q8 joins the SCC through link bodies.** Whether an `.Algorithm` link body is a calculation or a runtime reference
   depends on what formula lifting leaves it (META-S3-2), and the resolver's MAY→MUST refinement reads that.
   - B3-2★ keeps that refinement, reading engine structure instead of its own chase. That is today's documented split
     between detection's verdict and resolution's refinement, not a second authority.
   - The refinement moves with Q8; old stages B3-4 and B3-5 merge as B3-5★.
4. **Owner decision needed before B3-5★.** Inside a sibling cycle, today's rule is the documented processing-order
   fallback (X-04): members are processed in declaration order, and the first one reads the others' unprocessed
   signatures. A least-fixed-point Q8 changes that observably. The order-independent choices are:
   - (a) the least fixed point over lifted-parameter sets, where each member of the cycle gets the union;
   - (b) rejecting lifting cycles the way A1 rejects self-dependent inference.

   Neither A1 ("implicit parameter inference") nor B3 ("preserve existing non-alias behavior") decides this.
5. **Monotonicity.** Every edge in the SCC is a three-valued read with branch agreement.
   - A binding whose input decision is Unknown is itself Unknown, unless both branches select the same declaration.
   - Input-ness is "unbound and used" or "a certain fallback"; three-valued negation is monotone.
   - OD-D's lower and final readings are stratified (the stratum is part of the key; the final reading reads the lower
     one), so no cycle crosses strata.
   - An ambiguous open (two providers) is a definite value.

   No non-monotone selected rule was found. This is an analysis, not yet a proof on real queries; B3-2★ adds
   order-permutation tests per query.
6. **Editor.** The editor reads the published elaborated tree: formed aliases carry their targets, and inputs are
   `Param` nodes. B3-2★ must list every `ElaboratedScopeLookup` chase entry point the editor still calls. Any that
   remains reads the front end's engine through the parse result, never a third chase.

### 9.3 Revised stages

| Stage | Content |
| --- | --- |
| **B3-0, B3-1** | Done |
| **B3-2★** | Q1–Q7 and A1, as above. The scale: `ElaboratedScopeLookup` (2,730 lines), `ParameterDetector` (3,568), `ImplicitArgumentResolver` (6,630) and `PropertyDependencyGraph` (4,322) together hold the mechanisms it replaces. The list is in the B3-1 checkpoint report. |
| **B3-5★** | Q8/Q9, the miss refinement and the processing order, after the owner decision in § 9.2(4) |
| **B3-6, B3-7** | Unchanged |

## 8. Risks

- **Monotonicity.** Every query definition must be monotone and must apply branch agreement. Limits can detect some
  failures to converge, but cannot certify monotonicity. Each query needs independent oracle and permutation tests;
  dependency-only circuit tests alone do not validate OD-D path-context handling.
- **Callback cost.** Batching reads alone does not bound repeated wide scans. Real queries must establish the R/fan-in
  bound in § 3; FE-1 complexity tests read `Statistics`, including total reads and allocation cost.
- **OD-D strata.** The lower, final and formation readings must keep their exact current meaning. Port them with the
  existing OD-D regression classes as the oracle.
- **Size.** `ElaboratedScopeLookup`, `ParameterDetector` and `ImplicitArgumentResolver` are large. The stage gates
  above are the protection against a half-migrated capability.
- **Obstacle protocol.** A fundamental obstacle, such as a selected rule that is not monotone in any information
  order, is to be documented here and stopped for an owner decision. It must not be worked around by narrowing M4★.
