# Asynchronous Evaluation Surface (Phase 2, August 2026)

Status: implemented at v0.8.169 (same related development set as the Phase 1 evaluation
cancellation work — deliberately no version bump). C#-only host-execution surface; no
Lean change (Lean models no host asynchrony).

Phase 3 (public asynchronous host operations, same set and version) is documented in
[the Phase 3 section below](#phase-3-public-asynchronous-host-operations-august-2026).

## What was added

- Public async entry points mirroring the synchronous surface exactly:
  `Evaluator.RunAsync(expr)` / `(expr, limits)` / `(expr, limits, token)` →
  `Task<EvalResult<Result>>`, the same triple for `RunFlatAsync`, and
  `KatLangEngine.RunAsync(source, options?)` → `Task<RunResult>` with `Run`'s exact
  result/error projection (shared projection helpers, not a re-implementation).
  Parsing, module loading, and front-end elaboration remain synchronous.
- Internal async entry points (`RunCountedAsync`, `RunCountedWithTopLevelPropertyAsync`,
  `RunCountedObservedAsync`) and the async TWIN FAMILY in `Evaluator.Async.cs` —
  `async ValueTask` mirrors of the counted evaluation family (~70 members), each marked
  `// MIRROR OF <sync name>`.
- The async host-operation seam: `IAsyncZeroArgPropertyResultCache` (internal), with the
  run-scoped reference implementation `RunScopedAsyncZeroArgPropertyResultCache`, plus
  `GetOrBindAsync` on the internal deconstruction-binding cache.

## Architecture: the sync-delegating async twin spine

One decision per run, at the async entry point:

1. **Fast path** — the run has no component that can complete asynchronously: the
   zero-argument property cache does not implement the async seam and (since Phase 3)
   no asynchronous host operation is configured. This is every configuration without
   asynchronous host operations. The async entry executes the ORDINARY synchronous
   pipeline inline on the calling thread and returns a completed task. Results,
   diagnostics, budget verdicts, counters, optimizer eligibility, and stack behavior
   are those of the synchronous entry point by identity. No `Task.Run`, no
   `Task.Yield`, no thread placement — host scheduling remains the host's
   responsibility.
2. **Twin path** — a run component is async-capable. Evaluation runs through the twin
   family; the internal seam is awaited at every zero-argument property access and
   (since Phase 3) an asynchronous host operation is awaited at its wrapper-body site,
   so a `ValueTask` that has not completed suspends the whole evaluation spine and
   resumes it when the host operation finishes. This is the structural capability the
   surface exists for — adding an operation class means adding an await site in the
   already-async twin, nothing more, and Phase 3's public host operations are exactly
   that extension.

### Why not the alternatives

- **Single async core shared by sync and async APIs**: rejected — per-node async
  state-machine overhead and changed frame sizes on the synchronous path would break
  both the performance contract and the calibrated stack-depth guarantees
  (`EvaluationLimits.MaxSupportedDepth`/`MaxSupportedAstDepth` are calibrated against
  the synchronous frames). Phase 2 left the synchronous evaluator byte-unchanged
  (apart from the `class` → `partial class` split); Phase 3 later added synchronous
  host dispatch to that semantic oracle without making its execution path async.
- **Suspend-by-unwinding + replay (React-Suspense style)**: rejected as semantically
  unsound — replay re-executes host-visible work (host cache seam invocations, the
  nondeterministic `Math.Random`), and memoizing async results by encounter order or by
  argument value is either misaligned under nondeterminism or wrong for effectful
  future operations.
- **Dedicated-thread blocking**: rejected — that is host-side thread offloading, which
  the surface explicitly must not be.
- C# has no zero-cost abstraction over "asyncness" of a method body (the red/blue
  function problem), so genuine suspension at arbitrary evaluation depth requires an
  async-colored recursion spine; the twin family is that spine, scoped to the exact
  recursion SCC through `Eval`/`EvalCounted` (~87 methods in the synchronous family;
  the twins mirror the counted side plus the root projections).

### Twin discipline (normative)

- A twin may call: other `*Async` twins; shared helpers verified not to evaluate
  expressions; and the plain synchronous `Eval` only for proven-leaf dispatch kinds
  (the `EvalCountedAsync` default case: Num/StringLiteral/NativeCall/illegal — no child
  evaluation).
- The twins are COUNTED-family mirrors. Where the synchronous family used a
  plain-evaluation wrapper, the twin awaits the counted core and projects its value —
  every such synchronous wrapper is exactly that projection, and the plain/counted
  value equivalence is a Lean-modelled invariant pinned by the explorer corpus.
- The twin root context pins the GENERIC loop and sequence strategies (loop
  optimization and pipeline fusion off — the same generic mode configured step/string/
  materialization budgets already force on the synchronous path). Limit verdicts are
  strategy-independent by the budget architecture, so this is an internal execution
  choice, not an observable one; a fail-loud guard
  (`ThrowIfAsyncStrategyPinningViolated`) turns a pinning violation into an
  `InvalidOperationException` instead of silent divergence. The optimized executors can
  be taught to cooperate with the twin family later (split "planned portion" from
  "fallback continuation") without an architectural change.
- Budget protocol, chokepoints, and cancellation are the SHARED code — `try/finally`
  around `TryEnterInvocation`/`TryEnterArgumentEvaluation` is mirrored verbatim, so
  Phase 1's conservation and cancellation-before-mutation contracts carry over
  unchanged. Cancellation surfaces as `OperationCanceledException` (supplied token)
  through the returned task, never an `EvalError`, never a retained binding.

### Twin-only structural-nesting stack backstop

Discovered by the probe suite: nested algorithm/capture bodies recurse through the twin
family without passing any invocation chokepoint (structural nesting charges no dynamic
depth), and the twins' async state-machine frames are larger than the calibrated
synchronous frames — a 120-level host-built nested-body chain overflowed the process on
a 1 MiB thread where the synchronous evaluator completes. Fix: the two row-loop funnels
every nested written structure passes through (`EvalOutputRowsPreparedCoreAsync`,
`EvalExplicitSequenceValueRowSlotsAsync`) carry a twin-only
`RuntimeHelpers.TryEnsureSufficientExecutionStack` probe returning the structured
`EvalError.EvaluationStackExhausted`. Like the invocation-chokepoint probe, it can only
stop a run EARLIER than a physical overflow, never change a completing run, and it
moves no budget counter. The synchronous path deliberately keeps its calibrated
no-per-node-probe policy — unchanged.

### Measured synchronous-completion stack capacity (1 MiB thread, `--async-stack-capacity`)

Largest recursion request completing without the structured stack backstop
(`>=ceiling` = the deterministic MaxDepth request cap of 127 was reached):

| shape                | sync Debug | twin Debug | sync Release | twin Release |
|----------------------|------------|------------|--------------|--------------|
| plain-clause         | 91         | 51         | >=ceiling    | 63–64        |
| through-if           | 35         | 19         | 52           | 25           |
| dotted               | 33         | 18         | 51           | 24           |
| collection-callback  | 21         | 11         | 31           | 15           |
| nested-bodies (AST)  | 149        | 86         | 149          | 114          |

The twin's per-level stack cost is roughly 1.8–2× the synchronous cost for
call-shaped recursion. Beyond the boundary both paths stay structured
(`evaluationDepthExceeded` / `evaluationStackExhausted`). A genuine suspension unwinds
the evaluator frames that led to the await, but it does **not** promise a fresh
thread-pool stack: continuation thread and stack placement belong to the awaited host
operation and the runtime. The twin-only stack checks therefore remain part of the
post-resumption safety envelope. The synchronous guarantees and ceilings are untouched;
the twin path's reduced synchronous-completion capacity is documented and structured.
(At Phase 2 no public configuration reached the twin path; since Phase 3, a public
configuration containing an asynchronous host operation does, and these capacities and
structured outcomes apply to it unchanged.)

The capacity sweep is a diagnostic characterization, not a semantic threshold. Near a
boundary, JIT/runtime stack-check placement can move the largest successful request by
one level (the Release plain-clause twin was observed at both 63 and 64); every request
beyond the available headroom still returns a structured resource error.

## Divergence pinning

`tests/KatLang.Tests/AsyncEvaluation/`:

- `AsyncTwinDifferentialTests` — the language-spec and semantic-explorer corpora
  through the twin path with OUTCOME equality against the sync default strategies and
  OUTCOME + OPERATIONAL-COUNTER equality (steps, peak depth, materialized items/string
  units) against the sync generic strategies, plus a full language-spec pass with
  GENUINE suspension (thread-hopping host yield) at every property access requiring
  identical outcomes and counters. The twin path must never touch the synchronous seam
  member (asserted).
- `AsyncEvaluationApiTests` — public fast-path identity (results, errors, limit
  verdicts, counters, engine projection incl. load-failure additional errors,
  synchronous completion of the returned task).
- `AsyncSuspensionTests` — construct-family suspension coverage, deterministic
  held-run incompleteness + correct resumption, cache-miss callback exactly-once/no-
  replay assertions, awaited host-exception identity + depth conservation, async
  deconstruction shared-bind reuse, concurrent sync/async lanes over one shared parsed
  root, retained-resource-limit parity.
- `AsyncCancellationTests` — the Phase 1 matrix on the async surface: already-cancelled
  evaluation and source-processing tokens (canceled task, token identity, nothing
  evaluated), mid-run via the async seam, completion-edge, cancellation while genuinely
  suspended, never-a-retained-error, uncancelled-token inertness, depth-conservation
  after unwind.
- `AsyncStackDepthTests` — structured-outcome pins on 1 MiB / 384 KiB threads (the
  384 KiB flat-spine pin holds for the twin machine: it stays iterative, one async
  driver frame).

## Performance

`AsyncEvaluationBenchmarks` (BenchmarkDotNet, `benchmarks/KatLang.Benchmarks`) compares
four modes per scenario: SyncOptimized (production baseline), SyncGeneric (the strategy
mode the twins mirror — fair twin baseline), AsyncFastPath (public `RunAsync`, default
cache), AsyncTwinPath (async-capable cache, no actual suspension).

Measured (Release, .NET 10; headline pairs re-run on an idle machine — the
allocation columns are exact):

- **Synchronous APIs**: unchanged by construction — the synchronous evaluator differs
  by one `partial` keyword; no code it executes was touched.
- **AsyncFastPath vs SyncOptimized** (idle-machine run): time identical within noise
  (ScalarHelperSumCalls 25.58 µs vs 25.84 µs; RepeatManyIterations 2,448 µs vs
  2,476 µs — the fast path keeps the OPTIMIZED loop executor, because it IS the
  synchronous pipeline); allocations +0.05 KB per run, exactly the completed `Task`
  plus async-method plumbing (41.46 KB vs 41.41 KB).
- **AsyncTwinPath vs SyncGeneric** (idle-machine run): allocations essentially
  IDENTICAL or lower (RepeatManyIterations 82,663 KB vs 82,666 KB;
  ScalarHelperSumCalls 37.56 KB vs 41.41 KB) — synchronously-completing
  `async ValueTask` twins keep their state machines on the stack and never box. CPU:
  +30% on the call/property-shaped scenario (33.58 µs vs 25.92 µs) and +17% on
  generic-loop-iteration-heavy work (33.0 ms vs 28.2 ms). A contended earlier full
  sweep additionally put the most callback-dense fused-pipeline-replacement shape
  (SequenceFilterCountEvenRange) at roughly 2–3× with high variance. This cost is
  pay-per-use: it exists only on runs that explicitly request async capability
  (since Phase 3, exactly the runs configured with asynchronous host operations), and
  a genuinely asynchronous workload's IO dwarfs it; sequencing-overhead reduction
  (e.g. per-subtree async-free fast paths inside the twins) is an available
  refinement, not an architectural change.

# Phase 3: Public asynchronous host operations (August 2026)

Status: implemented at v0.8.169 (same related development set — deliberately no
version bump). C#-only host-execution surface; no Lean change and NO KatLang language
change: async remains a hosting capability, never an `await` language feature.

## What was added

- `HostOperation` — one named host-provided operation, created with
  `HostOperation.Create(name, implementation, params parameterNames)` (synchronous,
  `Func<IReadOnlyList<Result>, CancellationToken, Result>`) or
  `HostOperation.CreateAsync(...)` (asynchronous,
  `Func<IReadOnlyList<Result>, CancellationToken, ValueTask<Result>>`). Names and
  parameter names must be valid KatLang identifiers (language keywords are not
  identifiers); reserved prelude names (builtins, `Math`, `load`) are rejected at
  construction.
- `HostOperations` — a validated immutable set (`HostOperations.Create(...)`,
  duplicate names rejected), safe to share across concurrent and sequential runs like
  `EvaluationLimits`. It precomputes and caches the extended runtime and semantic
  preludes, so runs sharing one instance share declaration identities.
- `RunOptions.HostOperations` — the engine-level opt-in
  (`KatLangEngine.Run`/`RunAsync`/`EvaluateToAtoms(Async)`/`EvaluateToString(Async)`,
  `Parser.Parse(source, options)`).
- `Evaluator.Run(Expr, HostOperations, EvaluationLimits?, CancellationToken)` and
  `Evaluator.RunAsync(Expr, HostOperations, EvaluationLimits?, CancellationToken)` —
  parsed-tree reuse: parse once with the names in scope, evaluate many times under any
  host configuration with matching names. Both overloads take every parameter
  explicitly, so existing call sites (including literal-null arguments) bind unchanged.
- Engine async conveniences `EvaluateToAtomsAsync` / `EvaluateToStringAsync` — thin
  mirrors of their synchronous counterparts over `RunAsync`.

## How a program reaches a host operation

The mechanism generalizes the EXISTING host-extension model — the built-in `Math`
module — rather than inventing a parallel subsystem:

- Each operation becomes one ambient PRELUDE property whose value is a parentless
  `Algorithm.User` with the operation's declared parameters and a single output row
  `Expr.NativeCall("host:" + name, parameterNames)`. `':'` cannot appear in a KatLang
  identifier, so host dispatch names can never collide with built-in native names
  (a host operation named `Abs` coexists with `Math.Abs`).
- Programs simply write `Data` or `Fetch(id)`. Resolution is the ordinary prelude
  fallback; program-defined properties shadow operations by ownership-first lookup;
  calls bind positionally under the ordinary arity rules; zero-parameter operations
  participate in the per-run zero-argument property cache with the Lean-modeled
  `A` vs `A()` distinction (property-style access reuses within the run context,
  explicit call `Data()` bypasses that property's cache entry).
- The front end resolves the names too: `FrontEndPipeline.Process(source, options)` /
  `Parser.Parse(source, options)` hand the configuration to
  `ParameterDetector.DetectPrevalidated`, which uses the configuration's extended
  SIGNATURE-ONLY semantic prelude — so a referenced operation name never becomes an
  implicit parameter. This is the same name-level agreement between the runtime and
  semantic preludes that `Math` relies on; the evaluator resolves against the
  configuration's extended RUNTIME prelude selected in `CreateRootCtx`.
- Dispatch happens where a Math native dispatches: the shared `EvalNativeCall`
  consults the run's registry first (synchronous operations, both pipelines), and the
  async twin's `EvalCountedAsync` carries ONE new guarded `Expr.NativeCall` case that
  awaits an ASYNCHRONOUS operation's `ValueTask` — exactly the "adding an operation
  class means adding an await site in the already-async twin" extension Phase 2 was
  built for. The configuration itself rides the run-scoped `EvaluationBudget`
  (immutable configuration on the run-identity object), so the prelude choice and the
  dispatch registry can never disagree within a run and the hot by-value `EvalCtx`
  struct did not grow.

## Contracts

- **Invocation**: the delegate receives one evaluated `Result` per declared parameter,
  in declaration order (empty list for zero-parameter operations), plus the run's
  evaluation cancellation token. It must return a non-null `Result` (public
  constructors: `Result.Atom`, `Result.Str`, `Result.SequenceValue`,
  `Result.ListValue`); a null return is a fail-loud `InvalidOperationException` (host
  contract violation). One KatLang-level evaluation = exactly one invocation.
- **Suspension (exactly-once)**: an incomplete awaitable from an asynchronous
  operation suspends the whole evaluation spine — no thread is blocked, `RunAsync`
  does not imply background-thread execution, and thread placement of the resumption
  belongs to the host awaitable and the runtime — and resumes it at the same point
  when the operation completes. Nothing is replayed: suspension/resumption is the C#
  state machine of the twin spine, and the no-replay property is pinned with
  deterministically gated operations (nested depth, cache-hit/miss, per-element
  callback work).
- **Cancellation**: Phase 1 semantics unchanged. The operation receives the exact
  evaluation token (identity-comparable); a token cancelled while the run is
  suspended is observed as soon as evaluation resumes (a dedicated observation after
  the await, ahead of the next chokepoint), surfacing as
  `OperationCanceledException` carrying the supplied token through the returned task
  — never an `EvalError`, never a retained binding. A host that itself throws
  cancellation with the supplied token produces the same outcome. Budget conservation
  on unwind is the shared `try/finally` protocol.
- **Host exceptions**: evaluator/language failures remain KatLang errors (arity
  mismatches on host-operation calls are ordinary diagnostics); exceptions thrown by
  host delegates, and faulted awaitables, propagate to the host UNCHANGED, by
  identity — the same contract as the internal cache seam. A host wanting a
  KatLang-visible failure returns a value encoding it.
- **Synchronous compatibility**: synchronous operations work on every entry point and
  never wrap values in fake completed tasks. `KatLangEngine.RunAsync` with only
  synchronous operations keeps the synchronous FAST PATH (completes synchronously,
  optimizers eligible as usual). Synchronous entry points reject a configuration
  containing an asynchronous operation with `InvalidOperationException` BEFORE any
  parsing or evaluation.

## Routing (enforced, not documented)

`RequiresAsyncEvaluationPath` now names exactly two async-capable run components: an
async-capable zero-argument property cache (the internal Phase 2 seam) and a
configured asynchronous host operation. Enforcement:

- Public async entry points construct an async-capable run cache whenever the
  configuration contains an asynchronous operation (the twin path awaits the property
  seam, so the two capabilities travel together).
- Internal async entries fail loud (`InvalidOperationException`) if asynchronous
  operations are configured with a sync-only cache.
- Synchronous entries (`Evaluator.Run*`, `KatLangEngine.Run`,
  `EvaluateToAtoms`/`EvaluateToString`, and the internal sync family) throw before
  evaluating anything when the configuration contains an asynchronous operation.
- An asynchronous operation reaching the synchronous `EvalNativeCall` anyway is a
  fail-loud ownership violation (mirroring `ThrowIfAsyncStrategyPinningViolated`).
- A `HostOperations` set is immutable, so no asynchronous operation can APPEAR after
  routing committed to the synchronous pipeline.

Strategy pinning is unchanged from Phase 2: the twin path pins the generic
loop/sequence strategies; synchronous host operations on the synchronous pipeline
coexist with the optimizers untouched (the loop planner already rejects every
`NativeCall`/call shape a host operation can appear in, so loop steps containing host
operations fall back to the generic loop — pinned by test).

## Known limitations (documented and pinned)

- Like `open Math` + `[1, 2, 3].map(Abs)` today, a native-call wrapper referenced
  DIRECTLY as a flat higher-order callback fails with `Unknown name: x` (the flat
  callback funnel binds parameters into the counted environment, which native-call
  bodies do not read). Wrap the operation in a user property
  (`Step(x) = Enrich(x)`) for callback positions. Host operations deliberately
  inherit Math-member behavior here; any future lift must cover both together
  (pinned by `DirectFlatCallbackReference_InheritsTheMathMemberLimitation_Identically`).
- Editor semantic models (`src/KatLang/Semantics/`) keep their static prelude: hover/
  resolution does not surface host operations yet. Engine and evaluator behavior is
  complete; semantic-model awareness is deferred until an editor host needs it.
- `RunFlat`/`RunFlatAsync` have no host-operation overloads; use the engine
  conveniences or project a `Run` result (`RunResult.Success.Atoms`,
  `Result.ToHostAtoms`).

## Performance

- The no-configuration paths are unchanged in structure: `EvalNativeCall` gained one
  predicted-null registry check ahead of the built-in switch, `EvalCtx` did not grow
  (the configuration rides the existing `EvaluationBudget` reference), and the
  synchronous entry points gained one null-check guard each. The Phase 2 fast-path
  and twin benchmarks (`AsyncEvaluationBenchmarks`) remain the relevant
  characterization; host-operation runs add one prefix check, one dictionary lookup,
  and one read-only argument array per invocation. Configured runs skip the dictionary
  entirely for Math natives because their names lack the `host:` prefix.
  Native-signature integrity validation is an O(1) reference check on synthesized
  wrappers (only host-constructed native calls need an element comparison).
- Prelude extension cost is paid once per `HostOperations` INSTANCE (cached extended
  preludes), not per run.

## Divergence pinning

`tests/KatLang.Tests/Hosting/`:

- `HostOperationApiTests` — construction validation, synchronous engine/evaluator
  behavior, argument order and full-value passing, shadowing, `Data` vs `Data()`
  cache contract, builtin-argument and loop-step paths, arity diagnostics, host
  exception identity, reentrancy, sync-entry rejection of async configurations, and
  the corpus-wide differential that an UNUSED configuration (sync or async) changes
  no language-spec program's outcome.
- `AsyncHostOperationTests` — fast-path routing with synchronous operations,
  deterministically gated genuine suspension/resumption (top-level and nested),
  exactly-once/no-replay, per-element callback suspension, cache-hit no-duplicate
  work, token identity, cancellation while suspended (evaluator-observed and
  host-observed), host exception and faulted-awaitable identity, depth conservation
  after host faults, concurrent independent runs, one shared configuration across
  concurrent runs, shared parsed tree under different host configurations with a
  synchronous lane completing while an async lane is suspended, sync/async semantic
  equivalence, and the async engine conveniences.
