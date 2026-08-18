namespace KatLang.Tests.ConcurrencyReentrancy;

/// <summary>
/// One two-lane concurrency differential case: compute each lane's sequential
/// baseline, then run both lanes concurrently (barrier-released dedicated
/// threads) for several rounds and require every concurrent observation to
/// equal its own sequential baseline. Baselines are recomputed per round
/// BEFORE the concurrent round, which doubles as sequential repeat-stability:
/// a mutation that accumulates state across runs (a shared budget, a global
/// cache) is killed by the baselines themselves, deterministically, before
/// any scheduling is involved.
/// </summary>
public sealed record ConcurrencyPairCase
{
    public required string Id { get; init; }

    public required ConcurrencyScenario Scenario { get; init; }

    /// <summary>The isolation invariant this case pins, with implementation anchor.</summary>
    public required string Invariant { get; init; }

    public required string ProgramA { get; init; }

    public required EvalEntryPoint EntryA { get; init; }

    public required string ProgramB { get; init; }

    public required EvalEntryPoint EntryB { get; init; }

    /// <summary>Optional per-lane limits. <see cref="EvaluationLimits"/> is an
    /// immutable, caller-shareable options object; cases may deliberately alias
    /// ONE instance into both lanes (see <see cref="ConcurrencyCorpus.SharedLimits"/>)
    /// to pin that sharing options never shares counters.</summary>
    public EvaluationLimits? LimitsA { get; init; }

    public EvaluationLimits? LimitsB { get; init; }

    /// <summary>Optional POWER check: required prefix of the lane's sequential
    /// baseline ("ok", "err", "engine ok", "engine evalFailure"). Set on cases
    /// whose meaning depends on the outcome class — a failure case whose
    /// program quietly stops failing (or a zero-output case that starts
    /// emitting) has lost its point, and pure differential equality would not
    /// notice.</summary>
    public string? ExpectedClassA { get; init; }

    public string? ExpectedClassB { get; init; }

    /// <summary>Concurrent rounds after the baselines. Each round re-runs both
    /// lanes simultaneously; assertions are interleaving-independent, so any
    /// scheduling outcome must satisfy them.</summary>
    public int Rounds { get; init; } = 6;

    public override string ToString() => Id;
}

/// <summary>
/// The concurrency corpus. Programs are compact counted-matrix-style
/// sentinels chosen for leverage: multi-output vs one-sequence distinctions,
/// capture/spread, nested scope creation, user calls and clause dispatch,
/// collecting parameters, loops, per-run cached zero-argument properties, and
/// deterministic failures. Expected values are never hand-snapshotted here —
/// the oracle is equality with the same lane's sequential baseline.
/// </summary>
public static class ConcurrencyCorpus
{
    // ── Sentinel programs ───────────────────────────────────────────────────

    /// <summary>Multi-output counted sentinel (spread rows, grouping, collecting
    /// forwarding) — the highest-leverage cardinality program from the counted
    /// matrix / lifetime campaigns.</summary>
    public const string MultiOut = "P0 = ()\nP1 = 7\nP2 = 10, 20\nItems(*i) = i.count\nP2*, P1, (P0, P1), Items(P2*)";

    /// <summary>Zero visible output (spread of the empty sequence).</summary>
    public const string ZeroOut = "Z = ()\nZ*";

    public const string Scalar = "6 * 7";

    /// <summary>Capture/spread interplay with index projection.</summary>
    public const string CaptureSpread = "S = 1, (2, 3), 4\nS*, (S:1)*";

    /// <summary>Per-call brace scopes: each call mints fresh scope contexts
    /// (Evaluator.AsScopeCtx) registered in the process-global owner table.</summary>
    public const string NestedScopes = "x = 2\nF(a) = {Inner = a * x\nInner}\nD = {G = 5\nG}\nF(3), D";

    public const string DeepScopes = "A = {B = {C = {V = 41\nV + 1}\nC}\nB}\nA";

    public const string UserCallHeavy = "Add(a, b) = a + b\nMul(a, b) = a * b\nCompose(x) = Add(Mul(x, 2), Mul(x, 3))\nCompose(1), Compose(2), Compose(3)";

    public const string ClauseFamily = "C(0) = 100\nC(x) = x + 1\nC(0), C(41), C(0 - 1)";

    public const string Collecting = "Q(*args) = args.count\nQ(), Q(1, 2), Q((1, 2))";

    public const string Deconstruct = "x, *y, z = (1, 2, 3, 4)\nx, y, z";

    public const string Loop = "step(s) = s * 2\nrepeat(step, 8, 1)";

    /// <summary>Legal recursion well under the depth ceiling (128).</summary>
    public const string RecursionLegal = "F(0) = 0\nF(x) = F(x - 1)\nF(60)";

    /// <summary>Deterministic depth-limit failure (runaway recursion).</summary>
    public const string RecursionRunaway = "F(x) = F(x + 1)\nF(0)";

    /// <summary>Deterministic index failure.</summary>
    public const string FailingIndex = "(1, 2):9";

    /// <summary>Substantial but legal work under a configured step budget.</summary>
    public const string HeavyLoop = "step(s) = s + 1\nrepeat(step, 4000, 0)";

    public const string PreludeMath = "Math.Pi, sum((1, 2, 3)), avg((2, 4)), min((9, 4, 7))";

    public const string CollectionBuiltins = "order((3, 1, 2)), distinct((1, 1, 2)), take((5, 6, 7), 2)";

    // Same-named/same-shaped programs with different semantics: the
    // collision-maximizing family for scope-owner and cache-identity tests.
    public const string CachedPropA = "P = 7, 8\nP, P";
    public const string CachedPropB = "P = 9\nP, P";
    public const string StructuralPropA = "Box = {P = 5}\nBox.P, Box.P";
    public const string StructuralPropB = "Box = {P = 6}\nBox.P, Box.P";
    public const string FailingProp = "P = (1, 2):9\nP, P";
    public const string PropAndBypassA = "P = 7\nP, P()";
    public const string PropAndBypassB = "P = 8\nP, P()";
    public const string ScopeShapeA = "Outer = {Mid = {Leaf = 11\nLeaf}\nMid}\nOuter, Outer";
    public const string ScopeShapeB = "Outer = {Mid = {Leaf = 22\nLeaf}\nMid}\nOuter, Outer";
    public const string OwnerErrorA = "Obj = {V = 3}\nObj.W";
    public const string OwnerErrorB = "Obj = {V = 4}\nObj.U";
    public const string ManyScopesA = "F(x) = {V = x * 2\nV}\nF(1), F(2), F(3)";
    public const string ManyScopesB = "F(x) = {V = x + 10\nV}\nF(1), F(2), F(3)";
    public const string SameNameArityA = "P = 7\nF(x) = x + P\nF(1)";
    public const string SameNameArityB = "P = 100\nF(x, y) = x * y + P\nF(2, 3)";

    /// <summary>Clean post-failure sentinel run sequentially after every
    /// ConcurrentFailure round: concurrency + failure must leave no
    /// process-global evaluator state behind.</summary>
    public const string CleanupSentinel = MultiOut;

    // ── Module-backed engine sentinels (lifetime-campaign shapes) ───────────

    public const string ModuleProgram = "open Lib\npublic Lib = load('https://katlang.org/conc/m.kat')\nVals*, Extra";

    /// <summary>3 output rows (Vals spread 2 + Extra).</summary>
    public const string ModuleContentA = "public Vals = 1, 2\npublic Extra = 9";

    /// <summary>4 output rows (Vals spread 3 + Extra).</summary>
    public const string ModuleContentB = "public Vals = 5, 6, 7\npublic Extra = 8";

    // ── Outer programs whose instrumented property access sits INSIDE a
    // sensitive evaluation phase (reentrancy at sensitive semantic points) ──

    /// <summary>First property access happens inside a user-function call.</summary>
    public const string SensitiveUserCall = "P = 5\nF(x) = x + P\nF(1), F(2)";

    /// <summary>First property access happens inside a loop step.</summary>
    public const string SensitiveLoopStep = "P = 3\nstep(s) = s + P\nrepeat(step, 4, 0)";

    /// <summary>First property access happens inside a map-callback invocation.</summary>
    public const string SensitiveMapCallback = "P = 2\nM(x) = x * P\n[1, 2, 3].map(M)";

    /// <summary>ONE immutable limits instance deliberately aliased into both
    /// lanes of the shared-limits case: options are documented caller-shareable
    /// because counters live in the per-run <c>EvaluationBudget</c>, never in
    /// the options object.</summary>
    public static readonly EvaluationLimits SharedLimits = new() { MaxSteps = 60_000 };

    /// <summary>A step budget the heavy loop deterministically exceeds
    /// (~4000 iterations; generic loop path charges at least one step per
    /// iteration).</summary>
    public static readonly EvaluationLimits TinySteps = new() { MaxSteps = 100 };

    public static IReadOnlyList<ConcurrencyPairCase> PairCases { get; } =
    [
        // ── IndependentRun ──────────────────────────────────────────────────
        new()
        {
            Id = "indep/multi-vs-scalar-counted",
            Scenario = ConcurrencyScenario.IndependentRun,
            Invariant = "Independent RunCounted calls share nothing: each observes its baseline count/shape/value (fresh EvaluationBudget + fresh RunScopedZeroArgPropertyResultCache per call, Evaluator.CreateRootCtx).",
            ProgramA = MultiOut, EntryA = EvalEntryPoint.RunCounted,
            ProgramB = Scalar, EntryB = EvalEntryPoint.RunCounted,
        },
        new()
        {
            Id = "indep/zero-vs-multi-counted",
            Scenario = ConcurrencyScenario.IndependentRun,
            Invariant = "A zero-output run beside a multi-output run keeps both emitted counts exact (root output accumulation is per-run state).",
            ProgramA = ZeroOut, EntryA = EvalEntryPoint.RunCounted,
            ProgramB = MultiOut, EntryB = EvalEntryPoint.RunCounted,
            ExpectedClassA = "ok", ExpectedClassB = "ok",
        },
        new()
        {
            Id = "indep/capture-vs-collect-plain",
            Scenario = ConcurrencyScenario.IndependentRun,
            Invariant = "Capture/spread and collecting-parameter machinery hold no shared mutable state across public Run calls.",
            ProgramA = CaptureSpread, EntryA = EvalEntryPoint.RunPlain,
            ProgramB = Collecting, EntryB = EvalEntryPoint.RunPlain,
        },
        new()
        {
            Id = "indep/scopes-vs-clause-engine",
            Scenario = ConcurrencyScenario.IndependentRun,
            Invariant = "Full engine runs (front end + evaluation + display) are independent: nested scope creation beside clause dispatch.",
            ProgramA = NestedScopes, EntryA = EvalEntryPoint.EngineRun,
            ProgramB = ClauseFamily, EntryB = EvalEntryPoint.EngineRun,
        },
        new()
        {
            Id = "indep/loop-vs-calls-flat",
            Scenario = ConcurrencyScenario.IndependentRun,
            Invariant = "The public host-atom boundary (RunFlat) is independent per call: loop state beside user calls.",
            ProgramA = Loop, EntryA = EvalEntryPoint.RunFlat,
            ProgramB = UserCallHeavy, EntryB = EvalEntryPoint.RunFlat,
        },
        new()
        {
            Id = "indep/deconstruct-vs-recursion-counted",
            Scenario = ConcurrencyScenario.IndependentRun,
            Invariant = "Deconstruction binding (run-scoped DeconstructionBindingCache) beside legal recursion depth: per-run caches and depth counters do not interact.",
            ProgramA = Deconstruct, EntryA = EvalEntryPoint.RunCounted,
            ProgramB = RecursionLegal, EntryB = EvalEntryPoint.RunCounted,
        },

        // ── CrossEntryPoint ─────────────────────────────────────────────────
        new()
        {
            Id = "cross/plain-vs-counted",
            Scenario = ConcurrencyScenario.CrossEntryPoint,
            Invariant = "Evaluator.Run and Evaluator.RunCounted running simultaneously on the same program text do not interact (independent root contexts).",
            ProgramA = MultiOut, EntryA = EvalEntryPoint.RunPlain,
            ProgramB = MultiOut, EntryB = EvalEntryPoint.RunCounted,
        },
        new()
        {
            Id = "cross/plain-vs-engine",
            Scenario = ConcurrencyScenario.CrossEntryPoint,
            Invariant = "A raw evaluator run beside a full engine run (its own front end, DisplayDecimals property probe, and display) do not interact.",
            ProgramA = Scalar, EntryA = EvalEntryPoint.RunPlain,
            ProgramB = MultiOut, EntryB = EvalEntryPoint.EngineRun,
        },
        new()
        {
            Id = "cross/counted-vs-engine-zero",
            Scenario = ConcurrencyScenario.CrossEntryPoint,
            Invariant = "Zero-output semantics survive cross-entry-point concurrency (counted n=0 vs engine zero-row display).",
            ProgramA = ZeroOut, EntryA = EvalEntryPoint.RunCounted,
            ProgramB = ZeroOut, EntryB = EvalEntryPoint.EngineRun,
            ExpectedClassA = "ok", ExpectedClassB = "engine ok",
        },
        new()
        {
            Id = "cross/flat-vs-counted",
            Scenario = ConcurrencyScenario.CrossEntryPoint,
            Invariant = "The host-atom projection beside a counted run: list/sequence opening at the host boundary is per-run.",
            ProgramA = Loop, EntryA = EvalEntryPoint.RunFlat,
            ProgramB = CaptureSpread, EntryB = EvalEntryPoint.RunCounted,
        },
        new()
        {
            Id = "cross/flat-vs-engine",
            Scenario = ConcurrencyScenario.CrossEntryPoint,
            Invariant = "RunFlat beside a prelude-consuming engine run: shared immutable prelude wiring, independent budgets.",
            ProgramA = UserCallHeavy, EntryA = EvalEntryPoint.RunFlat,
            ProgramB = PreludeMath, EntryB = EvalEntryPoint.EngineRun,
        },

        // ── SameProgram (same source, independently parsed per lane) ───────
        new()
        {
            Id = "same/multi-counted",
            Scenario = ConcurrencyScenario.SameProgram,
            Invariant = "The same multi-output source in both lanes: no state is keyed by source text or structural shape (each lane parses and runs its own tree).",
            ProgramA = MultiOut, EntryA = EvalEntryPoint.RunCounted,
            ProgramB = MultiOut, EntryB = EvalEntryPoint.RunCounted,
        },
        new()
        {
            Id = "same/zero-engine",
            Scenario = ConcurrencyScenario.SameProgram,
            Invariant = "The same zero-output source through two simultaneous engine runs.",
            ProgramA = ZeroOut, EntryA = EvalEntryPoint.EngineRun,
            ProgramB = ZeroOut, EntryB = EvalEntryPoint.EngineRun,
        },
        new()
        {
            Id = "same/deep-scopes-plain",
            Scenario = ConcurrencyScenario.SameProgram,
            Invariant = "The same deeply nested scope program in both lanes: every lane mints its own ScopeCtx chain in the process-global owner table without cross-talk.",
            ProgramA = DeepScopes, EntryA = EvalEntryPoint.RunPlain,
            ProgramB = DeepScopes, EntryB = EvalEntryPoint.RunPlain,
        },
        new()
        {
            Id = "same/usercalls-counted",
            Scenario = ConcurrencyScenario.SameProgram,
            Invariant = "The same call-heavy source concurrently: call-stack contexts are per-run values.",
            ProgramA = UserCallHeavy, EntryA = EvalEntryPoint.RunCounted,
            ProgramB = UserCallHeavy, EntryB = EvalEntryPoint.RunCounted,
        },
        new()
        {
            Id = "same/failing-index-counted",
            Scenario = ConcurrencyScenario.SameProgram,
            Invariant = "The same FAILING source concurrently: identical structured failures, no cross-run error-state bleed.",
            ProgramA = FailingIndex, EntryA = EvalEntryPoint.RunCounted,
            ProgramB = FailingIndex, EntryB = EvalEntryPoint.RunCounted,
            ExpectedClassA = "err", ExpectedClassB = "err",
        },

        // ── ScopeOwnership ──────────────────────────────────────────────────
        new()
        {
            Id = "scope/identical-shape-distinct-identity",
            Scenario = ConcurrencyScenario.ScopeOwnership,
            Invariant = "Identical scope structure and names with distinct identities: ScopeOwnerAlgorithms (ConditionalWeakTable, fresh ScopeCtx keys per wiring) never associates one run's scopes with the other run's algorithms.",
            ProgramA = ScopeShapeA, EntryA = EvalEntryPoint.EngineRun,
            ProgramB = ScopeShapeB, EntryB = EvalEntryPoint.EngineRun,
        },
        new()
        {
            Id = "scope/error-owner-paths",
            Scenario = ConcurrencyScenario.ScopeOwnership,
            Invariant = "Errors that render owner/member names (structural dot miss) name each run's OWN identifiers; concurrent diagnostics cannot swap owners (Evaluator.TryGetAlgorithmPath reads the owner table).",
            ProgramA = OwnerErrorA, EntryA = EvalEntryPoint.EngineRun,
            ProgramB = OwnerErrorB, EntryB = EvalEntryPoint.EngineRun,
            ExpectedClassA = "engine evalFailure", ExpectedClassB = "engine evalFailure",
        },
        new()
        {
            Id = "scope/structural-dot-same-names",
            Scenario = ConcurrencyScenario.ScopeOwnership,
            Invariant = "Same-named structural members under same-shaped owners resolve to each run's own values (structural owner identity distinguishes distinct declaration lists).",
            ProgramA = StructuralPropA, EntryA = EvalEntryPoint.RunCounted,
            ProgramB = StructuralPropB, EntryB = EvalEntryPoint.RunCounted,
        },
        new()
        {
            Id = "scope/many-scopes-per-call",
            Scenario = ConcurrencyScenario.ScopeOwnership,
            Invariant = "Many per-call brace scopes minted concurrently in both lanes (same shape, same names, different bodies) stay correctly owned.",
            ProgramA = ManyScopesA, EntryA = EvalEntryPoint.RunCounted,
            ProgramB = ManyScopesB, EntryB = EvalEntryPoint.RunCounted,
        },
        new()
        {
            Id = "scope/same-names-different-arity",
            Scenario = ConcurrencyScenario.ScopeOwnership,
            Invariant = "Same property/function/parameter names with different arities and values across concurrent runs: name-keyed contamination anywhere would flip one lane's result.",
            ProgramA = SameNameArityA, EntryA = EvalEntryPoint.RunCounted,
            ProgramB = SameNameArityB, EntryB = EvalEntryPoint.RunCounted,
        },

        // ── RunScopedCache ──────────────────────────────────────────────────
        new()
        {
            Id = "cache/same-name-different-value",
            Scenario = ConcurrencyScenario.RunScopedCache,
            Invariant = "Zero-argument property caching is per run: same-named P with different values in concurrent runs each serve their own cached value (RunScopedZeroArgPropertyResultCache is constructed per entry-point call; cache keys carry the run identity).",
            ProgramA = CachedPropA, EntryA = EvalEntryPoint.RunCounted,
            ProgramB = CachedPropB, EntryB = EvalEntryPoint.RunCounted,
        },
        new()
        {
            Id = "cache/structural-same-shape",
            Scenario = ConcurrencyScenario.RunScopedCache,
            Invariant = "STRUCTURAL access cache entries (StructuralOwnerIdentity keys distinct declaration lists) never alias across concurrent runs of same-shaped programs.",
            ProgramA = StructuralPropA, EntryA = EvalEntryPoint.RunCounted,
            ProgramB = StructuralPropB, EntryB = EvalEntryPoint.RunCounted,
        },
        new()
        {
            Id = "cache/success-vs-failing-property",
            Scenario = ConcurrencyScenario.RunScopedCache,
            Invariant = "A failing cached property in one run (errors are never stored — RunScopedZeroArgPropertyResultCache stores on success only) cannot poison or be masked by the other run's same-named success.",
            ProgramA = CachedPropA, EntryA = EvalEntryPoint.RunCounted,
            ProgramB = FailingProp, EntryB = EvalEntryPoint.RunCounted,
            ExpectedClassA = "ok", ExpectedClassB = "err",
        },
        new()
        {
            Id = "cache/property-vs-call-bypass",
            Scenario = ConcurrencyScenario.RunScopedCache,
            Invariant = "The semantic A-vs-A() distinction (property access may cache; explicit call bypasses) survives concurrency in both lanes.",
            ProgramA = PropAndBypassA, EntryA = EvalEntryPoint.RunCounted,
            ProgramB = PropAndBypassB, EntryB = EvalEntryPoint.RunCounted,
        },

        // ── BudgetIsolation ─────────────────────────────────────────────────
        new()
        {
            Id = "budget/shared-limits-instance",
            Scenario = ConcurrencyScenario.BudgetIsolation,
            Invariant = "ONE EvaluationLimits instance aliased into both concurrent lanes: limits are immutable configuration; counters live in each run's own EvaluationBudget (EvaluationBudget doc contract).",
            ProgramA = HeavyLoop, EntryA = EvalEntryPoint.RunCounted, LimitsA = SharedLimits,
            ProgramB = HeavyLoop, EntryB = EvalEntryPoint.RunCounted, LimitsB = SharedLimits,
            ExpectedClassA = "ok", ExpectedClassB = "ok",
        },
        new()
        {
            Id = "budget/overbudget-vs-small",
            Scenario = ConcurrencyScenario.BudgetIsolation,
            Invariant = "A run failing on ITS step budget beside an unlimited small run: the failure consumes nothing from the other run and vice versa.",
            ProgramA = HeavyLoop, EntryA = EvalEntryPoint.RunCounted, LimitsA = TinySteps,
            ProgramB = Scalar, EntryB = EvalEntryPoint.RunCounted,
            ExpectedClassA = "err", ExpectedClassB = "ok",
        },
        new()
        {
            Id = "budget/small-vs-overbudget",
            Scenario = ConcurrencyScenario.BudgetIsolation,
            Invariant = "Role reversal of overbudget-vs-small: order/lane assignment cannot matter.",
            ProgramA = Scalar, EntryA = EvalEntryPoint.RunCounted,
            ProgramB = HeavyLoop, EntryB = EvalEntryPoint.RunCounted, LimitsB = TinySteps,
            ExpectedClassA = "ok", ExpectedClassB = "err",
        },
        new()
        {
            Id = "budget/depth-failure-vs-legal-recursion",
            Scenario = ConcurrencyScenario.BudgetIsolation,
            Invariant = "A depth-limit failure (always-active per-run depth counter) beside legal recursion: depth is balanced per run, never shared.",
            ProgramA = RecursionRunaway, EntryA = EvalEntryPoint.RunCounted,
            ProgramB = RecursionLegal, EntryB = EvalEntryPoint.RunCounted,
            ExpectedClassA = "err", ExpectedClassB = "ok",
        },

        // ── ConcurrentFailure ───────────────────────────────────────────────
        new()
        {
            Id = "fail/success-vs-index-error",
            Scenario = ConcurrencyScenario.ConcurrentFailure,
            Invariant = "A structured runtime failure beside a multi-output success: failure unwind (balanced budget releases) is invisible to the concurrent run.",
            ProgramA = MultiOut, EntryA = EvalEntryPoint.RunCounted,
            ProgramB = FailingIndex, EntryB = EvalEntryPoint.RunCounted,
            ExpectedClassA = "ok", ExpectedClassB = "err",
        },
        new()
        {
            Id = "fail/index-vs-depth",
            Scenario = ConcurrencyScenario.ConcurrentFailure,
            Invariant = "Two different failure classes concurrently: each run reports its own error category.",
            ProgramA = FailingIndex, EntryA = EvalEntryPoint.RunCounted,
            ProgramB = RecursionRunaway, EntryB = EvalEntryPoint.RunCounted,
            ExpectedClassA = "err", ExpectedClassB = "err",
        },
        new()
        {
            Id = "fail/budget-failure-vs-prelude-success",
            Scenario = ConcurrencyScenario.ConcurrentFailure,
            Invariant = "A step-budget failure beside a prelude-consuming success: budget exhaustion in one run cannot leak into shared prelude wiring or the other run's verdict.",
            ProgramA = HeavyLoop, EntryA = EvalEntryPoint.RunCounted, LimitsA = TinySteps,
            ProgramB = PreludeMath, EntryB = EvalEntryPoint.RunCounted,
            ExpectedClassA = "err", ExpectedClassB = "ok",
        },
        new()
        {
            Id = "fail/multiout-vs-runaway",
            Scenario = ConcurrencyScenario.ConcurrentFailure,
            Invariant = "Multi-output success beside runaway-recursion failure: counted output slots are unaffected by a concurrent deep unwind.",
            ProgramA = MultiOut, EntryA = EvalEntryPoint.RunCounted,
            ProgramB = RecursionRunaway, EntryB = EvalEntryPoint.RunCounted,
            ExpectedClassA = "ok", ExpectedClassB = "err",
        },
        new()
        {
            Id = "fail/engine-failure-vs-engine-success",
            Scenario = ConcurrencyScenario.ConcurrentFailure,
            Invariant = "Engine-level failure display beside engine success display: diagnostic rendering shares only immutable formatter tables.",
            ProgramA = FailingIndex, EntryA = EvalEntryPoint.EngineRun,
            ProgramB = Scalar, EntryB = EvalEntryPoint.EngineRun,
            ExpectedClassA = "engine evalFailure", ExpectedClassB = "engine ok",
        },

        // ── SharedImmutable ─────────────────────────────────────────────────
        new()
        {
            Id = "immutable/prelude-both-lanes",
            Scenario = ConcurrencyScenario.SharedImmutable,
            Invariant = "Both lanes consume the shared static prelude/Math ASTs simultaneously: wiring uses derived copies (WithParent), never mutating the shared originals — repeated rounds would expose any mutation.",
            ProgramA = PreludeMath, EntryA = EvalEntryPoint.RunCounted,
            ProgramB = PreludeMath, EntryB = EvalEntryPoint.RunCounted,
        },
        new()
        {
            Id = "immutable/collection-builtins",
            Scenario = ConcurrencyScenario.SharedImmutable,
            Invariant = "Collection builtins (shared static BuiltinRegistry metadata) used concurrently across two entry points produce exact per-run lists.",
            ProgramA = CollectionBuiltins, EntryA = EvalEntryPoint.RunCounted,
            ProgramB = CollectionBuiltins, EntryB = EvalEntryPoint.RunFlat,
        },
        new()
        {
            Id = "immutable/math-vs-math",
            Scenario = ConcurrencyScenario.SharedImmutable,
            Invariant = "Two different Math-member consumers concurrently: the shared MathAlgorithm AST serves both without cross-talk.",
            ProgramA = "Math.Pi, sum((1, 2))", EntryA = EvalEntryPoint.RunCounted,
            ProgramB = "Math.Pi * 2, avg((4, 8))", EntryB = EvalEntryPoint.RunCounted,
        },
    ];

    /// <summary>Programs for the same-AST-OBJECT lanes: one parsed tree handed
    /// to two concurrent evaluations. Includes a failing program (shared tree +
    /// error path) and the scope-heavy shapes most likely to expose hidden
    /// mutation of prepared AST objects.</summary>
    public static IReadOnlyList<(string Id, string Program)> SameAstPrograms { get; } =
    [
        ("sameast/multi", MultiOut),
        ("sameast/scalar", Scalar),
        ("sameast/deep-scopes", DeepScopes),
        ("sameast/usercall-heavy", UserCallHeavy),
        ("sameast/cached-property", CachedPropA),
        ("sameast/failing-index", FailingIndex),
    ];
}
