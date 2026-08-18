using static KatLang.Tests.LifetimeDifferential.LifetimeScenario;

namespace KatLang.Tests.LifetimeDifferential;

/// <summary>
/// Front-end/module-loader lifetime differential corpus.
///
/// <para>THE INVARIANT: for a KatLang program P, observable semantics are
/// independent of unrelated prior front-end/module-loader/evaluator activity,
/// except where KatLang explicitly specifies persistent state. The production
/// isolation boundaries are: a fresh <see cref="ModuleLoader"/> +
/// <see cref="SourceProcessingBudget"/> per front-end elaboration
/// (<c>FrontEndPipeline.Process</c>), fresh run-scoped caches/budgets per
/// evaluation (<c>Evaluator.CreateRootCtx</c>), and immutable process statics
/// (BuiltinRegistry, prelude algorithms). The only state that crosses runs by
/// design is the caller-owned <c>DownloadCode</c> delegate — so every polluted
/// history here reuses ONE <see cref="LifetimeModuleHost"/> instance across
/// its steps, exactly the seam a real reusable host would share.</para>
///
/// <para>DOCUMENTED persistent state this corpus deliberately does NOT treat
/// as a defect (pinned instead by the loader-instance facts in
/// <c>LifetimeDifferentialTests</c>): one <see cref="ModuleLoader"/> INSTANCE
/// is one module-elaboration scope — its URL-keyed module cache and its
/// source-processing budget are shared by every <c>Elaborate</c> call on that
/// instance, so within one instance a module identity pins its first
/// successfully loaded content, and budget headroom accumulates.</para>
///
/// <para>The oracle is pure differential equality (fresh observation ==
/// history-polluted observation) over outcome class, neutral raw structure,
/// root emitted count, structural cardinality shape, error category, display,
/// and ordered front-end diagnostics. No expectation is recorded from the
/// implementation; the per-case outcome-class annotations only keep each
/// scenario's discriminating power visible.</para>
/// </summary>
public static class LifetimeDifferentialCorpus
{
    // ── Target programs ──────────────────────────────────────────────────────

    /// <summary>Multi-output counted sentinel: spread, capture, visible empty,
    /// collecting parameter — a leak cannot hide behind a scalar.</summary>
    public const string TargetCounted =
        "P0 = ()\nP1 = 7\nP2 = 10, 20\nItems(*i) = i.count\nP2*, P1, (P0, P1), Items(P2*)";

    /// <summary>Zero-output target: n=0 is a first-class observation.</summary>
    public const string TargetZero = "Z = ()\nZ*";

    /// <summary>Scope-graph-heavy target: lexical capture, clause family,
    /// sequence-value pattern, nested brace shadowing, collecting parameter —
    /// every name also appears (with incompatible meanings) in the histories.</summary>
    public const string TargetScopes =
        "x = 5\nF(a) = a + x\nItems(*i) = i\nD(0) = 111\nD(v) = F(v)\n" +
        "G((h, *t)) = t.count\nInner = {x = 50\nF(x)}\n" +
        "D(0), D(2), G((1, 2, 3)), Inner, Items(x)*";

    /// <summary>Runtime-error target: error-category equality across histories.</summary>
    public const string TargetRuntimeError = "(1, 2):9";

    // ── History programs (no modules) ───────────────────────────────────────

    /// <summary>Overlapping names with incompatible meanings: x as a different
    /// value, F with another arity, Items as a fixed-arity callee, D as a
    /// two-argument clause family.</summary>
    public const string HistB =
        "x = 99\nF(a, b) = a * b\nItems(*i) = i\nD(0, 0) = 5\nD(p, q) = p + q\n" +
        "F(x, 2), Items(3, 4), D(1, 2)";

    /// <summary>More overlap: G with a different pattern result, a different
    /// Inner scope, P2 as a scalar.</summary>
    public const string HistC =
        "G((a, *b)) = b\nInner = {x = 1\nx}\nP2 = 77\nG((1, 2))*, Inner, P2";

    public const string HistParseError = "1 ; 2";

    public const string HistParenDecl = "(y = 1)\n5";

    public const string HistRuntimeIndexError = "(1, 2):9";

    /// <summary>Unbounded recursion: rejected by the always-active dynamic depth
    /// ceiling — a resource-limit failure history.</summary>
    public const string HistRuntimeDepthError = "F(x) = F(x + 1)\nF(0)";

    // ── Module graph ─────────────────────────────────────────────────────────

    public const string UrlM = "https://katlang.org/lt/m.kat";
    public const string ModuleMv1 = "public Vals = 1, 2\npublic Extra = 9";
    public const string ModuleMv2 = "public Vals = 5, 6, 7\npublic Extra = 8";
    public const string ModuleMBroken = "Vals = 1 ; 2";

    /// <summary>Module-backed multi-output target: n and shape change with the
    /// module content, so stale module state is immediately visible.</summary>
    public const string TargetModule =
        "open Lib\npublic Lib = load('https://katlang.org/lt/m.kat')\nVals*, Extra";

    public const string HistMissingModule =
        "public L = load('https://katlang.org/lt/missing.kat')\nL.X";

    /// <summary>Elaboration-phase failure BEFORE any fetch: load in a runtime
    /// expression position.</summary>
    public const string HistLoadPosition = "1 + load('https://katlang.org/lt/m.kat')";

    public const string UrlBroken = "https://katlang.org/lt/broken.kat";
    public const string HistLoadBrokenOther =
        "public L = load('https://katlang.org/lt/broken.kat')\nL.X";

    public const string UrlC1 = "https://katlang.org/lt/c1.kat";
    public const string UrlC2 = "https://katlang.org/lt/c2.kat";
    public const string ModuleC1 = "public Other = load('https://katlang.org/lt/c2.kat')\npublic V = 1";
    public const string ModuleC2 = "public Back = load('https://katlang.org/lt/c1.kat')\npublic W = 2";
    public const string HistLoadCycle = "public L = load('https://katlang.org/lt/c1.kat')\nL.V";

    public const string HistLoadBadDomain = "public L = load('https://evil.example/x.kat')\nL.X";

    public const string UrlDb = "https://katlang.org/lt/db.kat";
    public const string UrlDc = "https://katlang.org/lt/dc.kat";
    public const string UrlDd = "https://katlang.org/lt/dd.kat";
    public const string ModuleDb = "public Dep = load('https://katlang.org/lt/dd.kat')\npublic BV = Dep.Base + 1";
    public const string ModuleDc = "public Dep = load('https://katlang.org/lt/dd.kat')\npublic CV = Dep.Base + 2";
    public const string ModuleDd = "public Base = 40";

    public const string TargetDiamondBFirst =
        "public LibB = load('https://katlang.org/lt/db.kat')\npublic LibC = load('https://katlang.org/lt/dc.kat')\nLibB.BV, LibC.CV";

    public const string TargetDiamondCFirst =
        "public LibC = load('https://katlang.org/lt/dc.kat')\npublic LibB = load('https://katlang.org/lt/db.kat')\nLibB.BV, LibC.CV";

    public const string HistLoadOnlyB = "public L = load('https://katlang.org/lt/db.kat')\nL.BV";
    public const string HistLoadOnlyC = "public L = load('https://katlang.org/lt/dc.kat')\nL.CV";

    public const string UrlN1 = "https://katlang.org/lt/n1.kat";
    public const string UrlN2 = "https://katlang.org/lt/n2.kat";
    public const string ModuleN1 = "public X = 1, 2";
    public const string ModuleN2 = "public X = 30";

    public const string TargetSameNames =
        "public L1 = load('https://katlang.org/lt/n1.kat')\npublic L2 = load('https://katlang.org/lt/n2.kat')\nL1.X*, L2.X";

    public const string HistUseN2 = "public W = load('https://katlang.org/lt/n2.kat')\nW.X + 1";

    public const string TargetRepeatedImport =
        "public L1 = load('https://katlang.org/lt/m.kat')\npublic L2 = load('https://katlang.org/lt/m.kat')\nL1.Vals*, L2.Extra";

    // ── Source identity ──────────────────────────────────────────────────────

    public const string UrlI1 = "https://katlang.org/lt/i1.kat";
    public const string UrlI2 = "https://katlang.org/lt/i2.kat";
    public const string ModuleI = "public X = 20";

    public const string TargetTwoUrlsSameText =
        "public L1 = load('https://katlang.org/lt/i1.kat')\npublic L2 = load('https://katlang.org/lt/i2.kat')\nL1.X + L2.X";

    /// <summary>Two spellings of ONE identity: the loader keys its cache and cycle
    /// detection by <c>Uri.AbsoluteUri</c>, which compresses dot segments.</summary>
    public const string TargetDotSegmentAlias =
        "public L1 = load('https://katlang.org/lt/sub/../i1.kat')\npublic L2 = load('https://katlang.org/lt/i1.kat')\nL1.X + L2.X";

    /// <summary>Host case-insensitivity: AbsoluteUri lowercases the host.</summary>
    public const string TargetHostCaseAlias =
        "public L1 = load('https://KATLANG.ORG/lt/i1.kat')\npublic L2 = load('https://katlang.org/lt/i1.kat')\nL1.X + L2.X";

    public const string UrlI3Upper = "https://katlang.org/lt/I3.kat";
    public const string UrlI3Lower = "https://katlang.org/lt/i3.kat";
    public const string ModuleI3Upper = "public X = 1";
    public const string ModuleI3Lower = "public X = 2";

    /// <summary>Path case is significant in AbsoluteUri: two distinct modules.</summary>
    public const string TargetPathCaseDistinct =
        "public L1 = load('https://katlang.org/lt/I3.kat')\npublic L2 = load('https://katlang.org/lt/i3.kat')\nL1.X + L2.X";

    // ── Name-collision extras ────────────────────────────────────────────────

    public const string TargetCollectItems = "Items(*i) = i.count\nItems(1, 2, 3)";
    public const string HistFixedItems = "Items(a, b) = a + b\nItems(1, 2)";
    public const string TargetClauseOneArity = "D(0) = 1\nD(x) = 2\nD(0), D(9)";
    public const string HistClauseTwoArity = "D(0, 0) = 5\nD(x, y) = 6\nD(0, 0), D(1, 2)";
    public const string TargetFOneParam = "F(a) = a + 1\nF(5)";
    public const string HistFTwoParams = "F(a, b) = a * b\nF(2, 3)";
    public const string TargetShadowing =
        "x = 1\nOuter = {x = 2\nInner2 = {x = 3\nx}\nInner2, x}\nOuter*, x";
    public const string HistShadowing = "x = 9\nOuter = {x = 8\nx}\nOuter, x";

    private static readonly (string Url, string Content)[] MapMv1 = [(UrlM, ModuleMv1)];
    private static readonly (string Url, string Content)[] MapMv2 = [(UrlM, ModuleMv2)];
    private static readonly (string Url, string Content)[] MapMBroken = [(UrlM, ModuleMBroken)];
    private static readonly (string Url, string Content)[] MapMv1PlusBroken =
        [(UrlM, ModuleMv1), (UrlBroken, ModuleMBroken)];
    private static readonly (string Url, string Content)[] MapCycle =
        [(UrlC1, ModuleC1), (UrlC2, ModuleC2)];
    private static readonly (string Url, string Content)[] MapDiamond =
        [(UrlDb, ModuleDb), (UrlDc, ModuleDc), (UrlDd, ModuleDd)];
    private static readonly (string Url, string Content)[] MapNames =
        [(UrlN1, ModuleN1), (UrlN2, ModuleN2)];
    private static readonly (string Url, string Content)[] MapIdentity =
        [(UrlI1, ModuleI), (UrlI2, ModuleI)];
    private static readonly (string Url, string Content)[] MapPathCase =
        [(UrlI3Upper, ModuleI3Upper), (UrlI3Lower, ModuleI3Lower)];

    public static IReadOnlyList<LifetimeCase> Cases() =>
    [
        // ── Fresh vs unrelated successful history ───────────────────────────
        new()
        {
            Id = "fresh/b-then-counted", Scenario = FreshVsPriorSuccess,
            Invariant = "an unrelated successful program leaves no parser/binder/evaluator state behind (fresh loader+budget+caches per run)",
            Target = TargetCounted, ExpectedFreshOutcome = "ok",
            History = [HistB], ExpectedHistoryOutcomes = ["ok"],
        },
        new()
        {
            Id = "fresh/c-then-counted", Scenario = FreshVsPriorSuccess,
            Invariant = "a second unrelated-name profile leaves no state behind",
            Target = TargetCounted, ExpectedFreshOutcome = "ok",
            History = [HistC], ExpectedHistoryOutcomes = ["ok"],
        },
        new()
        {
            Id = "fresh/b-c-then-counted", Scenario = FreshVsPriorSuccess,
            Invariant = "stacked unrelated histories do not accumulate observable state",
            Target = TargetCounted, ExpectedFreshOutcome = "ok",
            History = [HistB, HistC], ExpectedHistoryOutcomes = ["ok", "ok"],
        },
        new()
        {
            Id = "fresh/b-then-zero", Scenario = FreshVsPriorSuccess,
            Invariant = "a zero-output target stays zero-output after unrelated history",
            Target = TargetZero, ExpectedFreshOutcome = "ok",
            History = [HistB], ExpectedHistoryOutcomes = ["ok"],
        },
        new()
        {
            Id = "fresh/b-then-module", Scenario = FreshVsPriorSuccess,
            Invariant = "a module-backed target is unaffected by module-less prior programs",
            Target = TargetModule, ExpectedFreshOutcome = "ok", ExpectedFreshEmitted = 3,
            History = [HistB], ExpectedHistoryOutcomes = ["ok"],
            TargetModules = MapMv1,
        },
        new()
        {
            Id = "fresh/module-then-counted", Scenario = FreshVsPriorSuccess,
            Invariant = "a prior module-loading program leaves no loader state for a module-less target",
            Target = TargetCounted, ExpectedFreshOutcome = "ok",
            History = [TargetModule], ExpectedHistoryOutcomes = ["ok"],
            TargetModules = [], HistoryModules = MapMv1,
        },

        // ── Repeat stability ─────────────────────────────────────────────────
        new()
        {
            Id = "repeat/counted-once", Scenario = RepeatStability,
            Invariant = "seeing the same source before changes nothing (no memo keyed by source text or AST identity)",
            Target = TargetCounted, ExpectedFreshOutcome = "ok",
            History = [TargetCounted], ExpectedHistoryOutcomes = ["ok"],
        },
        new()
        {
            Id = "repeat/counted-twice", Scenario = RepeatStability,
            Invariant = "third execution equals first",
            Target = TargetCounted, ExpectedFreshOutcome = "ok",
            History = [TargetCounted, TargetCounted], ExpectedHistoryOutcomes = ["ok", "ok"],
        },
        new()
        {
            Id = "repeat/zero", Scenario = RepeatStability,
            Invariant = "repeat stability of a zero-output program",
            Target = TargetZero, ExpectedFreshOutcome = "ok",
            History = [TargetZero], ExpectedHistoryOutcomes = ["ok"],
        },
        new()
        {
            Id = "repeat/scopes", Scenario = RepeatStability,
            Invariant = "repeat stability of nested scopes, clause families, and patterns",
            Target = TargetScopes, ExpectedFreshOutcome = "ok",
            History = [TargetScopes], ExpectedHistoryOutcomes = ["ok"],
        },
        new()
        {
            Id = "repeat/module", Scenario = RepeatStability,
            Invariant = "re-loading the same module graph in a new run re-elaborates identically (no cross-run module cache exists)",
            Target = TargetModule, ExpectedFreshOutcome = "ok", ExpectedFreshEmitted = 3,
            History = [TargetModule], ExpectedHistoryOutcomes = ["ok"],
            TargetModules = MapMv1,
        },
        new()
        {
            Id = "repeat/runtime-error", Scenario = RepeatStability,
            Invariant = "a failing program fails identically on repeat (no retained evaluation state)",
            Target = TargetRuntimeError, ExpectedFreshOutcome = "err",
            History = [TargetRuntimeError], ExpectedHistoryOutcomes = ["err"],
        },
        new()
        {
            Id = "repeat/parse-error", Scenario = RepeatStability,
            Invariant = "a parse-failing program reports the same diagnostics on repeat (no diagnostic accumulation)",
            Target = HistParseError, ExpectedFreshOutcome = "parseError",
            History = [HistParseError], ExpectedHistoryOutcomes = ["parseError"],
        },

        // ── Parse-error poisoning ────────────────────────────────────────────
        new()
        {
            Id = "poison/parse-error-then-counted", Scenario = ParseErrorPoisoning,
            Invariant = "a failed parse retains no tokens, declarations, or diagnostics",
            Target = TargetCounted, ExpectedFreshOutcome = "ok",
            History = [HistParseError], ExpectedHistoryOutcomes = ["parseError"],
        },
        new()
        {
            Id = "poison/parse-errors-then-scopes", Scenario = ParseErrorPoisoning,
            Invariant = "stacked parse failures leave the scope graph of the next program untouched",
            Target = TargetScopes, ExpectedFreshOutcome = "ok",
            History = [HistParseError, HistParenDecl], ExpectedHistoryOutcomes = ["parseError", "parseError"],
        },
        new()
        {
            Id = "poison/paren-decl-then-counted", Scenario = ParseErrorPoisoning,
            Invariant = "the parenthesized-declaration rejection (with recovery tree) leaks nothing",
            Target = TargetCounted, ExpectedFreshOutcome = "ok",
            History = [HistParenDecl], ExpectedHistoryOutcomes = ["parseError"],
        },
        new()
        {
            Id = "poison/parse-error-then-module", Scenario = ParseErrorPoisoning,
            Invariant = "a failed parse cannot affect a later module elaboration",
            Target = TargetModule, ExpectedFreshOutcome = "ok",
            History = [HistParseError], ExpectedHistoryOutcomes = ["parseError"],
            TargetModules = MapMv1,
        },

        // ── Front-end (elaboration/guard) error poisoning ────────────────────
        new()
        {
            Id = "poison/load-position-then-module", Scenario = FrontEndErrorPoisoning,
            Invariant = "a load-position rejection (pre-fetch elaboration failure) leaves no loader or diagnostic state",
            Target = TargetModule, ExpectedFreshOutcome = "ok",
            History = [HistLoadPosition], ExpectedHistoryOutcomes = ["parseError"],
            TargetModules = MapMv1,
        },
        new()
        {
            Id = "poison/load-unavailable-then-counted", Scenario = FrontEndErrorPoisoning,
            Invariant = "the no-downloader load guard rejection poisons nothing",
            Target = TargetCounted, ExpectedFreshOutcome = "ok",
            History = [TargetModule], ExpectedHistoryOutcomes = ["parseError"],
        },

        // ── Module-load failure poisoning ────────────────────────────────────
        new()
        {
            Id = "poison/missing-module-then-counted", Scenario = ModuleLoadErrorPoisoning,
            Invariant = "a failed fetch (downloader throw) leaves no half-built module or loader state",
            Target = TargetCounted, ExpectedFreshOutcome = "ok",
            History = [HistMissingModule], ExpectedHistoryOutcomes = ["parseError"],
            TargetModules = [],
        },
        new()
        {
            Id = "poison/missing-module-then-module", Scenario = ModuleLoadErrorPoisoning,
            Invariant = "a failed fetch of one identity cannot affect a later load of another identity",
            Target = TargetModule, ExpectedFreshOutcome = "ok",
            History = [HistMissingModule], ExpectedHistoryOutcomes = ["parseError"],
            TargetModules = MapMv1,
        },
        new()
        {
            Id = "poison/broken-module-then-module", Scenario = ModuleLoadErrorPoisoning,
            Invariant = "a module whose CONTENT fails to parse is never committed and cannot poison a sibling load",
            Target = TargetModule, ExpectedFreshOutcome = "ok",
            History = [HistLoadBrokenOther], ExpectedHistoryOutcomes = ["parseError"],
            TargetModules = MapMv1PlusBroken,
        },
        new()
        {
            Id = "poison/cycle-then-counted", Scenario = ModuleLoadErrorPoisoning,
            Invariant = "a load-cycle rejection fully unwinds its in-progress set (ModuleLoader._inProgress finally-cleanup)",
            Target = TargetCounted, ExpectedFreshOutcome = "ok",
            History = [HistLoadCycle], ExpectedHistoryOutcomes = ["parseError"],
            TargetModules = MapCycle,
        },
        new()
        {
            Id = "poison/bad-domain-then-module", Scenario = ModuleLoadErrorPoisoning,
            Invariant = "an allowlist rejection (no fetch at all) poisons nothing",
            Target = TargetModule, ExpectedFreshOutcome = "ok",
            History = [HistLoadBadDomain], ExpectedHistoryOutcomes = ["parseError"],
            TargetModules = MapMv1,
        },

        // ── Runtime-error poisoning ──────────────────────────────────────────
        new()
        {
            Id = "poison/index-error-then-counted", Scenario = RuntimeErrorPoisoning,
            Invariant = "an evaluation failure leaves no evaluator preparation or cache state",
            Target = TargetCounted, ExpectedFreshOutcome = "ok",
            History = [HistRuntimeIndexError], ExpectedHistoryOutcomes = ["err"],
        },
        new()
        {
            Id = "poison/depth-error-then-counted", Scenario = RuntimeErrorPoisoning,
            Invariant = "a resource-limit rejection (dynamic depth) is run-scoped: the next run starts with full budgets",
            Target = TargetCounted, ExpectedFreshOutcome = "ok",
            History = [HistRuntimeDepthError], ExpectedHistoryOutcomes = ["err"],
        },
        new()
        {
            Id = "poison/depth-error-then-module", Scenario = RuntimeErrorPoisoning,
            Invariant = "a resource-limit rejection cannot affect a later module-backed run",
            Target = TargetModule, ExpectedFreshOutcome = "ok",
            History = [HistRuntimeDepthError], ExpectedHistoryOutcomes = ["err"],
            TargetModules = MapMv1,
        },
        new()
        {
            Id = "poison/mixed-errors-then-scopes", Scenario = RuntimeErrorPoisoning,
            Invariant = "runtime, parse, and resource failures in sequence leave nothing behind",
            Target = TargetScopes, ExpectedFreshOutcome = "ok",
            History = [HistRuntimeIndexError, HistParseError, HistRuntimeDepthError],
            ExpectedHistoryOutcomes = ["err", "parseError", "err"],
        },

        // ── Same-identity correction (failure → corrected content) ──────────
        new()
        {
            Id = "identity/broken-then-corrected", Scenario = SameIdentityCorrection,
            Invariant = "a module whose content failed to parse is NOT negatively cached: the corrected content under the SAME url must match a fresh host (commit-on-success, ModuleLoader.FetchAndSplice)",
            Target = TargetModule, ExpectedFreshOutcome = "ok", ExpectedFreshEmitted = 3,
            History = [TargetModule], ExpectedHistoryOutcomes = ["parseError"],
            TargetModules = MapMv1, HistoryModules = MapMBroken,
        },
        new()
        {
            Id = "identity/missing-then-added", Scenario = SameIdentityCorrection,
            Invariant = "a failed fetch is not remembered: adding the module afterwards matches a fresh host",
            Target = TargetModule, ExpectedFreshOutcome = "ok", ExpectedFreshEmitted = 3,
            History = [TargetModule], ExpectedHistoryOutcomes = ["parseError"],
            TargetModules = MapMv1, HistoryModules = [],
        },
        new()
        {
            Id = "identity/v1-then-v2", Scenario = SameIdentityCorrection,
            Invariant = "replacing module content under the same url between RUNS is fully visible: the emitted count and shape follow the new content (no cross-run module cache)",
            Target = TargetModule, ExpectedFreshOutcome = "ok", ExpectedFreshEmitted = 4,
            History = [TargetModule], ExpectedHistoryOutcomes = ["ok"],
            TargetModules = MapMv2, HistoryModules = MapMv1,
        },

        // ── Success-to-failure correctness ───────────────────────────────────
        new()
        {
            Id = "stale/valid-then-broken", Scenario = StaleSuccessInvalidation,
            Invariant = "a previously successful load must not mask a now-broken module: the next run fails exactly like a fresh host",
            Target = TargetModule, ExpectedFreshOutcome = "parseError",
            History = [TargetModule], ExpectedHistoryOutcomes = ["ok"],
            TargetModules = MapMBroken, HistoryModules = MapMv1,
        },
        new()
        {
            Id = "stale/valid-then-removed", Scenario = StaleSuccessInvalidation,
            Invariant = "a previously successful load must not mask a now-missing module",
            Target = TargetModule, ExpectedFreshOutcome = "parseError",
            History = [TargetModule], ExpectedHistoryOutcomes = ["ok"],
            TargetModules = [], HistoryModules = MapMv1,
        },

        // ── Name/scope collisions ────────────────────────────────────────────
        new()
        {
            Id = "collide/scope-graph", Scenario = NameScopeCollision,
            Invariant = "x/F/Items/D/G/Inner with incompatible prior meanings cannot contaminate the target's scope graph",
            Target = TargetScopes, ExpectedFreshOutcome = "ok",
            History = [HistB, HistC], ExpectedHistoryOutcomes = ["ok", "ok"],
        },
        new()
        {
            Id = "collide/collecting-vs-fixed", Scenario = NameScopeCollision,
            Invariant = "the same callable name with a collecting parameter after a fixed-arity prior meaning",
            Target = TargetCollectItems, ExpectedFreshOutcome = "ok",
            History = [HistFixedItems], ExpectedHistoryOutcomes = ["ok"],
        },
        new()
        {
            Id = "collide/clause-family-arity", Scenario = NameScopeCollision,
            Invariant = "a clause family name reused at a different arity in history",
            Target = TargetClauseOneArity, ExpectedFreshOutcome = "ok",
            History = [HistClauseTwoArity], ExpectedHistoryOutcomes = ["ok"],
        },
        new()
        {
            Id = "collide/function-arity", Scenario = NameScopeCollision,
            Invariant = "the same function name with another arity in history",
            Target = TargetFOneParam, ExpectedFreshOutcome = "ok",
            History = [HistFTwoParams], ExpectedHistoryOutcomes = ["ok"],
        },
        new()
        {
            Id = "collide/nested-shadowing", Scenario = NameScopeCollision,
            Invariant = "nested shadowing scope graphs are rebuilt per run, never keyed by bare name",
            Target = TargetShadowing, ExpectedFreshOutcome = "ok",
            History = [HistShadowing], ExpectedHistoryOutcomes = ["ok"],
        },
        new()
        {
            Id = "collide/module-member-names", Scenario = NameScopeCollision,
            Invariant = "two modules declaring the same member name stay separate; prior use of one cannot contaminate the other",
            Target = TargetSameNames, ExpectedFreshOutcome = "ok", ExpectedFreshEmitted = 3,
            History = [HistUseN2], ExpectedHistoryOutcomes = ["ok"],
            TargetModules = MapNames,
        },

        // ── Module graph and load order ──────────────────────────────────────
        new()
        {
            Id = "graph/diamond-after-unrelated", Scenario = ModuleGraphAndOrder,
            Invariant = "a diamond dependency graph elaborates identically after unrelated history",
            Target = TargetDiamondBFirst, ExpectedFreshOutcome = "ok", ExpectedFreshEmitted = 2,
            History = [HistB], ExpectedHistoryOutcomes = ["ok"],
            TargetModules = MapDiamond,
        },
        new()
        {
            Id = "graph/diamond-after-other-order", Scenario = ModuleGraphAndOrder,
            Invariant = "having loaded the same graph in the other traversal order before changes nothing",
            Target = TargetDiamondBFirst, ExpectedFreshOutcome = "ok",
            History = [TargetDiamondCFirst], ExpectedHistoryOutcomes = ["ok"],
            TargetModules = MapDiamond,
        },
        new()
        {
            Id = "graph/deps-loaded-b-then-c-first", Scenario = ModuleGraphAndOrder,
            Invariant = "loading B then C in prior runs does not change A (load B → load C → run A)",
            Target = TargetDiamondBFirst, ExpectedFreshOutcome = "ok",
            History = [HistLoadOnlyB, HistLoadOnlyC], ExpectedHistoryOutcomes = ["ok", "ok"],
            TargetModules = MapDiamond,
        },
        new()
        {
            Id = "graph/deps-loaded-c-then-b-first", Scenario = ModuleGraphAndOrder,
            Invariant = "the opposite prior load order also changes nothing (load C → load B → run A)",
            Target = TargetDiamondBFirst, ExpectedFreshOutcome = "ok",
            History = [HistLoadOnlyC, HistLoadOnlyB], ExpectedHistoryOutcomes = ["ok", "ok"],
            TargetModules = MapDiamond,
        },
        new()
        {
            Id = "graph/repeated-import", Scenario = ModuleGraphAndOrder,
            Invariant = "loading the same url twice in one program, repeated across runs, stays stable",
            Target = TargetRepeatedImport, ExpectedFreshOutcome = "ok", ExpectedFreshEmitted = 3,
            History = [TargetRepeatedImport], ExpectedHistoryOutcomes = ["ok"],
            TargetModules = MapMv1,
        },

        // ── Source identity ──────────────────────────────────────────────────
        new()
        {
            Id = "identity/same-text-two-urls", Scenario = SourceIdentity,
            Invariant = "identical source text under two urls is two distinct modules, unaffected by history",
            Target = TargetTwoUrlsSameText, ExpectedFreshOutcome = "ok", ExpectedFreshEmitted = 1,
            History = [HistB], ExpectedHistoryOutcomes = ["ok"],
            TargetModules = MapIdentity,
        },
        new()
        {
            Id = "identity/dot-segment-alias", Scenario = SourceIdentity,
            Invariant = "dot-segment spellings normalize to ONE identity (Uri.AbsoluteUri) — stable across repeats",
            Target = TargetDotSegmentAlias, ExpectedFreshOutcome = "ok",
            History = [TargetDotSegmentAlias], ExpectedHistoryOutcomes = ["ok"],
            TargetModules = MapIdentity,
        },
        new()
        {
            Id = "identity/host-case-alias", Scenario = SourceIdentity,
            Invariant = "host case differences normalize to one identity",
            Target = TargetHostCaseAlias, ExpectedFreshOutcome = "ok",
            History = [HistB], ExpectedHistoryOutcomes = ["ok"],
            TargetModules = MapIdentity,
        },
        new()
        {
            Id = "identity/path-case-distinct", Scenario = SourceIdentity,
            Invariant = "path case is part of the identity: two distinct modules with distinct content",
            Target = TargetPathCaseDistinct, ExpectedFreshOutcome = "ok",
            History = [HistB], ExpectedHistoryOutcomes = ["ok"],
            TargetModules = MapPathCase,
        },

        // ── Counted sentinels under kitchen-sink pollution ───────────────────
        new()
        {
            Id = "sentinel/counted-kitchen-sink", Scenario = CountedSentinel,
            Invariant = "count and shape of the multi-output target survive success, parse-failure, runtime-failure, and self-repeat history",
            Target = TargetCounted, ExpectedFreshOutcome = "ok", ExpectedFreshEmitted = 5,
            History = [HistB, HistParseError, HistRuntimeIndexError, TargetCounted],
            ExpectedHistoryOutcomes = ["ok", "parseError", "err", "ok"],
        },
        new()
        {
            Id = "sentinel/zero-kitchen-sink", Scenario = CountedSentinel,
            Invariant = "the zero-output observation (n=0) survives mixed history",
            Target = TargetZero, ExpectedFreshOutcome = "ok", ExpectedFreshEmitted = 0,
            History = [HistParseError, HistB, HistRuntimeDepthError],
            ExpectedHistoryOutcomes = ["parseError", "ok", "err"],
        },
        new()
        {
            Id = "sentinel/module-kitchen-sink", Scenario = CountedSentinel,
            Invariant = "module-backed count and shape survive broken-module, unrelated, and self-repeat history",
            Target = TargetModule, ExpectedFreshOutcome = "ok", ExpectedFreshEmitted = 3,
            History = [HistLoadBrokenOther, HistB, TargetModule],
            ExpectedHistoryOutcomes = ["parseError", "ok", "ok"],
            TargetModules = MapMv1PlusBroken,
        },
    ];
}
