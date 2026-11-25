using System.Collections.Immutable;
using System.Globalization;
using KatLang;

namespace KatLang.ParserFuzz;

/// <summary>The three explicitly classified kinds of generated case (SEM-2B).</summary>
internal enum SemanticCaseKind
{
    /// <summary>A valid program that must parse cleanly and succeed with the constructed value.</summary>
    ValidSuccess,

    /// <summary>A valid program that must parse cleanly and then fail at RUNTIME with the constructed error kind.</summary>
    ValidRuntimeFailure,

    /// <summary>A deliberately invalid program whose named front-end diagnostic and phase are the subject.</summary>
    InvalidFrontEnd,
}

/// <summary>
/// Intended execution paths a case claims. Evidence-backed paths participate in admission: a
/// claimed path the required profile did not show is recorded as a REJECTED claim with a reason
/// (never a pass of that path, never automatically a language mismatch), and corpus floors fail the
/// suite when a category ends up with zero exercised cases. Anchor-backed paths are established by
/// the case's exact event and outcome anchors.
/// </summary>
[Flags]
internal enum SemanticPath
{
    None = 0,

    // ── Evidence-backed (optimizer, cache and async diagnostics) ─────────────
    /// <summary>Optimized: an optimized loop plan selected AND planned expressions executed; generic: the generic loop ran.</summary>
    OptimizedLoop = 1 << 0,

    /// <summary>The zero-iteration short circuit: the loop returned before the optimizer was consulted.</summary>
    LoopShortCircuit = 1 << 1,

    /// <summary>The optimizer was consulted and DECLINED (a recorded fallback) on the optimized profile.</summary>
    LoopFallback = 1 << 2,

    /// <summary>A generic expression ran inside an otherwise optimized loop.</summary>
    GenericInsideOptimizedLoop = 1 << 3,

    /// <summary>An actual zero-argument property cache hit (not merely repeated equal output).</summary>
    CacheHit = 1 << 4,

    /// <summary>Every demanded <c>wait</c> genuinely suspended the asynchronous run.</summary>
    AsyncSuspension = 1 << 5,

    /// <summary>A scheduled cancellation reached a suspended run and ended it as a cancellation.</summary>
    Cancellation = 1 << 6,

    // ── Anchor-backed (exact host events and outcomes) ───────────────────────
    /// <summary>Argument-view cells transported unforced: only the selected cell's effect occurs.</summary>
    LazyTransport = 1 << 8,

    /// <summary><c>Invoke()</c>/<c>Algorithm(…)</c> are fresh invocations: a body effect repeats.</summary>
    FreshInvocation = 1 << 9,

    /// <summary>A syntactically present failing computation is never demanded.</summary>
    DeadComputationUntouched = 1 << 10,

    /// <summary>A terminal failure stops the run: no later row's effect occurs.</summary>
    FirstFailureStops = 1 << 11,

    /// <summary>Cardinality is checked before any supplied argument is demanded.</summary>
    CardinalityBeforeDemand = 1 << 12,

    EvidenceBacked = OptimizedLoop | LoopShortCircuit | LoopFallback | GenericInsideOptimizedLoop | CacheHit
        | AsyncSuspension | Cancellation,
}

/// <summary>
/// The construction-derived expectation of one case. Every field comes from how the case was BUILT
/// and from established semantics — never from a preliminary run of the implementation, and never
/// from a second general evaluator.
/// </summary>
internal sealed record SemanticExpectation(
    SemanticCaseKind Kind,
    Result? Value,
    int? EmittedCount,
    string? ErrorCategory,
    DiagnosticCode? Diagnostic,
    string? DiagnosticPhase,
    ImmutableArray<string> Events)
{
    /// <summary>Front-end phase name of a raw-parser diagnostic.</summary>
    internal const string SyntaxPhase = "syntax";

    /// <summary>Front-end phase name of a diagnostic the raw parse does not report (elaboration).</summary>
    internal const string ElaborationPhase = "elaboration";

    /// <summary>Events a cancellation profile must observe before its run ends as cancelled.</summary>
    public ImmutableArray<string> CancelledEventsPrefix { get; init; } = [];

    /// <summary>The value's durable identity (success only).</summary>
    public string? ValueIdentity => Value is null ? null : MetamorphicStructuralIdentity.Encode(Value);

    public override string ToString() => Kind switch
    {
        SemanticCaseKind.ValidSuccess =>
            $"success value={MetamorphicStructuralIdentity.Preview(ValueIdentity)} emitted={EmittedCount?.ToString(CultureInfo.InvariantCulture)} events=[{string.Join(",", Events)}]",
        SemanticCaseKind.ValidRuntimeFailure => $"runtime-failure kind={ErrorCategory} events=[{string.Join(",", Events)}]",
        _ => $"front-end diagnostic={Diagnostic} phase={DiagnosticPhase}",
    };
}

/// <summary>
/// One compared member of a case: the base program or a well-founded transformation of it. Every
/// member carries its exact rendered source, so a reproducer never depends on re-rendering.
/// </summary>
internal sealed record SemanticMember(string Role, string Source)
{
    internal const string BaseRole = "base";

    /// <summary>Binding-preserving renaming of every declaration (validated against the scope graph).</summary>
    internal const string AlphaRenameRole = "alpha-rename";

    /// <summary>Root declarations reversed: declarations in one scope are order-independent.</summary>
    internal const string DeclarationReorderRole = "declaration-reorder";

    public string Fingerprint => SemanticFingerprint.Of(Source);
}

/// <summary>
/// A generated grammar-aware semantic case (SEM-2B): its versioned identity, its members, the
/// construction-derived expectation, the intended paths, and the deliberate profile selection.
/// Nothing here holds evaluator state.
/// </summary>
internal sealed record SemanticCase(
    string CaseId,
    string Tier,
    ulong? Seed,
    int? Index,
    SemanticExpectation Expected,
    ImmutableArray<SemanticMember> Members,
    ImmutableArray<string> Families,
    ImmutableArray<string> Features,
    SemanticPath Paths,
    int MinimumCacheHits,
    ImmutableArray<string> Profiles)
{
    public string Source => Members[0].Source;

    public SemanticCaseKind Kind => Expected.Kind;

    /// <summary>Expected <c>wait</c> calls: one per <c>wait:</c> event.</summary>
    public int ExpectedWaitCalls => Expected.Events.Count(static e => e.StartsWith("wait:", StringComparison.Ordinal));

    public override string ToString() => CaseId;
}

/// <summary>Integrity fingerprints for durable source and descriptor text.</summary>
internal static class SemanticFingerprint
{
    internal static string Of(string text)
    {
        ArgumentNullException.ThrowIfNull(text);
        return "sha256:" + Convert.ToHexStringLower(
            System.Security.Cryptography.SHA256.HashData(System.Text.Encoding.UTF8.GetBytes(text)));
    }
}
