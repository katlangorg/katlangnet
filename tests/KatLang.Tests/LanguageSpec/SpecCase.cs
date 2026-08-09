namespace KatLang.Tests.LanguageSpec;

/// <summary>Expected top-level outcome of a specification case.</summary>
public enum SpecOutcome
{
    /// <summary>The program parses and evaluates; value expectations apply.</summary>
    Evaluates,

    /// <summary>The program parses but evaluation fails with a stable error category.</summary>
    EvalError,

    /// <summary>The program is rejected by the parser (C#-only; Lean has no surface parser).</summary>
    ParseError,
}

/// <summary>
/// An auxiliary observation attached to a case: a complete standalone KatLang
/// program (typically deriving an equality, count, <c>.count</c>, or indexing
/// view of the case's value) pinned to a canonical neutral observation.
/// Probes execute on the C# side only; they are not part of the Lean-guarded
/// partition.
/// </summary>
/// <param name="Probe">Complete standalone KatLang program.</param>
/// <param name="ExpectedNeutral">
/// Canonical neutral observation, in the harness encoding:
/// <c>ok raw=... n=...</c> or <c>err CATEGORY</c>.
/// </param>
public sealed record SpecProbe(string Probe, string ExpectedNeutral);

/// <summary>
/// One canonical language-specification case. Unlike the semantic-explorer
/// corpus (which re-pins <em>observed</em> behavior on regeneration), every
/// expectation here is hand-written canonical language behavior: if the
/// implementation drifts, the runner fails and the fix is either a reviewed
/// implementation fix or a reviewed edit of the canonical case — never a
/// silent regeneration.
/// </summary>
public sealed record SpecCase
{
    /// <summary>Stable kebab-case identifier. Tutorial markers and generated artifacts reference it.</summary>
    public required string Id { get; init; }

    /// <summary>Feature category; must be one of <see cref="LanguageSpecCorpus.Categories"/>.</summary>
    public required string Category { get; init; }

    /// <summary>Complete KatLang source program ("\n" line separators).</summary>
    public required string Source { get; init; }

    /// <summary>Expected outcome partition of the case.</summary>
    public required SpecOutcome Outcome { get; init; }

    /// <summary>Reader-facing explanation, phrased in tutorial vocabulary.</summary>
    public required string Explanation { get; init; }

    /// <summary>
    /// Canonical engine display text ("\n" row separators; "" for zero-row
    /// output). Required when <see cref="Outcome"/> is Evaluates.
    /// </summary>
    public string? ExpectedDisplay { get; init; }

    /// <summary>
    /// Canonical raw result structure in the neutral encoding shared with the
    /// Lean artifact (atom → <c>1</c>, string → <c>'x'</c>, sequence →
    /// <c>S[a, b]</c>, empty → <c>S[]</c>). Required when Evaluates.
    /// </summary>
    public string? ExpectedRaw { get; init; }

    /// <summary>Canonical root emitted count. Required when Evaluates.</summary>
    public int? ExpectedEmittedCount { get; init; }

    /// <summary>
    /// Canonical innermost-error category (harness/Lean shared taxonomy, e.g.
    /// "arity", "index", "missingOutput"). Required when EvalError.
    /// </summary>
    public string? ExpectedErrorCategory { get; init; }

    /// <summary>
    /// Optional stable fragment of a parser diagnostic message. Parser
    /// diagnostics carry no structured kind today, so use this only for
    /// deliberately-worded diagnostics (e.g. the semicolon message) and keep
    /// fragments short enough to survive harmless rewording.
    /// </summary>
    public string? ExpectedParseDiagnosticFragment { get; init; }

    /// <summary>
    /// Lean AST construction equivalent to <see cref="Source"/> (the same
    /// encoding the semantic-explorer corpus uses: surviving parenthesized
    /// lists are <c>.capture</c> bundles, never <c>.sequenceConstruct</c>).
    /// Non-null iff
    /// the case is in the Lean-guarded partition.
    /// </summary>
    public string? LeanProgram { get; init; }

    /// <summary>
    /// Required exactly when a non-parse-error case has no
    /// <see cref="LeanProgram"/>: why the case is C#-only (e.g. decimal
    /// display semantics outside the Lean Int core, or a Lean AST encoding
    /// that has not been authored yet).
    /// </summary>
    public string? LeanExclusionReason { get; init; }

    /// <summary>Auxiliary canonical observations (C#-only partition).</summary>
    public IReadOnlyList<SpecProbe> Probes { get; init; } = [];

    /// <summary>
    /// Include this case in the generated verified-examples block of the
    /// katlang-generator prompt files.
    /// </summary>
    public bool IncludeInGeneratorPrompt { get; init; }

    /// <summary>Optional maintainer notes (e.g. intentional surface-vs-internal differences).</summary>
    public string? Notes { get; init; }

    /// <summary>True when the case belongs to the Lean-guarded partition.</summary>
    public bool IsLeanRepresentable => LeanProgram is not null;

    /// <summary>
    /// The canonical neutral observation string this case pins, in the
    /// encoding shared between the C# harness and the generated Lean guards.
    /// Null for parse-error cases (Lean has no surface parser).
    /// </summary>
    public string? CanonicalNeutral => Outcome switch
    {
        SpecOutcome.Evaluates => $"ok raw={ExpectedRaw} n={ExpectedEmittedCount}",
        SpecOutcome.EvalError => $"err {ExpectedErrorCategory}",
        _ => null,
    };
}
