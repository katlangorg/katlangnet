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
    /// Optional stable fragment of a parser diagnostic message. The structured
    /// classification lives in <see cref="ExpectedDiagnosticCode"/>; use the
    /// fragment additionally for deliberately-worded diagnostics (e.g. the
    /// semicolon message) and keep fragments short enough to survive harmless
    /// rewording.
    /// </summary>
    public string? ExpectedParseDiagnosticFragment { get; init; }

    /// <summary>
    /// Canonical structured family of the expected parser/front-end
    /// diagnostic (<see cref="Diagnostic.Code"/>). Required when
    /// <see cref="Outcome"/> is ParseError: at least one error diagnostic of
    /// the case must carry this code. Like every expectation here it is
    /// hand-written canonical behavior, never regenerated from observation.
    /// </summary>
    public DiagnosticCode? ExpectedDiagnosticCode { get; init; }

    /// <summary>
    /// EXCEPTIONAL escape hatch: a hand-authored Lean program used INSTEAD of
    /// the canonical encoder derivation. Ordinary cases must not set this —
    /// the corpus derives <see cref="LeanProgram"/> from the source's real
    /// elaborated AST through <c>LeanAstEncoder</c>, which is what makes the
    /// two sides of the differential provably the same program. Setting an
    /// override requires <see cref="LeanOverrideReason"/> (schema-enforced),
    /// and the overriding text is NOT same-program-verified: it exists only
    /// for a deliberately different Lean construction.
    /// </summary>
    public string? LeanProgramOverride { get; init; }

    /// <summary>
    /// Required exactly when <see cref="LeanProgramOverride"/> is set: why
    /// this case hand-authors its Lean program instead of deriving it.
    /// </summary>
    public string? LeanOverrideReason { get; init; }

    /// <summary>
    /// The encoder-derived Lean program, set ONLY by
    /// <c>LanguageSpecCorpus.AllCases</c>'s derivation step (never by a case
    /// author). Kept internal so a corpus case cannot smuggle hand-written
    /// Lean text into the derived channel.
    /// </summary>
    internal string? DerivedLeanProgram { get; init; }

    /// <summary>
    /// Lean AST construction equivalent to <see cref="Source"/>: the encoder
    /// derivation, or the explicit override. Non-null iff the case is in the
    /// Lean-guarded partition.
    /// </summary>
    public string? LeanProgram => LeanProgramOverride ?? DerivedLeanProgram;

    /// <summary>
    /// Required exactly when a non-parse-error case has no
    /// <see cref="LeanProgram"/>: why the case is C#-only (an intentional
    /// model divergence such as decimal semantics outside the Lean Int core,
    /// or a shape the encoder deliberately does not cover). The derivation
    /// step skips excluded cases, so this is also the explicit unsupported
    /// inventory — a case can never silently leave the Lean partition.
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
