namespace KatLang.Tests.LanguageSpec;

/// <summary>
/// Loads the hand-written shared cases from conformance/ and derives the elaborated
/// Lean programs used by the differential checks. All .NET consumers use this corpus.
/// </summary>
public static class LanguageSpecCorpus
{
    private static readonly SharedConformanceFiles Files = new(Path.Combine(RepoRoot.Find(), "conformance"));
    public static IReadOnlyList<string> Categories => Files.Categories;

    /// <summary>
    /// All canonical cases, with each Lean-guarded case's Lean program DERIVED
    /// from the source's real elaborated AST through <see cref="LeanAstEncoder"/>
    /// (see <see cref="SpecCase.LeanProgram"/>). Derivation is fail-loud: a
    /// non-parse-error case must either derive cleanly, carry an explicit
    /// <see cref="SpecCase.LeanExclusionReason"/>, or carry an explicit
    /// <see cref="SpecCase.LeanProgramOverride"/> with a reason — so an encoder
    /// or parser regression fails corpus construction naming the case instead
    /// of silently shrinking the Lean-guarded partition. The corpus is
    /// deterministic and immutable, so it is built once per process.
    /// </summary>
    public static IReadOnlyList<SpecCase> AllCases() => LazyCases.Value;

    private static readonly Lazy<IReadOnlyList<SpecCase>> LazyCases =
        new(() => Files.ReadCases().Select(DeriveLeanProgram).ToList().AsReadOnly());

    private static SpecCase DeriveLeanProgram(SpecCase specCase)
    {
        // The corpus is cached process-wide. Freeze every nested collection too,
        // so a caller cannot mutate a probe list and make later tests depend on
        // which test first touched AllCases().
        specCase = specCase with
        {
            Probes = specCase.Probes.ToList().AsReadOnly(),
            DisplayChecks = specCase.DisplayChecks.ToList().AsReadOnly(),
        };

        if (specCase.Outcome == SpecOutcome.ParseError
            || specCase.LeanExclusionReason is not null
            || specCase.LeanProgramOverride is not null)
        {
            return specCase;
        }

        var parsed = Parser.Parse(specCase.Source);
        if (parsed.HasErrors)
        {
            throw new InvalidOperationException(
                $"Language-spec case '{specCase.Id}' is not a ParseError case but its source does not parse cleanly: "
                + string.Join(" | ", parsed.Diagnostics.Select(d => d.Message.Split('\n')[0]))
                + $"\nSource:\n{specCase.Source}");
        }

        try
        {
            return specCase with { DerivedLeanProgram = LeanAstEncoder.EncodeProgram(parsed.Root) };
        }
        catch (NotSupportedException ex)
        {
            throw new InvalidOperationException(
                $"Language-spec case '{specCase.Id}' cannot be Lean-encoded; either extend LeanAstEncoder "
                + "deliberately, exclude the case with a reviewed LeanExclusionReason, or (exceptionally) supply a "
                + $"LeanProgramOverride with a reason. Encoder said: {ex.Message}"
                + $"\nSource:\n{specCase.Source}", ex);
        }
    }
}
