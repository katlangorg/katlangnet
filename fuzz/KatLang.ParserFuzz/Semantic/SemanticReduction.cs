using System.Collections.Immutable;
using System.Globalization;
using System.Text;
using System.Text.Json;
using KatLang;

namespace KatLang.ParserFuzz;

// SEM-2C automatic reduction of failing SEM-2B generated cases (fuzz/README.md § Reduction).
//
// A reduced case is a REAL generated case: the same builder that made the failing case runs again
// over a smaller choice sequence, so SemanticCorpus.Assemble constructs its expectation. Nothing
// edits a rendered source.

/// <summary>A case together with the generation shape a reducer measures (root fragments, declarations).</summary>
internal sealed record SemanticBuiltCase(SemanticCase Case, int Fragments, int Declarations);

/// <summary>
/// The production sequence of ONE durable case id, separated from its decision source. Building with
/// <see cref="NewChooser"/> is exactly the corpus case; building with any other chooser is a
/// generated case of the same recipe shape whose expectation is constructed by the same assembly.
/// </summary>
internal sealed class SemanticCaseBuilder(string localId, Func<SemanticChooser> chooser, Func<SemanticGrammar.Gen, SemanticBuiltCase> body)
{
    public string LocalId { get; } = localId;

    public string CaseId => SemanticRecipe.CasePrefix + LocalId;

    /// <summary>The decision source the durable id has always used.</summary>
    public SemanticChooser NewChooser() => chooser();

    public SemanticBuiltCase Build(SemanticChooser decisions) => body(new SemanticGrammar.Gen(decisions));

    public SemanticCase Build() => Build(NewChooser()).Case;

    internal static SemanticCaseBuilder Systematic(string localId, int chooserIndex, Func<SemanticGrammar.Gen, SemanticBuiltCase> body)
        => new(localId, () => SemanticChooser.Systematic(chooserIndex), body);
}

/// <summary>One recorded generation decision: the dimension, its value count, and the value taken.</summary>
internal readonly record struct SemanticChoice(string Dimension, int Count, int Value);

/// <summary>
/// Records every <see cref="SemanticChooser.Pick"/> of an inner chooser and returns the inner value
/// unchanged, so recording never changes a decision (<see cref="SemanticChooser.Chance"/> goes
/// through <c>Pick</c> and is recorded as a pick of 100).
/// </summary>
internal sealed class RecordingChooser(SemanticChooser inner) : SemanticChooser
{
    private readonly List<SemanticChoice> _choices = [];

    public ImmutableArray<SemanticChoice> Choices => [.. _choices];

    public override int Pick(string dimension, int count)
    {
        var value = inner.Pick(dimension, count);
        _choices.Add(new SemanticChoice(dimension, count, value));
        return value;
    }
}

/// <summary>
/// Returns recorded values in order, CLAMPED to <c>count - 1</c> (a value recorded for a wider
/// dimension stays a valid choice after a deletion shifts it), and <c>0</c> once the sequence is
/// exhausted. Productions are valid for every choice, so every replay is a generated case.
/// </summary>
internal sealed class ReplayingChooser(IReadOnlyList<int> values) : SemanticChooser
{
    private int _next;

    public override int Pick(string dimension, int count)
    {
        if (count <= 0) throw new ArgumentOutOfRangeException(nameof(count));
        if (_next >= values.Count)
        {
            _next++;
            return 0;
        }

        return Math.Clamp(values[_next++], 0, count - 1);
    }
}

/// <summary>
/// Reduction size, compared lexicographically: rendered base source length, then root fragments,
/// then declarations. Choice-sequence length and value sum are recorded separately: simpler
/// decisions can normalize an IDENTICAL case, but never make an unchanged case a reduction.
/// </summary>
internal readonly record struct SemanticCaseSize(int SourceLength, int Fragments, int Declarations, int Choices, long ChoiceSum)
    : IComparable<SemanticCaseSize>
{
    public int CompareTo(SemanticCaseSize other)
    {
        var c = SourceLength.CompareTo(other.SourceLength);
        if (c == 0) c = Fragments.CompareTo(other.Fragments);
        if (c == 0) c = Declarations.CompareTo(other.Declarations);
        return c;
    }

    public override string ToString() => string.Create(CultureInfo.InvariantCulture,
        $"source={SourceLength} fragments={Fragments} declarations={Declarations} choices={Choices} sum={ChoiceSum}");
}

/// <summary>
/// What a reduced case must preserve: the verdict plus the FIRST finding's location (member role and
/// profile, pair or relation) and facet (which anchor template, relation or path failed). Built from
/// the runner's STRUCTURED finding (<see cref="SemanticCaseResult.FindingRecords"/>) whenever the
/// result carries aligned records, so rewording a finding never changes it. Only a result without
/// them (a worker result document that predates them) falls back to the text classifier, which
/// parses the fixed templates and never the variable values (values, events). Both produce the same
/// strings, which <c>kl-sem2b-reduction</c> v1 records store.
/// </summary>
internal sealed record SemanticFailureSignature(SemanticVerdict Verdict, string Member, string Profile, string Facet)
{
    internal const string None = "-";

    public override string ToString() => $"{Verdict} {Member}@{Profile} {Facet}";

    internal static SemanticFailureSignature Of(SemanticCaseResult result)
    {
        ArgumentNullException.ThrowIfNull(result);
        if (result.Findings.IsEmpty) return new SemanticFailureSignature(result.Verdict, None, None, None);
        var (member, profile, facet) = HasAlignedRecords(result) ? Classify(result.FindingRecords[0]) : ClassifyText(result.Findings[0]);
        return new SemanticFailureSignature(result.Verdict, member, profile, facet);
    }

    /// <summary>Records are used only when they describe exactly the findings (one per finding).</summary>
    internal static bool HasAlignedRecords(SemanticCaseResult result)
        => !result.FindingRecords.IsDefaultOrEmpty && result.FindingRecords.Length == result.Findings.Length;

    /// <summary>The signature location and facet of one structured finding.</summary>
    internal static (string Member, string Profile, string Facet) Classify(SemanticFinding finding)
    {
        ArgumentNullException.ThrowIfNull(finding);
        return (finding.Member, finding.Profile, SemanticFindingFacets.SignatureFacet(finding));
    }

    // (message prefix after "location: ", facet) for the anchor templates of SemanticRunner.CheckAnchors.
    private static readonly (string Prefix, string Facet)[] AnchorFacets =
    [
        ("value ", "value"),
        ("emitted count ", "emitted-count"),
        ("the emitted-count facet is empty", "emitted-count-missing"),
        ("the structure facet carries no value", "structure-missing"),
        ("host events ", "host-events"),
        ("host effects ran", "front-end-effects"),
        ("events [", "cancellation-events"),
        ("expected a scheduled cancellation", "cancellation"),
        ("an unscheduled cancellation", "unscheduled-cancellation"),
        ("the surface refused the valid source", "surface-refused"),
        ("the surface returned no observation", "observation-missing"),
        ("observation does not carry", "facet-contract"),
        ("stopped at a resource limit", "resource-limit"),
        ("expected success", "outcome"),
        ("expected runtime failure", "outcome"),
        ("the structured-error facet is empty", "error-missing"),
        ("error ", "error-kind"),
        ("failure stage ", "failure-stage"),
        ("an invalid source reached the evaluator", "front-end-reached"),
        ("expected a front-end failure", "front-end-failure"),
    ];

    /// <summary>
    /// The FALLBACK text classifier, for findings without a structured record. It depends on the
    /// runner's message templates; <c>SemanticFindingSignatureTests</c> pins that it agrees with
    /// <see cref="Classify(SemanticFinding)"/> on every template the runner currently produces.
    /// </summary>
    internal static (string Member, string Profile, string Facet) ClassifyText(string finding)
    {
        var colon = finding.IndexOf(": ", StringComparison.Ordinal);
        var head = colon < 0 ? finding : finding[..colon];
        var rest = colon < 0 ? "" : finding[(colon + 2)..];

        // Path admission: "required path not admitted: <Path>: <reason>".
        if (head == "required path not admitted")
        {
            var parts = rest.Split(':', 2);
            var reason = parts.Length > 1 ? parts[1].TrimStart() : "";
            var profile = SemanticProfiles.All.OrderByDescending(p => p.Id.Length).FirstOrDefault(p =>
                reason.StartsWith(p.Id + " ", StringComparison.Ordinal)
                || reason.StartsWith(p.Id + "-", StringComparison.Ordinal))?.Id ?? None;
            return (SemanticMember.BaseRole, profile, "path:" + parts[0]);
        }

        // Transformation relation: "relation:<role>: <headline>".
        if (head.StartsWith("relation:", StringComparison.Ordinal))
            return (head["relation:".Length..], SemanticProfiles.SyncOptimized, "relation:" + ComparisonFacet(rest));

        // Declared profile parity: "<pair id>: host events differ …" or "<pair id>: <headline>".
        if (head.StartsWith("parity:", StringComparison.Ordinal))
            return (SemanticMember.BaseRole, head, rest.StartsWith("host events differ", StringComparison.Ordinal) ? "parity-host-events" : "parity:" + ComparisonFacet(rest));
        if (head == "cancellation parity")
            return (SemanticMember.BaseRole, head, "parity");

        // Anchors: "<member>@<profile>: <template>".
        var at = head.IndexOf('@', StringComparison.Ordinal);
        if (at > 0)
        {
            var facet = "other";
            foreach (var (prefix, name) in AnchorFacets)
            {
                if (rest.StartsWith(prefix, StringComparison.Ordinal))
                {
                    facet = name;
                    break;
                }
            }

            // A harness problem ("<where>: <problem>") stays "other"; its verdict already names it.
            return (head[..at], head[(at + 1)..], facet);
        }

        // Front end: "<role>: valid source rejected by the front end (<Code>: …)" and the invalid-case templates.
        if (head is SemanticMember.BaseRole or SemanticMember.AlphaRenameRole or SemanticMember.DeclarationReorderRole)
        {
            const string rejected = "valid source rejected by the front end (";
            if (rest.StartsWith(rejected, StringComparison.Ordinal))
                return (head, "front-end", "front-end:" + rest[rejected.Length..].Split(':', 2)[0]);
            var facet = rest.StartsWith("invalid source accepted", StringComparison.Ordinal) ? "front-end:accepted"
                : rest.StartsWith("rejected in phase", StringComparison.Ordinal) ? "front-end:phase"
                : rest.StartsWith("expected diagnostic", StringComparison.Ordinal) ? "front-end:diagnostic"
                : "front-end:other";
            return (head, "front-end", facet);
        }

        return (None, None, "case");
    }

    // MetamorphicMismatch.Headline separates the class and compared FIELD from the variable
    // left/right values. Keep that field: steps and materialized items on the same pair are
    // different failures. The observation values and free-form diagnostic text never enter it.
    private static string ComparisonFacet(string finding)
    {
        const string separator = " relation violated on ";
        var at = finding.IndexOf(separator, StringComparison.Ordinal);
        var end = finding.IndexOf(": left=", StringComparison.Ordinal);
        return at > 0 && end > at + separator.Length
            && Enum.TryParse<MetamorphicMismatchClass>(finding[..at], out var kind) && Enum.IsDefined(kind)
                ? finding[..end]
                : "observation-missing";
    }
}

/// <summary>Bounds and the execution seam of one reduction.</summary>
internal sealed record SemanticReductionOptions
{
    internal const int DefaultMaxAttempts = 200;

    /// <summary>The maximum number of candidate EXECUTIONS (generation alone is cheap and not counted).</summary>
    public int MaxAttempts { get; init; } = DefaultMaxAttempts;

    /// <summary>How a case is judged; <see cref="SemanticRunner.Run"/> by default, a supervised child in <c>--supervised</c>.</summary>
    public Func<SemanticCase, SemanticCaseResult> Runner { get; init; } = static c => SemanticRunner.Run(c);

    public bool Supervised { get; init; }
}

internal enum SemanticReductionStatus
{
    /// <summary>A smaller generated case with the same signature was found.</summary>
    Reduced,

    /// <summary>The case fails, but no smaller candidate preserved its signature within the bounds.</summary>
    AlreadyMinimal,

    /// <summary>The case passes: there is no failure to reduce.</summary>
    NothingToReduce,
}

/// <summary>One accepted reduction step (for the reduction record and the tests).</summary>
internal sealed record SemanticReductionStep(string Move, SemanticCaseSize Size, bool FrontEndClean, bool ExpectationConstructed);

/// <summary>A candidate generation that threw or violated its construction contract: never silently skipped.</summary>
internal sealed record SemanticGenerationFailure(ImmutableArray<int> Choices, string Error);

/// <summary>The complete, deterministic outcome of one reduction.</summary>
internal sealed record SemanticReductionResult(
    SemanticReductionStatus Status,
    string OriginalCaseId,
    SemanticCase Original,
    SemanticCaseResult OriginalResult,
    SemanticFailureSignature Signature,
    ImmutableArray<SemanticChoice> OriginalChoices,
    SemanticCaseSize OriginalSize,
    SemanticCase Reduced,
    SemanticCaseResult ReducedResult,
    ImmutableArray<SemanticChoice> ReducedChoices,
    SemanticCaseSize ReducedSize,
    int Attempts,
    int Generations,
    bool AttemptLimitReached,
    ImmutableArray<SemanticReductionStep> Accepted,
    ImmutableArray<SemanticGenerationFailure> GenerationFailures,
    int MaxAttempts,
    bool Supervised)
{
    public string Describe() => string.Create(CultureInfo.InvariantCulture,
        $"{Status} {OriginalCaseId} [{Signature}]: {OriginalSize} -> {ReducedSize}; attempts={Attempts}/{MaxAttempts}{(AttemptLimitReached ? " (limit reached)" : "")} generations={Generations} accepted={Accepted.Length} generation-failures={GenerationFailures.Length}");
}

/// <summary>
/// Choice-sequence reduction of a failing SEM-2B case (SEM-2C). The failing case's generation is
/// recorded; candidates are smaller choice sequences replayed through the SAME builder, so each is a
/// generated case with its own constructed expectation. Moves, in order and repeated to a fixpoint:
/// delete blocks of 8, 4, 2 and 1 choices; lower single values to 0; decrement them. A candidate is
/// accepted when it is strictly smaller (<see cref="SemanticCaseSize"/>) and fails with the same
/// <see cref="SemanticFailureSignature"/>. A candidate that generates the IDENTICAL case is adopted
/// without running (the run is deterministic), so normalizing the sequence costs no attempt.
/// Bounded by <see cref="SemanticReductionOptions.MaxAttempts"/> executions; same input, same output.
/// </summary>
internal static class SemanticReducer
{
    private static readonly int[] BlockSizes = [8, 4, 2, 1];

    internal static SemanticReductionResult Reduce(SemanticCaseBuilder builder, SemanticReductionOptions? options = null)
    {
        ArgumentNullException.ThrowIfNull(builder);
        options ??= new SemanticReductionOptions();
        if (options.MaxAttempts < 0) throw new ArgumentOutOfRangeException(nameof(options), "max attempts must be non-negative");

        var recorder = new RecordingChooser(builder.NewChooser());
        var original = builder.Build(recorder);
        var originalChoices = recorder.Choices;
        var originalResult = options.Runner(original.Case);
        var signature = SemanticFailureSignature.Of(originalResult);
        var originalSize = SizeOf(original, originalChoices);

        var current = original;
        var currentChoices = originalChoices;
        var currentResult = originalResult;
        var currentSize = originalSize;
        var currentText = SemanticDescriptor.Write(original.Case);
        var attempts = 0;
        var generations = 0;
        var limitReached = false;
        var accepted = new List<SemanticReductionStep>();
        var failures = new List<SemanticGenerationFailure>();
        var tried = new HashSet<string>(StringComparer.Ordinal);

        if (originalResult.Passed)
        {
            return new SemanticReductionResult(SemanticReductionStatus.NothingToReduce, original.Case.CaseId, original.Case, originalResult,
                signature, originalChoices, originalSize, original.Case, originalResult, originalChoices, originalSize,
                0, 0, false, [], [], options.MaxAttempts, options.Supervised);
        }

        // Returns true when the candidate was adopted.
        bool Try(string move, ImmutableArray<int> values)
        {
            if (limitReached || failures.Count > 0) return false;
            generations++;
            var replay = new RecordingChooser(new ReplayingChooser(values));
            SemanticBuiltCase candidate;
            try
            {
                candidate = builder.Build(replay);
            }
            catch (Exception exception) when (exception is not OutOfMemoryException)
            {
                failures.Add(new SemanticGenerationFailure(values, exception.GetType().Name + ": " + exception.Message));
                return false;
            }

            if (!ExpectationConstructed(candidate.Case.Expected) || !FrontEndClean(candidate.Case))
            {
                failures.Add(new SemanticGenerationFailure(values,
                    "a candidate lacks its constructed expectation or a valid member was rejected by the front end"));
                return false;
            }

            var effective = replay.Choices;
            var size = SizeOf(candidate, effective);
            var comparison = size.CompareTo(currentSize);
            if (comparison > 0) return false;
            var text = SemanticDescriptor.Write(candidate.Case);
            // Equal-size cases are not reductions. Only normalize the very same case, using a
            // strictly decreasing sequence measure so these free moves also reach a fixpoint.
            if (comparison == 0 && (text != currentText || size.Choices > currentSize.Choices
                || (size.Choices == currentSize.Choices && size.ChoiceSum >= currentSize.ChoiceSum))) return false;
            SemanticCaseResult result;
            if (text == currentText)
            {
                result = currentResult; // the identical case: a deterministic run gives the same result
            }
            else
            {
                if (!tried.Add(text)) return false; // an identical candidate already failed differently
                if (attempts >= options.MaxAttempts)
                {
                    limitReached = true;
                    return false;
                }

                attempts++;
                result = options.Runner(candidate.Case);
                if (result.Passed || SemanticFailureSignature.Of(result) != signature) return false;
            }

            current = candidate;
            currentChoices = effective;
            currentResult = result;
            currentSize = size;
            currentText = text;
            accepted.Add(new SemanticReductionStep(move, size, FrontEndClean(candidate.Case), ExpectationConstructed(candidate.Case.Expected)));
            return true;
        }

        var progress = true;
        while (progress && !limitReached && failures.Count == 0)
        {
            progress = false;
            foreach (var block in BlockSizes)
            {
                var i = 0;
                while (i + block <= currentChoices.Length && !limitReached && failures.Count == 0)
                {
                    var values = Values(currentChoices);
                    if (Try($"delete {block.ToString(CultureInfo.InvariantCulture)} at {i.ToString(CultureInfo.InvariantCulture)}",
                            values.RemoveRange(i, block)))
                        progress = true; // the next block now starts at i
                    else
                        i++;
                }
            }

            for (var i = 0; i < currentChoices.Length && !limitReached && failures.Count == 0; i++)
            {
                if (currentChoices[i].Value == 0) continue;
                if (Try($"zero {i.ToString(CultureInfo.InvariantCulture)}", Values(currentChoices).SetItem(i, 0))) progress = true;
            }

            for (var i = 0; i < currentChoices.Length && !limitReached && failures.Count == 0; i++)
            {
                while (i < currentChoices.Length && currentChoices[i].Value > 0 && !limitReached
                       && Try($"decrement {i.ToString(CultureInfo.InvariantCulture)}", Values(currentChoices).SetItem(i, currentChoices[i].Value - 1)))
                    progress = true;
            }
        }

        var status = currentSize.CompareTo(originalSize) < 0 ? SemanticReductionStatus.Reduced : SemanticReductionStatus.AlreadyMinimal;
        return new SemanticReductionResult(status, original.Case.CaseId, original.Case, originalResult, signature, originalChoices, originalSize,
            current.Case, currentResult, currentChoices, currentSize, attempts, generations, limitReached, [.. accepted], [.. failures],
            options.MaxAttempts, options.Supervised);
    }

    internal static ImmutableArray<int> Values(ImmutableArray<SemanticChoice> choices) => [.. choices.Select(static c => c.Value)];

    internal static SemanticCaseSize SizeOf(SemanticBuiltCase built, ImmutableArray<SemanticChoice> choices)
        => new(built.Case.Source.Length, built.Fragments, built.Declarations, choices.Length, choices.Sum(static c => (long)c.Value));

    /// <summary>A valid kind's members pass the real front end with no error (invalid kinds: vacuously true).</summary>
    internal static bool FrontEndClean(SemanticCase semanticCase)
        => semanticCase.Kind == SemanticCaseKind.InvalidFrontEnd
            || semanticCase.Members.All(member => !Parser.Parse(member.Source,
                new RunOptions { HostOperations = MetamorphicHostFixture.Synchronous().Operations }).HasErrors);

    /// <summary>The expectation names exactly what its kind needs (it was constructed by assembly).</summary>
    internal static bool ExpectationConstructed(SemanticExpectation e) => e.Kind switch
    {
        SemanticCaseKind.ValidSuccess => e.Value is not null && e.EmittedCount is not null,
        SemanticCaseKind.ValidRuntimeFailure => !string.IsNullOrEmpty(e.ErrorCategory),
        _ => e.Diagnostic is not null && e.DiagnosticPhase is not null,
    };
}

/// <summary>
/// Reduced-case identities, the <c>kl-sem2b-reduction</c> v1 record, and the <c>semantic-reduce</c>
/// command.
///
/// <para><b>Artifacts.</b> A reduced case is written as an ordinary <c>kl-sem2b-case</c> v1 descriptor
/// (exact sources, constructed expectation, the run's result) under the reserved id prefix
/// <c>sem2b/v1/reduced/</c>. No recipe ever built such an id, so the v1 reader's acceptance is
/// unchanged: it parses the descriptor, <c>--exact-source</c> replays it, and recipe mode REFUSES it
/// with an explicit message instead of reporting it as a recipe case. Beside it, a separately
/// versioned <c>kl-sem2b-reduction</c> v1 record keeps the original id, both choice sequences, the
/// signature, the bounds and both sizes; <see cref="TryRebuild"/> regenerates the reduced case from
/// the record and so re-verifies the descriptor.</para>
/// </summary>
internal static class SemanticReduction
{
    internal const string RecordFormat = "kl-sem2b-reduction";
    internal const int RecordFormatVersion = 1;

    /// <summary>The reserved local-id prefix of reduced cases (after <see cref="SemanticRecipe.CasePrefix"/>).</summary>
    internal const string ReducedLocalPrefix = "reduced/";

    internal const string ReducedTier = "reduced";

    internal const int MaxRecordChoices = 4096;

    /// <summary>Exit code of <c>semantic-reduce</c> for a case that passes (nothing to reduce).</summary>
    internal const int NothingToReduceExitCode = 3;

    private static readonly JsonWriterOptions WriterOptions = new()
    {
        Indented = true,
        NewLine = "\n",
        Encoder = System.Text.Encodings.Web.JavaScriptEncoder.UnsafeRelaxedJsonEscaping,
    };

    internal static bool IsReducedCaseId(string caseId)
        => caseId.StartsWith(SemanticRecipe.CasePrefix + ReducedLocalPrefix, StringComparison.Ordinal);

    internal static string RecipeRefusal(string caseId)
        => $"case id '{caseId}' is a REDUCED case: it was regenerated from a recorded choice sequence and is not a " +
            $"{SemanticRecipe.GeneratorId} v{SemanticRecipe.RecipeVersion.ToString(CultureInfo.InvariantCulture)} recipe case; " +
            "replay its recorded sources with --exact-source (its kl-sem2b-reduction record names the original case).";

    /// <summary><c>sem2b/v1/reduced/&lt;original local id&gt;/&lt;16 hex of the reduced sequence&gt;</c>.</summary>
    internal static string ReducedCaseId(string originalCaseId, ImmutableArray<SemanticChoice> reducedChoices)
    {
        var local = originalCaseId.StartsWith(SemanticRecipe.CasePrefix, StringComparison.Ordinal)
            ? originalCaseId[SemanticRecipe.CasePrefix.Length..]
            : originalCaseId;
        var digest = SemanticFingerprint.Of(string.Join(",", reducedChoices.Select(c => c.Value.ToString(CultureInfo.InvariantCulture))));
        return SemanticRecipe.CasePrefix + ReducedLocalPrefix + local + "/" + digest["sha256:".Length..][..16];
    }

    /// <summary>The reduced generated case under its reserved identity (members, expectation and profiles unchanged).</summary>
    internal static SemanticCase AsReduced(SemanticCase generated, string originalCaseId, ImmutableArray<SemanticChoice> choices)
        => generated with { CaseId = ReducedCaseId(originalCaseId, choices), Tier = ReducedTier };

    // ── The reduction record ────────────────────────────────────────────────

    internal sealed record Record(
        string OriginalCaseId,
        string ReducedCaseId,
        string ReducedBaseSha256,
        string Status,
        SemanticFailureSignature Signature,
        ImmutableArray<SemanticChoice> OriginalChoices,
        ImmutableArray<SemanticChoice> ReducedChoices,
        SemanticCaseSize OriginalSize,
        SemanticCaseSize ReducedSize,
        int Attempts,
        int MaxAttempts,
        int Generations,
        bool AttemptLimitReached,
        bool Supervised);

    internal static Record RecordOf(SemanticReductionResult result)
    {
        var reduced = AsReduced(result.Reduced, result.OriginalCaseId, result.ReducedChoices);
        return new Record(result.OriginalCaseId, reduced.CaseId, reduced.Members[0].Fingerprint, result.Status.ToString(), result.Signature,
            result.OriginalChoices, result.ReducedChoices, result.OriginalSize, result.ReducedSize, result.Attempts, result.MaxAttempts,
            result.Generations, result.AttemptLimitReached, result.Supervised);
    }

    internal static string WriteRecord(Record record)
    {
        using var stream = new MemoryStream();
        using (var w = new Utf8JsonWriter(stream, WriterOptions))
        {
            w.WriteStartObject();
            w.WriteString("format", RecordFormat);
            w.WriteNumber("formatVersion", RecordFormatVersion);
            w.WriteString("generator", SemanticRecipe.GeneratorId);
            w.WriteNumber("recipeVersion", SemanticRecipe.RecipeVersion);
            w.WriteString("originalCaseId", record.OriginalCaseId);
            w.WriteString("reducedCaseId", record.ReducedCaseId);
            w.WriteString("reducedBaseSha256", record.ReducedBaseSha256);
            w.WriteString("status", record.Status);
            w.WriteStartObject("signature");
            w.WriteString("verdict", record.Signature.Verdict.ToString());
            w.WriteString("member", record.Signature.Member);
            w.WriteString("profile", record.Signature.Profile);
            w.WriteString("facet", record.Signature.Facet);
            w.WriteEndObject();
            WriteSize(w, "originalSize", record.OriginalSize);
            WriteSize(w, "reducedSize", record.ReducedSize);
            w.WriteNumber("attempts", record.Attempts);
            w.WriteNumber("maxAttempts", record.MaxAttempts);
            w.WriteNumber("generations", record.Generations);
            w.WriteBoolean("attemptLimitReached", record.AttemptLimitReached);
            w.WriteBoolean("supervised", record.Supervised);
            WriteChoices(w, "originalChoices", record.OriginalChoices);
            WriteChoices(w, "reducedChoices", record.ReducedChoices);
            w.WriteEndObject();
        }

        return Encoding.UTF8.GetString(stream.ToArray()) + "\n";
    }

    private static void WriteSize(Utf8JsonWriter w, string name, SemanticCaseSize size)
    {
        w.WriteStartObject(name);
        w.WriteNumber("sourceLength", size.SourceLength);
        w.WriteNumber("fragments", size.Fragments);
        w.WriteNumber("declarations", size.Declarations);
        w.WriteNumber("choices", size.Choices);
        w.WriteNumber("choiceSum", size.ChoiceSum);
        w.WriteEndObject();
    }

    private static void WriteChoices(Utf8JsonWriter w, string name, ImmutableArray<SemanticChoice> choices)
    {
        w.WriteStartArray(name);
        foreach (var choice in choices)
        {
            w.WriteStartObject();
            w.WriteString("dimension", choice.Dimension);
            w.WriteNumber("count", choice.Count);
            w.WriteNumber("value", choice.Value);
            w.WriteEndObject();
        }

        w.WriteEndArray();
    }

    /// <summary>Parses a reduction record under explicit bounds; unknown formats, versions and generators are refused.</summary>
    internal static bool TryParseRecord(string text, out Record record, out string problem)
    {
        record = null!;
        if (text is null || text.Length > SemanticDescriptor.MaxDescriptorChars)
        {
            problem = "reduction record is missing or exceeds its bound";
            return false;
        }

        try
        {
            using var document = JsonDocument.Parse(text, new JsonDocumentOptions { MaxDepth = 8 });
            var root = document.RootElement;
            if (root.ValueKind != JsonValueKind.Object) { problem = "reduction record is not a JSON object"; return false; }
            if (Str(root, "format") != RecordFormat) { problem = $"unknown reduction record format '{Str(root, "format")}' (expected '{RecordFormat}')"; return false; }
            var version = root.GetProperty("formatVersion").GetInt32();
            if (version != RecordFormatVersion)
            {
                problem = $"unsupported {RecordFormat} version {version.ToString(CultureInfo.InvariantCulture)} (this harness reads version {RecordFormatVersion.ToString(CultureInfo.InvariantCulture)})";
                return false;
            }

            if (Str(root, "generator") != SemanticRecipe.GeneratorId) { problem = $"unknown generator '{Str(root, "generator")}'"; return false; }
            var recipeVersion = root.GetProperty("recipeVersion").GetInt32();
            if (recipeVersion != SemanticRecipe.RecipeVersion)
            {
                problem = $"recipe version {recipeVersion.ToString(CultureInfo.InvariantCulture)} is not built by this generator; the reduced descriptor still replays with --exact-source";
                return false;
            }

            var signature = root.GetProperty("signature");
            if (!Enum.TryParse<SemanticVerdict>(Str(signature, "verdict"), ignoreCase: false, out var verdict) || !Enum.IsDefined(verdict))
            {
                problem = $"unknown signature verdict '{Str(signature, "verdict")}'";
                return false;
            }

            var originalCaseId = Str(root, "originalCaseId") ?? throw new FormatException("missing originalCaseId");
            var reducedCaseId = Str(root, "reducedCaseId") ?? throw new FormatException("missing reducedCaseId");
            if (!IsReducedCaseId(reducedCaseId) || IsReducedCaseId(originalCaseId))
                throw new FormatException("the reduced id must carry the reserved prefix and the original id must not");
            var reducedChoices = Choices(root, "reducedChoices");
            if (reducedCaseId != ReducedCaseId(originalCaseId, reducedChoices))
                throw new FormatException("reducedCaseId does not match the reduced choice sequence");
            record = new Record(
                originalCaseId, reducedCaseId,
                Str(root, "reducedBaseSha256") ?? throw new FormatException("missing reducedBaseSha256"),
                Str(root, "status") ?? throw new FormatException("missing status"),
                new SemanticFailureSignature(verdict,
                    Str(signature, "member") ?? throw new FormatException("missing signature member"),
                    Str(signature, "profile") ?? throw new FormatException("missing signature profile"),
                    Str(signature, "facet") ?? throw new FormatException("missing signature facet")),
                Choices(root, "originalChoices"), reducedChoices,
                Size(root.GetProperty("originalSize")), Size(root.GetProperty("reducedSize")),
                root.GetProperty("attempts").GetInt32(), root.GetProperty("maxAttempts").GetInt32(),
                root.GetProperty("generations").GetInt32(), root.GetProperty("attemptLimitReached").GetBoolean(),
                root.GetProperty("supervised").GetBoolean());
            if (!Enum.TryParse<SemanticReductionStatus>(record.Status, ignoreCase: false, out var status) || !Enum.IsDefined(status)
                || status == SemanticReductionStatus.NothingToReduce)
                throw new FormatException($"invalid reduction status '{record.Status}'");
            if (record.Signature.Verdict == SemanticVerdict.Passed)
                throw new FormatException("a reduction record must describe a failure");
            if (record.Attempts < 0 || record.Attempts > record.MaxAttempts || record.Generations < record.Attempts)
                throw new FormatException("attempts exceed the recorded bound");
            ValidateSize(record.OriginalSize, record.OriginalChoices);
            ValidateSize(record.ReducedSize, record.ReducedChoices);
            var comparison = record.ReducedSize.CompareTo(record.OriginalSize);
            if (status == SemanticReductionStatus.Reduced ? comparison >= 0 : comparison != 0)
                throw new FormatException("reduction status disagrees with the recorded sizes");
            problem = "";
            return true;
        }
        catch (Exception exception) when (exception is JsonException or InvalidOperationException or KeyNotFoundException or FormatException)
        {
            problem = "malformed reduction record: " + exception.Message;
            return false;
        }
    }

    /// <summary>
    /// Regenerates the reduced case from a record: the original id's builder replays the reduced
    /// sequence, which must be the generator's OWN trace (every recorded dimension, count and value
    /// reproduced) and must render to the recorded base fingerprint.
    /// </summary>
    internal static bool TryRebuild(Record record, out SemanticCase reduced, out string problem)
    {
        reduced = null!;
        if (!SemanticCorpus.TryBuilder(record.OriginalCaseId, SemanticRecipe.RecipeVersion, out var builder, out problem)) return false;
        var originalRecorder = new RecordingChooser(builder.NewChooser());
        var original = builder.Build(originalRecorder);
        if (!originalRecorder.Choices.SequenceEqual(record.OriginalChoices)
            || SemanticReducer.SizeOf(original, originalRecorder.Choices) != record.OriginalSize)
        {
            problem = "the original choice sequence or size does not match its recipe";
            return false;
        }

        var replay = new RecordingChooser(new ReplayingChooser(SemanticReducer.Values(record.ReducedChoices)));
        var built = builder.Build(replay);
        if (!replay.Choices.SequenceEqual(record.ReducedChoices))
        {
            problem = "the reduced choice sequence is not the generator's own trace under this recipe";
            return false;
        }

        reduced = AsReduced(built.Case, record.OriginalCaseId, replay.Choices);
        if (reduced.CaseId != record.ReducedCaseId || reduced.Members[0].Fingerprint != record.ReducedBaseSha256
            || SemanticReducer.SizeOf(built, replay.Choices) != record.ReducedSize)
        {
            problem = "the regenerated reduced case does not match the record";
            return false;
        }

        problem = "";
        return true;
    }

    private static void ValidateSize(SemanticCaseSize size, ImmutableArray<SemanticChoice> choices)
    {
        if (size.SourceLength < 0 || size.Fragments < 1 || size.Declarations < 0
            || size.Choices != choices.Length || size.ChoiceSum != choices.Sum(static c => (long)c.Value))
            throw new FormatException("size is negative or disagrees with its choice sequence");
    }

    private static string? Str(JsonElement element, string name)
    {
        if (!element.TryGetProperty(name, out var value) || value.ValueKind == JsonValueKind.Null) return null;
        var text = value.GetString() ?? throw new FormatException($"'{name}' is not a string");
        if (text.Length > SemanticDescriptor.MaxStringChars) throw new FormatException($"'{name}' exceeds its bound");
        return text;
    }

    private static SemanticCaseSize Size(JsonElement e) => new(
        e.GetProperty("sourceLength").GetInt32(), e.GetProperty("fragments").GetInt32(), e.GetProperty("declarations").GetInt32(),
        e.GetProperty("choices").GetInt32(), e.GetProperty("choiceSum").GetInt64());

    private static ImmutableArray<SemanticChoice> Choices(JsonElement root, string name)
    {
        var array = root.GetProperty(name);
        if (array.ValueKind != JsonValueKind.Array) throw new FormatException($"'{name}' is not an array");
        if (array.GetArrayLength() > MaxRecordChoices) throw new FormatException($"'{name}' exceeds {MaxRecordChoices} choices");
        var choices = ImmutableArray.CreateBuilder<SemanticChoice>();
        foreach (var item in array.EnumerateArray())
        {
            var choice = new SemanticChoice(
                Str(item, "dimension") ?? throw new FormatException("choice without dimension"),
                item.GetProperty("count").GetInt32(), item.GetProperty("value").GetInt32());
            if (choice.Count <= 0 || choice.Value < 0 || choice.Value >= choice.Count)
                throw new FormatException($"choice {choice} is outside its dimension");
            choices.Add(choice);
        }

        return choices.ToImmutable();
    }

    // ── Command ─────────────────────────────────────────────────────────────

    /// <summary>
    /// <c>semantic-reduce DESCRIPTOR|CASE-ID OUT [--max-attempts N] [--supervised]</c>. Writes
    /// <c>OUT/&lt;reduced id&gt;.json</c> (descriptor with result) and <c>OUT/&lt;reduced id&gt;.reduction.json</c>.
    /// Exit codes: 0 — artifacts written (reduced or already minimal); 1 — generation failures were
    /// observed (a generator precondition defect; artifacts are still written); 2 — usage, an
    /// unreadable or drifted descriptor, or an unsupported id; 3 — the case passes, nothing to reduce.
    /// </summary>
    public static int RunReduce(string[] args) => RunReduce(args, workerCommand: null);

    /// <summary>
    /// <c>semantic-reduce</c> with its internal, test-only supervision seam. <paramref name="workerCommand"/>
    /// builds the child launch for one candidate descriptor and its result path (default:
    /// <see cref="SemanticSupervisor.SelfWorker"/> in exact-source mode); <paramref name="evidenceDirectory"/>
    /// replaces the printed temporary evidence directory. Both only matter with <c>--supervised</c>;
    /// the supervisor itself (deadlines, crash detection, output bounds) is unchanged.
    /// </summary>
    internal static int RunReduce(string[] args, Func<string, string, SemanticWorkerCommand>? workerCommand, string? evidenceDirectory = null)
    {
        var positional = new List<string>();
        int? maxAttempts = null;
        var supervised = false;
        for (var i = 1; i < args.Length; i++)
        {
            if (args[i] == "--supervised") supervised = true;
            else if (args[i] == "--max-attempts" && i + 1 < args.Length
                     && int.TryParse(args[i + 1], NumberStyles.None, CultureInfo.InvariantCulture, out var n))
            {
                maxAttempts = n;
                i++;
            }
            else if (args[i].StartsWith("--", StringComparison.Ordinal))
            {
                positional.Clear();
                break;
            }
            else positional.Add(args[i]);
        }

        if (positional.Count != 2)
        {
            Console.Error.WriteLine("usage: semantic-reduce DESCRIPTOR|CASE-ID OUT [--max-attempts N] [--supervised]");
            return 2;
        }

        var (input, outDir) = (positional[0], positional[1]);
        string caseId;
        if (File.Exists(input))
        {
            string text;
            try
            {
                text = SemanticReplay.ReadBounded(input);
            }
            catch (Exception exception) when (exception is IOException or UnauthorizedAccessException or InvalidDataException)
            {
                Console.Error.WriteLine($"semantic-reduce: {input}: {exception.Message}");
                return 2;
            }

            if (!SemanticDescriptor.TryParse(text, out var parsed, out var problem))
            {
                Console.Error.WriteLine($"semantic-reduce: {input}: descriptor rejected: {problem}");
                return 2;
            }

            caseId = parsed.Case.CaseId;
            if (!SemanticCorpus.TryReconstruct(caseId, parsed.RecipeVersion, out var rebuilt, out problem))
            {
                Console.Error.WriteLine("semantic-reduce: " + problem);
                return 2;
            }

            if (SemanticReplay.Drift(parsed.Case, rebuilt) is { } drift)
            {
                Console.Error.WriteLine($"semantic-reduce: {input}: recipe drift ({drift}); a drifted descriptor cannot be reduced by its recipe.");
                return 2;
            }
        }
        else
        {
            caseId = input;
        }

        if (!SemanticCorpus.TryBuilder(caseId, SemanticRecipe.RecipeVersion, out var builder, out var builderProblem))
        {
            Console.Error.WriteLine("semantic-reduce: " + builderProblem);
            return 2;
        }

        var options = new SemanticReductionOptions { MaxAttempts = maxAttempts ?? SemanticReductionOptions.DefaultMaxAttempts, Supervised = supervised };
        string? evidence = null;
        if (supervised)
        {
            evidence = evidenceDirectory is null
                ? Directory.CreateTempSubdirectory("katlang-sem2c-reduce-").FullName
                : Directory.CreateDirectory(evidenceDirectory).FullName;
            var counter = 0;
            var command = workerCommand ?? DefaultWorker;
            options = options with { Runner = c => SuperviseOne(c, evidence, ++counter, command) };
        }

        var result = SemanticReducer.Reduce(builder, options);
        Console.WriteLine("semantic-reduce: " + result.Describe());
        if (evidence is not null) Console.WriteLine("  worker evidence retained at " + evidence);
        if (result.Status == SemanticReductionStatus.NothingToReduce)
        {
            Console.WriteLine($"semantic-reduce: {caseId} passes; nothing to reduce.");
            return NothingToReduceExitCode;
        }

        Directory.CreateDirectory(outDir);
        var record = RecordOf(result);
        var reduced = AsReduced(result.Reduced, result.OriginalCaseId, result.ReducedChoices);
        var stem = Path.Combine(outDir, SemanticReplay.SafeName(reduced.CaseId));
        File.WriteAllText(stem + ".json", SemanticDescriptor.Write(reduced, result.ReducedResult with { CaseId = reduced.CaseId }));
        File.WriteAllText(stem + ".reduction.json", WriteRecord(record));
        Console.WriteLine($"wrote {stem}.json and {stem}.reduction.json ({reduced.CaseId})");
        foreach (var failure in result.GenerationFailures.Take(4))
            Console.WriteLine($"GENERATION FAILURE: {failure.Error} choices=[{string.Join(",", failure.Choices)}]");
        return result.GenerationFailures.IsEmpty ? 0 : 1;
    }

    private static SemanticWorkerCommand DefaultWorker(string descriptor, string result)
        => SemanticSupervisor.SelfWorker(descriptor, result, SemanticReplay.Mode.ExactSource);

    /// <summary>One candidate in a bounded supervised child (exact-source: a candidate is not a recipe case).</summary>
    private static SemanticCaseResult SuperviseOne(
        SemanticCase semanticCase, string evidence, int number, Func<string, string, SemanticWorkerCommand> workerCommand)
    {
        var descriptor = Path.Combine(evidence, "candidate-" + number.ToString("D4", CultureInfo.InvariantCulture) + ".json");
        File.WriteAllText(descriptor, SemanticDescriptor.Write(semanticCase));
        var run = SemanticSupervisor.Run(workerCommand(descriptor, descriptor + ".result.json"), SemanticSupervisor.DefaultDeadline);
        return run.Result is { } summary && summary.Verdict == run.Verdict
            ? summary.CoverageResult
            : new SemanticCaseResult(semanticCase.CaseId, run.Verdict, [], [], SemanticPath.None, [], []);
    }
}
