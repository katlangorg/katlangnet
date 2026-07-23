using KatLang;
using KatLang.Semantics;

namespace KatLang.ParserFuzz;

/// <summary>The stage the editor harness was executing, so a thrown exception names its culprit.</summary>
internal enum EditorPhase
{
    Build,
    Tooling,
    ModelInvariants,
    Surface,
    Determinism,
    Edit,
    EditInvariants,
    EditDeterminism,
    StaleSource,
    RelationWhitespace,
    RelationLineEnding,
    RelationRename,
    RelationUnrelated,
    RelationDotted,
    Fingerprint,
}

/// <summary>Thrown when the editor harness observes a violated invariant or relation.</summary>
internal sealed class EditorInvariantException(string message) : Exception(message);

/// <summary>What one editor request produced, in stable structural buckets.</summary>
internal sealed record EditorObservation(
    EditorToolingOutcome Outcome,
    int DiagnosticCount,
    string FirstDiagnosticBucket,
    int OccurrenceCount,
    int DeclarationCount,
    int ResolutionCount,
    int PropertyCount,
    string ClassificationsPresent,
    string CursorResolutionClass,
    bool CursorHasProperty,
    bool AnyMultilineDiagnosticSpan,
    string SurfaceObservation);

/// <summary>Everything one editor payload produced. Replay compares two of these.</summary>
internal sealed record EditorReport(
    EditorCase Case,
    EditorObservation Observation,
    EditorRelationOutcome Relations,
    string Fingerprint);

/// <summary>
/// The <c>KATLANG_FUZZ_MODE=editor</c> target.
///
/// <para>The payload is not source text: it selects a trusted editor template, the difficult UTF-16
/// code units to inject into it, a cursor placement, and a bounded edit, then builds the KatLang
/// semantic model (<c>KatLang.Semantics</c>) over the result and every query surface the model
/// exposes.</para>
///
/// <para>The goal is NOT to make difficult source resolve. A structured "no result", an ordinary
/// diagnostic, or a declined unresolved-load request is a perfectly good outcome. What must never
/// happen is an unexpected exception, an out-of-range or self-inconsistent span, a resolution to a
/// differently named or non-existent symbol, an invented or synthetic symbol, a non-deterministic
/// result, stale source surviving a request boundary, or a contradictory metamorphic projection.</para>
///
/// <para>Every violation — and every unexpected CLR exception — escapes to the fuzzing engine with
/// its original type and stack. Nothing here converts one into an ordinary tooling response.</para>
/// </summary>
internal static class EditorInvariants
{
    /// <summary>An unrelated program processed between two runs of the same request (A/B/A).</summary>
    private const string ProbeSource = "p = 1\nHelper(x) = x + p\nq, r = (2, 3)\nOutput = Helper(q) + r";

    /// <summary>libFuzzer callback. Lets everything escape, by design.</summary>
    public static void Check(ReadOnlySpan<byte> payload) => _ = Run(payload);

    public static EditorReport Run(ReadOnlySpan<byte> payload)
    {
        var phase = EditorPhase.Build;
        return Run(payload, ref phase);
    }

    /// <summary>Runs every stage, advancing <paramref name="phase"/> before each so a thrown
    /// exception leaves it naming the stage that failed.</summary>
    public static EditorReport Run(ReadOnlySpan<byte> payload, ref EditorPhase phase)
    {
        phase = EditorPhase.Build;
        var parameters = EditorDecoder.Decode(payload);
        var testCase = EditorSourceBuilder.Build(parameters);

        phase = EditorPhase.Tooling;
        var baseResult = EditorModel.Run(testCase.Source, parameters.ExecutionMode);

        var (cursorLine, cursorColumn) = EditorCursor.QueryPosition(parameters, testCase.Source, testCase.CursorOffset);

        phase = EditorPhase.ModelInvariants;
        if (baseResult.Model is { } model)
        {
            EditorModel.ValidateModel(testCase.Source, model);
            EditorSurfaces.CheckCoreInvariants(testCase.Source, model);
        }

        phase = EditorPhase.Surface;
        var surfaceObservation = EditorSurfaces.Exercise(testCase, baseResult, cursorLine, cursorColumn);

        phase = EditorPhase.Determinism;
        var baseDigest = CheckRequestDeterminism(testCase.Source, parameters, testCase.CursorOffset);

        phase = EditorPhase.Edit;
        RunEditStages(testCase, parameters, baseDigest, ref phase);

        phase = EditorPhase.RelationWhitespace;
        var relations = EditorRelations.Check(testCase, baseResult, ref phase);

        phase = EditorPhase.Fingerprint;
        var observation = Observe(baseResult, cursorLine, cursorColumn, surfaceObservation);
        var fingerprint = EditorFingerprint.Describe(testCase, observation, relations);

        return new EditorReport(testCase, observation, relations, fingerprint);
    }

    private static void RunEditStages(
        EditorCase testCase, EditorParameters parameters, string baseDigest, ref EditorPhase phase)
    {
        if (!testCase.EditApplied)
            return;

        phase = EditorPhase.EditInvariants;
        var editedResult = EditorModel.Run(testCase.EditedSource, parameters.ExecutionMode);
        if (editedResult.Model is { } editedModel)
        {
            EditorModel.ValidateModel(testCase.EditedSource, editedModel);
            EditorSurfaces.CheckCoreInvariants(testCase.EditedSource, editedModel);
        }

        phase = EditorPhase.EditDeterminism;
        CheckRequestDeterminism(testCase.EditedSource, parameters, testCase.EditedCursorOffset);

        // No stale source: a fresh request on the ORIGINAL source, made after the edited source was
        // processed, must reproduce the original result exactly. Stateless tooling makes this hold;
        // a static cache keyed by anything but the source would break it.
        phase = EditorPhase.StaleSource;
        var afterEdit = FullDigest(testCase.Source, parameters, testCase.CursorOffset);
        if (!string.Equals(baseDigest, afterEdit, StringComparison.Ordinal))
            throw new EditorInvariantException(
                "A fresh tooling request on the original source changed after the edited source was processed: " +
                "edited-source state leaked across the request boundary.");
    }

    /// <summary>A/A and A/B/A for one request: the same source, cursor and mode must give the same
    /// digest, and an unrelated program processed between the two runs must not change it. Returns
    /// the digest so callers can compare it against later requests.</summary>
    private static string CheckRequestDeterminism(string source, EditorParameters parameters, int cursorOffset)
    {
        var first = FullDigest(source, parameters, cursorOffset);
        var second = FullDigest(source, parameters, cursorOffset);
        if (!string.Equals(first, second, StringComparison.Ordinal))
            throw new EditorInvariantException("Two tooling requests for the same source produced different digests.");

        RunProbe();
        var third = FullDigest(source, parameters, cursorOffset);
        if (!string.Equals(first, third, StringComparison.Ordinal))
            throw new EditorInvariantException(
                "A tooling request's digest changed after an unrelated source was processed (leaked state).");

        return first;
    }

    private static string FullDigest(string source, EditorParameters parameters, int cursorOffset)
    {
        var result = EditorModel.Run(source, parameters.ExecutionMode);
        var (line, column) = EditorCursor.QueryPosition(parameters, source, cursorOffset);
        var lookup = result.Model is { } model ? EditorSurfaces.ChooseLookupName(model) : "Output";
        return EditorModel.Digest(result, line, column, lookup);
    }

    private static void RunProbe()
    {
        var result = EditorModel.Run(ProbeSource, EditorExecutionMode.Elaborated);
        _ = EditorModel.Digest(result, 1, 1, "Output");
    }

    private static EditorObservation Observe(
        EditorToolingResult result, int cursorLine, int cursorColumn, string surfaceObservation)
    {
        var model = result.Model;
        var classifications = new SortedSet<string>(StringComparer.Ordinal);
        if (model is not null)
            foreach (var resolution in model.IdentifierResolutions)
                classifications.Add(resolution.Classification.ToString());

        var cursorResolution = model?.FindResolutionAt(cursorLine, cursorColumn);
        var cursorProperty = model?.FindPropertyAt(cursorLine, cursorColumn);

        var multilineDiagnostic = result.Diagnostics.Any(diagnostic =>
            diagnostic.Span is { } span && span.EndLineNumber != span.StartLineNumber);

        return new EditorObservation(
            Outcome: result.Outcome,
            DiagnosticCount: result.Diagnostics.Count,
            FirstDiagnosticBucket: Utf16Fingerprint.DiagnosticBucket(result.Diagnostics),
            OccurrenceCount: model?.IdentifierOccurrences.Count ?? 0,
            DeclarationCount: model?.Declarations.Count ?? 0,
            ResolutionCount: model?.IdentifierResolutions.Count ?? 0,
            PropertyCount: model?.PropertyInfos.Count ?? 0,
            ClassificationsPresent: classifications.Count == 0 ? "none" : string.Join('+', classifications),
            CursorResolutionClass: cursorResolution is null ? "none" : cursorResolution.Classification.ToString(),
            CursorHasProperty: cursorProperty is not null,
            AnyMultilineDiagnosticSpan: multilineDiagnostic,
            SurfaceObservation: surfaceObservation);
    }
}
