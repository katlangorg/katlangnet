using System.Collections.Generic;
using System.Reflection;
using System.Threading.Tasks;
using KatLang;
using KatLang.ParserFuzz;
using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// Phase 7 editor-tooling harness tests. These exercise the exact decoder, source/cursor/edit model,
/// oracle, executor, relations and replay driver the campaign runs, plus deliberately doctored models
/// that prove each invariant is actually caught rather than merely believed to be.
/// </summary>
public class EditorFuzzHarnessTests
{
    // ── Decoder ──────────────────────────────────────────────────────────────

    [Fact]
    public void Decoder_RoundTripsAndNormalizesArbitraryBytes()
    {
        var payload = new byte[EditorDecoder.MaxPayloadPrefixBytes];
        for (var seed = 0; seed < 4096; seed++)
        {
            var state = (uint)((seed * 2654435761u) + 1u);
            for (var i = 0; i < payload.Length; i++)
            {
                state = (state * 1664525u) + 1013904223u;
                payload[i] = (byte)(state >> 24);
            }

            var decoded = EditorDecoder.Decode(payload);
            Assert.Equal(decoded, EditorDecoder.Normalize(decoded));
            Assert.Equal(decoded, EditorDecoder.Decode(decoded.Encode()));
        }
    }

    [Fact]
    public void Decoder_AcceptsTheEmptyPayloadAndIgnoresTheTail()
    {
        var empty = EditorDecoder.Decode([]);
        Assert.Equal(EditorTemplateKind.Empty, empty.Template);
        Assert.Equal(EditorSurfaceKind.Classification, empty.Surface);
        Assert.Equal(EditorEditKind.None, empty.Edit);

        var prefix = empty.Encode();
        var padded = prefix.Concat(Enumerable.Repeat((byte)0x5A, 128)).ToArray();
        Assert.Equal(empty, EditorDecoder.Decode(padded));
    }

    // ── Source, cursor and edit model ────────────────────────────────────────

    [Fact]
    public void EverySource_IsExactlyItsCodeUnits_AndTheCursorStaysInRange()
    {
        foreach (var parameters in EditorSpace.EnumerateStratified())
        {
            var testCase = EditorSourceBuilder.Build(parameters);
            Assert.Equal(Utf16CodeUnits.ToStringExact(testCase.SourceCodeUnits), testCase.Source);
            Assert.InRange(testCase.CursorOffset, 0, testCase.Source.Length);
            Assert.InRange(testCase.EditedCursorOffset, 0, testCase.EditedSource.Length);
            Assert.True(testCase.SourceCodeUnits.Length <= EditorTables.MaxSourceCodeUnits);
            Assert.True(testCase.EditedCodeUnits.Length <= EditorTables.MaxSourceCodeUnits);
        }
    }

    [Fact]
    public void CursorQueryPosition_IsOneBased_AndPastEndOfFileGoesOutOfRange()
    {
        var parameters = EditorDecoder.Decode([]) with { Cursor = EditorCursorKind.PastEndOfFile, CursorBias = 1 };
        var source = "A = 1";
        var (line, column) = EditorCursor.QueryPosition(parameters, source, source.Length);
        Assert.Equal(1, line);
        Assert.True(column > source.Length + 1, "PastEndOfFile must query a column past the last line.");
    }

    // ── Replay determinism and isolation ─────────────────────────────────────

    [Fact]
    public void RepeatedRuns_AreIdentical_AndIndependentAcrossInterleaving()
    {
        var payloads = EditorSpace.EnumerateStratified().Take(400).Select(p => p.Encode()).ToList();

        for (var i = 0; i < payloads.Count; i++)
        {
            var first = EditorInvariants.Run(payloads[i]);
            // An unrelated payload processed between the two runs must not change the second.
            _ = EditorInvariants.Run(payloads[(i + 7) % payloads.Count]);
            var second = EditorInvariants.Run(payloads[i]);
            Assert.Equal(first.Fingerprint, second.Fingerprint);
        }
    }

    [Fact]
    public void ConcurrentRuns_ObserveIndependentResults()
    {
        var payloads = EditorSpace.EnumerateStratified().Take(256).Select(p => p.Encode()).ToArray();
        var sequential = payloads.Select(p => EditorInvariants.Run(p).Fingerprint).ToArray();

        var concurrent = new string[payloads.Length];
        Parallel.For(0, payloads.Length, i => concurrent[i] = EditorInvariants.Run(payloads[i]).Fingerprint);

        Assert.Equal(sequential, concurrent);
    }

    // ── Static state ─────────────────────────────────────────────────────────

    [Fact]
    public void TheEditorHarness_HoldsNoStaticMutableState()
    {
        var mutable = new List<string>();
        var scanned = 0;

        var types = typeof(EditorInvariants).Assembly
            .GetTypes()
            .Where(type => type.Namespace == "KatLang.ParserFuzz")
            .Where(type => type.Name.StartsWith("Editor", StringComparison.Ordinal));

        foreach (var type in types)
        {
            scanned++;

            foreach (var field in type.GetFields(BindingFlags.Static | BindingFlags.Public | BindingFlags.NonPublic))
            {
                if (field.IsLiteral) continue;
                if (!field.IsInitOnly)
                    mutable.Add($"{type.Name}.{field.Name} is a writable static field.");
                else if (IsMutableContainer(field.FieldType))
                    mutable.Add($"{type.Name}.{field.Name} is a readonly static holding mutable {field.FieldType.Name}.");
            }

            foreach (var property in type.GetProperties(BindingFlags.Static | BindingFlags.Public | BindingFlags.NonPublic))
                if (property.SetMethod is not null)
                    mutable.Add($"{type.Name}.{property.Name} is a settable static property.");
        }

        Assert.True(scanned > 10, $"Only {scanned} editor harness types were scanned; the filter is wrong.");
        Assert.True(mutable.Count == 0, "The editor harness holds static mutable state:\n  " + string.Join("\n  ", mutable));
    }

    private static bool IsMutableContainer(Type type)
    {
        if (type.IsArray) return true;
        if (!type.IsGenericType) return false;
        var name = type.GetGenericTypeDefinition().Name;
        return name.StartsWith("List`", StringComparison.Ordinal)
            || name.StartsWith("Dictionary`", StringComparison.Ordinal)
            || name.StartsWith("HashSet`", StringComparison.Ordinal)
            || name.StartsWith("Queue`", StringComparison.Ordinal)
            || name.StartsWith("Stack`", StringComparison.Ordinal);
    }

    // ── Documented tooling contracts ─────────────────────────────────────────

    [Fact]
    public void UnresolvedLoad_ThrowsFromBuild_ButTheHarnessDeclinesCleanly()
    {
        const string source = "Data = load('lib')\nData";
        var root = Parser.Parse(source).Root;

        // The contract: building a semantic model from an AST that still carries a load throws.
        Assert.Throws<InvalidOperationException>(() => SemanticModelBuilder.Build(root));

        // The harness pre-checks and declines exactly as a correct editor caller must, never tripping it.
        var result = EditorModel.Run(source, EditorExecutionMode.Elaborated);
        Assert.Equal(EditorToolingOutcome.DeclinedUnresolvedLoad, result.Outcome);
        Assert.Null(result.Model);

        var raw = EditorModel.Run(source, EditorExecutionMode.RawSyntax);
        Assert.Equal(EditorToolingOutcome.DeclinedUnresolvedLoad, raw.Outcome);
    }

    [Fact]
    public void SyntheticDeconstructionHelpers_NeverSurface()
    {
        const string source = "A = 1, 2, 3\nx, *y, z = A\nx + y.sum + z";
        var result = EditorModel.Run(source, EditorExecutionMode.Elaborated);
        var model = Assert.IsType<SemanticModel>(result.Model);

        Assert.DoesNotContain(model.PropertyInfos, property => property.Name.Contains('$'));
        Assert.DoesNotContain(model.Declarations, declaration => declaration.Name.Contains('$'));
        Assert.DoesNotContain(model.IdentifierOccurrences, occurrence => occurrence.Name.Contains('$'));
        EditorModel.ValidateModel(source, model);
        EditorSurfaces.CheckCoreInvariants(source, model);
    }

    [Fact]
    public void OrdinaryAndDottedCall_ResolveToTheSameDeclaration()
    {
        const string source = "MmF(c, n) = c.take(n)\nData = (1, 2, 3)\nA = MmF(Data, 2)\nB = Data.MmF(2)\nA";
        var model = Assert.IsType<SemanticModel>(EditorModel.Run(source, EditorExecutionMode.Elaborated).Model);

        var ordinary = model.IdentifierResolutions.Single(resolution =>
            resolution.Occurrence.Name == "MmF" && resolution.Occurrence.Kind == OccurrenceKind.ResolveReference);
        var dotted = model.IdentifierResolutions.Single(resolution =>
            resolution.Occurrence.Name == "MmF" && resolution.Occurrence.Kind == OccurrenceKind.DotMemberReference);

        Assert.NotNull(ordinary.ResolvedDeclaration);
        Assert.Equal(ordinary.ResolvedDeclaration, dotted.ResolvedDeclaration);
    }

    // ── Negative harness tests: the validator must catch each violation class ─

    private static SemanticModel DoctoredModel(
        string okSource,
        IReadOnlyList<IdentifierOccurrence>? occurrences = null,
        IReadOnlyList<DeclarationOccurrence>? declarations = null,
        IReadOnlyList<IdentifierResolution>? resolutions = null)
    {
        var root = Parser.Parse(okSource).Root;
        return new SemanticModel(
            root,
            occurrences ?? [],
            declarations ?? [],
            resolutions ?? [],
            [],
            new Dictionary<DeclarationOccurrence, KatLang.Semantics.PropertyInfo>());
    }

    [Fact]
    public void SpanValidator_DetectsEveryOutOfRangeClass()
    {
        var lineWidths = SourceSpanValidator.LineWidths("ab = 1");
        Assert.NotNull(SourceSpanValidator.Validate(new SourceSpan(1, 0, 1, 1), lineWidths));   // negative/zero start column
        Assert.NotNull(SourceSpanValidator.Validate(new SourceSpan(1, 3, 1, 1), lineWidths));   // reversed range
        Assert.NotNull(SourceSpanValidator.Validate(new SourceSpan(5, 1, 5, 1), lineWidths));   // line beyond source
        Assert.NotNull(SourceSpanValidator.Validate(new SourceSpan(1, 1, 1, 99), lineWidths));  // column beyond line width
        Assert.Null(SourceSpanValidator.Validate(new SourceSpan(1, 1, 1, 2), lineWidths));      // valid
    }

    [Fact]
    public void ValidateModel_ThrowsOnAnOutOfRangeOccurrenceSpan()
    {
        var occurrence = new IdentifierOccurrence("ab", new SourceSpan(1, 1, 9, 9), OccurrenceKind.ResolveReference);
        var model = DoctoredModel("ab = 1", occurrences: [occurrence]);
        Assert.Throws<EditorInvariantException>(() => EditorModel.ValidateModel("ab = 1", model));
    }

    [Fact]
    public void ValidateModel_ThrowsOnASyntheticName()
    {
        var occurrence = new IdentifierOccurrence("$x", new SourceSpan(1, 1, 1, 2), OccurrenceKind.ResolveReference);
        var model = DoctoredModel("ab = 1", occurrences: [occurrence]);
        Assert.Throws<EditorInvariantException>(() => EditorModel.ValidateModel("ab = 1", model));
    }

    [Fact]
    public void ValidateModel_ThrowsOnAnInventedBuiltin()
    {
        var occurrence = new IdentifierOccurrence("nostuff", new SourceSpan(1, 1, 1, 7), OccurrenceKind.ResolveReference);
        var resolution = new IdentifierResolution(occurrence, IdentifierClassification.Builtin, null, null);
        var model = DoctoredModel("nostuff", resolutions: [resolution]);
        Assert.Throws<EditorInvariantException>(() => EditorModel.ValidateModel("nostuff", model));
    }

    [Fact]
    public void ValidateModel_ThrowsWhenAResolutionTargetsADifferentlyNamedDeclaration()
    {
        var source = "A = 1\nB = 2";
        var occurrence = new IdentifierOccurrence("A", new SourceSpan(1, 1, 1, 1), OccurrenceKind.ResolveReference);
        var declaration = new DeclarationOccurrence("B", new SourceSpan(2, 1, 2, 1), OccurrenceKind.PropertyDefinition);
        var resolution = new IdentifierResolution(occurrence, IdentifierClassification.PropertyReference, declaration, null);
        var model = DoctoredModel(source, occurrences: [occurrence], declarations: [declaration], resolutions: [resolution]);
        Assert.Throws<EditorInvariantException>(() => EditorModel.ValidateModel(source, model));
    }

    // ── Seed manifest ────────────────────────────────────────────────────────

    [Fact]
    public void SeedManifest_ParsesAValidLine_AndReportsAStaleTemplate()
    {
        var payload = EditorDecoder.Encode(EditorDecoder.Decode([]) with { Template = EditorTemplateKind.DottedCall });
        var hex = string.Join(' ', payload.Select(b => b.ToString("X2")));
        var line = $"template=dotted-call bytes={hex} desc=smoke";

        Assert.True(EditorSeedFile.TryParse(line, "seeds.txt", 1, out var seed, out var problem), problem);
        Assert.Equal(EditorTemplateKind.DottedCall, seed.DeclaredTemplate);

        var stale = $"template=empty bytes={hex} desc=stale";
        Assert.False(EditorSeedFile.TryParse(stale, "seeds.txt", 2, out _, out var staleProblem));
        Assert.Contains("does not match", staleProblem, StringComparison.Ordinal);
    }
}
