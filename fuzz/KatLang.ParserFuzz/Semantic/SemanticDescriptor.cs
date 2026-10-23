using System.Collections.Immutable;
using System.Globalization;
using System.Reflection;
using System.Text;
using System.Text.Json;
using KatLang;

namespace KatLang.ParserFuzz;

/// <summary>
/// The durable, directly replayable SEM-2B case descriptor: format <c>kl-sem2b-case</c>, version 1.
///
/// <para>A descriptor is self-sufficient: generator and recipe versions, the durable case id with its
/// seed and index, the exact source of every compared member with its SHA-256, the profile matrix
/// (surface, optimizer setting, limits, host fixture, suspension/cancellation schedule, run order),
/// the comparison policy, the construction-derived expectation (value identity, emitted count, error
/// kind or diagnostic and phase, exact host events, intended paths), build provenance, and — when
/// the case was run — the recorded verdict and per-profile observations. Parsing is bounded; an
/// unknown format or version is refused, never reinterpreted.</para>
///
/// <para>The legacy metamorphic seed manifests (<c>family=… bytes=…</c>) are a different format
/// owned by <see cref="MetamorphicSeedFile"/> and are not touched by this one.</para>
/// </summary>
internal static class SemanticDescriptor
{
    internal const string Format = "kl-sem2b-case";
    internal const int FormatVersion = 1;
    internal const string ResultFormat = "kl-sem2b-result";

    internal const int MaxDescriptorChars = 1 << 20;
    internal const int MaxSourceChars = 64 * 1024;
    internal const int MaxMembers = 8;
    internal const int MaxListItems = 512;
    internal const int MaxStringChars = 16 * 1024;

    // Relaxed escaping keeps recorded sources readable (`<`, `+`, quotes as written); descriptors
    // are data files, never embedded in HTML. A fixed LF keeps descriptor text platform-independent.
    private static readonly JsonWriterOptions WriterOptions = new()
    {
        Indented = true,
        NewLine = "\n",
        Encoder = System.Text.Encodings.Web.JavaScriptEncoder.UnsafeRelaxedJsonEscaping,
    };

    private static readonly JsonDocumentOptions ReaderOptions = new()
    {
        MaxDepth = 16,
        AllowTrailingCommas = false,
        CommentHandling = JsonCommentHandling.Disallow,
    };

    /// <summary>Build provenance: the language assembly's informational version (with its source revision).</summary>
    internal static string Provenance()
    {
        var katlang = typeof(Parser).Assembly;
        var version = katlang.GetCustomAttribute<AssemblyInformationalVersionAttribute>()?.InformationalVersion ?? "unknown";
        var host = Assembly.GetEntryAssembly()?.GetName().Name ?? "unknown-host";
        return $"KatLang {version}; harness {typeof(SemanticDescriptor).Assembly.GetName().Name}; host {host}";
    }

    // ── Writing ─────────────────────────────────────────────────────────────

    internal static string Write(SemanticCase semanticCase, SemanticCaseResult? result = null)
    {
        ArgumentNullException.ThrowIfNull(semanticCase);
        using var stream = new MemoryStream();
        using (var w = new Utf8JsonWriter(stream, WriterOptions))
        {
            w.WriteStartObject();
            w.WriteString("format", Format);
            w.WriteNumber("formatVersion", FormatVersion);
            w.WriteString("generator", SemanticRecipe.GeneratorId);
            w.WriteNumber("recipeVersion", SemanticRecipe.RecipeVersion);
            w.WriteString("caseId", semanticCase.CaseId);
            w.WriteString("tier", semanticCase.Tier);
            if (semanticCase.Seed is { } seed) w.WriteString("seed", "0x" + seed.ToString("X", CultureInfo.InvariantCulture));
            else w.WriteNull("seed");
            if (semanticCase.Index is { } index) w.WriteNumber("index", index);
            else w.WriteNull("index");
            w.WriteString("kind", KindId(semanticCase.Kind));
            Strings(w, "families", semanticCase.Families);
            Strings(w, "features", semanticCase.Features);

            w.WriteStartArray("members");
            foreach (var member in semanticCase.Members)
            {
                w.WriteStartObject();
                w.WriteString("role", member.Role);
                w.WriteString("sha256", member.Fingerprint);
                w.WriteString("source", member.Source);
                w.WriteEndObject();
            }

            w.WriteEndArray();

            w.WriteStartArray("profiles");
            foreach (var id in semanticCase.Profiles)
            {
                var profile = SemanticProfiles.Get(id);
                w.WriteStartObject();
                w.WriteString("id", id);
                w.WriteString("surface", profile.Definition.Id);
                w.WriteString("facets", profile.Definition.Facets.ToString());
                w.WriteString("detail", profile.Describe());
                w.WriteEndObject();
            }

            w.WriteEndArray();
            w.WriteNull("runtimeRandomSeed"); // generated programs draw no random numbers
            w.WriteString("hostFixture", MetamorphicHostFixture.FixtureId);

            w.WriteStartObject("comparison");
            w.WriteString("structure", MetamorphicStructuralIdentity.Version + " + Result.ValueComparer");
            w.WriteString("errors", "strict-same-source (profiles); normalized (transformations)");
            w.WriteString("facets", "declared surface intersection; root emitted count separate; host events exact");
            Strings(w, "relations", SemanticProfiles.RelationsFor(semanticCase));
            w.WriteEndObject();

            var expected = semanticCase.Expected;
            w.WriteStartObject("expected");
            w.WriteString("kind", KindId(expected.Kind));
            if (expected.ValueIdentity is { } identity) w.WriteString("value", identity);
            else w.WriteNull("value");
            if (expected.EmittedCount is { } count) w.WriteNumber("emittedCount", count);
            else w.WriteNull("emittedCount");
            w.WriteString("errorCategory", expected.ErrorCategory);
            w.WriteString("diagnostic", expected.Diagnostic?.ToString());
            w.WriteString("diagnosticPhase", expected.DiagnosticPhase);
            Strings(w, "events", expected.Events);
            Strings(w, "cancelledEventsPrefix", expected.CancelledEventsPrefix);
            w.WriteString("paths", semanticCase.Paths.ToString());
            w.WriteNumber("minimumCacheHits", semanticCase.MinimumCacheHits);
            w.WriteEndObject();

            w.WriteString("provenance", Provenance());
            if (result is not null)
            {
                w.WritePropertyName("result");
                WriteResult(w, result);
            }

            w.WriteEndObject();
        }

        return Encoding.UTF8.GetString(stream.ToArray()) + "\n";
    }

    /// <summary>The worker's output document: one case result, no live state.</summary>
    internal static string WriteResultDocument(SemanticCaseResult result)
    {
        using var stream = new MemoryStream();
        using (var w = new Utf8JsonWriter(stream, WriterOptions))
        {
            w.WriteStartObject();
            w.WriteString("format", ResultFormat);
            w.WriteNumber("formatVersion", FormatVersion);
            w.WritePropertyName("result");
            WriteResult(w, result);
            w.WriteEndObject();
        }

        return Encoding.UTF8.GetString(stream.ToArray());
    }

    private static void WriteResult(Utf8JsonWriter w, SemanticCaseResult result)
    {
        w.WriteStartObject();
        w.WriteString("caseId", result.CaseId);
        w.WriteString("verdict", result.Verdict.ToString());
        Strings(w, "findings", result.Findings);
        w.WriteString("pathsExercised", result.PathsExercised.ToString());
        Strings(w, "pathRejections", result.PathRejections);
        Strings(w, "relations", result.RelationsChecked);
        w.WriteStartArray("observations");
        foreach (var run in result.Runs)
        {
            var o = run.Observation;
            w.WriteStartObject();
            w.WriteString("profile", run.Profile);
            w.WriteString("member", run.Member);
            w.WriteString("outcome", run.OutcomeText);
            w.WriteString("valueIdentity", o?.Semantic.StructuralIdentity);
            if (o?.Semantic.EmittedCount is { } emitted) w.WriteNumber("emittedCount", emitted);
            else w.WriteNull("emittedCount");
            w.WriteString("errorCategory", o?.Semantic.ErrorCategory);
            w.WriteString("failureStage", o?.FailureStage);
            Strings(w, "events", run.Events);
            w.WriteNumber("waitCalls", run.WaitCalls);
            w.WriteNumber("suspensions", run.Suspensions);
            w.WriteBoolean("cancelled", run.Cancelled);
            w.WriteString("optimizerEvidence", o?.OptimizerEvidence?.ToString());
            w.WriteString("cacheEvidence", o?.CacheEvidence?.ToString());
            w.WriteString("harness", run.HarnessProblem);
            w.WriteEndObject();
        }

        w.WriteEndArray();
        w.WriteEndObject();
    }

    private static void Strings(Utf8JsonWriter w, string name, IEnumerable<string> values)
    {
        w.WriteStartArray(name);
        foreach (var value in values) w.WriteStringValue(value);
        w.WriteEndArray();
    }

    private static string KindId(SemanticCaseKind kind) => kind switch
    {
        SemanticCaseKind.ValidSuccess => "valid-success",
        SemanticCaseKind.ValidRuntimeFailure => "valid-runtime-failure",
        _ => "invalid-front-end",
    };

    private static bool TryKind(string? text, out SemanticCaseKind kind)
    {
        (kind, var ok) = text switch
        {
            "valid-success" => (SemanticCaseKind.ValidSuccess, true),
            "valid-runtime-failure" => (SemanticCaseKind.ValidRuntimeFailure, true),
            "invalid-front-end" => (SemanticCaseKind.InvalidFrontEnd, true),
            _ => (default, false),
        };
        return ok;
    }

    // ── Reading ─────────────────────────────────────────────────────────────

    /// <summary>A parsed descriptor: the recorded case, its recipe identity, and any recorded verdict.</summary>
    internal sealed record Parsed(
        string Generator,
        int RecipeVersion,
        SemanticCase Case,
        string Provenance,
        string? RecordedVerdict);

    /// <summary>
    /// Parses a descriptor under explicit bounds. Every member's recorded source is verified against
    /// its recorded SHA-256; unknown formats, versions, generators, kinds, profiles and paths are
    /// refused with a clear problem.
    /// </summary>
    internal static bool TryParse(string text, out Parsed parsed, out string problem)
    {
        parsed = null!;
        if (text is null) { problem = "no descriptor text"; return false; }
        if (text.Length > MaxDescriptorChars)
        {
            problem = $"descriptor exceeds {MaxDescriptorChars.ToString(CultureInfo.InvariantCulture)} characters";
            return false;
        }

        JsonDocument document;
        try
        {
            document = JsonDocument.Parse(text, ReaderOptions);
        }
        catch (JsonException exception)
        {
            problem = "malformed descriptor JSON: " + exception.Message;
            return false;
        }

        using (document)
        {
            try
            {
                return TryRead(document.RootElement, out parsed, out problem);
            }
            catch (Exception exception) when (exception is InvalidOperationException or FormatException or KeyNotFoundException or ArgumentException or OverflowException)
            {
                problem = "malformed descriptor: " + exception.Message;
                return false;
            }
        }
    }

    private static bool TryRead(JsonElement root, out Parsed parsed, out string problem)
    {
        parsed = null!;
        if (root.ValueKind != JsonValueKind.Object) { problem = "descriptor is not a JSON object"; return false; }

        var format = Str(root, "format");
        if (format != Format) { problem = $"unknown descriptor format '{format}' (expected '{Format}')"; return false; }
        var version = root.GetProperty("formatVersion").GetInt32();
        if (version != FormatVersion)
        {
            problem = $"unsupported {Format} version {version.ToString(CultureInfo.InvariantCulture)} (this harness reads version {FormatVersion.ToString(CultureInfo.InvariantCulture)})";
            return false;
        }

        var generator = Str(root, "generator");
        if (generator != SemanticRecipe.GeneratorId) { problem = $"unknown generator '{generator}'"; return false; }
        var recipeVersion = root.GetProperty("recipeVersion").GetInt32();
        var caseId = Str(root, "caseId") ?? throw new FormatException("missing caseId");
        var tier = Str(root, "tier") ?? throw new FormatException("missing tier");
        ulong? seed = root.GetProperty("seed").ValueKind == JsonValueKind.Null
            ? null
            : ulong.Parse(Str(root, "seed")!.Replace("0x", "", StringComparison.Ordinal), NumberStyles.HexNumber, CultureInfo.InvariantCulture);
        int? index = root.GetProperty("index").ValueKind == JsonValueKind.Null ? null : root.GetProperty("index").GetInt32();
        if (!TryKind(Str(root, "kind"), out var kind)) { problem = $"unknown case kind '{Str(root, "kind")}'"; return false; }

        var members = new List<SemanticMember>();
        foreach (var member in Array(root, "members"))
        {
            var role = Str(member, "role") ?? throw new FormatException("member without role");
            if (role is not (SemanticMember.BaseRole or SemanticMember.AlphaRenameRole or SemanticMember.DeclarationReorderRole))
                throw new FormatException("unknown member role '" + role + "'");
            var source = Str(member, "source") ?? throw new FormatException("member without source");
            if (source.Length > MaxSourceChars) { problem = $"member '{role}' source exceeds {MaxSourceChars} characters"; return false; }
            var recorded = Str(member, "sha256");
            var actual = SemanticFingerprint.Of(source);
            if (recorded != actual) { problem = $"member '{role}' source does not match its recorded fingerprint ({recorded} vs {actual})"; return false; }
            members.Add(new SemanticMember(role, source));
        }

        if (members.Count == 0 || members.Count > MaxMembers || members[0].Role != SemanticMember.BaseRole)
        {
            problem = "a descriptor needs 1.." + MaxMembers + " members, the first being the base";
            return false;
        }

        if (members.Select(m => m.Role).Distinct(StringComparer.Ordinal).Count() != members.Count)
            throw new FormatException("duplicate member roles");

        var profiles = new List<string>();
        foreach (var profile in Array(root, "profiles"))
        {
            var id = Str(profile, "id") ?? throw new FormatException("profile without id");
            if (!SemanticProfiles.TryGet(id, out var definition)) { problem = $"unknown profile '{id}'"; return false; }
            if (Str(profile, "surface") != definition.Definition.Id
                || Str(profile, "facets") != definition.Definition.Facets.ToString()
                || Str(profile, "detail") != definition.Describe())
                throw new FormatException($"profile '{id}' execution contract drift (surface, facets or settings)");
            profiles.Add(id);
        }

        if (profiles.Count == 0 || profiles.Distinct(StringComparer.Ordinal).Count() != profiles.Count)
            throw new FormatException("a descriptor needs nonempty, unique execution profiles; nothing verified");
        if (members.Count > 1 && !profiles.Contains(SemanticProfiles.SyncOptimized, StringComparer.Ordinal))
            throw new FormatException("transformed members require the sync-optimized comparison profile");
        if (Str(root, "hostFixture") != MetamorphicHostFixture.FixtureId
            || root.GetProperty("runtimeRandomSeed").ValueKind != JsonValueKind.Null)
            throw new FormatException("unsupported host fixture or runtime random seed");
        var comparison = root.GetProperty("comparison");
        if (Str(comparison, "structure") != MetamorphicStructuralIdentity.Version + " + Result.ValueComparer"
            || Str(comparison, "errors") != "strict-same-source (profiles); normalized (transformations)"
            || Str(comparison, "facets") != "declared surface intersection; root emitted count separate; host events exact")
            throw new FormatException("comparison policy drift");

        var expected = root.GetProperty("expected");
        if (!TryKind(Str(expected, "kind"), out var expectedKind) || expectedKind != kind)
        {
            problem = "expected.kind disagrees with the case kind";
            return false;
        }

        Result? value = null;
        if (Str(expected, "value") is { } identity
            && !MetamorphicStructuralIdentity.TryDecode(identity, out value, out var identityProblem))
        {
            problem = "expected value is not a valid " + MetamorphicStructuralIdentity.Version + " identity: " + identityProblem;
            return false;
        }

        int? emitted = expected.GetProperty("emittedCount").ValueKind == JsonValueKind.Null ? null : expected.GetProperty("emittedCount").GetInt32();
        DiagnosticCode? diagnostic = null;
        if (Str(expected, "diagnostic") is { } diagnosticText)
        {
            if (!Enum.TryParse<DiagnosticCode>(diagnosticText, ignoreCase: false, out var code) || !Enum.IsDefined(code))
            {
                problem = $"unknown diagnostic '{diagnosticText}'";
                return false;
            }

            diagnostic = code;
        }

        const SemanticPath knownPaths = SemanticPath.EvidenceBacked | SemanticPath.LazyTransport | SemanticPath.FreshInvocation
            | SemanticPath.DeadComputationUntouched | SemanticPath.FirstFailureStops | SemanticPath.CardinalityBeforeDemand;
        if (!Enum.TryParse<SemanticPath>(Str(expected, "paths") ?? "None", ignoreCase: false, out var paths)
            || (paths & ~knownPaths) != 0)
        {
            problem = $"unknown path set '{Str(expected, "paths")}'";
            return false;
        }

        var expectation = new SemanticExpectation(
            kind, value, emitted, Str(expected, "errorCategory"), diagnostic, Str(expected, "diagnosticPhase"), [.. StringArray(expected, "events")])
        {
            CancelledEventsPrefix = [.. StringArray(expected, "cancelledEventsPrefix")],
        };
        if (!Consistent(expectation, out problem)) return false;
        if (kind == SemanticCaseKind.ValidRuntimeFailure
            && !profiles.Any(p => SemanticProfiles.Get(p).Definition.Facets.HasFlag(MetamorphicFacets.StructuredError)))
            throw new FormatException("a runtime failure needs a profile that exposes its required structured error");
        var minimumCacheHits = expected.GetProperty("minimumCacheHits").GetInt32();
        if (minimumCacheHits < 0 || paths.HasFlag(SemanticPath.CacheHit) != (minimumCacheHits > 0))
            throw new FormatException("cache-hit path and minimum cache hits disagree");

        var semanticCase = new SemanticCase(
            caseId, tier, seed, index, expectation, [.. members],
            [.. StringArray(root, "families")], [.. StringArray(root, "features")],
            paths, minimumCacheHits, [.. profiles]);
        if (!StringArray(comparison, "relations").SequenceEqual(SemanticProfiles.RelationsFor(semanticCase)))
            throw new FormatException("declared relation policy drift");
        string? recordedVerdict = root.TryGetProperty("result", out var result) ? Str(result, "verdict") : null;
        parsed = new Parsed(generator!, recipeVersion, semanticCase, Str(root, "provenance") ?? "", recordedVerdict);
        problem = "";
        return true;
    }

    /// <summary>An expectation must name exactly what its kind needs; anything else is a corrupt descriptor.</summary>
    private static bool Consistent(SemanticExpectation e, out string problem)
    {
        problem = e.Kind switch
        {
            SemanticCaseKind.ValidSuccess when e.Value is null || e.EmittedCount is null => "a success expectation needs a value and an emitted count",
            SemanticCaseKind.ValidRuntimeFailure when string.IsNullOrEmpty(e.ErrorCategory) => "a runtime-failure expectation needs an error category",
            SemanticCaseKind.InvalidFrontEnd when e.Diagnostic is null
                || (e.DiagnosticPhase != SemanticExpectation.SyntaxPhase && e.DiagnosticPhase != SemanticExpectation.ElaborationPhase)
                => "a front-end expectation needs a diagnostic and a phase",
            _ => "",
        };
        return problem.Length == 0;
    }

    /// <summary>A worker result document reduced to what a supervisor needs.</summary>
    internal sealed record ResultSummary(string CaseId, SemanticVerdict Verdict, ImmutableArray<string> Findings,
        ImmutableArray<string> ObservedProfiles, SemanticCaseResult CoverageResult);

    internal static bool TryParseResult(string text, out ResultSummary summary, out string problem)
    {
        summary = null!;
        if (text.Length > MaxDescriptorChars) { problem = "result document exceeds its bound"; return false; }
        try
        {
            using var document = JsonDocument.Parse(text, ReaderOptions);
            var root = document.RootElement;
            if (Str(root, "format") != ResultFormat || root.GetProperty("formatVersion").GetInt32() != FormatVersion)
            {
                problem = "not a " + ResultFormat + " v" + FormatVersion + " document";
                return false;
            }

            var result = root.GetProperty("result");
            if (!Enum.TryParse<SemanticVerdict>(Str(result, "verdict"), ignoreCase: false, out var verdict) || !Enum.IsDefined(verdict))
            {
                problem = $"unknown verdict '{Str(result, "verdict")}'";
                return false;
            }

            var runs = new List<SemanticProfileRun>();
            foreach (var o in Array(result, "observations"))
            {
                var profile = Str(o, "profile") ?? throw new FormatException("observation without profile");
                _ = SemanticProfiles.Get(profile);
                var member = Str(o, "member") ?? throw new FormatException("observation without member");
                var outcome = Str(o, "outcome") ?? throw new FormatException("observation without outcome");
                if (outcome is not ("ok" or "err" or "cancelled" or "harness") && !outcome.StartsWith("not-run:", StringComparison.Ordinal))
                    throw new FormatException("unknown observation outcome");
                if (outcome == "ok" && (Str(o, "valueIdentity") is not { } identity
                    || !MetamorphicStructuralIdentity.TryDecode(identity, out _, out _)
                    || o.GetProperty("emittedCount").ValueKind != JsonValueKind.Number))
                    throw new FormatException("successful observation lacks its structure or emitted count");
                runs.Add(new SemanticProfileRun(profile, member, outcome is "ok" or "err", outcome, null,
                    [.. StringArray(o, "events")], o.GetProperty("waitCalls").GetInt32(), o.GetProperty("suspensions").GetInt32(),
                    false, o.GetProperty("cancelled").GetBoolean(), Str(o, "harness")));
            }
            var observed = runs.Select(o => o.Profile + "/" + o.Member).ToImmutableArray();
            if (observed.Distinct(StringComparer.Ordinal).Count() != observed.Length)
                throw new FormatException("duplicate observations");
            var findings = StringArray(result, "findings").ToImmutableArray();
            if (verdict == SemanticVerdict.Passed && !findings.IsEmpty) throw new FormatException("passed result has findings");
            var caseId = Str(result, "caseId") ?? throw new FormatException("result without caseId");
            if (!Enum.TryParse<SemanticPath>(Str(result, "pathsExercised"), out var exercised)) throw new FormatException("invalid exercised paths");
            var coverage = new SemanticCaseResult(caseId, verdict, findings, [.. runs], exercised,
                [.. StringArray(result, "pathRejections")], [.. StringArray(result, "relations")]);
            summary = new ResultSummary(caseId, verdict, findings, observed, coverage);
            problem = "";
            return true;
        }
        catch (Exception exception) when (exception is JsonException or InvalidOperationException or KeyNotFoundException or FormatException or MetamorphicHarnessException)
        {
            problem = "malformed result document: " + exception.Message;
            return false;
        }
    }

    private static string? Str(JsonElement element, string name)
    {
        if (!element.TryGetProperty(name, out var value) || value.ValueKind == JsonValueKind.Null) return null;
        var text = value.GetString() ?? throw new FormatException($"'{name}' is not a string");
        if (text.Length > MaxSourceChars) throw new FormatException($"'{name}' exceeds its bound");
        return text;
    }

    private static IEnumerable<JsonElement> Array(JsonElement element, string name)
    {
        var array = element.GetProperty(name);
        if (array.ValueKind != JsonValueKind.Array) throw new FormatException($"'{name}' is not an array");
        if (array.GetArrayLength() > MaxListItems) throw new FormatException($"'{name}' exceeds {MaxListItems} items");
        return array.EnumerateArray().ToList();
    }

    private static List<string> StringArray(JsonElement element, string name)
        => Array(element, name).Select(item =>
        {
            var text = item.GetString() ?? throw new FormatException($"'{name}' holds a non-string");
            if (text.Length > MaxStringChars) throw new FormatException($"'{name}' item exceeds its bound");
            return text;
        }).ToList();
}
