using System.Numerics;

namespace KatLang.Tests;

/// <summary>
/// EXPOSURE AND THE PROVENANCE FINALIZER ENTER A DEFERRED UNIT'S INLINE OPEN TARGET WHERE VALIDATION DOES (2026-11-24;
/// C#-only front end, no Lean counterpart: Lean has no deferred-region model, Q-63). An inline block written as an
/// open target (<c>open { … }</c>) is declared at the prelude, without the opener's declarations, so every pass that
/// walks into it starts a region of its own at a prelude level. A load-bearing clause branch is one deferred unit,
/// elaborated when it is selected under the scope chain the parse recorded at its branch, and that chain's root level
/// carries the EAGER program's completed facts, where the block is the entry of the unit's placeholder: the same
/// declaration, with no body.
///
/// <para>Open-provider validation already entered the block at the prelude level over the facts that answer for a
/// block head, the unit's own (<c>ElaboratedScopeLookup.OpenBlockHeadLevel</c>, pinned by
/// <see cref="DeferredOpenTargetValidationTests"/>). Exposure (<c>PropertyExposureResolver.OpenTargetRegion</c>, for a
/// level's and a host family's open list) and the provenance finalizer
/// (<c>DotMemberProvenanceFinalizer.VisitOpenExpression</c>) entered it at the recorded chain's root instead, so the
/// block's levels were bound to the bodiless eager entry. On the investigation's revision that made a valid
/// program throw (a block-headed member read, <c>{ public Q = 7 }.Q</c>: "A completed block-head requirement body is
/// unavailable"), classified a member that captures a parameter <c>Exported</c> (a valid program refused with
/// <c>LocalOnlyProperty</c>, or, on an earlier revision, the value 44 instead of 45), blamed the wrong member, and
/// dropped the receiver-aware lines of a dot-member fallback note. Below a load-free branch the loader keeps by
/// reference the block has one static key in both publications and only the note was lost, except in a hoisted
/// deconstruction row, which is summarized with its level's own context and lost its capture too.</para>
///
/// <para><b>The oracle is the plain twin</b>: the same text with the holder <c>H = load('…/unused.kat')</c> written
/// <c>H = 0</c>, at the end of its line, so every other token keeps its position. Every witness must give the twin's
/// value, or its error with the same code, span and message, notes included, and the materialized unit must classify
/// every property as the twin's branch body does: exposure, required parameters and capture positions. Only the
/// holder's own members differ (a loaded module against a number) and are left out. The twin's outcome and the
/// decisive classifications are also pinned, so the oracle cannot drift with the defect.</para>
///
/// <para>Every program runs through <see cref="KatLangEngine.RunAsync(string, RunOptions?)"/> with a fixed local
/// downloader (one module, <c>public ZzUnused = 0</c>, at one URL; <c>AllowedHosts = ["modules.example"]</c>) after a
/// clean parse that holds a region and downloads nothing. The host-tree cases stage a raw tree through the loader and
/// the production passes as <see cref="DeferredSharedOpenTargetBlockTests"/> does.</para>
/// </summary>
public class DeferredInlineOpenTargetExposureTests
{
    private const string Host = "modules.example";
    private const string UnusedUrl = "https://" + Host + "/unused.kat";
    private const string Load = "load('" + UnusedUrl + "')";
    private const string ModuleText = "public ZzUnused = 0\n";

    /// <summary>The fixed local downloader of one run: the one module, its downloads counted.</summary>
    private sealed class ModuleHost
    {
        public int Fetches { get; private set; }

        public ValueTask<string> Download(string url, CancellationToken cancellationToken)
        {
            Assert.Equal(UnusedUrl, url);
            Fetches++;
            return ValueTask.FromResult(ModuleText);
        }

        public RunOptions Options => new() { AllowedHosts = [Host], DownloadCode = Download };
    }

    /// <summary>
    /// The witness frame: <c>F</c>'s second clause is the unit, whose first row holds the unused module (deferred) or
    /// the number 0 (the plain twin), at the end of its line; <paramref name="body"/> starts on line 3, and every further
    /// holder it writes as <c>$H</c>, also at the end of a line, becomes the same.
    /// </summary>
    private static string Unit(string body, bool deferred)
        => ("F(0) = 0\nF(n) = { H = $H\n" + body + " }\nF(1)\n").Replace("$H", deferred ? Load : "0", StringComparison.Ordinal);

    // ── Outcomes ────────────────────────────────────────────────────────────

    private static string Describe(KatLangError error) => $"{error.Code}@{error.Span}: {error.Message}";

    private static string Outcome(RunResult result) => result switch
    {
        RunResult.Success success => "value " + success.ToDisplayString(),
        RunResult.EvalFailure failure => string.Join("\n|\n", failure.Errors.Select(Describe)),
        RunResult.ParseFailure failure => "parse failure " + string.Join("\n|\n", failure.Errors.Select(Describe)),
        RunResult.NoProgramOutput none => "no program output " + Describe(none.Diagnostic),
    };

    private static string Outcome(EvalResult<IReadOnlyList<Decimal128>> result)
        => result.IsError ? Describe(KatLangError.FromEvalError(result.Error)) : "value " + string.Join(", ", result.Value);

    // ── Classification ──────────────────────────────────────────────────────

    /// <summary>A property's classification: its exposure, the parameters it requires, and their owner positions.</summary>
    private static string Classification(Property property)
    {
        var text = property.Exposure.ToString();
        if (property.RequiredAncestorParameters.Count > 0)
            text += " requires [" + string.Join(",", property.RequiredAncestorParameters) + "]";
        if (property.CaptureRequirements is { Count: > 0 } captures)
            text += " captures [" + string.Join(",", captures.Select(static capture => capture.Name + "@" + capture.OwnerDepth)) + "]";
        return text;
    }

    /// <summary>
    /// Every property below <paramref name="algorithm"/> by path: <c>/Name</c> for a property, <c>#i</c> for a branch,
    /// <c>/open{}</c> for an open target's block and <c>/{}</c> for a block in a row; a materialized region is read
    /// through its unit.
    /// </summary>
    private static void Classify(Algorithm algorithm, string path, SortedDictionary<string, string> into, HashSet<object> seen)
    {
        if (!seen.Add(algorithm))
            return;
        if (algorithm.DeferredRegion is { } region)
        {
            if (region.TryGetMaterialized(out var materialized))
                Classify(materialized, path, into, seen);
            else
                into[path] = "(not materialized)";
            return;
        }

        foreach (var property in algorithm.Properties)
        {
            into[path + "/" + property.Name] = Classification(property);
            Classify(property.Value, path + "/" + property.Name, into, seen);
        }

        var open = 0;
        foreach (var expression in algorithm.Opens)
            foreach (var block in BlocksIn(expression))
                Classify(block, path + "/open{}" + (open++ == 0 ? "" : open.ToString(System.Globalization.CultureInfo.InvariantCulture)), into, seen);
        if (algorithm is Algorithm.Conditional family)
            for (var index = 0; index < family.Branches.Count; index++)
                Classify(family.Branches[index].Body, path + "#" + index, into, seen);
        var row = 0;
        foreach (var block in RowBlocks(algorithm))
            Classify(block, path + "/{}" + (row++ == 0 ? "" : row.ToString(System.Globalization.CultureInfo.InvariantCulture)), into, seen);
    }

    private static IEnumerable<Algorithm> RowBlocks(Algorithm algorithm)
    {
        if (algorithm is Algorithm.User user)
            foreach (var expression in user.Output)
                foreach (var block in BlocksIn(expression))
                    yield return block;
        if (algorithm is Algorithm.Alias alias)
            foreach (var block in BlocksIn(alias.Target))
                yield return block;
    }

    /// <summary>The outermost blocks of an expression, in no particular order.</summary>
    private static IEnumerable<Algorithm> BlocksIn(object node)
    {
        var pending = new Stack<object>();
        var seen = new HashSet<object>(ReferenceEqualityComparer.Instance);
        pending.Push(node);
        while (pending.TryPop(out var at))
        {
            if (!seen.Add(at))
                continue;
            if (at is Algorithm found)
            {
                yield return found;
                continue;
            }

            for (var index = 0; AstStructuralPreflight.TryGetChild(at, index, out var child); index++)
                pending.Push(child!);
        }
    }

    /// <summary>
    /// The unit as classified, under the path <c>F#1</c>: <c>F</c>'s second clause (the materialized unit, or the plain
    /// twin's body), or <c>F</c> itself when a twin made it one clause.
    /// </summary>
    private static SortedDictionary<string, string> UnitClassification(Algorithm root)
    {
        var declared = root.Properties.Single(static property => property.Name == "F").Value;
        var body = declared is Algorithm.Conditional family ? family.Branches[1].Body : Assert.IsType<Algorithm.User>(declared);
        var into = new SortedDictionary<string, string>(StringComparer.Ordinal);
        Classify(body, "F#1", into, new HashSet<object>(ReferenceEqualityComparer.Instance));
        // A holder (H, H2) is a loaded module in the unit and a number in the twin: its own members are not compared.
        foreach (var holderMember in into.Keys.Where(static path => path.Contains("/H/", StringComparison.Ordinal)
                     || path.Contains("/H2/", StringComparison.Ordinal)).ToList())
            into.Remove(holderMember);
        return into;
    }

    // ── The witnesses ───────────────────────────────────────────────────────

    private const string LocalOnlyRequiringA = "LocalOnlyCapturedAncestorParameters requires [a]";

    private const string ArityR = "Callable `R(zz)` expects 1 argument, but was called with 0 arguments.";

    private const string FallbackNote = "Property 'zz' was not found on `P`, so the dotted call fell back to a lexical callable named 'zz'.";

    /// <summary>
    /// One witness: its unit body, the twin's outcome, and the classifications the twin gives that the defect changed
    /// (path, then classification without capture positions).
    /// </summary>
    public sealed record Witness(string Name, string Body, string Expected, params (string Path, string Classification)[] Pins)
    {
        public override string ToString() => Name;
    }

    private static readonly Witness[] Witnesses =
    [
        // ── An ordinary (rebuilt) block: the loader rebuilt the unit body, so the block has the unit's own key ──
        new("w1 rebuilt: a block-headed member read in the block (threw)",
            "  A = { open { public X = { public Q = 7 }.Q }\n    X }\n  A",
            "value 7"),
        new("w1b rebuilt: a block-headed member read inside a row of the block (threw)",
            "  A = { open { public X = { { public Q = 7 }.Q + 1 } }\n    X }\n  A",
            "value 8"),
        new("w2b rebuilt: a captured member read outside its owner's activation (blamed V on Inner)",
            "  A = { open { public G(a) = { Inner = { public V = a }\n      public W = Inner.V\n      W } }\n    G.W }\n  A",
            "LocalOnlyProperty@[6:5, 6:8): Property 'W' on `G` is local-only because it depends on parameter 'a', and a required owner activation is unavailable in this lexical context.",
            ("F#1/A/open{}/G/W", LocalOnlyRequiringA)),
        new("w8e rebuilt: a captured member classified Exported, read by an outer reader (refused, earlier 44)",
            "  A = { open { public G(a) = { Inner = { public V = a }\n      public W = Inner.V\n      public T = { W + 1 }\n      T } }\n    G(3) * 10 + G(4) }\n  A",
            "value 45",
            ("F#1/A/open{}/G/W", LocalOnlyRequiringA), ("F#1/A/open{}/G/T", LocalOnlyRequiringA)),
        new("w4 rebuilt: the receiver-aware lines of a dot-member fallback note (dropped)",
            "  A = { open { public P = { public W = 4 }\n      public R = P.zz }\n    R() }\n  A",
            "ArityMismatch@[5:5, 5:8): while evaluating call to F: " + ArityR + "\nAn implicit parameter 'zz' was inferred at [4:20].\n" + FallbackNote),
        new("w4d rebuilt: a dot-member fallback note in a dotted inline target (dropped)",
            "  A = { open { public S = { public P = { public W = 4 }\n        public R = P.zz } }.S\n    R() }\n  A",
            "ArityMismatch@[5:5, 5:8): while evaluating call to F: " + ArityR + "\nAn implicit parameter 'zz' was inferred at [4:22].\n" + FallbackNote),
        new("w2a rebuilt: the same value from a misclassified captured member",
            "  A = { open { public G(a) = { Inner = { public V = a }\n      W = Inner.V\n      W } }\n    G(3) * 10 + G(4) }\n  A",
            "value 34",
            ("F#1/A/open{}/G/W", LocalOnlyRequiringA)),
        new("w6 rebuilt: a captured member below a dotted inline target",
            "  A = { open { public S = { public G(a) = { Inner = { public V = a }\n        W = Inner.V\n        W } } }.S\n    G(3) * 10 + G(4) }\n  A",
            "value 34",
            ("F#1/A/open{}/S/G/W", LocalOnlyRequiringA)),
        new("o1 rebuilt: a hoisted deconstruction row reading a captured member path (refused)",
            "  A = { open { public K(a) = { Inner = { public V = a }\n      p, q = Inner.V, 1\n      p + q } }\n    K(3) * 10 + K(4) }\n  A",
            "value 45",
            ("F#1/A/open{}/K/$deconstruct$0", LocalOnlyRequiringA), ("F#1/A/open{}/K/p", LocalOnlyRequiringA), ("F#1/A/open{}/K/q", LocalOnlyRequiringA)),
        new("w7 nested unit: a block in a load-bearing branch of a family the unit declares",
            "  G(0) = 0\n  G(m) = { H2 = $H\n    A = { open { public K(a) = { Inner = { public V = a }\n        W = Inner.V\n        W } }\n      K(3) * 10 + K(4) }\n    A + m }\n  G(5)",
            "value 39",
            ("F#1/G#1/A/open{}/K/W", LocalOnlyRequiringA)),

        // ── A kept block: below a load-free branch the loader keeps by reference, one static key in both publications ──
        new("w5c kept: the receiver-aware lines of a dot-member fallback note (dropped)",
            "  G(0) = 0\n  G(m) = { open { public P = { public W = 4 }\n      public R = P.zz }\n    R() + m }\n  G(5)",
            "ArityMismatch@[6:5, 6:8): while evaluating call to F: while evaluating call to G: " + ArityR + "\nAn implicit parameter 'zz' was inferred at [5:20].\n" + FallbackNote),
        new("k1 kept: a hoisted deconstruction row reading a captured member path (refused)",
            "  G(0) = 0\n  G(m) = { open { public K(a) = { Inner = { public V = a }\n      p, q = Inner.V, 1\n      p + q } }\n    K(3) * 10 + K(4) + m }\n  G(5)",
            "value 50",
            ("F#1/G#1/open{}/K/$deconstruct$0", LocalOnlyRequiringA), ("F#1/G#1/open{}/K/p", LocalOnlyRequiringA), ("F#1/G#1/open{}/K/q", LocalOnlyRequiringA)),
        new("k5 kept: a member reading a hoisted row, read outside its owner's activation",
            "  G(0) = 0\n  G(m) = { open { public K(a) = { Inner = { public V = a }\n      p, q = Inner.V, 1\n      public W = p + q\n      W } }\n    K.W + m }\n  G(5)",
            "LocalOnlyProperty@[8:5, 8:8): while evaluating call to F: while evaluating call to G: Property 'W' on `K` is local-only because it depends on parameter 'a', and a required owner activation is unavailable in this lexical context.",
            ("F#1/G#1/open{}/K/W", LocalOnlyRequiringA)),

        // ── Controls that agreed before the repair as well ──
        new("control: a plain open target", "  A = { open { public X = 1 }\n    X }\n  A", "value 1"),
        new("control: a block-headed read in a row of the opener", "  A = { open { public X = 1 }\n    { public Q = X + 6 }.Q }\n  A", "value 7"),
        new("control: a block that opens a block", "  A = { open { open { public Z = 2 }\n      public X = Z + 1 }\n    X }\n  A", "value 3"),
        new("control: a block beside a named target in one open list", "  L = { public Z = 2 }\n  A = { open { public X = 1 }, L\n    X + Z }\n  A", "value 3"),
        new("control: the block does not see the opener's declarations", "  v = 5\n  A = { open { public X = v * 2 }\n    X(3) }\n  A", "value 6"),
        new("control: the note in the unit body, not in a block",
            "  P = { public W = 4 }\n  R = P.zz\n  A = { R() }\n  A",
            "ArityMismatch@[5:9, 5:12): while evaluating call to F: " + ArityR + "\nAn implicit parameter 'zz' was inferred at [4:9].\n" + FallbackNote),
        new("control kept: a plain open target", "  G(0) = 0\n  G(m) = { open { public X = 1 }\n    X + m }\n  G(5)", "value 6"),
        new("control kept: a block-headed member read", "  G(0) = 0\n  G(m) = { open { public X = { public Q = 7 }.Q }\n    X + m }\n  G(5)", "value 12"),
        new("control kept: a captured member path",
            "  G(0) = 0\n  G(m) = { open { public K(a) = { Inner = { public V = a }\n      W = Inner.V\n      W } }\n    K(3) * 10 + K(4) + m }\n  G(5)",
            "value 39",
            ("F#1/G#1/open{}/K/W", LocalOnlyRequiringA)),
    ];

    public static TheoryData<Witness> WitnessCases()
    {
        var data = new TheoryData<Witness>();
        foreach (var witness in Witnesses)
            data.Add(witness);
        return data;
    }

    /// <summary>
    /// THE WITNESSES AGAINST THEIR TWINS: the deferred program has the twin's value or error (code, span and message,
    /// notes included), downloads the module once, and its materialized unit classifies every property as the twin
    /// does. The twin's outcome and the pinned classifications are what the same text gives with nothing deferred.
    /// </summary>
    [Theory]
    [MemberData(nameof(WitnessCases))]
    public async Task Witness_RunsAndClassifiesLikeItsPlainTwin(Witness witness)
    {
        var deferred = Unit(witness.Body, deferred: true);
        var twin = Unit(witness.Body, deferred: false);

        var parseHost = new ModuleHost();
        var parsed = await SourceProvenance.ParseValidAsync(deferred, parseHost.Options);
        Assert.Empty(parsed.Diagnostics);
        Assert.Equal(0, parseHost.Fetches);
        Assert.True(DeferredModuleRegion.RequiresAsyncEvaluation(new Expr.AlgorithmExpr(parsed.Root)), "the program holds no deferred region");
        var twinParse = await SourceProvenance.ParseValidAsync(twin, new ModuleHost().Options);
        Assert.False(DeferredModuleRegion.RequiresAsyncEvaluation(new Expr.AlgorithmExpr(twinParse.Root)), "the twin holds a deferred region");

        var twinResult = await KatLangEngine.RunAsync(twin, new ModuleHost().Options);
        Assert.Equal(witness.Expected, Outcome(twinResult));

        var host = new ModuleHost();
        var result = await KatLangEngine.RunAsync(deferred, host.Options);
        Assert.Equal(witness.Expected, Outcome(result));
        // One module per canonical URL in a program: a nested unit's holder reuses the one the outer unit loaded.
        Assert.Equal(1, host.Fetches);

        var unit = UnitClassification(RootOf(result));
        var plain = UnitClassification(RootOf(twinResult));
        Assert.Equal(plain, unit);
        foreach (var (path, classification) in witness.Pins)
        {
            Assert.True(plain.TryGetValue(path, out var actual), $"the twin has no property at {path}");
            Assert.StartsWith(classification, actual, StringComparison.Ordinal);
            Assert.Equal(actual, unit[path]);
        }
    }

    private static Algorithm.User RootOf(RunResult result) => result switch
    {
        RunResult.Success success => success.Root,
        RunResult.EvalFailure failure => failure.Root,
        RunResult.NoProgramOutput none => none.Root,
        RunResult.ParseFailure failure => throw new Xunit.Sdk.XunitException("parse failure: " + string.Join(" | ", failure.Errors.Select(Describe))),
    };

    /// <summary>
    /// A LOADED MODULE BESIDE A BLOCK IN ONE OPEN LIST. Exposure enters the whole open list at the unit's prelude level;
    /// a loaded module there is still classified from its own publication, once, and the block beside it from the
    /// unit's facts (with the module holder in the list, the block-headed read threw before). The twin cannot drop the
    /// load, so it makes the family one clause instead (<c>F(0) = 0</c> becomes <c>F0 = 0</c>), which loads eagerly and
    /// keeps every other token in place.
    /// </summary>
    [Theory]
    [InlineData("  A = { open '" + UnusedUrl + "', { public X = 1 }\n    X + ZzUnused }\n  A", "value 1")]
    [InlineData("  A = { open H, { public X = { public Q = 7 }.Q }\n    X + ZzUnused }\n  A", "value 7")]
    public async Task ModuleBesideABlockInOneOpenList_RunsAndClassifiesLikeItsEagerTwin(string body, string expected)
    {
        var deferred = Unit(body, deferred: true);
        var twin = deferred.Replace("F(0) = 0\n", "F0 = 0\n", StringComparison.Ordinal);
        Assert.NotEqual(deferred, twin);
        var parsed = await SourceProvenance.ParseValidAsync(deferred, new ModuleHost().Options);
        Assert.True(DeferredModuleRegion.RequiresAsyncEvaluation(new Expr.AlgorithmExpr(parsed.Root)), "the program holds no deferred region");
        var twinParse = await SourceProvenance.ParseValidAsync(twin, new ModuleHost().Options);
        Assert.False(DeferredModuleRegion.RequiresAsyncEvaluation(new Expr.AlgorithmExpr(twinParse.Root)), "the twin holds a deferred region");

        var twinResult = await KatLangEngine.RunAsync(twin, new ModuleHost().Options);
        Assert.Equal(expected, Outcome(twinResult));
        var host = new ModuleHost();
        var result = await KatLangEngine.RunAsync(deferred, host.Options);
        Assert.Equal(expected, Outcome(result));
        Assert.Equal(1, host.Fetches);
        Assert.Equal(UnitClassification(RootOf(twinResult)), UnitClassification(RootOf(result)));
    }

    // ── Attempt cleanup ─────────────────────────────────────────────────────

    /// <summary>The four tables of a chain's lookup cache, by count (see <see cref="DeferredAttemptCacheRetentionTests"/>).</summary>
    private readonly record struct Tables(int CompletedLevels, int OpenBlockHeadLevels, int MemberIndexes, int BodyLevels)
    {
        public static Tables Of(OpenMemberIndexCache cache)
            => new(cache.CompletedLevels.Count, cache.OpenBlockHeadLevels.Count, cache.Count, cache.BodyLevelCount);
    }

    /// <summary>
    /// THE LOOKUPS STAY INSIDE THE ATTEMPT. Exposure and the finalizer now enter the block at the unit's prelude level,
    /// shared through the recorded chain's lookup cache, and build the block's levels over the unit's facts there. They
    /// do so before the attempt's early take-back, which removes them with the rest: the cache holds what it held before
    /// the selection, and the value or diagnostic is the twin's.
    /// </summary>
    [Theory]
    [InlineData("w8e rebuilt: a captured member classified Exported, read by an outer reader (refused, earlier 44)")]
    [InlineData("w4 rebuilt: the receiver-aware lines of a dot-member fallback note (dropped)")]
    [InlineData("k1 kept: a hoisted deconstruction row reading a captured member path (refused)")]
    [InlineData("w1 rebuilt: a block-headed member read in the block (threw)")]
    public async Task Attempt_LeavesNothingInTheRecordedChainsCache(string name)
    {
        var witness = Witnesses.Single(candidate => candidate.Name == name);
        var host = new ModuleHost();
        var parsed = await SourceProvenance.ParseValidAsync(Unit(witness.Body, deferred: true), host.Options);
        Assert.Empty(parsed.Diagnostics);
        var family = Assert.IsType<Algorithm.Conditional>(parsed.Root.Properties.Single(static property => property.Name == "F").Value);
        var region = Assert.Single(family.Branches, static branch => branch.Body.DeferredRegion is not null).Body.DeferredRegion!;
        var cache = region.Exposure!.Scope.PropertyScope.MemberIndexes;
        Assert.NotNull(cache);
        var before = Tables.Of(cache);

        var result = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root), null, CancellationToken.None);
        Assert.True(region.TryGetMaterialized(out _));
        Assert.Equal(before, Tables.Of(cache));
        Assert.Equal(witness.Expected, Outcome(result));
        Assert.Equal(1, host.Fetches);
    }

    // ── Host trees ──────────────────────────────────────────────────────────

    /// <summary>
    /// A raw tree, shaped by <paramref name="shape"/>, through the loader and the production passes, and evaluated
    /// through the public asynchronous evaluator (the elaboration of <see cref="DeferredSharedOpenTargetBlockTests"/>).
    /// </summary>
    private static async Task<(Algorithm Root, string Outcome)> StageAndRun(string source, Func<Algorithm.User, Algorithm.User> shape, ModuleHost host)
    {
        var diagnostics = new DiagnosticBag();
        var input = FrontEndPipeline.ElaborationInput.Parse(source, diagnostics);
        Assert.Empty(diagnostics);
        var raw = shape(Assert.IsType<Algorithm.User>(input.Take()));
        var loader = new ModuleLoader(diagnostics, host.Download, [Host]);
        input.Put(await loader.ElaborateAsync(raw));
        Assert.Empty(diagnostics);
        Assert.Null(AstStructuralPreflight.Check(input.Current, EvaluationLimits.MaxSupportedAstDepth, AstConsumerProfile.FullyRecursive));
        var modules = loader.ModuleUnits.BeginOperation();
        var rejected = FrontEndPipeline.CompleteBeforeExposure(input, diagnostics, null, modules,
            loader.DeferredRegionCount > 0, null, out var deferredOperation, CancellationToken.None);
        Assert.Null(rejected);
        Assert.Empty(diagnostics);
        var exposed = PropertyExposureResolver.ResolveCompilation(input.Take(), null, null, modules, CancellationToken.None);
        modules.Publish(deferredOperation?.Freeze());
        return (exposed, Outcome(await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(exposed), null, CancellationToken.None)));
    }

    private static Algorithm.Conditional Family(Algorithm owner, string name)
        => Assert.IsType<Algorithm.Conditional>(owner.Properties.Single(property => property.Name == name).Value);

    private static Algorithm.User WithProperty(Algorithm.User owner, string name, Algorithm value)
        => owner with { Properties = [.. owner.Properties.Select(property => property.Name == name ? property.WithValue(value) : property)] };

    private static Algorithm.User WithSecondBranch(Algorithm.User owner, string name, Func<Algorithm.User, Algorithm.User> rewrite)
    {
        var family = Family(owner, name);
        var second = family.Branches[1];
        return WithProperty(owner, name, family with
        {
            Branches = [family.Branches[0], second with { Body = rewrite(Assert.IsType<Algorithm.User>(second.Body)) }],
        });
    }

    private static Expr.AlgorithmExpr OpenBlock(Algorithm owner) => Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(owner.Opens));

    /// <summary>The dot edges named <paramref name="member"/> below <paramref name="block"/>.</summary>
    private static List<Expr.DotCall> DotEdges(Algorithm block, string member)
    {
        var found = new List<Expr.DotCall>();
        var pending = new Stack<object>();
        var seen = new HashSet<object>(ReferenceEqualityComparer.Instance);
        pending.Push(block);
        while (pending.TryPop(out var at))
        {
            if (!seen.Add(at))
                continue;
            if (at is Expr.DotCall { Name: var name } edge && name == member)
                found.Add(edge);
            for (var index = 0; AstStructuralPreflight.TryGetChild(at, index, out var child); index++)
                pending.Push(child!);
        }

        return found;
    }

    private const string NoteBlockAtK = "{ public P = { public W = 4 }\n      public R = P.zz }";
    private const string NoteBlockAtQ = "{ public P = { public W = 4 }\n        public R = P.zz }";

    /// <summary>
    /// The outer unit (<c>F</c>'s second clause) keeps <c>K</c>'s load-free branch, whose open target holds a dot-member
    /// fallback note; its family <c>G</c> has a load-bearing branch, the inner unit, which keeps <c>Q</c>'s load-free
    /// branch opening an equal block and calling <c>R()</c>: the inner unit's arity error carries the note. With
    /// <paramref name="trigger"/> the inner unit also writes a dot-member note of its own, outside that block.
    /// </summary>
    private static string NoteSource(bool trigger, bool loads = true)
    {
        var holder = loads ? Load : "0";
        return "F(0) = 0\n" +
               "F(n) = { H = " + holder + "\n" +
               "  K(0) = 0\n" +
               "  K(j) = { open " + NoteBlockAtK + "\n" +
               "    j }\n" +
               "  G(0) = 0\n" +
               "  G(m) = { H2 = " + holder + "\n" +
               (trigger ? "    Trig = { public W = 1 }.yy\n" : "    Trig = 0\n") +
               "    Q(0) = 0\n" +
               "    Q(k) = { open " + NoteBlockAtQ + "\n" +
               "      k + R() }\n" +
               "    Q(m) }\n" +
               "  K(5) + G(1) }\n" +
               "F(1)\n";
    }

    /// <summary>The raw tree with <c>Q</c>'s open target headed by <c>K</c>'s block object.</summary>
    private static Algorithm.User ShareTheNoteBlock(Algorithm.User raw)
    {
        var unit = Assert.IsType<Algorithm.User>(Family(raw, "F").Branches[1].Body);
        var kept = OpenBlock(Family(unit, "K").Branches[1].Body);
        return WithSecondBranch(raw, "F", outer => WithSecondBranch(outer, "G", inner => WithSecondBranch(inner, "Q", body =>
        {
            Assert.NotSame(kept, Assert.Single(body.Opens));
            return body with { Opens = [kept] };
        })));
    }

    /// <summary>
    /// A HOST-SHARED, ALREADY CLASSIFIED BLOCK KEEPS ITS NOTE. A host tree shares ONE open-target block between the outer
    /// unit's kept branch <c>K</c> and the inner unit's kept branch <c>Q</c>. The outer unit classifies it, its finalizer
    /// confirms the dot-member note of <c>P.zz</c> (a kept position, the <c>w5c</c> row), and the inner unit receives
    /// that classified view with the outer unit's completed entry and keeps it as it is (exposure's inherited-block
    /// arm). Its own dot-member note (<paramref name="trigger"/>) makes its finalizer run, which walks the inherited block
    /// as well: it must judge the receiver against the facts that answer for the block, which name that very view, and
    /// keep the note. The inner unit's arity error therefore carries the note, positioned at <c>K</c>'s block, which the
    /// tree shares; without the sharing, and in the source, it is positioned at <c>Q</c>'s own block.
    /// </summary>
    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public async Task HostSharedClassifiedBlock_KeepsItsNote_ThroughTheInnerUnitsFinalizer(bool trigger)
    {
        var source = NoteSource(trigger);
        var arity = "ArityMismatch@[13:11, 13:14): while evaluating call to F: while evaluating call to G: while evaluating call to Q: " + ArityR;
        var atQ = arity + "\nAn implicit parameter 'zz' was inferred at [12:22].\n" + FallbackNote;
        var atK = arity + "\nAn implicit parameter 'zz' was inferred at [5:20].\n" + FallbackNote;

        var normal = await KatLangEngine.RunAsync(source, new ModuleHost().Options);
        Assert.Equal(atQ, Outcome(normal));
        Assert.Equal(atQ, Outcome(await KatLangEngine.RunAsync(NoteSource(trigger, loads: false), new ModuleHost().Options)));
        var (_, unshared) = await StageAndRun(source, static raw => raw, new ModuleHost());
        Assert.Equal(atQ, unshared);

        var host = new ModuleHost();
        var (root, shared) = await StageAndRun(source, ShareTheNoteBlock, host);
        Assert.Equal(atK, shared);
        Assert.Equal(1, host.Fetches);

        // The inner unit holds the outer unit's classified view and completed entry, and the note on its edge survived.
        Assert.True(Family(root, "F").Branches[1].Body.DeferredRegion!.TryGetMaterialized(out var outer));
        var kept = OpenBlock(Family(outer, "K").Branches[1].Body).Algorithm;
        Assert.True(Family(outer, "G").Branches[1].Body.DeferredRegion!.TryGetMaterialized(out var inner));
        var inside = OpenBlock(Family(inner, "Q").Branches[1].Body).Algorithm;
        Assert.Same(kept, inside);
        var facts = inner.CompletedStructure!.Facts;
        var key = facts.Child(facts.PreludeKey, inside);
        Assert.NotNull(key);
        var inherited = outer.CompletedStructure!.Facts.Facts(key);
        Assert.NotNull(inherited);
        Assert.Same(kept, inherited.Body);
        Assert.Same(inherited, facts.Facts(key));
        var edge = Assert.Single(DotEdges(inside, "zz"));
        Assert.NotNull(edge.InferredFallbackProvenance?.DotMemberOrigin);
        if (trigger)
            Assert.NotNull(Assert.Single(DotEdges(inner, "yy")).InferredFallbackProvenance?.DotMemberOrigin);
    }

    /// <summary>
    /// A FAMILY'S OWN OPEN LIST (host trees only: a parsed family owns none). A host moves the open target of the nested
    /// family <c>G</c>'s load-free branch to the family, so its block is the family's open level for both branches. The
    /// unit enters it at the prelude level over its own facts like any other open list, so the hoisted deconstruction row
    /// keeps its capture and the program gives the value and the classification of the same tree with nothing deferred.
    /// </summary>
    [Fact]
    public async Task FamilyOwnedOpenTarget_InADeferredUnit_RunsAndClassifiesLikeTheTreeWithNothingDeferred()
    {
        const string body = "  G(0) = 0\n  G(m) = { open { public K(a) = { Inner = { public V = a }\n      p, q = Inner.V, 1\n      p + q } }\n    K(3) * 10 + K(4) + m }\n  G(5)";
        static Algorithm.User FamilyOwnsTheOpen(Algorithm.User raw) => WithSecondBranch(raw, "F", unit =>
        {
            var family = Family(unit, "G");
            var second = Assert.IsType<Algorithm.User>(family.Branches[1].Body);
            return WithProperty(unit, "G", family with
            {
                Opens = [OpenBlock(second)],
                Branches = [family.Branches[0], family.Branches[1] with { Body = second with { Opens = [] } }],
            });
        });

        var (plainRoot, plain) = await StageAndRun(Unit(body, deferred: false), FamilyOwnsTheOpen, new ModuleHost());
        Assert.Equal("value 50", plain);
        var host = new ModuleHost();
        var (root, deferred) = await StageAndRun(Unit(body, deferred: true), FamilyOwnsTheOpen, host);
        Assert.Equal(plain, deferred);
        Assert.Equal(1, host.Fetches);

        var unit = UnitClassification(root);
        var twin = UnitClassification(plainRoot);
        Assert.Equal(twin, unit);
        Assert.StartsWith(LocalOnlyRequiringA, twin["F#1/G/open{}/K/$deconstruct$0"], StringComparison.Ordinal);
        Assert.StartsWith(LocalOnlyRequiringA, twin["F#1/G/open{}/K/p"], StringComparison.Ordinal);
    }
}
