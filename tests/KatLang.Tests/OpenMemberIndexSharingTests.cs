using System.Reflection;
using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// An <c>open</c> provider's public-member index is a pure function of its TARGET's ordered
/// property list (<see cref="OpenTargetMemberIndex"/>), so within one front-end or analysis
/// operation every provider of the same target object shares one index through the operation's
/// <see cref="OpenMemberIndexCache"/>. K levels opening one W-member target formerly built K
/// identical indexes (O(K × W)); they now build one (O(K + W)). Only the TARGET index is shared:
/// which providers a level has, their dedup, ambiguity, and precedence stay per level.
///
/// <para>The pins: the index semantics (first PUBLIC entry by ordinal name wins; private
/// same-name entries are skipped), the structural build counts per operation
/// (<see cref="FrontEndTraversalObservations.LookupOpenMemberIndexBuilds"/>), exact target identity
/// (same spelling or value-equal targets never collapse), per-level resolution under different
/// surrounding providers, cache lifetime (no process-shared object carries one; sequential
/// operations never share one; no finished parse or model retains one, except the chains a
/// deferred module region keeps for its own continuation), unchanged module/deferred behavior,
/// and a design-independent allocation guard over the public parse and the semantic-model
/// build.</para>
/// </summary>
public class OpenMemberIndexSharingTests
{
    private static Algorithm.User ValueAlgorithm(int sentinel)
        => new(null, [], [], [], [new Expr.Num(sentinel)]);

    private static Algorithm.User Owner(params Property[] properties)
        => new(null, [], [], [.. properties], OutputBundle.Empty);

    private static ElaboratedPropertyScope Opening(Algorithm target, ElaboratedPropertyScope? parent, OpenMemberIndexCache? cache)
        => new(parent, [new Expr.AlgorithmExpr(target)], [], observations: null, memberIndexes: cache);

    /// <summary>K sibling blocks each opening one W-member library and reading one member.</summary>
    private static string SiblingOpens(int blocks, int width)
        => "Lib = {\n" + string.Concat(Enumerable.Range(0, width).Select(i => $"    public m{i} = {i}\n")) + "    1\n}\n"
            + string.Concat(Enumerable.Range(0, blocks).Select(i => $"B{i} = {{\n    open Lib\n    m0\n}}\n"))
            + "1";

    private static FrontEndTraversalObservations Detect(string source)
    {
        var syntax = SourceProvenance.ParseSyntaxValidRoot(source);
        var observations = new FrontEndTraversalObservations();
        var (_, diagnostics) = ParameterDetector.DetectPrevalidated(syntax, null, observations);
        Assert.DoesNotContain(diagnostics, diagnostic => diagnostic.Severity == DiagnosticSeverity.Error);
        return observations;
    }

    private static FrontEndTraversalObservations BuildModel(ParseResult parsed)
    {
        var observations = new FrontEndTraversalObservations();
        _ = SemanticModelBuilder.Build(parsed, observations);
        return observations;
    }

    // ── The index: first PUBLIC entry by ordinal name ──────────────────────────────────

    /// <summary>
    /// <c>private x, public x, public x</c> and <c>public x, private x, public x</c>: the FIRST
    /// PUBLIC entry wins in both, a private entry is never an answer, and the shared index, a
    /// provider without a cache, and the linear public lookup all select the same declaration.
    /// </summary>
    [Fact]
    public void FirstPublicEntryWins_AndPrivateEntriesAreSkipped()
    {
        var privateFirst = new Property("x", ValueAlgorithm(1));
        var publicSecond = new Property("x", ValueAlgorithm(2), IsPublic: true);
        var publicThird = new Property("x", ValueAlgorithm(3), IsPublic: true);
        var privateThenPublic = Owner(privateFirst, publicSecond, publicThird);

        var publicFirst = new Property("x", ValueAlgorithm(4), IsPublic: true);
        var privateMiddle = new Property("x", ValueAlgorithm(5));
        var publicLast = new Property("x", ValueAlgorithm(6), IsPublic: true);
        var publicThenPrivate = Owner(publicFirst, privateMiddle, publicLast);

        var onlyPrivate = Owner(new Property("x", ValueAlgorithm(7)));

        foreach (var (target, expected) in new[] { (privateThenPublic, publicSecond), (publicThenPrivate, publicFirst), (onlyPrivate, (Property?)null) })
        {
            var cache = new OpenMemberIndexCache();
            var shared = new ResolvedOpenProvider(target, observations: null, cache).TryLookupPublicMember("x");
            var alone = new ResolvedOpenProvider(target, observations: null).TryLookupPublicMember("x");
            var linear = ElaboratedScopeLookup.TryLookupPublicProperty(target, "x");
            Assert.Same(expected, shared?.Property);
            Assert.Same(expected, alone?.Property);
            Assert.Same(expected, linear?.Property);
            if (shared is { } hit)
                Assert.Same(target, hit.Owner);

            // Through a scope level: open resolution yields exactly that member.
            var matches = ElaboratedScopeLookup.LookupOpenPropertyMatches(Opening(target, null, cache), "x");
            Assert.Equal(expected is null ? 0 : 1, matches.Count);
            if (expected is not null)
                Assert.Same(expected, matches[0].Property);
            Assert.Null(new ResolvedOpenProvider(target, null, cache).TryLookupPublicMember("absent"));
        }
    }

    /// <summary>
    /// A null-named public entry (host-built) is found by the null query exactly as before, and
    /// a name the target lacks returns nothing — through the shared and the private index alike.
    /// </summary>
    [Fact]
    public void NullNamedAndAbsentEntries_BehaveAsTheLinearLookup()
    {
        var privateNull = new Property(null!, ValueAlgorithm(1));
        var publicNull = new Property(null!, ValueAlgorithm(2), IsPublic: true);
        var target = Owner(privateNull, publicNull);
        var cache = new OpenMemberIndexCache();
        Assert.Same(publicNull, new ResolvedOpenProvider(target, null, cache).TryLookupPublicMember(null!)?.Property);
        Assert.Same(publicNull, new ResolvedOpenProvider(target, null).TryLookupPublicMember(null!)?.Property);
        Assert.Null(new ResolvedOpenProvider(target, null, cache).TryLookupPublicMember("y"));
    }

    // ── Exact target identity ─────────────────────────────────────────────────────────

    /// <summary>
    /// Two VALUE-EQUAL but distinct target objects (the same property list) never share an index:
    /// the cache keys by reference, and each index answers with its own target as the owner.
    /// </summary>
    [Fact]
    public void DistinctTargetObjects_NeverShareAnIndex()
    {
        var first = Owner(new Property("m", ValueAlgorithm(1), IsPublic: true));
        var second = first with { };
        Assert.Equal(first, second);
        Assert.NotSame(first, second);

        var observations = new FrontEndTraversalObservations();
        var cache = new OpenMemberIndexCache(observations);
        Assert.Same(cache.IndexOf(first), cache.IndexOf(first));
        Assert.NotSame(cache.IndexOf(first), cache.IndexOf(second));
        Assert.Equal(2, cache.Count);
        Assert.Equal(2, observations.LookupOpenMemberIndexBuilds);
        Assert.Same(first, cache.IndexOf(first).Lookup("m")!.Value.Owner);
        Assert.Same(second, cache.IndexOf(second).Lookup("m")!.Value.Owner);
    }

    /// <summary>
    /// Same member spelling on two distinct libraries: each block's reference resolves to ITS
    /// library's declaration (never collapsed by spelling), two indexes are built, and the
    /// program's value is unchanged.
    /// </summary>
    [Fact]
    public void SameSpellingOnDistinctTargets_ResolvesPerTarget()
    {
        const string source = "L1 = {\n    public m = 1\n    1\n}\nL2 = {\n    public m = 2\n    1\n}\nA = {\n    open L1\n    m\n}\nB = {\n    open L2\n    m\n}\nA * 10 + B";
        Assert.Equal(2, Detect(source).LookupOpenMemberIndexBuilds);
        var parsed = SourceProvenance.ParseValid(source).Parsed;
        Assert.Equal(2, BuildModel(parsed).LookupOpenMemberIndexBuilds);

        var model = SemanticModelBuilder.Build(parsed);
        var references = model.FindResolutions("m").Where(resolution => resolution.Occurrence.Kind == OccurrenceKind.ResolveReference).ToList();
        Assert.Equal(2, references.Count);
        Assert.Equal(2, references[0].ResolvedDeclaration!.Span.Start.Line);
        Assert.Equal(6, references[1].ResolvedDeclaration!.Span.Start.Line);
        Assert.Equal("12", KatLangEngine.Run(source).ToDisplayString());
    }

    // ── Structural build counts per operation ─────────────────────────────────────────

    /// <summary>
    /// K sibling levels opening ONE target build ONE index per operation — in parameter detection
    /// and in the semantic-model build alike — whatever K and W are; K levels opening TWO targets
    /// alternately build two.
    /// </summary>
    [Theory]
    [InlineData(8, 8)]
    [InlineData(64, 32)]
    [InlineData(256, 256)]
    public void SiblingOpensOfOneTarget_BuildOneIndexPerOperation(int blocks, int width)
    {
        var source = SiblingOpens(blocks, width);
        Assert.Equal(1, Detect(source).LookupOpenMemberIndexBuilds);
        Assert.Equal(1, BuildModel(SourceProvenance.ParseValid(source).Parsed).LookupOpenMemberIndexBuilds);

        var twoTargets = "L1 = {\n" + string.Concat(Enumerable.Range(0, width).Select(i => $"    public m{i} = {i}\n")) + "    1\n}\n"
            + "L2 = {\n" + string.Concat(Enumerable.Range(0, width).Select(i => $"    public m{i} = {i}\n")) + "    1\n}\n"
            + string.Concat(Enumerable.Range(0, blocks).Select(i => $"B{i} = {{\n    open L{1 + (i % 2)}\n    m0\n}}\n")) + "1";
        Assert.Equal(2, Detect(twoTargets).LookupOpenMemberIndexBuilds);
        Assert.Equal(2, BuildModel(SourceProvenance.ParseValid(twoTargets).Parsed).LookupOpenMemberIndexBuilds);
    }

    /// <summary>Nested levels each re-opening the same target share its one index too.</summary>
    [Fact]
    public void NestedReopensOfOneTarget_BuildOneIndex()
    {
        var text = new System.Text.StringBuilder("Lib = {\n    public m0 = 1\n    public m1 = 2\n    1\n}\n");
        for (var level = 0; level < 24; level++)
            text.Append($"L{level} = {{\n    open Lib\n");
        for (var level = 23; level >= 0; level--)
            text.Append("    m0\n}\n");
        var source = text.Append('1').ToString();
        Assert.Equal(1, Detect(source).LookupOpenMemberIndexBuilds);
        Assert.Equal(1, BuildModel(SourceProvenance.ParseValid(source).Parsed).LookupOpenMemberIndexBuilds);
    }

    /// <summary>
    /// One target opened under DIFFERENT surrounding providers shares its index while each level
    /// keeps its own resolution: alone, <c>x</c> resolves to <c>Lib.x</c>; beside <c>Other</c>, which
    /// also provides <c>x</c>, the name is ambiguous there and is neither offered nor resolved —
    /// yet exactly two indexes (Lib, Other) are built.
    /// </summary>
    [Fact]
    public void SharedIndex_DoesNotShareResolutionOrAmbiguity()
    {
        const string source = "Lib = {\n    public x = 1\n    public y = 2\n    1\n}\nOther = {\n    public x = 3\n    1\n}\nA = {\n    open Lib\n    x + y\n}\nB = {\n    open Lib, Other\n    y\n}\nA + B";
        Assert.Equal(2, Detect(source).LookupOpenMemberIndexBuilds);
        var parsed = SourceProvenance.ParseValid(source).Parsed;
        Assert.Equal(2, BuildModel(parsed).LookupOpenMemberIndexBuilds);

        var model = SemanticModelBuilder.Build(parsed);
        var a = model.FindScopeAt(new SourcePosition(12, 5));
        var b = model.FindScopeAt(new SourcePosition(16, 5));
        Assert.NotSame(a, b);
        Assert.Contains(a.Symbols, symbol => symbol.Name == "x" && symbol.Declaration!.Span.Start.Line == 2);
        Assert.DoesNotContain(b.Symbols, symbol => symbol.Name == "x");
        Assert.Contains(b.Symbols, symbol => symbol.Name == "y" && symbol.Declaration!.Span.Start.Line == 3);
        Assert.Equal("5", KatLangEngine.Run(source).ToDisplayString());

        // The same split directly over scope levels sharing one cache.
        var lib = Owner(new Property("x", ValueAlgorithm(1), IsPublic: true));
        var other = Owner(new Property("x", ValueAlgorithm(3), IsPublic: true));
        var cache = new OpenMemberIndexCache();
        var alone = Opening(lib, null, cache);
        var beside = new ElaboratedPropertyScope(null, [new Expr.AlgorithmExpr(lib), new Expr.AlgorithmExpr(other)], [], memberIndexes: cache);
        Assert.Single(ElaboratedScopeLookup.LookupOpenPropertyMatches(alone, "x"));
        Assert.Equal(2, ElaboratedScopeLookup.LookupOpenPropertyMatches(beside, "x").Count);
        Assert.Equal(2, cache.Count);
    }

    // ── Cache ownership and lifetime ──────────────────────────────────────────────────

    /// <summary>
    /// Sequential operations never share a cache: two detections over one syntax tree and two
    /// model builds over one parse each build their own index, and every level an operation
    /// derives inherits that operation's cache.
    /// </summary>
    [Fact]
    public void SequentialOperations_DoNotShareCaches()
    {
        var source = SiblingOpens(16, 16);
        Assert.Equal(1, Detect(source).LookupOpenMemberIndexBuilds);
        Assert.Equal(1, Detect(source).LookupOpenMemberIndexBuilds);
        var parsed = SourceProvenance.ParseValid(source).Parsed;
        Assert.Equal(1, BuildModel(parsed).LookupOpenMemberIndexBuilds);
        Assert.Equal(1, BuildModel(parsed).LookupOpenMemberIndexBuilds);

        var cache = new OpenMemberIndexCache();
        var root = ElaboratedScopeLookup.CreateScope(Owner(), memberIndexes: cache);
        var child = ElaboratedScopeLookup.CreateScope(Owner(), root);
        var grandchild = ElaboratedScopeLookup.CreateScope(Owner(), child);
        Assert.Same(cache, child.MemberIndexes);
        Assert.Same(cache, grandchild.MemberIndexes);
        var other = new OpenMemberIndexCache();
        Assert.Same(other, ElaboratedScopeLookup.CreateScope(Owner(), grandchild, memberIndexes: other).MemberIndexes);
        Assert.Null(ElaboratedScopeLookup.CreateScope(Owner()).MemberIndexes);
    }

    /// <summary>
    /// Every open-target member-index cache, and the number of member indexes, reachable from
    /// <paramref name="root"/> through instance fields — boxed struct fields and array elements
    /// included, so dictionary slots and immutable arrays are searched — excluding reflection
    /// metadata, delegates, and threading infrastructure (none of which a front-end result owns).
    /// </summary>
    private static (HashSet<OpenMemberIndexCache> Caches, int Indexes) ReachableMemberIndexes(object root)
    {
        var caches = new HashSet<OpenMemberIndexCache>(ReferenceEqualityComparer.Instance);
        var indexes = 0;
        var seen = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<object>();
        pending.Push(root);
        while (pending.TryPop(out var item))
        {
            var type = item.GetType();
            if (type.IsPrimitive || type.IsEnum
                || item is string or MemberInfo or Delegate or Assembly or System.Reflection.Module
                    or Task or ExecutionContext or SynchronizationContext or Thread or WaitHandle
                || (!type.IsValueType && !seen.Add(item)))
            {
                continue;
            }

            if (item is OpenMemberIndexCache cache)
                caches.Add(cache);
            else if (item is OpenTargetMemberIndex)
                indexes++;

            if (item is Array array)
            {
                foreach (var element in array)
                    if (element is not null) pending.Push(element);
                continue;
            }

            for (var current = type; current is not null; current = current.BaseType)
            {
                foreach (var field in current.GetFields(BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.DeclaredOnly))
                {
                    if (!field.FieldType.IsPointer && !field.FieldType.IsFunctionPointer && field.GetValue(item) is { } value)
                        pending.Push(value);
                }
            }
        }

        return (caches, indexes);
    }

    /// <summary>
    /// The semantic model's process-shared prelude level never carries a per-operation cache,
    /// before or after builds (its providers keep private, prewarmed indexes), and a finished
    /// operation retains none: neither a parse of a program without deferred regions nor a model
    /// built from it reaches a member-index cache or a member index anywhere in its object graph,
    /// so every cache dies with its operation.
    /// </summary>
    [Fact]
    public void ProcessSharedPreludeLevel_RetainsNoOperationCache()
    {
        static ElaboratedPropertyScope PreludeLevel()
        {
            var builder = typeof(SemanticModelBuilder).GetNestedType("Builder", BindingFlags.NonPublic)!;
            var frame = builder.GetField("PreludeScope", BindingFlags.NonPublic | BindingFlags.Static)!.GetValue(null)!;
            return (ElaboratedPropertyScope)frame.GetType().GetProperty("PropertyScope")!.GetValue(frame)!;
        }

        Assert.Null(PreludeLevel().MemberIndexes);
        _ = SemanticModelBuilder.Build(SourceProvenance.ParseValid(SiblingOpens(8, 8)).Parsed);
        Assert.Null(PreludeLevel().MemberIndexes);

        var parsed = SourceProvenance.ParseValid(SiblingOpens(8, 8)).Parsed;
        var model = SemanticModelBuilder.Build(parsed);
        Assert.Null(PreludeLevel().MemberIndexes);
        var parseRetained = ReachableMemberIndexes(parsed);
        var modelRetained = ReachableMemberIndexes(model);
        Assert.Empty(parseRetained.Caches);
        Assert.Equal(0, parseRetained.Indexes);
        Assert.Empty(modelRetained.Caches);
        Assert.Equal(0, modelRetained.Indexes);
    }

    /// <summary>
    /// What a finished parse keeps reaches no member-index cache or member index, and neither does
    /// a model built from it: implicit parameters with their dot-member provenance notes and
    /// captured near-miss suggestions (rendered here first, by evaluating the same tree), local-only
    /// required ancestors, clause families, and — for invalid source — front-end diagnostics over a
    /// recovery tree. Only a deferred module region retains its chains.
    /// </summary>
    [Fact]
    public void FinishedOperations_RetainNoMemberIndexes()
    {
        const string valid = "Lib = {\n    public total = 1\n    public Scale(v) = v * 2\n}\nOuter(a) = {\n    open Lib\n    Inner = a + total\n    Inner\n}\nK = Lib.Scal\nB = {\n    open Lib\n    totl\n}\nF(0) = 1\nF(n) = n * F(n - 1)\nOuter(3) + F(3) + B";
        var parsed = SourceProvenance.ParseValid(valid).Parsed;
        var model = SemanticModelBuilder.Build(parsed);

        // The retained front-end state this case is about is really there, and its suggestion renders.
        var k = (Algorithm.User)parsed.Root.Properties.Single(static property => property.Name == "K").Value;
        var promoted = Assert.IsType<CaptureParameterPattern>(Assert.Single(k.ParameterPatterns));
        Assert.Equal("Lib", promoted.InferredProvenance?.DotMemberOrigin?.ReceiverDescription);
        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            model.PropertyInfos.Single(static property => property.Name == "Inner").Exposure);
        var failure = Evaluator.Run(new Expr.AlgorithmExpr(parsed.Root));
        Assert.True(failure.IsError, "expected the unsupplied implicit parameter to fail");
        Assert.Contains("Did you mean 'total'?", KatLangError.FromEvalError(failure.Error).Message, StringComparison.Ordinal);

        const string invalid = "Lib = {\n    public total = 1\n}\nB(x) = {\n    open Lib\n    totl + x\n}\nB(1)";
        var recovered = SourceProvenance.ParseAllowingDiagnostics(invalid).Parsed;
        Assert.True(recovered.HasErrors);
        Assert.All(recovered.Diagnostics, static diagnostic => Assert.NotEmpty(diagnostic.Message));

        foreach (var retainer in new object[] { parsed, model, recovered, SemanticModelBuilder.Build(recovered) })
        {
            var retained = ReachableMemberIndexes(retainer);
            Assert.Empty(retained.Caches);
            Assert.Equal(0, retained.Indexes);
        }
    }

    // ── Modules, deferred regions, shadowing: unchanged ───────────────────────────────

    /// <summary>
    /// A deferred region's demand-time continuation re-walks the eager chain (and its cache) under
    /// the loader's materialization gate: values, classifications, and opened members are exactly
    /// as before, with a local shadow over an opened member and the same module opened twice.
    /// </summary>
    [Fact]
    public async Task ModulesAndDeferredRegions_BehaveAsBefore()
    {
        var modules = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["https://katlang.org/idx/lib.kat"] = "public Total = 5\npublic Rate = 2\nFee = 9",
            ["https://katlang.org/idx/deferred.kat"] = "public Later = 1",
        };
        const string source = "open 'https://katlang.org/idx/lib.kat'\nF(0) = {\n    open 'https://katlang.org/idx/deferred.kat'\n    Total + Later\n}\nF(n) = Total + n\nA = {\n    open 'https://katlang.org/idx/lib.kat'\n    Rate = 7\n    Rate + Total\n}\nF(0) * 100 + F(1) * 10 + A";
        var options = new RunOptions { DownloadCode = (url, _) => ValueTask.FromResult(modules[url]), AllowedHosts = ["katlang.org"] };

        var result = await KatLangEngine.RunAsync(source, options);
        Assert.Equal("672", result.ToDisplayString());

        var parsed = (await SourceProvenance.ParseValidAsync(source, options)).Parsed;
        var model = SemanticModelBuilder.Build(parsed);
        Assert.Equal(IdentifierClassification.DeferredModuleReference, model.FindResolutionAt(new SourcePosition(4, 5))!.Classification);
        Assert.Equal(IdentifierClassification.PropertyReference, model.FindResolutionAt(new SourcePosition(6, 10))!.Classification);
        var shadow = model.FindResolutionAt(new SourcePosition(10, 5))!;
        Assert.Equal(9, shadow.ResolvedDeclaration!.Span.Start.Line);
        Assert.DoesNotContain(model.GetVisibleSymbolsAt(new SourcePosition(10, 5)), symbol => symbol.Name == "Fee");

        // The parse retains its chains' caches for the deferred region's demand-time continuation
        // (part of the same operation, serialized by the loader's gate); the model build adds none.
        var parseCaches = ReachableMemberIndexes(parsed).Caches;
        Assert.NotEmpty(parseCaches);
        Assert.Subset(parseCaches, ReachableMemberIndexes(model).Caches);
    }

    // ── Resource guard ────────────────────────────────────────────────────────────────

    /// <summary>
    /// A design-independent guard over the public parse and the semantic-model build: doubling
    /// K = W for K sibling blocks opening one W-member library roughly doubles the allocation
    /// (the per-level indexes quadrupled it — 2.8x and 3.6x per doubling at 256 -> 512).
    /// </summary>
    [Theory]
    [InlineData(256)]
    [InlineData(512)]
    public void SiblingOpens_AllocationGrowsLinearly(int size)
    {
        static (long Parse, long Model) Allocation(string source)
        {
            var parsed = Parser.Parse(source);
            Assert.False(parsed.HasErrors);
            _ = SemanticModelBuilder.Build(parsed);
            var before = GC.GetAllocatedBytesForCurrentThread();
            _ = Parser.Parse(source);
            var parse = GC.GetAllocatedBytesForCurrentThread() - before;
            before = GC.GetAllocatedBytesForCurrentThread();
            _ = SemanticModelBuilder.Build(parsed);
            return (parse, GC.GetAllocatedBytesForCurrentThread() - before);
        }

        var small = Allocation(SiblingOpens(size, size));
        var large = Allocation(SiblingOpens(2 * size, 2 * size));
        var parseRatio = (double)large.Parse / small.Parse;
        var modelRatio = (double)large.Model / small.Model;
        Assert.True(parseRatio < 2.5, $"Doubling K = W grew the parse allocation {parseRatio:F2}x ({small.Parse} -> {large.Parse} bytes).");
        Assert.True(modelRatio < 2.5, $"Doubling K = W grew the model allocation {modelRatio:F2}x ({small.Model} -> {large.Model} bytes).");
    }
}
