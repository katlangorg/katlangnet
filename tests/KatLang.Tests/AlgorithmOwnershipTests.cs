using System.Reflection;
using KatLang.Tests.LanguageSpec;

namespace KatLang.Tests;

/// <summary>
/// The variant-owned <see cref="Algorithm"/> model from the inside of the assembly: the ONE
/// parameter channel (<see cref="Algorithm.User.ParameterPatterns"/>) with its live projections,
/// the one explicit-list fact (<see cref="Algorithm.User.HasExplicitParameterList"/>) that
/// replaced the parallel <c>ExplicitParameters</c> / <c>ExplicitParameterPatterns</c> lists,
/// the capture leaf that HOLDS its declaration, the internal Lean-total accessors over the
/// closed hierarchy, and the root invariant every front-end pass preserves. The public half
/// (what a consumer can and cannot compile) is <c>AlgorithmPublicSurfaceTests</c> in the
/// non-friend public-API project.
/// </summary>
public class AlgorithmOwnershipTests
{
    // ── HasExplicitParameterList: exactly the syntactic distinction the front end needs ──

    [Fact]
    public void WrittenParameterList_IsExplicit_InferredSignatureIsNot()
    {
        var root = SourceProvenance.ParseValid("Inc(v) = v + 1\nTwice = a * 2\nInc(Twice(3))").Root;
        var inc = UserProperty(root, "Inc");
        var twice = UserProperty(root, "Twice");

        Assert.True(inc.HasExplicitParameterList);
        Assert.Equal(["v"], inc.Params);
        Assert.All(inc.Parameters, parameter => Assert.NotNull(parameter.Span));

        Assert.False(twice.HasExplicitParameterList);
        Assert.Equal(["a"], twice.Params);
        Assert.All(twice.Parameters, parameter => Assert.Null(parameter.Span));

        // The root is never written with a parameter list.
        Assert.False(root.HasExplicitParameterList);
    }

    [Fact]
    public void LiftedParameters_JoinAnInferredSignature_AndNeverAWrittenOne()
    {
        // `Use = Need` forwards Need's parameter: Use acquires `v` by lifting and stays an
        // inferred signature; the lifted capture is Need's own declaration record (it carries
        // Need's span), which is why explicitness is a FACT of the owner, not of its captures.
        var root = SourceProvenance.ParseValid("Need(v) = v\nUse = Need\nUse(7)").Root;
        var need = UserProperty(root, "Need");
        var use = UserProperty(root, "Use");

        Assert.True(need.HasExplicitParameterList);
        Assert.False(use.HasExplicitParameterList);
        Assert.Equal(["v"], use.Params);
        Assert.NotNull(Assert.Single(use.Parameters).Span);

        // A written list is CLOSED: an unresolved name inside its body is a front-end error,
        // never a lifted parameter, so the list never grows past what was written.
        var diagnostics = SourceProvenance.ExpectFrontEndError("Closed(x) = v + x\nClosed(1)");
        Assert.Contains(diagnostics, d => d.Code == DiagnosticCode.UndeclaredIdentifier);
        var closed = UserProperty(SourceProvenance.ParseAllowingDiagnostics("Closed(x) = v + x\nClosed(1)").Root, "Closed");
        Assert.True(closed.HasExplicitParameterList);
        Assert.Equal(["x"], closed.Params);
    }

    [Fact]
    public void DeconstructionHelpers_AndSequenceValueHeads_AreWrittenLists_BranchBodiesAreNot()
    {
        var root = SourceProvenance.ParseValid("x, *rest = (1, 2, 3)\nPairSum((p, q)) = p + q\nx + PairSum((1, 2))").Root;

        // The target helper of an assignment deconstruction carries the written N-capture
        // sequence-value pattern as its explicit list; the hoisted source does not.
        var x = UserProperty(root, "x");
        var helperCall = Assert.IsType<Expr.Call>(Assert.Single(x.Output));
        var helper = Assert.IsType<Algorithm.User>(Assert.IsType<Expr.AlgorithmExpr>(helperCall.Function).Algorithm);
        Assert.True(helper.HasExplicitParameterList);
        var group = Assert.IsType<SequenceValueParameterPattern>(Assert.Single(helper.ParameterPatterns));
        Assert.Equal(["x", "rest"], helper.Params);
        Assert.Equal(ParameterKind.Collecting, helper.Parameters[1].Kind);
        Assert.Same(group, Assert.Single(Assert.IsType<Algorithm.User>(
            Assert.IsType<Expr.AlgorithmExpr>(Assert.IsType<Expr.Call>(Assert.Single(UserProperty(root, "rest").Output)).Function).Algorithm).ParameterPatterns));
        var source = Assert.IsType<Algorithm.User>(Assert.Single(root.Properties, p => p.Name.StartsWith("$deconstruct$", StringComparison.Ordinal)).Value);
        Assert.False(source.HasExplicitParameterList);
        Assert.True(source.IsAssignmentDeconstructionSource);

        var pairSum = UserProperty(root, "PairSum");
        Assert.True(pairSum.HasExplicitParameterList);
        Assert.IsType<SequenceValueParameterPattern>(Assert.Single(pairSum.ParameterPatterns));
        Assert.Equal(["p", "q"], pairSum.Params);

        // Clause-family branch bodies bind through their patterns and declare no list.
        var familyRoot = SourceProvenance.ParseValid("F(0) = 1\nF(n) = n * 2\nF(3)").Root;
        var family = Assert.IsType<Algorithm.Conditional>(Assert.Single(familyRoot.Properties, p => p.Name == "F").Value);
        Assert.Equal(2, family.Branches.Count);
        foreach (var branch in family.Branches)
        {
            var body = Assert.IsType<Algorithm.User>(branch.Body);
            Assert.False(body.HasExplicitParameterList);
            Assert.Empty(body.ParameterPatterns);
            Assert.Empty(body.Params);
        }
    }

    [Fact]
    public void RecoveryBinder_IsTheOnlySpanlessCaptureOfAWrittenList()
    {
        // `F(*) = …` recovers the malformed item to the spanless `_error_` binder; the list is
        // still the WRITTEN one, and the diagnostics that quote parameters skip the binder.
        var parsed = SourceProvenance.ParseAllowingDiagnostics("F(*) = 5\nopen F\n1");
        Assert.Contains(parsed.Diagnostics, d => d.Code == DiagnosticCode.InvalidCollectMarker);
        var f = UserProperty(parsed.Root, "F");
        Assert.True(f.HasExplicitParameterList);
        var binder = Assert.Single(f.Parameters);
        Assert.Null(binder.Span);
        Assert.Equal("_error_", binder.Name);
        Assert.DoesNotContain("_error_", Evaluator.FormatOpenTargetRequiresArguments("F", f, sourceBacked: true), StringComparison.Ordinal);
    }

    [Fact]
    public void Corpus_EveryUserAlgorithm_DerivesParametersFromItsPatterns_AndAWrittenListIsSourceBacked()
    {
        // The whole executable specification plus every tutorial program: the one-channel
        // law (Parameters is the flatten of the stored patterns, Params its names, the count
        // free) and the explicit-list law (a written list's captures are source-backed — the
        // parser's recovery binder excepted — while a builtin or family declares no list).
        var sources = LanguageSpecCorpus.AllCases().Select(c => c.Source)
            .Concat(TutorialCorpus.Examples.Where(e => e.SkipReason is null).Select(e => e.Source))
            .Distinct(StringComparer.Ordinal)
            .ToList();
        Assert.True(sources.Count > 200, $"corpus unexpectedly small: {sources.Count}");

        var users = 0;
        var written = 0;
        foreach (var source in sources)
        {
            var parsed = Parser.Parse(source);
            if (parsed.HasErrors)
                continue;

            var collector = new AlgorithmCollector();
            collector.VisitAlgorithm(parsed.Root);
            foreach (var algorithm in collector.Algorithms)
            {
                if (algorithm is not Algorithm.User user)
                {
                    Assert.Empty(algorithm.ParameterPatterns);
                    Assert.False(algorithm.HasExplicitParameterList);
                    continue;
                }

                users++;
                Assert.Equal(ParameterPattern.FlattenCaptures(user.ParameterPatterns), user.Parameters);
                Assert.Equal(user.Parameters.Select(static p => p.Name), user.Params);
                Assert.Equal(user.Parameters.Count, user.ParameterCount);
                if (user.HasExplicitParameterList)
                {
                    written++;
                    // A deconstruction target helper is synthetic: its written pattern is the
                    // assignment's target list, whose captures carry no name-token span.
                    if (user.AssignmentDeconstructionTarget is null)
                        Assert.All(user.Parameters, p => Assert.True(p.Span is not null || p.Name == "_error_", $"unlocated written parameter {p.Name} in:\n{source}"));
                }
            }
        }

        Assert.True(users > 500, $"too few user algorithms walked: {users}");
        Assert.True(written > 100, $"too few written lists walked: {written}");
    }

    // ── The capture leaf holds its declaration ─────────────────────────────

    [Fact]
    public void CaptureLeaf_HoldsItsDeclaration_AndProjectionsReturnIt()
    {
        var declaration = new ParameterDeclaration("items", new SourceSpan(1, 3, 1, 8), ParameterKind.Collecting)
        {
            CollectMarkerSpan = new SourceSpan(1, 2, 1, 3),
        };
        var leaf = new CaptureParameterPattern(declaration);
        Assert.Same(declaration, leaf.Parameter);
        Assert.Same(declaration, Assert.Single(leaf.Captures));
        Assert.Same(declaration, declaration.ToPattern().Parameter);
        Assert.Equal("items", leaf.Name);
        Assert.Equal(ParameterKind.Collecting, leaf.Kind);
        Assert.Equal(declaration.Span, leaf.Span);
        Assert.Equal(declaration.CollectMarkerSpan, leaf.CollectMarkerSpan);
        Assert.Equal("*items", leaf.DisplayName);

        // The convenience constructor is the same value as an explicit declaration; equality
        // and hashing are the held declaration's.
        Assert.Equal(new CaptureParameterPattern("x"), new CaptureParameterPattern(new ParameterDeclaration("x")));
        Assert.Equal(new CaptureParameterPattern("x").GetHashCode(), new CaptureParameterPattern(new ParameterDeclaration("x")).GetHashCode());
        Assert.NotEqual(new CaptureParameterPattern("x"), new CaptureParameterPattern("x", Kind: ParameterKind.Collecting));
        Assert.Equal(leaf, leaf with { });
        Assert.Equal(
            new CaptureParameterPattern("items", new SourceSpan(1, 3, 1, 8), ParameterKind.Collecting) { CollectMarkerSpan = new SourceSpan(1, 2, 1, 3) },
            leaf);

        // A user algorithm's flat projection returns the held declarations — no copies.
        var algorithm = new Algorithm.User(null, [leaf, new SequenceValueParameterPattern([declaration.ToPattern()])], [], [], [new Expr.Num(1)]);
        Assert.All(algorithm.Parameters, parameter => Assert.Same(declaration, parameter));
        Assert.Equal(2, algorithm.ParameterCount);
    }

    [Fact]
    public void ParameterCount_AgreesWithTheFlatten_OnEveryShape()
    {
        ParameterPattern deep = new CaptureParameterPattern("d");
        for (var i = 0; i < 50; i++)
            deep = new SequenceValueParameterPattern([deep, new CaptureParameterPattern($"c{i}")]);

        IReadOnlyList<ParameterPattern>[] shapes =
        [
            [],
            [new CaptureParameterPattern("a")],
            [new CaptureParameterPattern("a"), new CaptureParameterPattern("a")],
            [new SequenceValueParameterPattern([])],
            [new SequenceValueParameterPattern([new CaptureParameterPattern("a"), new SequenceValueParameterPattern([new CaptureParameterPattern("b")])]), new CaptureParameterPattern("c")],
            [deep],
        ];
        foreach (var shape in shapes)
        {
            var user = new Algorithm.User(null, shape, [], [], [new Expr.Num(1)]);
            Assert.Equal(ParameterPattern.FlattenCaptures(shape).Count, user.ParameterCount);
            Assert.Equal(user.Parameters.Count, user.ParameterCount);
            Assert.Equal(user.Params.Count, user.ParameterCount);
        }
    }

    // ── Internal total accessors: Lean's total functions over the closed hierarchy ──

    [Fact]
    public void TotalAccessors_ReturnTheOwnersPayload_AndTheEmptyValueElsewhere()
    {
        var parent = new ScopeCtx(null, [], []);
        var user = new Algorithm.User(parent, [new CaptureParameterPattern("x")], [new Expr.Resolve("Math")], [new Property("P", new Algorithm.Builtin(BuiltinId.count))], [new Expr.Param("x")])
        {
            HasExplicitParameterList = true,
        };
        var family = new Algorithm.Conditional(parent, [new Expr.Resolve("Lib")], [new CondBranch(new Pattern.Bind("x"), user)]);
        var builtin = new Algorithm.Builtin(BuiltinId.count);

        Algorithm asUser = user;
        Assert.Same(parent, asUser.Parent);
        Assert.Same(user.ParameterPatterns, asUser.ParameterPatterns);
        Assert.Equal(["x"], asUser.Params);
        Assert.Equal(1, asUser.ParameterCount);
        Assert.Same(user.Opens, asUser.Opens);
        Assert.Same(user.Properties, asUser.Properties);
        Assert.Same(user.Output, asUser.Output);
        Assert.Empty(asUser.Branches);
        Assert.True(asUser.HasExplicitParameterList);
        Assert.Null(asUser.FindDuplicatePropName());
        Assert.False(asUser.HasDuplicateBranchPatterns());

        Algorithm asFamily = family;
        Assert.Same(parent, asFamily.Parent);
        Assert.Empty(asFamily.ParameterPatterns);
        Assert.Empty(asFamily.Parameters);
        Assert.Empty(asFamily.Params);
        Assert.Equal(0, asFamily.ParameterCount);
        Assert.Same(family.Opens, asFamily.Opens);
        Assert.Empty(asFamily.Properties);
        Assert.Same(OutputBundle.Empty, asFamily.Output);
        Assert.Same(family.Branches, asFamily.Branches);
        Assert.False(asFamily.HasExplicitParameterList);
        Assert.Null(asFamily.FindDuplicatePropName());

        Algorithm asBuiltin = builtin;
        Assert.Null(asBuiltin.Parent);
        Assert.Empty(asBuiltin.ParameterPatterns);
        Assert.Empty(asBuiltin.Params);
        Assert.Empty(asBuiltin.Opens);
        Assert.Empty(asBuiltin.Properties);
        Assert.Same(OutputBundle.Empty, asBuiltin.Output);
        Assert.Empty(asBuiltin.Branches);
        Assert.False(asBuiltin.HasExplicitParameterList);

        // The duplicate checks are total like Lean's: meaningful on the owner, false/none
        // elsewhere, and the owner's own method is what they read.
        var duplicated = user with { Properties = [new Property("P", builtin), new Property("P", builtin)] };
        Assert.Equal("P", ((Algorithm)duplicated).FindDuplicatePropName());
        var duplicatedBranches = family with { Branches = [new CondBranch(new Pattern.Bind("a"), user), new CondBranch(new Pattern.Bind("b"), user)] };
        Assert.True(((Algorithm)duplicatedBranches).HasDuplicateBranchPatterns());
        Assert.True(duplicatedBranches.HasDuplicateBranchPatterns());
    }

    [Fact]
    public void BaseAlgorithm_DeclaresNoPayload_AndTheTotalAccessorsCannotWrite()
    {
        // The reflection half of the ownership contract, from inside the assembly: the base
        // type declares exactly its two runtime slots and the record's equality contract,
        // the one settable slot is the internal deferred-region slot, its public instance
        // surface is equality, printing, cloning, and the three Lean-total updates, and the
        // internal total accessors compile to getters only — a helper that let a base-typed
        // value be WRITTEN would have to appear in one of these lists.
        const BindingFlags declared = BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.DeclaredOnly;
        var properties = typeof(Algorithm).GetProperties(declared);
        Assert.Equal(
            ["Declaration", "DeferredRegion", "EqualityContract"],
            properties.Select(p => p.Name).OrderBy(n => n, StringComparer.Ordinal));
        var slot = Assert.Single(properties, p => p.SetMethod is not null);
        Assert.Equal("DeferredRegion", slot.Name);
        Assert.True(slot.SetMethod!.IsAssembly, "the deferred-region slot is internal");

        var publicMethods = typeof(Algorithm)
            .GetMethods(BindingFlags.Instance | BindingFlags.Public | BindingFlags.DeclaredOnly)
            .Where(m => !m.IsSpecialName)
            .Select(m => m.Name)
            .Distinct()
            .OrderBy(n => n, StringComparer.Ordinal);
        Assert.Equal(["<Clone>$", "Equals", "GetHashCode", "ToString", "WithParameterPatterns", "WithParameters", "WithParams"], publicMethods);

        var accessorMethods = Descendants(typeof(AlgorithmAccessors))
            .SelectMany(t => t.GetMethods(BindingFlags.Static | BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.DeclaredOnly))
            .ToList();
        Assert.Contains(accessorMethods, m => m.Name.StartsWith("get_", StringComparison.Ordinal));
        Assert.DoesNotContain(accessorMethods, m => m.Name.StartsWith("set_", StringComparison.Ordinal) || m.Name.StartsWith("init_", StringComparison.Ordinal));
        Assert.All(
            accessorMethods.Where(m => m.IsStatic && m.Name.StartsWith("get_", StringComparison.Ordinal)),
            m => Assert.Equal(typeof(Algorithm), Assert.Single(m.GetParameters()).ParameterType));

        static IEnumerable<Type> Descendants(Type type)
        {
            yield return type;
            foreach (var nested in type.GetNestedTypes(BindingFlags.Public | BindingFlags.NonPublic))
            {
                foreach (var descendant in Descendants(nested))
                    yield return descendant;
            }
        }
    }

    // ── Roots: every pass returns the variant it was given; the program root is a User ──

    [Fact]
    public void EveryElaborationPass_PreservesTheRootVariant()
    {
        // The typed roots (ParseResult.Root, RunResult.*.Root : Algorithm.User) rest on two
        // facts: the parser produces a User (typed at ParseRootAlgorithm), and every pass
        // returns the variant of the algorithm it is given. Pinned here for all three variants
        // on every stage entry the pipeline calls.
        var userBody = new Algorithm.User(null, [], [], [], [new Expr.Num(1)]);
        Algorithm[] roots =
        [
            new Algorithm.User(null, [], [], [new Property("F", new Algorithm.User(null, [], [], [], [new Expr.Param("x")]))], [new Expr.Call(new Expr.Resolve("F"), [new Expr.Num(1)])]),
            new Algorithm.Conditional(null, [], [new CondBranch(new Pattern.Bind("x"), userBody)]),
            new Algorithm.Builtin(BuiltinId.count),
        ];

        foreach (var root in roots)
        {
            var (detected, _) = ParameterDetector.Detect(root);
            Assert.IsType(root.GetType(), detected);
            var resolved = ImplicitArgumentResolver.Resolve(detected);
            Assert.IsType(root.GetType(), resolved);
            var origins = new ImplicitArgumentResolver.ResolutionOrigins();
            var completed = ParameterDetector.CompleteOwnership(resolved, origins, hostOperations: null);
            Assert.IsType(root.GetType(), completed.Root);
            var exposed = PropertyExposureResolver.Resolve(resolved);
            Assert.IsType(root.GetType(), exposed);
        }
    }

    [Fact]
    public async Task ModuleLoader_PreservesTheRootVariant()
    {
        var userBody = new Algorithm.User(null, [], [], [], [new Expr.Num(1)]);
        Algorithm[] roots =
        [
            new Algorithm.User(null, [], [], [], [new Expr.Num(1)]),
            new Algorithm.Conditional(null, [], [new CondBranch(new Pattern.Bind("x"), userBody)]),
            new Algorithm.Builtin(BuiltinId.count),
        ];
        foreach (var root in roots)
        {
            var loader = new ModuleLoader([], static (_, _) => throw new InvalidOperationException("no loads here"));
            var loaded = await loader.ElaborateAsync(root);
            Assert.IsType(root.GetType(), loaded);
        }
    }

    [Fact]
    public void ParsedRoots_AreUserAlgorithms_OnEveryRecoveryPath()
    {
        // A parse that recovers, a parser-limit placeholder, and an unresolved load (the
        // synchronous entry rejects it and returns the syntax root) all yield a User root.
        Assert.IsType<Algorithm.User>(SourceProvenance.ParseAllowingDiagnostics("F(x) = \n)").Root);
        Assert.IsType<Algorithm.User>(SourceProvenance.ParseSyntaxAllowingDiagnosticsRoot("1 +"));
        Assert.IsType<Algorithm.User>(SourceProvenance.ParseAllowingDiagnostics("open 'https://example.invalid/m.kat'\n1").Root);
        Assert.IsType<Algorithm.User>(SourceProvenance.ParseAllowingDiagnostics(new string('(', Parser.MaxNestingDepth + 50) + "1").Root);
    }

    // ── Equality and copies ────────────────────────────────────────────────

    [Fact]
    public void Equality_IgnoresNothingStoredAndDerivesNothingStored()
    {
        // Two algorithms whose stored payload is the same instances are equal; the derived
        // projections are not stored fields, so they can never make equal payload unequal.
        IReadOnlyList<ParameterPattern> patterns = [new CaptureParameterPattern("x")];
        OutputBundle output = [new Expr.Param("x")];
        var a = new Algorithm.User(null, patterns, [], [], output);
        var b = new Algorithm.User(null, patterns, [], [], output);
        Assert.Equal(a, b);
        _ = a.Params;
        _ = b.Parameters;
        Assert.Equal(a, b);
        Assert.Equal(a.GetHashCode(), b.GetHashCode());

        // The explicit-list bit and every stored component participate; runtime slots do not.
        Assert.NotEqual(a, a with { HasExplicitParameterList = true });
        Assert.NotEqual(a, a with { ParameterPatterns = [new CaptureParameterPattern("x")] });
        Assert.Equal(a, a with { DeferredRegion = null });
        Assert.NotSame(a.Declaration, b.Declaration);
    }

    private static Algorithm.User UserProperty(Algorithm.User root, string name)
        => Assert.IsType<Algorithm.User>(Assert.Single(root.Properties, p => p.Name == name).Value);

    private sealed class AlgorithmCollector : AstWalker
    {
        public List<Algorithm> Algorithms { get; } = [];

        protected override bool VisitsExplicitParameterDeclarations => false;

        protected override void VisitUserAlgorithm(Algorithm.User algorithm)
        {
            Algorithms.Add(algorithm);
            base.VisitUserAlgorithm(algorithm);
        }

        protected override void VisitConditionalAlgorithm(Algorithm.Conditional algorithm)
        {
            Algorithms.Add(algorithm);
            base.VisitConditionalAlgorithm(algorithm);
        }

        protected override void VisitBuiltinAlgorithm(Algorithm.Builtin algorithm)
        {
            Algorithms.Add(algorithm);
        }
    }
}
