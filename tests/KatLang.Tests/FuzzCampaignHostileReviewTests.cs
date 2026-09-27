using System.Text.Json;
using KatLang.Semantics;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

public class FuzzCampaignHostileReviewTests
{
    [Theory]
    [InlineData(18)]
    [InlineData(36)]
    public void RejectedOpenDiamond_RemainsSharedAndBothPassesDoLinearWork(int depth)
    {
        Expr expression = new Expr.AlgorithmExpr(SourceProvenance.ParseSyntaxValidRoot("K = ~b - a\nK"));
        for (var i = 0; i < depth; i++)
            expression = new Expr.Binary(BinaryOp.Add, expression, expression);
        var root = new Algorithm.User(null, [], [expression], [], []);
        var observations = new FrontEndTraversalObservations();
        var (detected, _) = ParameterDetector.DetectPrevalidated(root, null, observations);
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected, observations: observations);
        foreach (var stage in new[] { detected, resolved })
        {
            var cursor = Assert.Single(stage.Opens);
            for (var i = 0; i < depth; i++)
            {
                var binary = Assert.IsType<Expr.Binary>(cursor);
                Assert.Same(binary.Left, binary.Right);
                cursor = binary.Left;
            }
            var block = Assert.IsType<Algorithm.User>(Assert.IsType<Expr.AlgorithmExpr>(cursor).Algorithm);
            Assert.Equal(["b", "a"], Assert.Single(block.Properties).Value.Params);
            if (ReferenceEquals(stage, resolved)) Assert.IsType<Expr.Call>(Assert.Single(block.Output));
        }
        Assert.InRange(observations.DetectorRewriteExpansions, depth, 8L * depth + 64);
        Assert.InRange(observations.ResolverRewriteExpansions, depth, 8L * depth + 64);
    }

    [Theory]
    [InlineData("-({ K = ~b - a\nK })")]
    [InlineData("not ({ K = ~b - a\nK })")]
    [InlineData("1 + { K = ~b - a\nK }")]
    [InlineData("true and { K = ~b - a\nK }")]
    [InlineData("0 < { K = ~b - a\nK } <= 2")]
    [InlineData("(0 < { K = ~b - a\nK }) == true")]
    [InlineData("[1, 2]:{ K = ~b - a\nK }")]
    [InlineData("1 + a.~b(~c)")]
    [InlineData("-((~a, b.~c):~d)")]
    [InlineData("not (a.~b < (~c, ~d):0)")]
    public void RejectedOpen_OrdinaryCaptureRowIsAnIndependentTraversalOracle(string expression)
    {
        // A capture's row uses the established ordinary-expression traversal. The expected
        // tree is parsed independently and never computed with an open-target helper.
        var direct = SourceProvenance.ParseAllowingDiagnostics("# prefix\nopen " + expression);
        var wrapped = SourceProvenance.ParseAllowingDiagnostics("open (" + expression + ", 42)");
        Assert.Contains(direct.Diagnostics, d => d.Code == DiagnosticCode.BadOpenForm);
        Assert.Contains(wrapped.Diagnostics, d => d.Code == DiagnosticCode.BadOpenForm);
        Assert.Null(DotCallElaborationInvariant.CheckElaborated(direct.Root));
        Assert.Null(DotCallElaborationInvariant.CheckElaborated(wrapped.Root));
        var expected = Assert.IsType<Expr.Capture>(Assert.Single(wrapped.Root.Opens)).Body[0];
        Assert.Equal(LeanAstEncoder.EncodeExpr(expected), LeanAstEncoder.EncodeExpr(Assert.Single(direct.Root.Opens)));
        Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(direct.Source));
        var model = SemanticModelBuilder.Build(direct.Parsed);
        Assert.InRange(model.IdentifierResolutions.Count, 0, 2 * direct.Source.Length);
        Assert.InRange(direct.Diagnostics.Count, 1, direct.Source.Length);
    }

    [Theory]
    [InlineData(927143)]
    [InlineData(143927)]
    public void CommentMetamorphism_PreservesRecoveryTreeSitesDiagnosticsAndGating(int seed)
    {
        var random = new Random(seed);
        string[] pieces = ["a", "b", "~x", "0", "not ", "open ", "true", "and ", "# note\n", "\n", " ",
            "(", ")", "[", "]", "{", "}", ".", ":", ",", "=", "+", "*", "<", "$", "@", "'s'", "é", "\uD800"];
        string[] fixedSources = ["$+", "!<", "`:", "$.F", "$*", "@\n+", ")\nKept = 7\nKept",
            "F(*) = 1\nKept = 7\nKept", "(1, 2]\nKept = 7\nKept", "open~e<", "open-~r",
            "a, *b = (1, 2, 3)\na", "A = 1 + # middle\n$\nKept = 7\nKept", "A.\nKept = 7\nKept"];
        var sources = fixedSources.Concat(Enumerable.Range(0, 200).Select(_ =>
            string.Concat(Enumerable.Range(0, random.Next(1, 35)).Select(_ => pieces[random.Next(pieces.Length)]))));
        foreach (var source in sources)
        {
            var original = SourceProvenance.ParseAllowingDiagnostics(source);
            var shape = LeanAstEncoder.EncodeAlgorithm(original.Root);
            var model = SemanticModelBuilder.Build(original.Parsed);
            foreach (var (prefix, crlf) in new[] { ("# c\n", false), ("# one\n# two\n\n", false), ("\n# c\n", true) })
            {
                var text = prefix + source;
                if (crlf) text = text.Replace("\n", "\r\n", StringComparison.Ordinal);
                var actual = SourceProvenance.ParseAllowingDiagnostics(text);
                var lineShift = prefix.Count(c => c == '\n');
                Assert.True(shape == LeanAstEncoder.EncodeAlgorithm(actual.Root), $"seed={seed}, source={JsonSerializer.Serialize(source)}");
                Assert.Equal(Diagnostics(original.Parsed, 0), Diagnostics(actual.Parsed, lineShift));
                Assert.Equal(Sites(model, 0), Sites(SemanticModelBuilder.Build(actual.Parsed), lineShift));
                Assert.Equal(original.HasFrontEndErrors, actual.HasFrontEndErrors);
                if (actual.HasFrontEndErrors)
                    Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(text));
            }
        }
    }

    private static string Diagnostics(ParseResult parse, int shift) => JsonSerializer.Serialize(parse.Diagnostics.Select(d =>
        new { d.Code, d.Message, Span = Shift(d.Span, shift) }));

    private static SourceSpan? Shift(SourceSpan? span, int lines) => span is { } s
        ? new SourceSpan(new(s.Start.Line - lines, s.Start.Column), new(s.End.Line - lines, s.End.Column)) : null;

    private static string Sites(SemanticModel model, int shift) => JsonSerializer.Serialize(new
    {
        Declarations = model.Declarations.Select(d => new { d.Name, d.Kind, Span = Shift(d.Span, shift) }),
        References = model.IdentifierResolutions.Select(r => new { r.Occurrence.Name, r.Occurrence.Kind, r.Classification,
            Span = Shift(r.Occurrence.Span, shift), Target = Shift(r.ResolvedDeclaration?.Span, shift) }),
    });

    public static TheoryData<string> DeconstructionCorpus => new()
    {
        "a, b = (1, 2)\na + b",
        "a, *middle, z = (1, 2, 3, 4)\na, middle, z",
        "a, a = (1, 1)\na",
        "a, a = (1, 2)\na",
        "Outer = { a, b = (1, 2)\nInner = { a, c = (3, 4)\na + c }\na + Inner }\nOuter",
        "Outer(p) = { a, b = (p, 2)\na + b }\nOuter(3)",
        "Outer = { a, b = (p, q)\nAlias = a\nAlias + b }\nOuter(3, 4)",
        "F(0) = { a, b = (1, 2)\na }\nF(n) = { a, *b = (n, 2, 3)\nb }\nF(0)",
        "open M\nM = { public X = 3 }\na, b = (X, 4)\na + b",
        "M = load('https://example.test/m')\na, b = (M.X, 4)\na",
        "a, *b, z = ([1, 2]*, 3, 4)\nb:0",
        "a, *b = (1, $)\na",
        "a, b = (1, $)\na",
        "Outer = { a, b = (1, 2)\nNested = { c, d = (a, b)\nc + d }\nNested }\nOuter",
    };

    [Fact]
    public async Task SeededDeconstruction_OpenRenamingGroupingAndExecutionStrategiesAgree()
    {
        var random = new Random(927314);
        for (var i = 0; i < 32; i++)
        {
            var a = random.Next(-20, 20);
            var b = random.Next(-20, 20);
            foreach (var rename in new[] { "Original", "Renamed" })
            foreach (var group in new[] { false, true })
            {
                var expression = group ? "((x + y + z))" : "x + y + z";
                var source = $"# layout\nopen M\nM = {{ public V = {a} }}\n"
                    + $"{rename}(p) = {{ x, *middle, z = (V, 11, 12, p)\ny = middle:0\n{expression} }}\n{rename}({b})";
                var parsed = SourceProvenance.ParseValid(source);
                var ast = new Expr.AlgorithmExpr(parsed.Root);
                var generic = Evaluator.RunCountedObserved(ast, enableOptimizations: false).Result;
                var optimized = Evaluator.RunCountedObserved(ast, enableOptimizations: true).Result;
                var cache = new SuspendingAsyncZeroArgPropertyResultCache();
                var suspended = (await Evaluator.RunCountedObservedAsync(ast, zeroArgPropertyResultCache: cache)).Result;
                Assert.True(cache.AsyncAccesses > 0);
                Assert.Equal(0, cache.SyncAccesses);
                foreach (var result in new[] { generic, optimized, suspended })
                {
                    Assert.False(result.IsError);
                    Assert.Equal(new Result.Atom(a + 11 + b), result.Value.Value);
                    Assert.Equal(1, result.Value.EmittedCount);
                }
            }
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task SuspendedHostComparisonInDeconstruction_IsEagerAfterFalseAndHonorsCancellation(bool cancel)
    {
        using var cancellation = new CancellationTokenSource();
        var trace = new List<int>();
        var operations = HostOperations.Create(Enumerable.Range(0, 3).Select(i =>
            HostOperation.CreateAsync($"H{i}", async (_, token) =>
            {
                await Task.Yield();
                trace.Add(i);
                if (cancel && i == 1) cancellation.Cancel();
                token.ThrowIfCancellationRequested();
                return new Result.Atom(3 - i);
            })).ToArray());
        var source = "x, y = (H0() < H1() < H2(), 7)\nx, y";
        var options = new RunOptions { HostOperations = operations, EvaluationCancellationToken = cancellation.Token };
        var parse = await Parser.ParseAsync(source, options);
        Assert.False(parse.HasErrors);
        if (cancel)
        {
            var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(async () =>
                await KatLangEngine.RunAsync(source, options));
            Assert.Equal(cancellation.Token, error.CancellationToken);
            Assert.Equal([0, 1], trace);
        }
        else
        {
            Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(source, options));
            Assert.Equal([0, 1, 2], trace);
        }
    }

    [Theory]
    [MemberData(nameof(DeconstructionCorpus))]
    public void InertHelpers_PreserveEveryEditorSurfaceAgainstOrdinaryHelperTraversal(string source)
    {
        var parse = SourceProvenance.ParseAllowingDiagnostics(source);
        var observations = new FrontEndTraversalObservations();
        var actual = SemanticModelBuilder.Build(parse.Root, observations);
        var referenceObservations = new FrontEndTraversalObservations();
        // Removing only the private optimization marker makes the very same helper enter
        // the literal pre-fix VisitUserAlgorithm/CreateScope path. No source is re-elaborated.
        var reference = SemanticModelBuilder.Build(OrdinaryHelpers(parse.Root), referenceObservations);
        Assert.True(referenceObservations.SemanticModelAlgorithmVisits > observations.SemanticModelAlgorithmVisits);
        Assert.Equal(EditorSnapshot(reference, source), EditorSnapshot(actual, source));
    }

    private static string EditorSnapshot(SemanticModel model, string source) => JsonSerializer.Serialize(new
    {
        model.Declarations, model.IdentifierOccurrences, model.IdentifierResolutions, model.PropertyInfos, model.ScopeVisibilities,
        Queries = source.Split('\n').SelectMany((line, index) => Enumerable.Range(1, line.Length + 1)
            .Select(column => new SourcePosition(index + 1, column))).Select(position => new
            {
                position, Resolution = model.FindResolutionAt(position), Property = model.FindPropertyAt(position),
                Scope = model.FindScopeAt(position), Visible = model.GetVisibleSymbolsAt(position),
            }),
    });

    private static Algorithm OrdinaryHelpers(Algorithm algorithm) => algorithm switch
    {
        Algorithm.User user => user with
        {
            AssignmentDeconstructionTarget = null,
            Opens = user.Opens.Select(Rewrite).ToArray(),
            Properties = user.Properties.Select(p => p with { Value = OrdinaryHelpers(p.Value) }).ToArray(),
            Output = new OutputBundle(user.Output.Select(Rewrite).ToArray()),
        },
        Algorithm.Conditional conditional => conditional with
        {
            Opens = conditional.Opens.Select(Rewrite).ToArray(),
            Branches = conditional.Branches.Select(b => b with { Body = OrdinaryHelpers(b.Body) }).ToArray(),
        },
        Algorithm.Builtin => algorithm,
    };

    private static Expr Rewrite(Expr expr) => expr switch
    {
        Expr.AlgorithmExpr block => block with { Algorithm = OrdinaryHelpers(block.Algorithm) },
        Expr.Call call => call with { Function = Rewrite(call.Function), Args = new(call.Args.Select(Rewrite).ToArray()) },
        Expr.Capture capture => capture with { Body = new(capture.Body.Select(Rewrite).ToArray()) },
        Expr.DotCall dot => dot with { Target = Rewrite(dot.Target), Args = dot.Args is null ? null : new(dot.Args.Select(Rewrite).ToArray()), LexicalFallback = Rewrite(dot.EffectiveLexicalFallback) },
        Expr.Unary unary => unary with { Operand = Rewrite(unary.Operand) },
        Expr.Binary binary => binary with { Left = Rewrite(binary.Left), Right = Rewrite(binary.Right) },
        Expr.Comparison comparison => comparison with { First = Rewrite(comparison.First), Links = comparison.Links.Select(l => l with { Operand = Rewrite(l.Operand) }).ToArray() },
        Expr.Index index => index with { Target = Rewrite(index.Target), Selector = Rewrite(index.Selector) },
        Expr.ListLiteral list => list with { Items = new(list.Items.Select(Rewrite).ToArray()) },
        Expr.SequenceSpread spread => spread with { Operand = Rewrite(spread.Operand) },
        Expr.SequenceConstruct join => join with { Left = Rewrite(join.Left), Right = Rewrite(join.Right) },
        Expr.Grace grace => grace with { Inner = Rewrite(grace.Inner) },
        Expr.Resolve or Expr.Param or Expr.Num or Expr.BoolLiteral or Expr.StringLiteral or Expr.EmptySequence or Expr.NativeCall => expr,
    };
}
