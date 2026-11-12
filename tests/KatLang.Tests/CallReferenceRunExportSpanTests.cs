using KatLang.Evaluation;
using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

/// <summary>
/// CR-6 POSITIONING (2026-11-10; C#-only diagnostics, Lean errors carry no location): the run-export
/// refusal "A call reference cannot leave its run" keeps its kind (<c>TypeMismatch</c>), message and
/// refusal conditions, and is positioned at the WRITTEN construct that exports the reference
/// (<c>Evaluator.RunExportSite</c>): the only output row; the first row whose item holds a reference when
/// every row supplies exactly one item; the hull of the output rows when a spread row makes the item-row
/// correspondence undecidable; the root's declaration of the named top-level property; a non-program
/// root's own span. Missing row/declaration spans fall back to the exported root's existing span (a
/// directly evaluated import view's local import site); with neither, the location stays absent.
/// The source-program matrix covers the generic and optimized synchronous evaluators, the forced async
/// twin, the plain run and the public engine (sync and async), which must agree on kind, message and span.
/// </summary>
public class CallReferenceRunExportSpanTests
{
    private const string Prelude = """
        Square(x) = x * x
        Capture(meta operation) = operation
        Add(a, b) = a + b
        Keep(r) = r
        """;

    private static Expr Program(string source)
    {
        var parsed = Parser.Parse(source);
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        return new Expr.AlgorithmExpr(parsed.Root);
    }

    private static string Render(EvalError error)
    {
        Assert.IsType<EvalError.TypeMismatch>(error);
        return $"{KatLangError.FromEvalError(error).Message} @{error.Span}";
    }

    private static string Render(RunResult run)
    {
        var failure = Assert.IsType<RunResult.EvalFailure>(run);
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.TypeMismatch, error.Code);
        return $"{error.Message} @{error.Span}";
    }

    private static string Expected(string span)
        => $"Type mismatch: {Evaluator.CallReferenceLeavesRunMessage} @{span}";

    /// <summary>The refusal of <paramref name="source"/> on every evaluator route, which must all agree.</summary>
    private static string ObserveEveryRoute(string source)
    {
        var program = Program(source);
        var (generic, _) = Evaluator.RunCountedObserved(program, enableOptimizations: false);
        var (optimized, _) = Evaluator.RunCountedObserved(program, enableOptimizations: true);
        var (twin, _) = Evaluator.RunCountedObservedAsync(program,
            zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache()).AsTask().GetAwaiter().GetResult();
        var plain = Evaluator.Run(program);
        var engine = KatLangEngine.Run(source);
        var engineAsync = KatLangEngine.RunAsync(source).GetAwaiter().GetResult();

        var observed = Render(generic.Error);
        Assert.Equal(observed, Render(optimized.Error));
        Assert.Equal(observed, Render(twin.Error));
        Assert.Equal(observed, Render(plain.Error));
        Assert.Equal(observed, Render(engine));
        Assert.Equal(observed, Render(engineAsync));
        return observed;
    }

    // Program line 1 is source line 5 (four prelude lines).
    [Theory]
    [InlineData("direct-reference", "R = Capture(Square(5))\nR", "[6:1, 6:2)")]
    [InlineData("argument-view", "R = Capture(Add(10, 20))\nR.Arguments", "[6:1, 6:12)")]
    [InlineData("nested-list", "R = Capture(Square(5))\n[1, [R]]", "[6:1, 6:9)")]
    [InlineData("nested-group", "R = Capture(Square(5))\n(1, (2, R))", "[6:1, 6:12)")]
    [InlineData("through-a-call", "R = Capture(Square(5))\nKeep(R)", "[6:1, 6:8)")]
    [InlineData("inline-capture", "Capture(Square(5))", "[5:1, 5:19)")]
    [InlineData("single-spread-row", "R = Capture(Square(5))\n[1, R]*", "[6:1, 6:8)")]
    [InlineData("later-row-same-line", "R = Capture(Square(5))\n1, R, 2", "[6:4, 6:5)")]
    [InlineData("later-row-next-line", "R = Capture(Square(5))\n1\n[R]", "[7:1, 7:4)")]
    [InlineData("first-of-two-escaping-rows", "R = Capture(Square(5))\n1, [R], R", "[6:4, 6:7)")]
    [InlineData("later-row-deep-list", "R = Capture(Square(5))\n1, [1, [2, R]], R", "[6:4, 6:15)")]
    [InlineData("view-in-later-row", "R = Capture(Add(10, 20))\n1, R.Arguments", "[6:4, 6:15)")]
    [InlineData("lifted-reference", "Id(v) = v\nH = x + 0\nC = Capture(Id(H + 0))\nC(4)", "[8:1, 8:5)")]
    [InlineData("lifted-reference-in-later-row", "Id(v) = v\nH = x + 0\nC = Capture(Id(H + 0))\n1, [C(4)]", "[8:4, 8:10)")]
    [InlineData("lifted-algorithm-call-returns-reference", "H = x + 0\nC = Capture(Capture(Square(H + 0))).Algorithm(Square(1))\nC(4)", "[7:1, 7:5)")]
    [InlineData("spread-among-rows-is-the-output-hull", "R = Capture(Square(5))\n[1]*, R", "[6:1, 6:8)")]
    [InlineData("spread-among-lines-is-the-output-hull", "R = Capture(Square(5))\n[1, 2]*\nR", "[6:1, 7:2)")]
    public void TheRefusal_IsPositionedAtTheWrittenExportSite(string route, string body, string span)
    {
        var observed = ObserveEveryRoute(Prelude + "\n" + body);
        Assert.True(Expected(span) == observed, $"{route}: {observed}");
    }

    [Fact]
    public async Task AMaxDecimalPlacesReference_IsPositionedAtThePropertyDeclaration()
    {
        var source = Prelude + "\nR = Capture(Square(5))\nMaxDecimalPlaces = [R]\n1";
        var root = SourceProvenance.ParseValid(source).Root;
        var declaration = Assert.IsType<SourceSpan>(root.Properties.Single(static p => p.Name == "MaxDecimalPlaces").FirstDeclarationSpan);
        Assert.Equal("[6:1, 6:17)", declaration.ToString()); // the declaration anchor of `MaxDecimalPlaces = [R]`
        var expected = Expected(declaration.ToString());

        Assert.Equal(expected, Render(KatLangEngine.Run(source)));
        Assert.Equal(expected, Render(await KatLangEngine.RunAsync(source)));
        var direct = Evaluator.RunCountedWithTopLevelProperties(
            new Expr.AlgorithmExpr(root), ["MaxDecimalPlaces"], new RunScopedZeroArgPropertyResultCache());
        Assert.Equal(expected, Render(direct.Error));
    }

    [Fact]
    public void AnEscapingOutput_WinsOverAnEscapingMaxDecimalPlaces()
        => Assert.Equal(Expected("[7:1, 7:2)"),
            Render(KatLangEngine.Run(Prelude + "\nR = Capture(Square(5))\nMaxDecimalPlaces = [R]\nR")));

    [Fact]
    public async Task ADeferredModulesReference_IsPositionedAtItsRow()
    {
        var options = new RunOptions
        {
            DownloadCode = (_, _) => ValueTask.FromResult("public Capture(meta op) = op"),
        };
        const string source = """
            Sq(x) = x * x
            F(0) = 0
            F(v) = {
                open 'https://katlang.org/fu2/deferred-capture.kat'
                [1, Capture(v)]
            }
            F(Sq(5))
            """;

        Assert.Equal(Expected("[7:1, 7:9)"), Render(await KatLangEngine.RunAsync(source, options)));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task ADirectlyEvaluatedImport_UsesItsWrittenImportSpan(bool propertyOnly)
    {
        const string source = "open 'https://katlang.org/cr6-export.kat'";
        var module = Prelude + "\nR = Capture(Square(5))\n" + (propertyOnly ? "MaxDecimalPlaces = [R]\n1" : "[R]");
        var parsed = await Parser.ParseAsync(source, new RunOptions { DownloadCode = (_, _) => ValueTask.FromResult(module) });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        var imported = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(parsed.Root.Opens));
        Assert.All(imported.Algorithm.Output, static row => Assert.Null(row.Span));
        var importSpan = new SourceSpan(new(1, 6), new(1, source.Length + 1));
        Assert.Equal(importSpan, imported.Span);
        var expected = Expected(importSpan.ToString());

        if (propertyOnly)
        {
            var result = Evaluator.RunCountedWithTopLevelProperties(
                imported, ["MaxDecimalPlaces"], new RunScopedZeroArgPropertyResultCache());
            Assert.Equal(expected, Render(result.Error));
            var twin = await Evaluator.RunCountedWithTopLevelPropertiesAsync(
                imported, ["MaxDecimalPlaces"], new RunScopedAsyncZeroArgPropertyResultCache());
            Assert.Equal(expected, Render(twin.Error));
        }
        else
        {
            Assert.Equal(expected, Render(Evaluator.Run(imported).Error));
            var (twin, _) = await Evaluator.RunCountedObservedAsync(imported,
                zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache());
            Assert.Equal(expected, Render(twin.Error));
        }

        // Detaching the local import site leaves no written coordinate anywhere in the import view.
        var detached = imported with { Span = null };
        var detachedError = propertyOnly
            ? Evaluator.RunCountedWithTopLevelProperties(detached, ["MaxDecimalPlaces"], new RunScopedZeroArgPropertyResultCache()).Error
            : Evaluator.Run(detached).Error;
        Assert.IsType<EvalError.TypeMismatch>(detachedError);
        Assert.Null(detachedError.Span);
    }

    // ── Host-built trees: a location the tree does not carry stays absent ──────────

    private static readonly Lazy<Result> CapturedReference = new(CaptureFromSeam);

    private static Result CaptureFromSeam()
    {
        Result.CallReference? captured = null;
        var operations = HostOperations.Create(
            HostOperation.Create("Grab", (_, _) => throw new InvalidOperationException("receiver missing"), "operation"));
        var seam = new InvocationPlanTestSeam(new Dictionary<string, Func<IReadOnlyList<NeedCell?>, Result>>
        {
            ["Grab"] = cells =>
            {
                captured = Evaluator.ReifyMeta(cells[0]).Value;
                return new Result.Atom(0);
            },
        });
        using (InvocationPlanTestSeam.Activate(seam))
        {
            var parsed = Parser.Parse("Sq(x) = x * x\nGrab(Sq(5))", new RunOptions { HostOperations = operations });
            Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
            var (result, _) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(parsed.Root), hostOperations: operations);
            Assert.True(result.IsOk);
        }

        return Assert.IsType<Result.CallReference>(captured);
    }

    private static Evaluator.EvalCtx RetainingCtx()
    {
        var budget = EvaluationBudget.Create(null);
        budget.DecideInvocationPlanRetention(programMayCapture: true);
        return Evaluator.EvalCtx.Empty with { Budget = budget };
    }

    private static SourceSpan At(int line, int start, int end) => new(new(line, start), new(line, end));

    private static SourceSpan? ExportSpan(Expr? exported, Result value)
    {
        var refused = Evaluator.ExportRunValue(EvalResult<Result>.Ok(value), exported, RetainingCtx());
        Assert.Equal(Evaluator.CallReferenceLeavesRunMessage, Assert.IsType<EvalError.TypeMismatch>(refused.Error).Message);
        return refused.Error.Span;
    }

    [Fact]
    public void ANonProgramRoot_IsPositionedAtItsOwnSpanOrNowhere()
    {
        var reference = CapturedReference.Value;
        Assert.Null(ExportSpan(null, reference));
        Assert.Null(ExportSpan(new Expr.Num(1), reference));
        Assert.Equal(At(2, 3, 9), ExportSpan(new Expr.Num(1) { Span = At(2, 3, 9) }, reference));
    }

    [Fact]
    public void SpanlessHostRows_LeaveTheRefusalUnpositioned()
    {
        var reference = CapturedReference.Value;
        Expr Root(params Expr[] rows) => new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [], rows));
        var pair = new Result.SequenceValue([new Result.Atom(1), reference]);

        Assert.Null(ExportSpan(Root(new Expr.Num(1)), reference));
        Assert.Null(ExportSpan(Root(new Expr.Num(1), new Expr.Num(2)), pair));
        // Row 2 is located, so it is named; a spanless sibling does not matter.
        Assert.Equal(At(1, 4, 5), ExportSpan(Root(new Expr.Num(1), new Expr.Num(2) { Span = At(1, 4, 5) }), pair));
        // An undecidable item-row correspondence uses the hull only when every row is located.
        var spread = new Expr.SequenceSpread(new Expr.Num(1)) { Span = At(1, 1, 3) };
        Assert.Null(ExportSpan(Root(spread, new Expr.Num(2)), pair));
        Assert.Equal(At(1, 1, 6), ExportSpan(Root(spread, new Expr.Num(2) { Span = At(1, 5, 6) }), pair));
        // More items than rows (no one-item-per-row correspondence) is the hull too.
        var triple = new Result.SequenceValue([new Result.Atom(1), new Result.Atom(2), reference]);
        Assert.Equal(At(1, 1, 6), ExportSpan(
            Root(new Expr.Num(1) { Span = At(1, 1, 2) }, new Expr.Num(2) { Span = At(1, 5, 6) }), triple));
    }

    [Fact]
    public void AReferenceFreeExport_IsUnchanged()
    {
        var value = new Result.ListValue([new Result.Atom(1)]);
        var exported = Evaluator.ExportRunValue(EvalResult<Result>.Ok(value), new Expr.Num(1) { Span = At(1, 1, 2) }, RetainingCtx());
        Assert.Same(value, exported.Value);
    }

    [Fact]
    public void LocatingTheEscapingRow_DoesNotRescanSharedCleanValuesPerRow()
    {
        const int cleanRows = 1024;
        Result shared = new Result.Atom(1);
        for (var depth = 0; depth < 128; depth++)
            shared = new Result.ListValue([shared, shared]);
        var value = EvalResult<Result>.Ok(new Result.SequenceValue(
            Enumerable.Repeat(shared, cleanRows).Append(CapturedReference.Value)));
        var rows = Enumerable.Range(1, cleanRows)
            .Select(static line => (Expr)new Expr.Resolve("Clean") { Span = At(line, 1, 6) })
            .Append(new Expr.Resolve("Ref") { Span = At(cleanRows + 1, 1, 4) })
            .ToArray();
        var program = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [], rows));
        var ctx = RetainingCtx();

        // A coarse bound on the complete refusal path, including location selection. Fresh per-row
        // scans allocate many MB for this small shared graph even if their work is unobserved.
        for (var warm = 0; warm < 3; warm++)
            Assert.True(Evaluator.ExportRunValue(value, program, ctx).IsError);
        var before = GC.GetAllocatedBytesForCurrentThread();
        var refused = Evaluator.ExportRunValue(value, program, ctx);
        var allocated = GC.GetAllocatedBytesForCurrentThread() - before;

        Assert.Equal(At(cleanRows + 1, 1, 4), refused.Error.Span);
        Assert.Equal(Evaluator.CallReferenceLeavesRunMessage, Assert.IsType<EvalError.TypeMismatch>(refused.Error).Message);
        Assert.InRange(allocated, 0, 4 * 1024 * 1024);
    }
}
