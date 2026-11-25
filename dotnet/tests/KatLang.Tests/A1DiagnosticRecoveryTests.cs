using KatLang.ParserFuzz;
using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// F4: diagnostic recovery after an A1 rejection (<see cref="DiagnosticCode.SelfDependentInferredParameters"/>).
/// The rejected unit is never forwarded, open-validated, output-validated, exposure-settled or
/// published; only the parameter/property collision rule, which is monotone in the parameters a
/// detected signature holds, still runs, so an independent collision is no longer hidden by A1
/// and nothing that depends on an undecided input is reported.
/// </summary>
public sealed class A1DiagnosticRecoveryTests
{
    private static readonly string[] Witnesses = ["A.3.1", "A.3.2", "A.3.3a", "A.3.3b"];

    // A collision with a WRITTEN parameter, and one with a parameter detection INFERRED
    // (Inf's row reads `iz`, which Inner's property cannot provide to Inf).
    private const string WrittenCollision = "Coll(cy) = {\n    cy = 1\n    cy\n}";
    private const string InferredCollision = "Inf = {\n    Inner = {\n        iz = 1\n        iz\n    }\n    iz + Inner\n}";

    // A.3.2 is the witness whose root row is a constant, so declarations can surround P.
    private static string A32 => StaticStructureWitnessSources.Cases["A.3.2"];

    private static string WithBefore(string witness, string declaration) => declaration + "\n" + witness;

    // Inserted before the witness's final root row, i.e. after every witness declaration.
    private static string WithAfter(string witness, string declaration)
    {
        var lastRow = witness.LastIndexOf('\n');
        return witness[..lastRow] + "\n" + declaration + witness[lastRow..];
    }

    private static ParseResult Parse(string source, int? maxDiagnostics = null)
        => Parser.Parse(source, new RunOptions { SourceProcessingLimits = new() { MaxDiagnosticCount = maxDiagnostics } });

    private static (int Line, int Column) PositionOf(string source, string lineText)
    {
        var lines = source.Split('\n');
        var index = Array.FindIndex(lines, line => line == lineText);
        Assert.True(index >= 0, $"line '{lineText}' not found");
        Assert.Equal(index, Array.FindLastIndex(lines, line => line == lineText));
        return (index + 1, lineText.Length - lineText.TrimStart().Length + 1);
    }

    private static (int, int) Start(Diagnostic diagnostic)
        => (diagnostic.Span!.Value.Start.Line, diagnostic.Span.Value.Start.Column);

    private static Diagnostic A1Alone(string witness)
        => Assert.Single(Parse(StaticStructureWitnessSources.Cases[witness]).Diagnostics);

    // ── Test A: A1 plus an independent later-stage error ───────────────────

    [Fact]
    public void IndependentCollisionIsReportedAfterA1()
    {
        // The collision alone is a later-stage (completed-signature) diagnostic of an ordinary program.
        var alone = Parse(WrittenCollision + "\n5");
        var expected = Assert.Single(alone.Diagnostics);
        Assert.Equal(DiagnosticCode.ParameterPropertyCollision, expected.Code);

        var source = WithBefore(A32, WrittenCollision);
        var parsed = Parse(source);
        Assert.True(parsed.HasErrors);
        Assert.Collection(parsed.Diagnostics,
            a1 =>
            {
                Assert.Equal(DiagnosticCode.SelfDependentInferredParameters, a1.Code);
                Assert.Equal(A1Alone("A.3.2").Message, a1.Message);
                Assert.Equal(PositionOf(source, "P = {"), Start(a1));
            },
            collision =>
            {
                Assert.Equal(DiagnosticCode.ParameterPropertyCollision, collision.Code);
                Assert.Equal(expected.Message, collision.Message);
                Assert.Equal(expected.Span, collision.Span);
                Assert.Equal(PositionOf(source, "    cy = 1"), Start(collision));
            });
    }

    // ── Test B: the witnesses alone keep exactly their A1 diagnostic ───────

    [Fact]
    public void WitnessesAloneKeepExactlyTheirA1Diagnostic()
    {
        foreach (var witness in Witnesses)
        {
            var source = StaticStructureWitnessSources.Cases[witness];
            var parsed = Parse(source);
            // Only detection's A1 reports, one per rejected body (A.3.3a also rejects its R2).
            Assert.All(parsed.Diagnostics, d => Assert.Equal(DiagnosticCode.SelfDependentInferredParameters, d.Code));
            Assert.Equal(parsed.Diagnostics.Count, parsed.Diagnostics.Select(d => d.Span).Distinct().Count());
            var p = Assert.Single(parsed.Diagnostics, d => d.Message.Contains("'P'", StringComparison.Ordinal));
            Assert.Equal(PositionOf(source, "P = {"), Start(p));
            Assert.Equal(witness == "A.3.3a" ? 2 : 1, parsed.Diagnostics.Count);
            Assert.Equal(parsed.Diagnostics.Select(d => (d.Code, d.Message, d.Span)),
                FrontEndPipeline.Process(source).Diagnostics.Select(d => (d.Code, d.Message, d.Span)));
        }
    }

    // ── Test C: diagnostics that depend on the undecided signature stay suppressed ──

    [Theory]
    [InlineData("H = {\n    open P\n    0\n}")]                 // provider rule over P's undecided signature
    [InlineData("H = {\n    open P.R\n    R2\n}")]              // a target and a member through P
    [InlineData("G(a) = P + a")]                                // forwarding P into a closed list
    [InlineData("G(a) = P(a, a, a) + a")]                       // a call against P's undecided arity
    [InlineData("Empty = {\n    W = P\n}")]                     // output rule reached through P
    public void DependentDiagnosticsAreNotInvented(string dependent)
    {
        foreach (var source in new[] { WithBefore(A32, dependent), WithAfter(A32, dependent) })
        {
            var parsed = Parse(source);
            var diagnostic = Assert.Single(parsed.Diagnostics);
            Assert.Equal(DiagnosticCode.SelfDependentInferredParameters, diagnostic.Code);
            Assert.Equal(A1Alone("A.3.2").Message, diagnostic.Message);
        }
    }

    // ── Test D: declaration order ──────────────────────────────────────────

    [Fact]
    public void IndependentErrorsOnBothSidesFollowTheReportingPhases()
    {
        var a = WithAfter(WithBefore(A32, WrittenCollision), InferredCollision);
        var b = WithAfter(WithBefore(A32, InferredCollision), WrittenCollision);
        // The ordinary programs holding the same two declarations in the same relative order are
        // the order oracle: recovery reports the collision phase's own walk order, never a sort.
        var oracleA = WrittenCollision + "\n" + InferredCollision + "\n5";
        var oracleB = InferredCollision + "\n" + WrittenCollision + "\n5";
        foreach (var (source, oracle) in new[] { (a, oracleA), (b, oracleB) })
        {
            var parsed = Parse(source);
            // A1 is detection's report, so it precedes the later collision phase's reports.
            Assert.Equal(
                [DiagnosticCode.SelfDependentInferredParameters, DiagnosticCode.ParameterPropertyCollision, DiagnosticCode.ParameterPropertyCollision],
                parsed.Diagnostics.Select(d => d.Code));
            Assert.Equal(PositionOf(source, "P = {"), Start(parsed.Diagnostics[0]));
            var ordinary = Parse(oracle).Diagnostics;
            Assert.All(ordinary, d => Assert.Equal(DiagnosticCode.ParameterPropertyCollision, d.Code));
            // The messages state the parameter's line, which the A1 declaration shifts; compare the names.
            Assert.Equal(ordinary.Select(d => d.Message[..d.Message.IndexOf(" conflicts", StringComparison.Ordinal)]),
                parsed.Diagnostics.Skip(1).Select(d => d.Message[..d.Message.IndexOf(" conflicts", StringComparison.Ordinal)]));
            foreach (var collision in parsed.Diagnostics.Skip(1))
            {
                var property = collision.Message.Contains("'cy'", StringComparison.Ordinal) ? "    cy = 1" : "        iz = 1";
                Assert.Equal(PositionOf(source, property), Start(collision));
            }
            Assert.Equal(parsed.Diagnostics.Select(d => (d.Code, d.Message, d.Span)), Parse(source).Diagnostics.Select(d => (d.Code, d.Message, d.Span)));
        }

        // The same errors whichever side of the A1 declaration they are written on (the messages
        // differ only in the parameter line they state).
        static IEnumerable<(DiagnosticCode, string)> Detected(string source)
            => Parse(source).Diagnostics.Select(d => (d.Code, d.Message.Split(" The parameter is declared")[0])).Order();
        Assert.Equal(Detected(a), Detected(b));
    }

    // ── Test E: editor recovery ────────────────────────────────────────────

    [Fact]
    public void EditorModelsTheRejectedTreeWithA1FactsUnavailable()
    {
        var parsed = Parse(WithBefore(A32, WrittenCollision));
        Assert.True(parsed.HasErrors);
        var publication = parsed.Root.CompletedStructure!;
        Assert.Null(publication.Facts.Facts(publication.Entry!)!.Body);

        var model = SemanticModelBuilder.Build(parsed);
        var coll = Assert.Single(model.PropertyInfos, p => p.Name == "Coll");
        Assert.Equal(["cy"], coll.Parameters.Select(p => p.Name));
        Assert.Equal((1, 1), (coll.Declaration!.Span.Start.Line, coll.Declaration.Span.Start.Column));

        // The undecided inputs never appear as P's parameters.
        var p = Assert.Single(model.PropertyInfos, p => p.Name == "P");
        Assert.Empty(p.Parameters);
    }

    // ── Test F: the diagnostic budget ──────────────────────────────────────

    [Fact]
    public void RecoveredDiagnosticsObeyThePrefixLaw()
    {
        var source = WithAfter(WithBefore(A32, WrittenCollision), InferredCollision);
        var unbounded = Parse(source);
        Assert.Equal(3, unbounded.Diagnostics.Count);
        var tree = FrontEndFingerprint.ComputeParseResult(unbounded.Root, []);

        for (var limit = 1; limit <= 3; limit++)
        {
            var bounded = Parse(source, limit);
            Assert.True(bounded.HasErrors);
            Assert.Equal(tree, FrontEndFingerprint.ComputeParseResult(bounded.Root, []));
            var stored = limit < 3 ? bounded.Diagnostics.Take(limit) : bounded.Diagnostics;
            Assert.Equal(unbounded.Diagnostics.Take(limit).Select(d => (d.Code, d.Message, d.Span)), stored.Select(d => (d.Code, d.Message, d.Span)));
            if (limit < 3)
            {
                Assert.Equal(limit + 1, bounded.Diagnostics.Count);
                var marker = bounded.Diagnostics[^1];
                Assert.Equal(DiagnosticCode.DiagnosticCountExceeded, marker.Code);
                Assert.Null(marker.Span);
            }
            else
            {
                Assert.Equal(3, bounded.Diagnostics.Count);
            }
        }
    }

    [Fact]
    public void DroppedA1StillTriggersRecoveryAndCountsEveryReport()
    {
        // A lexical report fills the bag before detection. A1 and the recovered collision
        // must still count, even though neither fits in the stored list.
        var source = "@\n" + WithBefore(A32, WrittenCollision);
        var roomy = FrontEndPipeline.Process(source);
        var tiny = FrontEndPipeline.Process(source, new RunOptions
        {
            SourceProcessingLimits = new() { MaxDiagnosticCount = 1 },
        });
        var roomyBag = Assert.IsType<DiagnosticBag>(roomy.Diagnostics);
        var tinyBag = Assert.IsType<DiagnosticBag>(tiny.Diagnostics);
        Assert.Equal(3, roomyBag.ReportedCount);
        Assert.Equal(roomyBag.ReportedCount, tinyBag.ReportedCount);
        Assert.Equal(roomyBag.ReportedErrorCount, tinyBag.ReportedErrorCount);
        Assert.True(tinyBag.HasReportedErrors);
        Assert.True(tinyBag.HasReported(DiagnosticCode.SelfDependentInferredParameters));
        Assert.True(tinyBag.HasReported(DiagnosticCode.ParameterPropertyCollision));
        Assert.Equal(roomyBag[0], tinyBag[0]);
        Assert.Equal(2, tinyBag.Count);
        Assert.Equal(DiagnosticCode.DiagnosticCountExceeded, tinyBag[1].Code);
        Assert.Null(tinyBag[1].Span);
        Assert.True(tiny.HasErrors);
        Assert.Equal(FrontEndFingerprint.ComputeParseResult(roomy.ElaboratedRoot, []),
            FrontEndFingerprint.ComputeParseResult(tiny.ElaboratedRoot, []));
    }

    [Fact]
    public void MissingModuleKeepsA1RecoveryDiagnosticsWithheld()
    {
        var source = "M = load('https://mods.test/missing.kat')\n" + WithBefore(A32, WrittenCollision);
        var parsed = Parse(source);
        Assert.True(parsed.HasErrors);
        Assert.Equal(DiagnosticCode.LoadElaborationUnavailable, Assert.Single(parsed.Diagnostics).Code);
        Assert.NotNull(SemanticModelBuilder.Build(parsed));
    }

    // ── Test G: a deferred branch ──────────────────────────────────────────

    [Fact]
    public async Task SharedImportedCollisionUsesTheFirstImportSiteOnce()
    {
        var downloads = 0;
        var options = new RunOptions
        {
            AllowedHosts = ["mods.test"],
            DownloadCode = (_, _) =>
            {
                downloads++;
                return ValueTask.FromResult(WithBefore(A32, WrittenCollision));
            },
        };
        const string source = "A=load('https://mods.test/a.kat')\nB=load('https://mods.test/a.kat')\n5";
        var compiled = await FrontEndPipeline.ProcessAsync(source, options);
        Assert.True(compiled.HasErrors);
        Assert.Equal(1, downloads);
        Assert.Equal([DiagnosticCode.SelfDependentInferredParameters, DiagnosticCode.ParameterPropertyCollision],
            compiled.Diagnostics.Select(d => d.Code));
        Assert.All(compiled.Diagnostics, d => Assert.Equal((1, 1), Start(d)));
        Assert.Equal(compiled.Diagnostics[0].Span, compiled.Diagnostics[1].Span);
        Assert.DoesNotContain("The parameter is declared at line", compiled.Diagnostics[1].Message, StringComparison.Ordinal);
    }

    [Fact]
    public async Task DeferredBranchReportsItsIndependentCollisionAndPublishesNothing()
    {
        var downloads = 0;
        var options = new RunOptions
        {
            AllowedHosts = ["mods.test"],
            DownloadCode = (_, _) => { downloads++; return ValueTask.FromResult(A32); },
        };
        var source = "F(0)=0\nF(n)={M=load('https://mods.test/a.kat')\n" + WrittenCollision + "\n42}\nF(1)";
        var compiled = await FrontEndPipeline.ProcessAsync(source, options);
        Assert.False(compiled.HasErrors, string.Join('\n', compiled.Diagnostics.Select(d => d.Message)));
        Assert.Equal(0, downloads);
        var region = Assert.IsType<DeferredModuleRegion>(Assert.IsType<Algorithm.Conditional>(
            compiled.ElaboratedRoot.Properties.Single(p => p.Name == "F").Value).Branches[1].Body.DeferredRegion);
        var before = region.Structure!.Registry.StructuralContinuation;

        var (actual, _) = await Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(compiled.ElaboratedRoot), null);
        Assert.True(actual.IsError);
        Assert.Equal(KatLangErrorCode.SelfDependentInferredParameters, actual.Error.Code);
        var cause = actual.Error;
        while (cause is EvalError.WithContext context) cause = context.Inner;
        var failure = Assert.IsType<EvalError.ModuleRegionMaterializationFailed>(cause);
        Assert.Collection(failure.Diagnostics,
            // A module's declaration has no document span: its A1 is reported at the import site (M).
            a1 =>
            {
                Assert.Equal(DiagnosticCode.SelfDependentInferredParameters, a1.Code);
                Assert.Equal(A1Alone("A.3.2").Message, a1.Message);
                Assert.Equal((2, 7), Start(a1));
            },
            collision =>
            {
                Assert.Equal(DiagnosticCode.ParameterPropertyCollision, collision.Code);
                Assert.Equal(PositionOf(source, "    cy = 1"), Start(collision));
            });
        Assert.False(region.IsMaterialized);
        Assert.Same(before, region.Structure.Registry.StructuralContinuation);
        Assert.Equal(1, downloads);
    }
}
