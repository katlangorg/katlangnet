using System.Numerics;
using KatLang.Evaluation.Caching;

namespace KatLang.Tests.Interpolation;

/// <summary>Independent STR-02 boundary witnesses, with expectations fixed before execution.</summary>
public class InterpolationHostileReviewTests
{
    private sealed class CountingLinks(int count) : IReadOnlyList<ComparisonLink>
    {
        public int Reads { get; private set; }
        public int Count => count;
        public ComparisonLink this[int index]
        {
            get
            {
                Assert.InRange(index, 0, Count - 1);
                Reads++;
                return new(ComparisonOp.Eq, new Expr.Num(1));
            }
        }
        public IEnumerator<ComparisonLink> GetEnumerator()
        {
            for (var i = 0; i < Count; i++)
                yield return this[i];
        }
        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();
    }

    [Fact]
    public void DiagnosticHoleClassification_BoundsWideChildReads()
    {
        var links = new CountingLinks(100_000);
        var node = new Expr.InterpolatedString("", [new(new Expr.Comparison(new Expr.Num(1), links), "")]);
        var text = ExprNameRenderer.Render(node, ExprNameMode.DiagnosticName);
        Assert.EndsWith(ExprNameRenderer.TruncationMarker, text);
        Assert.InRange(text.Length, 1, ExprNameRenderer.MaxRenderedNameLength + 1);
        Assert.True(links.Reads < 8_192, $"A bounded diagnostic read {links.Reads} comparison links.");
    }

    [Theory]
    [InlineData("open \"https://katlang.org/{x}", DiagnosticCode.UnterminatedStringLiteral)]
    [InlineData("open \"https://katlang.org/{x", DiagnosticCode.UnterminatedInterpolationHole)]
    [InlineData("open \"https://katlang.org/a\\q\"", DiagnosticCode.InvalidStringEscape)]
    [InlineData("open \"https://katlang.org/a}b\"", DiagnosticCode.UnmatchedBraceInString)]
    [InlineData("M = load(\"https://katlang.org/a\\q\")", DiagnosticCode.InvalidStringEscape)]
    [InlineData("M = load(\"https://katlang.org/{x\n)", DiagnosticCode.UnterminatedInterpolationHole)]
    [InlineData("open 'https://katlang.org/a", DiagnosticCode.UnterminatedStringLiteral)]
    public async Task ARecoveredStringToken_IsNeverADownloadTarget(string source, DiagnosticCode code)
    {
        foreach (var diagnosticCapacity in new[] { 1, 2, 1000 })
        {
            var requests = new List<string>();
            var parsed = await Parser.ParseAsync(source, new RunOptions
            {
                SourceProcessingLimits = new() { MaxDiagnosticCount = diagnosticCapacity },
                DownloadCode = async (url, _) =>
                {
                    await Task.Yield();
                    requests.Add(url);
                    return "public V = 1";
                },
            });
            Assert.True(parsed.HasErrors);
            if (diagnosticCapacity > 0)
                Assert.Contains(parsed.Diagnostics, d => d.Code == code);
            Assert.True(requests.Count == 0, $"Malformed target invoked downloader: {string.Join(", ", requests)}");
        }
    }

    [Fact]
    public async Task RecoveryRefusal_SurvivesDiagnosticOverflow_AndPreservesValidImports()
    {
        var requests = new List<string>();
        var parsed = await Parser.ParseAsync("@\nopen \"https://katlang.org/a\\q\", \"https://katlang.org/good.kat\"\nV",
            new RunOptions
            {
                SourceProcessingLimits = new() { MaxDiagnosticCount = 1 },
                DownloadCode = (url, _) =>
                {
                    requests.Add(url);
                    return ValueTask.FromResult("public V = 1");
                },
            });
        Assert.True(parsed.HasErrors);
        Assert.Contains(parsed.Diagnostics, d => d.Code == DiagnosticCode.DiagnosticCountExceeded);
        Assert.DoesNotContain(parsed.Diagnostics, d => d.Code == DiagnosticCode.InvalidStringEscape);
        Assert.Equal(new[] { "https://katlang.org/good.kat" }, requests);
        _ = Semantics.SemanticModelBuilder.Build(parsed);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task MalformedDownloadedTargets_CannotTriggerASecondAcquisition(bool deferred)
    {
        var requests = new List<string>();
        var source = deferred
            ? "F(0) = { open 'https://katlang.org/outer.kat'\nV }\nF(0)"
            : "open 'https://katlang.org/outer.kat'\nV";
        var result = await KatLangEngine.RunAsync(source, new RunOptions
        {
            DownloadCode = async (url, _) =>
            {
                await Task.Yield();
                requests.Add(url);
                return "open \"https://katlang.org/{x\npublic V = 1";
            },
        });
        Assert.Equal(new[] { "https://katlang.org/outer.kat" }, requests);
        if (deferred)
            Assert.IsType<RunResult.EvalFailure>(result);
        else
            Assert.IsType<RunResult.ParseFailure>(result);
    }

    [Fact]
    public void LiteralRecoveryProvenance_SurvivesCopiesWithoutChangingStructuralEquality()
    {
        var provenance = SourceProvenance.ParseAllowingDiagnostics("\"https://katlang.org/a\\q\"");
        Assert.True(provenance.HasFrontEndErrors);
        var literal = Assert.IsType<Expr.StringLiteral>(Assert.Single(provenance.Root.Output));
        Assert.True(literal.IsRecoveryLiteral);
        var copy = literal with { Span = null };
        Assert.True(copy.IsRecoveryLiteral);
        Assert.Equal(new Expr.StringLiteral(copy.Value), copy);
        Assert.Equal(new Expr.StringLiteral(copy.Value).GetHashCode(), copy.GetHashCode());
    }

    [Fact]
    public void MalformedHoles_CannotConsumeTheFollowingDeclaration_OrBreakTheEditor()
    {
        var random = new Random(8022026);
        string[] pieces = ["(", ")", "[", "]", "{1}", "\"x\"", "'y'", "1", ",", ":", "=", "+", "~", "open", "*", "#", "@"];
        for (var sample = 0; sample < 512; sample++)
        {
            var hole = string.Join(" ", Enumerable.Range(0, 12).Select(_ => pieces[random.Next(pieces.Length)]));
            var source = "A = \"{" + hole + "}\"\nB = 17\nB";
            var provenance = SourceProvenance.ParseAllowingDiagnostics(source);
            Assert.True(provenance.HasFrontEndErrors, source);
            Assert.Contains(provenance.Root.Properties, p => p.Name == "B");
            _ = Semantics.SemanticModelBuilder.Build(provenance.Parsed);
        }
    }

    public static TheoryData<string, string, string[]> DemandPrograms => new()
    {
        { "F(a, b) = a\nF(\"{trace(1)}\", \"{trace(2)}\")", "1", ["trace(1)"] },
        { "F(a) = \"{a}{a}\"\nF(\"{tock()}\")", "11", ["tock#1"] },
        { "A = \"{tock()}\"\n\"{A}|{A()}|{A}\"", "1|2|1", ["tock#1", "tock#2"] },
        { "if(false, \"{trace(1)}\", \"{trace(2)}\")", "2", ["trace(2)"] },
        { "\"{['42', 42, 'true', true, 'a, b', ()]}\"", "[42, 42, true, true, a, b, ()]", [] },
        { "Need(x) = x + 1\nF(x) = \"{Need}:{x}\"\nF(3)", "4:3", [] },
        { "F(x) = { G = \"{x}\"\nH(x) = G\nH(99) }\nF(3)", "3", [] },
    };

    [Theory]
    [MemberData(nameof(DemandPrograms))]
    public async Task ValueAndEffectExpectations_HoldOnSixRoutes(string source, string text, string[] calls)
    {
        var observed = await SixRouteAgreement.OnEveryRouteAsync(source,
            render: value => Assert.IsType<Result.Str>(value).Value);
        Assert.Equal("ok", observed.Kind);
        Assert.Equal(text, observed.Value);
        Assert.Equal(calls, observed.HostCalls);
    }

    [Theory]
    [InlineData("F(x) = x\nF(\"{trace(1)}\", \"{trace(2)}\")", new string[0])]
    [InlineData("F(x) = x\nF(\"{trace(1)}\", \"{trace(2)}\"*)", new[] { "trace(2)" })]
    public async Task CardinalityPrecedesOrdinaryDemand_AndExplicitSpreadStillRuns(string source, string[] calls)
    {
        var observed = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("err", observed.Kind);
        Assert.Contains(observed.Errors, e => e.StartsWith("ArityMismatch:"));
        Assert.Equal(calls, observed.HostCalls);
    }

    [Fact]
    public async Task StructuralConversionFailure_PrecedesEveryLaterHole_OnSixRoutes()
    {
        var observed = await SixRouteAgreement.OnEveryRouteAsync(
            "\"{[1, 2]}{trace(3)}{1 div 0}\"", limits: new() { MaxStringLength = 4 });
        Assert.Equal("err", observed.Kind);
        Assert.Contains(observed.Errors, e => e.StartsWith("StringSizeLimitExceeded:"));
        Assert.Empty(observed.HostCalls);
    }

    [Fact]
    public async Task DeepHostValues_RenderIteratively_AndStopAtTheStringLimit()
    {
        Result value = new Result.Str("raw{\"\n}");
        const int depth = 20_000;
        for (var i = 0; i < depth; i++)
            value = i % 2 == 0 ? new Result.ListValue([value]) : new Result.SequenceValue([value, new Result.Bool(true)]);
        var operations = HostOperations.Create(HostOperation.Create("Deep", (_, _) => value));
        var root = new Expr.InterpolatedString("", [new(new Expr.Call(new Expr.Resolve("Deep"), []), "")]);
        var result = Evaluator.Run(root, operations, limits: null, randomSeed: null, CancellationToken.None);
        Assert.False(result.IsError);
        Assert.Equal(5 * depth + 7, Assert.IsType<Result.Str>(result.Value).Value.Length);
        var limited = Evaluator.Run(root, operations, new() { MaxStringLength = 999 }, null, CancellationToken.None);
        Assert.IsType<EvalError.StringSizeLimitExceeded>(limited.Error);
        var twin = await Evaluator.RunCountedAsync(root, new RunScopedAsyncZeroArgPropertyResultCache(),
            new() { MaxStringLength = 999 }, operations, null, CancellationToken.None);
        Assert.IsType<EvalError.StringSizeLimitExceeded>(twin.Error);
    }

    [Fact]
    public void ExtremeNumbersAndHostUnicode_UseRawCanonicalText()
    {
        var numbers = new[] { Decimal128.MaxValue, Decimal128.Epsilon, Decimal128.NegativeZero,
            Decimal128.NaN, Decimal128.PositiveInfinity, Decimal128.NegativeInfinity };
        foreach (var number in numbers)
        {
            var atom = new Expr.Num(number);
            var expected = Evaluator.Run(new Expr.DotCall(atom, "string"));
            Assert.False(expected.IsError);
            var actual = Evaluator.Run(new Expr.InterpolatedString("", [new(atom, "")]));
            Assert.False(actual.IsError);
            Assert.Equal(expected.Value, actual.Value);
        }
        const string text = "\uD800\u0000\r\n{\"}\\\u202E";
        var unicode = Evaluator.Run(new Expr.InterpolatedString("", [new(new Expr.StringLiteral(text), "")]));
        Assert.Equal(text, Assert.IsType<Result.Str>(unicode.Value).Value);
    }
}
