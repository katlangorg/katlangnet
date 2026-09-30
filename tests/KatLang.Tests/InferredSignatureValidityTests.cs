using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// X-02 (decided September 30 2026): INFERRED SIGNATURES ARE HELD TO THE RULES OF WRITTEN ONES.
/// Formula lifting composes an owner's signature from its callees' contracts; a composition that
/// no source may declare — two collecting parameters at one pattern level, from
/// <c>C1(a, *p)</c> and <c>C2(b, *q)</c> in <c>K = C1 + C2</c> — is the definition's front-end
/// error (<see cref="DiagnosticCode.InvalidCollectingBinding"/>), reported when the definition is
/// elaborated. Before the fix the front end silently inferred <c>K(a, *p, b, *q)</c>: a call threw
/// the binding planner's <see cref="InvalidOperationException"/> out of
/// <see cref="KatLangEngine.Run(string, RunOptions?)"/> on every route, a bare read misreported
/// "expects 3 parameters", and the editor model threw while building the signature. One rule
/// decides validity everywhere (<see cref="ParameterPattern.FindSignatureViolation"/>, Lean
/// <c>ParameterPattern.signatureViolation?</c>): the parser's rules for a written head, the
/// resolver's check of an inferred one, and — for the collector rule — the pre-evaluation
/// validation of a host-built tree.
/// </summary>
public class InferredSignatureValidityTests
{
    private const string Callees = "C1(a, *p) = a\nC2(b, *q) = b\n";

    private static Task<RepeatedNameConstraintTests.Observation> OnEveryRoute(string source)
        => RepeatedNameConstraintTests.OnEveryRouteAsync(source);

    private static Algorithm.User Owner(Algorithm.User root, string name)
        => Assert.IsType<Algorithm.User>(Assert.Single(root.Properties, property => property.Name == name).Value);

    private static string Signature(Algorithm.User algorithm)
        => string.Join(", ", algorithm.ParameterPatterns.Select(static pattern => pattern.DisplayName));

    private static Diagnostic SingleError(string source)
    {
        var diagnostics = SourceProvenance.ExpectFrontEndError(source);
        return Assert.Single(diagnostics, static diagnostic => diagnostic.Severity == DiagnosticSeverity.Error);
    }

    // ── 1. Distinct collectors: rejected at the definition, in every lifting position ──────

    /// <summary>
    /// (id, definitions, offending reference line/column/length). The root never calls <c>K</c>:
    /// the invalid contract exists at the definition, so the front end rejects it there.
    /// </summary>
    public static TheoryData<string, string, int, int, int> DistinctCollectorDefinitions => new()
    {
        { "binary", Callees + "K = C1 + C2\n0", 3, 10, 2 },
        { "list", Callees + "K = [C1, C2]\n0", 3, 10, 2 },
        { "index", Callees + "K = C1:0 + C2:0\n0", 3, 12, 2 },
        { "math-arguments", Callees + "K = abs(C1) + abs(C2)\n0", 3, 19, 2 },
        { "nested-string-receiver", Callees + "K = (C1 + C2).string\n0", 3, 11, 2 },
        { "comparison", Callees + "K = C1 < C2\n0", 3, 10, 2 },
        { "transitive", Callees + "M = C1 + 0\nN = C2 + 0\nK = M + N\n0", 5, 9, 1 },
        { "leading-and-trailing", "L(*p, a) = a\nT(b, *q) = b\nK = L + T\n0", 3, 9, 1 },
        { "middle-and-trailing", "Mid(a, *p, c) = a\nT(b, *q) = b\nK = Mid + T\n0", 3, 11, 1 },
        { "fixed-callee-between", Callees + "F(x) = x\nK = C1 + F + C2\n0", 4, 14, 2 },
        { "nested-collector-beside-two-top-level", "T1(a, *p) = a\nN((b, *q)) = b\nT2(c, *r) = c\nK = T1 + N + T2\n0", 4, 14, 2 },
    };

    [Theory]
    [MemberData(nameof(DistinctCollectorDefinitions))]
    public void DistinctCollectingParameters_AreRejectedWhenTheDefinitionIsElaborated(
        string id, string source, int line, int column, int length)
    {
        var error = SingleError(source);
        Assert.True(error.Code == DiagnosticCode.InvalidCollectingBinding, $"{id}: {error.Code}: {error.Message}");
        Assert.Equal(new SourceSpan(new SourcePosition(line, column), new SourcePosition(line, column + length)), error.Span);
        Assert.StartsWith("Formula lifting cannot complete this definition's signature", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void MinimalWitness_NamesBothCollectorsAndTheCalleeToCallExplicitly()
    {
        var error = SingleError(Callees + "K = C1 + C2\n0");
        Assert.Equal(
            string.Join(
                Environment.NewLine,
                "Formula lifting cannot complete this definition's signature: it would need the collecting parameters "
                    + "'*p' (needed by 'C1') and '*q' (needed by 'C2') at the same pattern level, but a signature may "
                    + "declare at most one collecting parameter per pattern level.",
                "Call 'C2' with explicit arguments, or declare this definition's parameters explicitly."),
            error.Message);

        var three = SingleError("C1(a, *p) = a\nC2(b, *q) = b\nC3(c, *r) = c\nK = C1 + C2 + C3\n0");
        Assert.Contains("'*p' (needed by 'C1'), '*q' (needed by 'C2'), and '*r' (needed by 'C3')", three.Message, StringComparison.Ordinal);
    }

    // ── 2. No host exception, no evaluator entry ──────────────────────────────────────────

    public static TheoryData<string> CallingPrograms => new()
    {
        Callees + "K = C1 + C2\nK(1, 2)",
        Callees + "K = C1 + C2\nK",
        Callees + "K = C1 + C2\nmap([1, 2], K)",
        Callees + "K = [C1, C2]\nK(1, 2)",
        Callees + "M = C1 + 0\nN = C2 + 0\nK = M + N\nK(1, 2)",
    };

    [Theory]
    [MemberData(nameof(CallingPrograms))]
    public async Task EveryEngineRoute_ReportsTheFrontEndError_WithoutAHostException(string source)
    {
        foreach (var run in new Func<Task<RunResult>>[]
        {
            () => Task.FromResult(KatLangEngine.Run(source)),
            () => KatLangEngine.RunAsync(source),
        })
        {
            var result = await run();
            var failure = Assert.IsType<RunResult.ParseFailure>(result);
            Assert.Contains(failure.Errors, static error => error.Code == KatLangErrorCode.InvalidCollectingBinding);
        }
    }

    [Fact]
    public void TheRecoveredTree_CarriesOnlyValidSignatures_AndTheEditorModelBuilds()
    {
        var parsed = Parser.Parse(Callees + "K = C1 + C2\nK(1, 2)");
        Assert.True(parsed.HasErrors);

        // The recovery is the parser's shape for a written head: the first collector per level
        // stays, a later one becomes fixed — error recovery only, never the program's meaning.
        var k = Owner(parsed.Root, "K");
        Assert.Equal("a, *p, b, q", Signature(k));
        Assert.Null(ParameterPattern.FindSignatureViolation(k.ParameterPatterns));

        // Before the fix the editor model threw while building K's binding plan.
        var model = SemanticModelBuilder.Build(parsed);
        Assert.NotNull(model);
    }

    // ── 3. Controls: one binding per name, one collector per callable ─────────────────────

    [Fact]
    public async Task SameCollectingName_IsOneLiftedBinding()
    {
        var parsed = SourceProvenance.ParseValid("C1(a, *rest) = a\nC2(b, *rest) = b\nK = C1 + C2\n0");
        Assert.Equal("a, *rest, b", Signature(Owner(parsed.Root, "K")));
        Assert.Equal("ok 4", (await OnEveryRoute("C1(a, *rest) = a\nC2(b, *rest) = b\nK = C1 + C2\nK(1, 2, 3)")).Outcome);
    }

    [Fact]
    public async Task SameCallableTwice_IsOneCollector()
    {
        const string Definitions = "C(n, *xs) = n + xs.count\nK = C + C\n";
        Assert.Equal("n, *xs", Signature(Owner(SourceProvenance.ParseValid(Definitions + "0").Root, "K")));
        Assert.Equal("ok 6", (await OnEveryRoute(Definitions + "K(1, 2, 3)")).Outcome);
    }

    [Fact]
    public async Task CollectorOnlyCallee_IsNeverLifted_SoItNeverComposesACollector()
    {
        // Q-03: a callable that accepts zero supplied arguments is read, never lifted.
        const string Definitions = "C(*xs) = xs.count\nD(*ys) = ys.count + 10\nK = C + D\n";
        Assert.Equal("", Signature(Owner(SourceProvenance.ParseValid(Definitions + "0").Root, "K")));
        Assert.Equal("ok 10", (await OnEveryRoute(Definitions + "K")).Outcome);
    }

    public static TheoryData<string, string, string, string> ValidCompositions => new()
    {
        // One top-level collector beside fixed parameters, at every position.
        { "fixed-then-trailing", "F(x) = x\nT(d, *r) = d + r.count\nK = F + T\n", "x, d, *r", "K(1, 2, 3, 4) => ok 5" },
        { "leading-collector", "L(*p, a) = a + p.count\nF(x) = x\nK = L + F\n", "*p, a, x", "K(1, 2, 3, 4) => ok 9" },
        { "middle-collector", "Mid(a, *p, c) = a + c + p.count\nF(x) = x\nK = Mid + F\n", "a, *p, c, x", "K(1, 2, 3, 4, 5) => ok 12" },
        // A collector nested in its own group is that group's level.
        { "two-nested-collectors", "N1((a, *p)) = a\nN2((b, *q)) = b\nK = N1 + N2\n", "(a, *p), (b, *q)", "K((1, 2), (3, 4)) => ok 4" },
        { "nested-and-top-level", "N((a, *p)) = a\nT(d, *r) = d\nK = N + T\n", "(a, *p), d, *r", "K((1, 2), 3, 4) => ok 4" },
    };

    [Theory]
    [MemberData(nameof(ValidCompositions))]
    public async Task OneCollectorPerLevel_StaysValid(string id, string definitions, string signature, string call)
    {
        Assert.True(Signature(Owner(SourceProvenance.ParseValid(definitions + "0").Root, "K")) == signature, id);
        var (program, expected) = (call[..call.IndexOf(" => ", StringComparison.Ordinal)], call[(call.IndexOf(" => ", StringComparison.Ordinal) + 4)..]);
        Assert.Equal(expected, (await OnEveryRoute(definitions + program)).Outcome);
    }

    // ── 4. ONE validity rule: the parser's verdict on a written head is the validator's ────

    /// <summary>(written head, the patterns it describes, the parser's verdict).</summary>
    public static TheoryData<string, ParameterPattern[], DiagnosticCode?> WrittenHeads => new()
    {
        { "F(a, *p) = 1", [Capture("a"), Collecting("p")], null },
        { "F(a, *p, *q) = 1", [Capture("a"), Collecting("p"), Collecting("q")], DiagnosticCode.InvalidCollectingBinding },
        { "F((a, *p, *q)) = 1", [new SequenceValueParameterPattern([Capture("a"), Collecting("p"), Collecting("q")])], DiagnosticCode.InvalidCollectingBinding },
        { "F((a, *p), *q) = 1", [new SequenceValueParameterPattern([Capture("a"), Collecting("p")]), Collecting("q")], null },
        { "F([a, *p], [b, *q]) = 1", [new ListValueParameterPattern([Capture("a"), Collecting("p")]), new ListValueParameterPattern([Capture("b"), Collecting("q")])], null },
        { "F(x, *x) = 1", [Capture("x"), Collecting("x")], DiagnosticCode.InvalidCollectingBinding },
        { "F(x, x) = 1", [Capture("x"), Capture("x")], null },
        { "F((x)) = 1", [new SequenceValueParameterPattern([Capture("x")])], DiagnosticCode.SingletonSequencePattern },
        { "F((*xs)) = 1", [new SequenceValueParameterPattern([Collecting("xs")])], null },
        { "F([x]) = 1", [new ListValueParameterPattern([Capture("x")])], null },
    };

    [Theory]
    [MemberData(nameof(WrittenHeads))]
    public void TheValidator_DecidesExactlyWhatTheParserDecidesForAWrittenHead(
        string head, ParameterPattern[] patterns, DiagnosticCode? parserVerdict)
    {
        var parsed = Parser.Parse(head + "\n0");
        var errors = parsed.Diagnostics.Where(static diagnostic => diagnostic.Severity == DiagnosticSeverity.Error).ToList();
        if (parserVerdict is null)
            Assert.True(errors.Count == 0, $"{head}: {string.Join("; ", errors)}");
        else
            Assert.True(errors.Count == 1 && errors[0].Code == parserVerdict, $"{head}: {string.Join("; ", errors)}");

        DiagnosticCode? validatorVerdict = ParameterPattern.FindSignatureViolation(patterns) switch
        {
            null => null,
            ParameterSignatureViolation.SingletonSequencePattern => DiagnosticCode.SingletonSequencePattern,
            ParameterSignatureViolation.MultipleCollectingAtOneLevel => DiagnosticCode.InvalidCollectingBinding,
            ParameterSignatureViolation.RepeatedNameIncludesCollecting => DiagnosticCode.InvalidCollectingBinding,
            var unknown => throw new ArgumentOutOfRangeException(nameof(patterns), unknown, "Unknown signature violation."),
        };
        Assert.True(parserVerdict == validatorVerdict, $"{head}: parser {parserVerdict}, validator {validatorVerdict}");
    }

    [Fact]
    public void TheValidator_ReportsTheFirstRuleInTheParsersOrder()
    {
        Assert.Equal(ParameterSignatureViolation.MultipleCollectingAtOneLevel,
            ParameterPattern.FindSignatureViolation([Capture("a"), Collecting("p"), Collecting("q")]));
        Assert.Equal(ParameterSignatureViolation.RepeatedNameIncludesCollecting,
            ParameterPattern.FindSignatureViolation([Capture("x"), Collecting("x")]));
        // The singleton rule precedes the collector rules.
        Assert.Equal(ParameterSignatureViolation.SingletonSequencePattern,
            ParameterPattern.FindSignatureViolation([new SequenceValueParameterPattern([Capture("x")]), Collecting("p"), Collecting("q")]));
        // Two collectors outrank a repeated collecting name.
        Assert.Equal(ParameterSignatureViolation.MultipleCollectingAtOneLevel,
            ParameterPattern.FindSignatureViolation([Collecting("x"), Capture("x"), Collecting("q")]));
    }

    [Fact]
    public void TheRecovery_KeepsTheFirstCollectorOfEveryLevel_AndOnlyChangesWhatItMust()
    {
        IReadOnlyList<ParameterPattern> valid = [Capture("a"), Collecting("p"), new SequenceValueParameterPattern([Capture("b"), Collecting("q")])];
        Assert.Same(valid, ParameterPattern.KeepFirstCollectingCapturePerLevel(valid));

        var recovered = ParameterPattern.KeepFirstCollectingCapturePerLevel(
            [Collecting("p"), Capture("a"), Collecting("q"), new ListValueParameterPattern([Collecting("r"), Collecting("s")])]);
        Assert.Equal("*p, a, q, [*r, s]", string.Join(", ", recovered.Select(static pattern => pattern.DisplayName)));
        Assert.Null(ParameterPattern.FindSignatureViolation(recovered));
    }

    [Fact]
    public void SharedTemplateFacts_ComposeTheValidatorsVerdict()
    {
        var interner = new ImplicitSignatureTemplateInterner(observations: null);
        ParameterPattern[][] lists =
        [
            [Capture("a")],
            [Collecting("p")],
            [Capture("a"), Collecting("p")],
            [new SequenceValueParameterPattern([Capture("x")])],
            [new ListValueParameterPattern([Collecting("r"), Collecting("s")])],
            [Capture("x"), Collecting("x")],
        ];

        foreach (var tail in lists)
        {
            var flatTail = interner.InternFlat(tail);
            Assert.Equal(ParameterPattern.FindSignatureViolation(tail.ToList()), flatTail.Facts.SignatureViolation);
            foreach (var head in lists)
            {
                // Compose requires disjoint names; rename the head apart from the tail.
                var renamedHead = head.Select(static pattern => Renamed(pattern, "h_")).ToArray();
                var composed = ImplicitSignatureTemplate.Compose(renamedHead, flatTail);
                var materialized = renamedHead.Concat(tail).ToList();
                Assert.Equal(ParameterPattern.FindSignatureViolation(materialized), composed.Facts.SignatureViolation);
            }
        }
    }

    // ── 5. A host-built tree: the collector rule is a pre-evaluation violation ───────────

    [Fact]
    public void HostBuiltSignatureWithTwoCollectors_IsIllegalBeforeEvaluation_NeverAPlannerException()
    {
        var k = new Algorithm.User(
            Parent: null,
            ParameterPatterns: [Capture("a"), Collecting("p"), Capture("b"), Collecting("q")],
            Opens: [],
            Properties: [],
            Output: OutputBundle.From([new Expr.Param("a")]));
        var root = new Algorithm.User(
            Parent: null,
            ParameterPatterns: [],
            Opens: [],
            Properties: [new Property("K", k)],
            Output: OutputBundle.From([new Expr.Call(new Expr.Resolve("K"), OutputBundle.From([new Expr.Num(1), new Expr.Num(2)]))]));

        var result = Evaluator.RunCounted(new Expr.AlgorithmExpr(root));
        Assert.True(result.IsError);
        var illegal = Assert.IsType<EvalError.IllegalInEval>(result.Error);
        Assert.Equal("Only one collecting binding is allowed per pattern level.", illegal.Reason);
    }

    [Fact]
    public void HostBuiltNestedLevelWithTwoCollectors_IsIllegalBeforeEvaluation()
    {
        var k = new Algorithm.User(
            Parent: null,
            ParameterPatterns: [new ListValueParameterPattern([Collecting("p"), Collecting("q")])],
            Opens: [],
            Properties: [],
            Output: OutputBundle.From([new Expr.Num(0)]));
        var root = new Algorithm.User(
            Parent: null,
            ParameterPatterns: [],
            Opens: [],
            Properties: [new Property("K", k)],
            Output: OutputBundle.From([new Expr.Num(1)]));

        var result = Evaluator.RunCounted(new Expr.AlgorithmExpr(root));
        Assert.IsType<EvalError.IllegalInEval>(result.Error);
    }

    private static CaptureParameterPattern Capture(string name) => new(name);

    private static CaptureParameterPattern Collecting(string name) => new(name, Kind: ParameterKind.Collecting);

    private static ParameterPattern Renamed(ParameterPattern pattern, string prefix) => pattern switch
    {
        CaptureParameterPattern capture => new CaptureParameterPattern(prefix + capture.Name, Kind: capture.Kind),
        _ => ParameterPattern.WithStructuralItems(pattern, ParameterPattern.StructuralItems(pattern)!.Select(item => Renamed(item, prefix)).ToList()),
    };
}
