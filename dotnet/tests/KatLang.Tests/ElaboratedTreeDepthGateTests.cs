using System.Numerics;
using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// THE ELABORATED TREE IS GATED TOO (finding <c>lifting-signatures-elaboration-depth-past-gate</c> of the 2026-11-21
/// adversarial audit). Elaboration deepens a tree in proportion to its input: formula lifting and bare forwarding write
/// calls whose argument rebuilds the callee's nested parameter pattern, and declaration-level output spreading inserts a
/// spread per marked call. So the front end judges the tree it PUBLISHES with the same elaboration gate that judges the
/// tree it receives — <see cref="EvaluationLimits.MaxSupportedAstDepth"/> weighted units, fully recursive profile,
/// <see cref="DiagnosticCode.AstDepthLimitExceeded"/> into the operation's bag, the placeholder root. A deferred branch's
/// materialized body stays the run's to judge (MOD-10). Before, such a program parsed with no diagnostic, made
/// <see cref="SemanticModelBuilder.Build(ParseResult)"/> throw <see cref="ArgumentException"/> (documented never to happen
/// for a parser result), and failed or even ran at evaluation while its written counterpart was a parse failure. Every
/// program here is parsed on a large thread, so an outcome is the structural verdict, never a host-stack refusal.
/// </summary>
public class ElaboratedTreeDepthGateTests
{
    private const int LargeStack = 16 * 1024 * 1024;
    private const string ModuleUrl = "https://katlang.org/elaborated-depth/m.kat";

    private static int Ceiling => EvaluationLimits.MaxSupportedAstDepth;

    private static T OnLargeStack<T>(Func<T> body) => AstStructuralDepthProcessTests.RunOnThreadWithStack(LargeStack, body);

    // ── Sources ─────────────────────────────────────────────────────────────

    /// <summary><c>A(A(…A(inner)…))</c> with <paramref name="calls"/> calls; <paramref name="star"/> writes <c>*</c> after every inner call.</summary>
    private static string NestedCalls(int calls, bool star, string inner = "1")
    {
        var expression = inner;
        for (var level = 0; level < calls; level++)
            expression = $"A({expression}{(star && level > 0 ? "*" : "")})";
        return expression;
    }

    /// <summary>A marked identity called <paramref name="calls"/> deep, as a root row or as a property's row.</summary>
    private static string Marked(int calls, bool inProperty = false, string inner = "1")
        => "A(x)* = x\n" + (inner == "1" ? "" : "y = 5\n")
            + (inProperty ? "K = " + NestedCalls(calls, star: false, inner) + "\nK\n" : NestedCalls(calls, star: false, inner) + "\n");

    /// <summary>The written counterpart of <see cref="Marked"/>: no marker, and <c>*</c> after every eligible call.</summary>
    private static string Explicit(int calls, bool inProperty = false, string inner = "1")
        => "A(x) = x\n" + (inner == "1" ? "" : "y = 5\n")
            + (inProperty ? "K = " + NestedCalls(calls, star: true, inner) + "*\nK\n" : NestedCalls(calls, star: true, inner) + "*\n");

    /// <summary>A written spread chain the evaluator walks for free (a zero-weight join spine over a leaf).</summary>
    private static readonly string SpreadChain = "y" + new string('*', 250);

    /// <summary><c>(a0, (a1, … (a{levels-1}, a{levels})…))</c>, a structural parameter pattern of <paramref name="levels"/> levels.</summary>
    private static string NestedPattern(int levels)
    {
        var pattern = $"a{levels}";
        for (var i = levels - 1; i >= 0; i--)
            pattern = $"(a{i}, {pattern})";
        return pattern;
    }

    /// <summary>A module whose public <c>X</c> is <paramref name="calls"/> marked calls around a free spread chain.</summary>
    private static string ModuleSource(int calls) => "A(x)* = x\ny = 5\npublic X = " + NestedCalls(calls, star: false, SpreadChain) + "\n";

    // ── Assertions ──────────────────────────────────────────────────────────

    /// <summary>The weighted fully recursive height of an elaborated root: the profile the gate and the editor judge.</summary>
    private static int Height(Algorithm root)
    {
        Assert.Null(AstStructuralPreflight.CheckMeasuringHeight(
            root, AstStructuralPreflight.RawSyntaxMaxAstDepth, AstConsumerProfile.FullyRecursive, out var height));
        return height;
    }

    /// <summary>The height the raw gate measured for the written tree, before elaboration.</summary>
    private static int WrittenHeight(string source)
    {
        var syntax = OnLargeStack(() => Parser.ParseSyntax(source));
        Assert.False(syntax.HasErrors);
        return syntax.FullyRecursiveHeight;
    }

    /// <summary>A clean parse whose published root is within the ceiling, which the editor models.</summary>
    private static ParseResult AssertAdmitted(string source)
    {
        var parsed = OnLargeStack(() => SourceProvenance.ParseValid(source).Parsed);
        Assert.True(Height(parsed.Root) <= Ceiling);
        OnLargeStack(() => SemanticModelBuilder.Build(parsed));
        return parsed;
    }

    /// <summary>
    /// The elaboration gate's refusal, after <paramref name="before"/>: the one structural diagnostic with the written tree's
    /// message, the placeholder root, and a semantic model of that root (never an exception).
    /// </summary>
    private static Diagnostic AssertRefused(string source, params DiagnosticCode[] before)
    {
        var parsed = OnLargeStack(() => Parser.Parse(source));
        Assert.Equal([.. before, DiagnosticCode.AstDepthLimitExceeded], parsed.Diagnostics.Select(d => d.Code));
        var diagnostic = parsed.Diagnostics[^1];
        Assert.Equal(AstStructuralPreflight.ParseDepthDiagnosticMessage(Ceiling), diagnostic.Message);
        Assert.Empty(parsed.Root.Properties);
        Assert.Empty(parsed.Root.Output);
        Assert.Empty(OnLargeStack(() => SemanticModelBuilder.Build(parsed)).IdentifierResolutions);
        return diagnostic;
    }

    /// <summary>The source text a diagnostic's span starts at, to the end of its line.</summary>
    private static string TextAt(string source, Diagnostic diagnostic)
    {
        var span = Assert.NotNull(diagnostic.Span);
        return source.Split('\n')[span.Start.Line - 1][(span.Start.Column - 1)..];
    }

    private static void AssertEngineRefusesAtParse(string source)
    {
        var failure = Assert.IsType<RunResult.ParseFailure>(OnLargeStack(() => KatLangEngine.Run(source)));
        var error = failure.Errors[^1];
        Assert.Equal(KatLangErrorCode.AstDepthLimitExceeded, error.Code);
        // A front-end refusal is never a resource limit of a run (owner decision, 2026-11-26).
        Assert.False(error.IsResourceLimit);
    }

    private static void AssertEngineValue(string source, decimal expected)
    {
        var success = Assert.IsType<RunResult.Success>(OnLargeStack(() => KatLangEngine.Run(source)));
        Assert.Equal([(Decimal128)expected], success.Atoms);
    }

    // ── Output spreading: a marked program IS its explicit-`*` counterpart at the ceiling too ──

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MarkedCalls_JustBelowTheCeiling_ElaborateToTheirExplicitCounterpart(bool inProperty)
    {
        // 99 nested marked calls: the inserted spreads take the tree to the ceiling (299 as a row, 300 in a property),
        // exactly the height of the written counterpart, which the gate judges as written source.
        var marked = AssertAdmitted(Marked(99, inProperty));
        var written = AssertAdmitted(Explicit(99, inProperty));

        Assert.Equal(inProperty ? Ceiling : Ceiling - 1, Height(marked.Root));
        Assert.Equal(Height(written.Root), Height(marked.Root));
        Assert.Equal(Height(written.Root), WrittenHeight(Explicit(99, inProperty)));
        Assert.Equal(inProperty ? 201 : 200, WrittenHeight(Marked(99, inProperty)));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MarkedCalls_PastTheCeiling_AreRefusedExactlyAsTheirExplicitCounterpart(bool inProperty)
    {
        // 100 calls: 202 written units elaborate to 302 (303 in a property). Before the gate judged the elaborated tree, the
        // parse was clean, Build threw ArgumentException and the engine reported an evaluation failure.
        var marked = AssertRefused(Marked(100, inProperty));
        var written = AssertRefused(Explicit(100, inProperty));

        // The same diagnostic at the same written call: the inserted spread takes the call's span, as a written one does.
        Assert.Equal(written.Message, marked.Message);
        Assert.Equal(written.Span, marked.Span);
        Assert.StartsWith("A(", TextAt(Marked(100, inProperty), marked), StringComparison.Ordinal);
    }

    [Fact]
    public void MarkedCalls_EveryPublicRoute_AgreesWithTheExplicitCounterpart()
    {
        foreach (var source in new[] { Marked(100), Explicit(100) })
        {
            AssertEngineRefusesAtParse(source);
            var (parsed, run) = OnLargeStack(() => (Parser.ParseAsync(source).GetAwaiter().GetResult(),
                KatLangEngine.RunAsync(source).GetAwaiter().GetResult()));
            Assert.Equal([DiagnosticCode.AstDepthLimitExceeded], parsed.Diagnostics.Select(d => d.Code));
            var parseError = Assert.Single(Assert.IsType<RunResult.ParseFailure>(run).Errors);
            Assert.Equal(KatLangErrorCode.AstDepthLimitExceeded, parseError.Code);
            Assert.False(parseError.IsResourceLimit);
        }

        // Just below, both forms parse and are refused alike by the evaluator's own profile (its spread re-entry weight):
        // the same code, as the run's resource limit.
        foreach (var source in new[] { Marked(99), Explicit(99) })
        {
            var failure = Assert.IsType<RunResult.EvalFailure>(OnLargeStack(() => KatLangEngine.Run(source)));
            var error = Assert.Single(failure.Errors);
            Assert.Equal(KatLangErrorCode.AstDepthLimitExceeded, error.Code);
            Assert.True(error.IsResourceLimit);
        }
    }

    [Fact]
    public void TheRecordedCompatibilityWitness_IsAParseFailure_NotAResourceLimit()
    {
        // 20 marked calls around a free spread chain: 292 written units elaborate to 312, the written height of the explicit
        // counterpart. The evaluator's profile weighs the chain nothing, so this program RAN (5) while Build threw before
        // the gate judged the elaborated tree. Owner decision, 2026-11-26: every public source route now refuses it at parse.
        var witness = Marked(20, inner: SpreadChain);
        Assert.Equal(292, WrittenHeight(witness));
        Assert.Equal(312, WrittenHeight(Explicit(20, inner: SpreadChain)));
        AssertRefused(witness);

        var (run, runAsync) = OnLargeStack(() => (KatLangEngine.Run(witness), KatLangEngine.RunAsync(witness).GetAwaiter().GetResult()));
        foreach (var result in new[] { run, runAsync })
        {
            var error = Assert.Single(Assert.IsType<RunResult.ParseFailure>(result).Errors);
            Assert.Equal(KatLangErrorCode.AstDepthLimitExceeded, error.Code);
            Assert.False(error.IsResourceLimit);
        }
    }

    // ── Formula lifting and bare forwarding ─────────────────────────────────

    [Fact]
    public void FormulaLifting_ItsConstantGrowth_IsJudgedAtTheCeiling()
    {
        // Lifting turns the bare `Inc` into `Inc(x)`: two units. 295 prefix minus signs elaborate to exactly the ceiling.
        static string Lifted(int minus) => "Inc(x) = x + 1\nG = " + new string('-', minus) + "Inc\nG(1)\n";
        static string Written(int minus) => "Inc(x) = x + 1\nG(x) = " + new string('-', minus) + "Inc(x)\nG(1)\n";

        Assert.Equal(Ceiling, Height(AssertAdmitted(Lifted(295)).Root));

        var lifted = AssertRefused(Lifted(296));
        var written = AssertRefused(Written(296));
        Assert.StartsWith("Inc", TextAt(Lifted(296), lifted), StringComparison.Ordinal);
        Assert.StartsWith("Inc", TextAt(Written(296), written), StringComparison.Ordinal);
        AssertEngineRefusesAtParse(Lifted(296));
    }

    [Theory]
    [InlineData("lifting")]
    [InlineData("forwarding")]
    public void ARebuiltParameterPattern_PastTheCeiling_IsRefusedAtTheReference_EvenInAnUnusedHelper(string route)
    {
        // `F`'s pattern of P levels costs P units as a pattern and twice that as the argument the front end rebuilds at the
        // reference — formula lifting (`G = F + 0`) or bare forwarding (`G(<pattern>) = F`). `G` is never called.
        string Source(int levels) => route == "lifting"
            ? $"F({NestedPattern(levels)}) = a0\nG = F + 0\n1\n"
            : $"F({NestedPattern(levels)}) = a0\nG({NestedPattern(levels)}) = F\n1\n";

        var admitted = AssertAdmitted(Source(147));
        Assert.Equal(route == "lifting" ? Ceiling : Ceiling - 1, Height(admitted.Root));
        Assert.Equal(150, WrittenHeight(Source(147)));

        var refused = AssertRefused(Source(148));
        var reference = TextAt(Source(148), refused);
        Assert.True(reference == "F + 0" || reference == "F", $"positioned at the written reference, found '{reference}'");
        AssertEngineRefusesAtParse(Source(148));
    }

    [Fact]
    public void BareForwarding_ExactlyAtTheCeiling_IsAdmitted()
    {
        // Bare forwarding adds two units per pattern level, so the root-level helper above steps from 299 to 301. One block
        // around the helper lands the rebuilt pattern exactly on the ceiling, which passes; one level more is refused.
        static string Source(int levels) => $"F({NestedPattern(levels)}) = a0\nK = {{\n  G({NestedPattern(levels)}) = F\n  1\n}}\nK\n";

        Assert.Equal(151, WrittenHeight(Source(147)));
        Assert.Equal(Ceiling, Height(AssertAdmitted(Source(147)).Root));
        Assert.Equal("F", TextAt(Source(148), AssertRefused(Source(148))));
        AssertEngineRefusesAtParse(Source(148));
    }

    // ── Programs the evaluator's profile admits ─────────────────────────────

    [Fact]
    public void ProgramsTheEvaluatorProfileAdmits_AreJudgedLikeTheirWrittenCounterparts()
    {
        // A written spread chain weighs nothing on the evaluator's profile, so these programs RAN before the gate judged the
        // elaborated tree, while Build threw and their written counterparts were parse failures. The ceiling now decides
        // both forms alike: 16 marked calls elaborate to 300 and run, 17 elaborate to 303 and are refused.
        foreach (var source in new[] { Marked(16, inner: SpreadChain), Explicit(16, inner: SpreadChain) })
        {
            Assert.Equal(Ceiling, Height(AssertAdmitted(source).Root));
            AssertEngineValue(source, 5);
        }

        var marked = AssertRefused(Marked(17, inner: SpreadChain));
        var written = AssertRefused(Explicit(17, inner: SpreadChain));
        Assert.Equal(written.Span, marked.Span);
        AssertEngineRefusesAtParse(Marked(17, inner: SpreadChain));

        // Formula lifting under the same chain: `G`'s lifted `F` adds two units to 299 written ones.
        static string Lifted(int calls, bool written)
        {
            var body = written ? "F(x)" + new string('*', 250) : "F" + new string('*', 250);
            for (var level = 0; level < calls; level++)
                body = $"H({body})";
            return $"H(v) = v\nF(x) = x\n{(written ? "G(x)" : "G")} = {body}\n1\n";
        }

        Assert.Equal(Ceiling - 1, Height(AssertAdmitted(Lifted(22, written: false)).Root));
        AssertEngineValue(Lifted(22, written: false), 1);
        Assert.Equal(Ceiling - 1, Height(AssertAdmitted(Lifted(22, written: true)).Root));
        Assert.StartsWith("F", TextAt(Lifted(23, written: false), AssertRefused(Lifted(23, written: false))), StringComparison.Ordinal);
        Assert.StartsWith("F", TextAt(Lifted(23, written: true), AssertRefused(Lifted(23, written: true))), StringComparison.Ordinal);
    }

    // ── Deep trees elaboration does not deepen ──────────────────────────────

    [Fact]
    public void DeepTreesElaborationDoesNotDeepen_AreUnaffected()
    {
        // An unmarked call nest and a 295-level pattern the front end never rebuilds keep their written height and run.
        var unmarked = "A(x) = x\n" + NestedCalls(100, star: false) + "\n";
        var pattern = $"F({NestedPattern(295)}) = a0\nG({NestedPattern(295)}) = a0\n1\n";

        foreach (var (source, height) in new[] { (unmarked, 202), (pattern, 298) })
        {
            Assert.Equal(height, WrittenHeight(source));
            Assert.Equal(height, Height(AssertAdmitted(source).Root));
            AssertEngineValue(source, 1);
        }
    }

    // ── Every route that publishes an elaborated tree ───────────────────────

    [Fact]
    public void AProvisionalElaboration_ReportsTheGate_BesideItsMissingModule()
    {
        // Without a downloader the program elaborates provisionally and its pass diagnostics are withheld; the gate's
        // diagnostic is the operation's own, so it is reported, and the editor models the placeholder.
        static string Source(int calls) => $"Lib = load('{ModuleUrl}')\n" + Marked(calls);

        var below = OnLargeStack(() => Parser.Parse(Source(99)));
        Assert.Equal([DiagnosticCode.LoadElaborationUnavailable], below.Diagnostics.Select(d => d.Code));
        Assert.True(Height(below.Root) <= Ceiling);
        Assert.NotEmpty(OnLargeStack(() => SemanticModelBuilder.Build(below)).IdentifierResolutions);

        AssertRefused(Source(100), DiagnosticCode.LoadElaborationUnavailable);
    }

    [Fact]
    public void CancellationAtTheEndOfResolution_PreemptsTheDepthVerdict()
    {
        using var cancellation = new CancellationTokenSource();
        var observations = new FrontEndTraversalObservations
        {
            StageObserver = (stage, begin) =>
            {
                if (stage == FrontEndPassStage.Resolve && !begin)
                    cancellation.Cancel();
            },
        };
        var options = new RunOptions { SourceProcessingCancellationToken = cancellation.Token };
        var error = OnLargeStack(() => Assert.Throws<OperationCanceledException>(
            () => Parser.ParseObserved(Marked(100), options, observations)));
        Assert.Equal(cancellation.Token, error.CancellationToken);
    }

    [Fact]
    public void AModuleHeldByAProperty_ReportsElaborationDepthAtThatProperty()
    {
        var options = new RunOptions
        {
            AllowedHosts = ["katlang.org"],
            DownloadCode = (_, _) => ValueTask.FromResult(ModuleSource(20)),
        };
        var source = $"1\nLibrary = load('{ModuleUrl}')\n";
        var parsed = OnLargeStack(() => Parser.ParseAsync(source, options).GetAwaiter().GetResult());
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticCode.AstDepthLimitExceeded, diagnostic.Code);
        Assert.Equal(new SourceSpan(2, 1, 2, 8), Assert.NotNull(diagnostic.Span));
        Assert.Empty(OnLargeStack(() => SemanticModelBuilder.Build(parsed)).IdentifierResolutions);
    }

    [Fact]
    public void TheRecoveryAfterSelfDependentInference_GatesTheDetectedTreeItPublishes()
    {
        // Detection lowers a marked extension edge `A(r).F` to the call `F(A(r)*)` (D1), two units more per edge, and the
        // A1 recovery publishes the DETECTED tree. 59 edges detect to the ceiling; 60 to 305, which Build rejected.
        static string Chain(int edges)
        {
            var expression = "A(1)";
            for (var edge = 0; edge < edges; edge++)
                expression = $"A({expression}.F)";
            return StaticStructureWitnessSources.Cases["A.3.2"].Replace("\n5", "") + "\nA(x)* = x\nF(y) = y\nD = " + expression + "\n5\n";
        }

        var below = OnLargeStack(() => Parser.Parse(Chain(59)));
        Assert.Equal([DiagnosticCode.SelfDependentInferredParameters], below.Diagnostics.Select(d => d.Code));
        Assert.Equal(Ceiling, Height(below.Root));
        Assert.NotEmpty(OnLargeStack(() => SemanticModelBuilder.Build(below)).IdentifierResolutions);

        AssertRefused(Chain(60), DiagnosticCode.SelfDependentInferredParameters);
    }

    [Fact]
    public async Task ADeferredBranchsResolvedBody_IsJudgedByTheRunsAdmission_WhileTheEagerModuleIsJudgedAtParse()
    {
        // A selected branch compiles its module at run time, and the materialized (resolved) body is judged by the run's
        // own structural admission (MOD-10: the evaluator's profile at the run's limit less the placeholder's prefix, a run
        // verdict that leaves the materialization published); the editor never models it, and the compile adds no
        // elaboration gate of its own. The same module loaded eagerly is part of the parse result, whose published tree
        // the elaboration gate judges. Marked calls whose spreads the evaluator's profile also refuses are the run's
        // resource-limit verdict at the import site; a body the evaluator's profile admits (a free spread chain) runs.
        static string Deferred() => $"F(0) = 42\nF(n) = {{ open '{ModuleUrl}'\nX }}\nF(1)";
        static string Eager() => $"open '{ModuleUrl}'\nX";
        static string MarkedCallsModule(int calls) => "A(x)* = x\npublic X = " + NestedCalls(calls, star: false) + "\n";

        static Task<RunResult> Run(string source, string module)
        {
            var options = new RunOptions
            {
                AllowedHosts = ["katlang.org"],
                DownloadCode = (url, _) => url == ModuleUrl ? ValueTask.FromResult(module) : throw new Exception($"404: {url}"),
            };
            var (pending, synchronous) = AstStructuralDepthProcessTests.RunOnThreadWithStack(LargeStack, () =>
            {
                var run = KatLangEngine.RunAsync(source, options);
                return (run, run.IsCompleted);
            });
            Assert.True(synchronous, "a synchronously completing downloader keeps the run on the large thread");
            return pending;
        }

        static void AssertRefusedAtParse(RunResult result)
            => Assert.Equal(KatLangErrorCode.AstDepthLimitExceeded, Assert.Single(Assert.IsType<RunResult.ParseFailure>(result).Errors).Code);

        // 99 marked calls: the eager module is past the ceiling once elaborated; the branch body is the run's verdict.
        AssertRefusedAtParse(await Run(Eager(), MarkedCallsModule(99)));
        var error = Assert.Single(Assert.IsType<RunResult.EvalFailure>(await Run(Deferred(), MarkedCallsModule(99))).Errors);
        Assert.Equal(KatLangErrorCode.AstDepthLimitExceeded, error.Code);
        Assert.True(error.IsResourceLimit, "the run's admission verdict (MOD-10), not a materialization failure");
        var span = Assert.NotNull(error.Span);
        Assert.Equal(2, span.Start.Line);
        Assert.Equal(Deferred().Split('\n')[1].IndexOf('\'') + 1, span.Start.Column);

        // 16 marked calls around a free spread chain: refused at parse when loaded eagerly, admitted by the run when deferred.
        AssertRefusedAtParse(await Run(Eager(), ModuleSource(16)));
        Assert.Equal([(Decimal128)5], Assert.IsType<RunResult.Success>(await Run(Deferred(), ModuleSource(16))).Atoms);
    }

    // ── The boundary as a property ──────────────────────────────────────────

    [Fact]
    public void AcrossTheBoundary_EveryParseResultIsWithinTheGateItsEditorApplies_AndCounterpartsAgree()
    {
        // Every result Parser.Parse publishes is within the ceiling the semantic model applies (or is the refused
        // placeholder), so Build never throws for a parser result; a marked program and its explicit counterpart are refused
        // at exactly the same sizes.
        var refusedSizes = new List<(int Calls, bool Marked)>();
        for (var calls = 95; calls <= 105; calls++)
        {
            foreach (var marked in new[] { true, false })
            {
                var source = marked ? Marked(calls) : Explicit(calls);
                var parsed = OnLargeStack(() => Parser.Parse(source));
                var refused = parsed.Diagnostics.Any(d => d.Code == DiagnosticCode.AstDepthLimitExceeded);
                Assert.True(refused || Height(parsed.Root) <= Ceiling, $"{calls} calls, marked: {marked}");
                OnLargeStack(() => SemanticModelBuilder.Build(parsed));
                if (refused)
                    refusedSizes.Add((calls, marked));
            }
        }

        var markedRefusals = refusedSizes.Where(r => r.Marked).Select(r => r.Calls).ToList();
        Assert.Equal(markedRefusals, refusedSizes.Where(r => !r.Marked).Select(r => r.Calls));
        Assert.Equal(Enumerable.Range(100, 6), markedRefusals);
    }
}
