using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// Executable diagnostic-provenance map: for a given surface source, WHICH
/// language-processing stage decides the outcome — parser, front-end
/// elaboration, editor semantic model, or evaluator.
///
/// <para>
/// Track 13 built this after finding regression tests that asserted an
/// evaluator outcome while an earlier stage had already done the work. The
/// cases here are the ones where the stages genuinely disagree, pinned so the
/// disagreement is a reviewed contract rather than an accident, and so the
/// later structured-error/ownership audit has a factual starting point.
/// </para>
/// </summary>
public class DiagnosticProvenanceTests
{
    private static EvalError InnermostError(string source)
    {
        var provenance = SourceProvenance.ParseValid(source);
        return provenance.ExpectEvaluationError();
    }

    private static IReadOnlyList<string> EditorUnresolved(string source)
    {
        var parsed = Parser.Parse(source);
        Assert.False(parsed.HasErrors, string.Join(" | ", parsed.Diagnostics.Select(d => d.Message)));
        return SemanticModelBuilder.Build(parsed).IdentifierResolutions
            .Where(r => r.Classification == IdentifierClassification.Unresolved)
            .Select(r => r.Occurrence.Name)
            .ToList();
    }

    private static Result EvaluatesTo(string source)
    {
        var result = SourceProvenance.ParseValid(source).Evaluate();
        if (result.IsError)
            Assert.Fail($"Expected success but got: {KatLangError.FromEvalError(result.Error).Message.Split('\n')[0]}");
        return result.Value;
    }

    // ── `open` validation is DEMAND-DRIVEN ────────────────────────────────────

    /// <summary>
    /// An invalid <c>open</c> target is accepted by the parser and never
    /// diagnosed at runtime unless some name actually falls through to the
    /// opens. This is not a C# shortcut: Lean reaches <c>resolveAllOpens</c>
    /// only from <c>lookupOpens</c>, itself only step 3 of <c>lookupLexical</c>,
    /// so laziness is the modelled semantics.
    ///
    /// <para>
    /// The three target kinds below are all invalid for different reasons —
    /// missing name, missing dotted member, non-public dotted member — and all
    /// three evaluate successfully when the body uses only owned names. (A
    /// BUILTIN head is the exception since the final audit: the front end refuses
    /// it eagerly like a parameterized provider — see
    /// <see cref="BuiltinOpenTarget_IsRefusedEagerly_ByTheFrontEndAndByKindAtRuntime"/>.)
    /// </para>
    /// </summary>
    [Theory]
    [InlineData("open Nope\nQ = 5\nQ")]                                               // missing target
    [InlineData("open Lib.Nope\nLib = {\n    public S = 1\n}\nQ = 5\nQ")]             // missing member
    [InlineData("open Lib.S\nLib = {\n    S = {\n        public X = 1\n    }\n}\nQ = 5\nQ")] // non-public member
    public void InvalidOpenTarget_IsNotDiagnosedWhenNoNameFallsThroughToIt(string source)
        => Assert.Equal(new Result.Atom(5), EvaluatesTo(source));

    /// <summary>
    /// ... and the SAME declaration fails as soon as a lookup demands the opens.
    /// Demand, not declaration, is what triggers validation.
    /// </summary>
    [Fact]
    public void TheSameInvalidOpenFailsAsSoonAsALookupDemandsIt()
    {
        Assert.IsType<EvalError.UnknownName>(
            InnermostError("open Nope, Pub\nPub = {\n    public Y = 7\n}\nY"));

        // Owned name instead of `Y`: the very same declaration is fine.
        Assert.Equal(
            new Result.Atom(5),
            EvaluatesTo("open Nope, Pub\nPub = {\n    public Y = 7\n}\nQ = 5\nQ"));
    }

    [Theory]
    [InlineData("count")]
    [InlineData("if")]
    [InlineData("sum")]
    public void BuiltinNameShadowedByALexicalProvider_RemainsOpenable(string name)
    {
        foreach (var target in new[] { name, name + ".Sub" })
        {
            var source = $"open {target}\n{name} = {{ public X = 7\n public Sub = {{ public X = 7 }} }}\nX";
            SourceProvenance.ParseValid(source);
            Assert.Equal("7", Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString());
        }
    }

    [Theory]
    [InlineData("F(*) = 0")]
    [InlineData("F(a, *) = a")]
    public void OpenProviderDiagnostic_NeverNamesARecoveryBinder(string declaration)
    {
        var parsed = SourceProvenance.ParseAllowingDiagnostics($"open F\n{declaration}\n1");
        Assert.Contains(parsed.Diagnostics, d => d.Code == DiagnosticCode.InvalidCollectMarker);
        var diagnostic = Assert.Single(parsed.Diagnostics, d => d.Code == DiagnosticCode.IllegalInOpen);
        Assert.DoesNotContain("_error_", diagnostic.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("arguments ()", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void OpenProviderDiagnostic_PreservesRealNamesEvenWhenTheyMatchTheRecoverySpelling()
    {
        var parsed = SourceProvenance.ParseAllowingDiagnostics("open F\nF(_error_) = _error_\n1");
        Assert.Contains("(_error_)", Assert.Single(parsed.Diagnostics).Message, StringComparison.Ordinal);
        var provider = new Algorithm.User(null, [new CaptureParameterPattern("_error_")], [], [], [new Expr.Num(0)])
        {
            HasExplicitParameterList = true,
        };
        Assert.Contains("(_error_)", Evaluator.FormatOpenTargetRequiresArguments("F", provider), StringComparison.Ordinal);
    }

    [Fact]
    public void OpenProviderDiagnostic_PreservesHostParameterNamesWithPartialSpans()
    {
        ParameterDeclaration[] parameters =
        [
            new("located") { Span = new SourceSpan(1, 1, 1, 8) },
            new("unlocated"),
        ];
        var provider = new Algorithm.User(null, ParameterPattern.FromDeclarations(parameters), [], [], [new Expr.Num(0)])
        {
            HasExplicitParameterList = true,
        };
        Assert.Contains("(located, unlocated)",
            Evaluator.FormatOpenTargetRequiresArguments("F", provider), StringComparison.Ordinal);
    }

    /// <summary>
    /// Final audit (September 2026): a prelude builtin named as an open target is refused
    /// EAGERLY by the front end (OpenProviderValidator — the same rule that refuses a
    /// parameterized provider; a builtin's arity lives in registry metadata, not in
    /// <c>Params</c>) and by KIND at open resolution in the evaluator (Lean
    /// <c>resolveAlgForOpen</c>), whether or not any name is demanded through the list —
    /// the layer disagreement the editor already flagged is closed for builtins.
    /// </summary>
    [Theory]
    [InlineData("open count\nQ = 5\nQ", "count", 1, 6, 1, 11)]
    [InlineData("open if\nQ = 5\nQ", "if", 1, 6, 1, 8)]
    [InlineData("A = {\n    open sum, Lib\n    1\n}\nLib = { public Z = 1 }\nA", "sum", 2, 10, 2, 13)]
    // A builtin HEAD of a dotted target is refused by the same rule: a builtin has no members,
    // so the path can never provide, and the opener's names must not become implicit parameters.
    [InlineData("open count.X\nQ = 5\nQ", "count.X", 1, 6, 1, 13)]
    [InlineData("A = {\n    open if.X.Y, Lib\n    1\n}\nLib = { public Z = 1 }\nA", "if.X.Y", 2, 10, 2, 16)]
    public void BuiltinOpenTarget_IsRefusedEagerly_ByTheFrontEndAndByKindAtRuntime(
        string source, string runtimeTarget, int line, int column, int endLine, int endColumn)
    {
        var parsed = Parser.Parse(source);
        var diagnostic = Assert.Single(parsed.Diagnostics, d => d.Code == DiagnosticCode.IllegalInOpen);
        Assert.Equal(new SourceSpan(line, column, endLine, endColumn), diagnostic.Span);
        Assert.Contains("builtin callable", diagnostic.Message, StringComparison.Ordinal);

        // The runtime, handed the (recovery) tree regardless, refuses the same target by
        // kind as soon as the open list is demanded: the modelled lazy resolution is unchanged.
        var demanded = Parser.Parse($"open {runtimeTarget}, Pub\nPub = {{\n    public Y = 7\n}}\nY");
        Assert.Contains(demanded.Diagnostics, d => d.Code == DiagnosticCode.IllegalInOpen);
        var result = Evaluator.Run(new Expr.AlgorithmExpr(demanded.Root));
        Assert.True(result.IsError);
        var innermost = result.Error;
        while (innermost is EvalError.WithContext context) innermost = context.Inner;
        Assert.IsType<EvalError.IllegalInOpen>(innermost);
    }

    /// <summary>
    /// The EDITOR does not agree with the runtime here: the semantic model
    /// flags every invalid open target eagerly, including in programs that
    /// evaluate successfully. That is defensible (an editor should warn) but it
    /// IS a layer disagreement, and it is the clearest input this track has for
    /// the structured-error ownership audit: today no layer both accepts the
    /// program and reports the mistake.
    /// </summary>
    [Theory]
    [InlineData("open Nope\nQ = 5\nQ", "Nope")]
    public void EditorFlagsAnInvalidOpenTargetThatTheRuntimeNeverDiagnoses(string source, string flagged)
    {
        Assert.Contains(flagged, EditorUnresolved(source));
        Assert.Equal(new Result.Atom(5), EvaluatesTo(source));
    }

    /// <summary>
    /// `open` must precede every property and output row in its algorithm — a
    /// PARSER rule, and the one that 35 accidentally-invalid `EvaluatorTests`
    /// sources were unknowingly relying on (Track 13 repaired them by moving
    /// `open` to the front; Track 14 found the rule itself had no test at all).
    ///
    /// <para>
    /// The counterpart is also pinned: a target defined LATER in the same body
    /// is explicitly legal, which is why the repair preserved every test's
    /// intent rather than changing what it asserted.
    /// </para>
    /// </summary>
    [Fact]
    public void OpenMustPrecedePropertiesButMayTargetALaterDefinition()
    {
        var diagnostics = SourceProvenance.ExpectFrontEndError("A = { public X = 1 }\nopen A\nX");
        Assert.Contains(
            diagnostics,
            d => d.Message.Contains("'open' declaration must appear before any properties", StringComparison.Ordinal));

        // Same program, `open` first: legal, and the later definition resolves.
        Assert.Equal(new Result.Atom(1), EvaluatesTo("open A\nA = { public X = 1 }\nX"));
    }

    // ── Conditional accessed as a value ───────────────────────────────────────

    /// <summary>
    /// A genuine multi-clause family accessed as a value reports
    /// <c>NoMatchingBranch</c>. This IS surface-reachable.
    /// </summary>
    [Fact]
    public void BareMultiClauseReference_ReportsNoMatchingBranch()
    {
        var multi = Assert.IsType<EvalError.NoMatchingBranch>(InnermostError("F(0) = 1\nF(n) = 2\nF"));
        Assert.Equal("F", multi.AlgorithmName);

        Assert.IsType<EvalError.NoMatchingBranch>(
            InnermostError("A = {\n    public F(0) = 1\n    public F(n) = 2\n}\nA.F"));
    }

    /// <summary>
    /// The OTHER arm of <c>ConditionalValueAccessError</c> — the one that
    /// reports the friendlier arity error for a conditional equivalent to a flat
    /// binder callable — is NOT surface-reachable.
    ///
    /// <para>
    /// Track 12 mutated the selection to always report <c>NoMatchingBranch</c>
    /// and the mutant survived. Track 13 classified the cause, and it is source
    /// PRE-EMPTION, not a missing surface test: <c>TryGetFlatBinderUserEquivalent</c>
    /// requires a single-branch <c>Algorithm.Conditional</c> whose pattern is
    /// flat binders, and <c>Algorithm.ElaborateClauseGroup</c> converts exactly
    /// that shape into an ordinary <c>Algorithm.User</c>. Every written form
    /// tried — <c>F(a) = …</c>, <c>F(a, b) = …</c>, even the repeated-binder
    /// <c>F(x, x) = …</c> — elaborates to a User algorithm and reports its arity
    /// through the ordinary parameter-owning User-algorithm path instead.
    /// </para>
    ///
    /// <para>
    /// So this is a host-API defensive branch and is pinned as one, from a
    /// prebuilt AST. Writing it as a source test would have been exactly the
    /// vacuity this track exists to remove — the source test passes while the
    /// branch is dead code.
    /// </para>
    /// </summary>
    [Fact]
    public void FlatBinderConditionalValueAccess_IsReachableOnlyFromAPrebuiltAst()
    {
        var body = new Algorithm.User(
            Parent: null, ParameterPatterns: [], Opens: [], Properties: [],
            Output: [new Expr.Binary(BinaryOp.Add, new Expr.Param("a"), new Expr.Param("b"))]);

        var conditional = new Algorithm.Conditional(
            Parent: null,
            Opens: [],
            Branches: [new CondBranch(
                new Pattern.SequenceValue([new Pattern.Bind("a"), new Pattern.Bind("b")]),
                body)]);

        var root = new Algorithm.User(
            Parent: null, ParameterPatterns: [], Opens: [],
            Properties: [new Property("F", conditional)],
            Output: [new Expr.Resolve("F")]);

        var result = Evaluator.Run(new Expr.AlgorithmExpr(root));
        Assert.True(result.IsError);

        var error = result.Error;
        while (error is EvalError.WithContext context)
            error = context.Inner;

        var arity = Assert.IsType<EvalError.ArityMismatch>(error);
        Assert.Equal(2, arity.Expected);
        Assert.Equal(0, arity.Actual);
    }
}
