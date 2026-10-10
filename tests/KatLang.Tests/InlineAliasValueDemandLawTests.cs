using System.Numerics;
using KatLang.Evaluation;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using static KatLang.Tests.SixRouteAgreement;

namespace KatLang.Tests;

/// <summary>
/// FA-OQ-1 (owner decision Option B, 2026-10-10): THE ZERO-ARGUMENT VALUE DEMAND OF AN INLINE
/// CALLABLE ALIAS IS ITS TARGET'S. An inline block whose one row names a callable that declares
/// parameterized structure — <c>{ Inc }</c> — is a callable ALIAS (FWD-02, binding indirection):
/// it has no signature and no report of its own. A rejected zero-argument VALUE demand of it is
/// therefore reported exactly as its written target reference reports it — the target's ordinary
/// contract — and located at that reference:
/// <list type="bullet">
///   <item>a user algorithm (Math and host members included): the property-context
///   <see cref="EvalError.ArityMismatch"/> with its true minimum ("Property 'Inc' expects 1
///   parameter, but was called with 0 arguments."), exactly what the direct reference
///   <c>count(Inc)</c> reports under a closed list;</item>
///   <item>a named alias <c>{ A }</c>: what <c>count(A)</c> reports; a member path
///   <c>{ Lib.F }</c>: the bare arity <c>count(Lib.F)</c> reports;</item>
///   <item>a clause family: its <see cref="EvalError.NoMatchingBranch"/>, named by the reference;</item>
///   <item>a builtin: the builtin's own arity error, as before.</item>
/// </list>
/// Until this decision the demand reported the WRITTEN block's
/// <see cref="EvalError.UnresolvedImplicitParams"/>, presenting the target's parameters as
/// implicit parameters of the program. A written block with its OWN inferred parameters keeps
/// that report, and accepted, unused, invoked and forwarded aliases are untouched (Model C:
/// nothing is demanded earlier, later or more often). One mapping decides every demand site
/// (<c>Evaluator.ZeroArgumentValueDemandError</c>, Lean <c>zeroArgumentDemandError?</c>):
/// value position, a spread operand, a builtin value slot, the <c>.string</c> receiver and a
/// parameter read. Every case runs on the six established routes and must agree; the Lean side
/// is <c>lean/CoreTests/ValueDemand.lean</c> § FA-OQ-1 and the <c>inline-alias-*</c> spec cases.
/// </summary>
public class InlineAliasValueDemandLawTests
{
    private const string Inc = "Inc(x) = x + 1\n";

    // ── helpers ────────────────────────────────────────────────────────────────

    /// <summary>
    /// The span the report must carry: the written target reference <paramref name="target"/>
    /// inside the FIRST written inline alias block <c>{ target }</c> of <paramref name="source"/>.
    /// </summary>
    private static string TargetReferenceSpan(string source, string target)
    {
        var block = "{ " + target + " }";
        var index = source.IndexOf(block, StringComparison.Ordinal);
        Assert.True(index >= 0, $"the source has no inline alias block {block}");
        var start = index + 2;
        var line = 1 + source[..start].Count(static c => c == '\n');
        var column = start - (source.LastIndexOf('\n', start - 1) + 1) + 1;
        return $"[{line}:{column}, {line}:{column + target.Length})";
    }

    private static string WithoutSpan(string described) => described[..described.LastIndexOf(" @ ", StringComparison.Ordinal)];

    private static string SpanOf(string described) => described[(described.LastIndexOf(" @ ", StringComparison.Ordinal) + 3)..];

    private sealed class HostLog
    {
        private int _ticks;

        public List<string> Calls { get; } = [];

        public HostOperations Operations => HostOperations.Create(
            HostOperation.Create("tick", (_, _) =>
            {
                Calls.Add($"tick#{++_ticks}");
                return new Result.Atom((Decimal128)_ticks);
            }),
            HostOperation.Create("trace", (args, _) =>
            {
                Calls.Add($"trace({Neutral(args[0])})");
                return args[0];
            }, "x"));
    }

    private sealed record Observed(
        EvalResult<Evaluator.CountedResult> Result,
        EvaluationBudget Budget,
        LoopOptimizationDiagnostics Loops,
        SequencePipelineDiagnostics Sequences,
        IReadOnlyList<string> HostCalls);

    /// <summary>The generic (or optimized) evaluator route over a source that must parse cleanly.</summary>
    private static Observed Observe(string source, bool optimized)
    {
        var log = new HostLog();
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = log.Operations });
        Assert.False(parsed.HasErrors, "the source must parse cleanly:\n" + source + "\n"
            + string.Join("\n", parsed.Diagnostics.Select(static d => d.Message)));
        var loops = new LoopOptimizationDiagnostics();
        var sequences = new SequencePipelineDiagnostics();
        var (result, budget) = Evaluator.RunCountedObserved(
            new Expr.AlgorithmExpr(parsed.Root),
            enableOptimizations: optimized,
            loopDiagnostics: loops,
            sequenceDiagnostics: sequences,
            hostOperations: log.Operations);
        return new Observed(result, budget, loops, sequences, log.Calls);
    }

    private static EvalError FailureOf(string source)
    {
        var observed = Observe(source, optimized: false);
        Assert.True(observed.Result.IsError, "expected an evaluation failure:\n" + source);
        return observed.Result.Error;
    }

    private static IEnumerable<EvalError> Chain(EvalError error)
    {
        for (var current = error; ; current = ((EvalError.WithContext)current).Inner)
        {
            yield return current;
            if (current is not EvalError.WithContext)
                yield break;
        }
    }

    private static EvalError Innermost(EvalError error) => Chain(error).Last();

    /// <summary>The innermost error's kind and structured payload, without its location.</summary>
    private static string Payload(EvalError error) => error switch
    {
        EvalError.ArityMismatch arity => $"ArityMismatch({arity.Expected},{arity.Actual})",
        EvalError.NoMatchingBranch branch => $"NoMatchingBranch({branch.AlgorithmName})",
        EvalError.UnresolvedImplicitParams unresolved => $"UnresolvedImplicitParams[{string.Join(",", unresolved.ParamNames)}]",
        _ => (error with { Span = null }).ToString(),
    };

    private static bool HasPropertyFrame(EvalError error, string name)
        => Chain(error).OfType<EvalError.WithContext>().Any(frame => frame.ErrorContext.FormatMessage() == $"while evaluating property {name}");

    private static bool MentionsUnresolvedImplicitParams(EvalError error)
        => Chain(error).Any(static node => node is EvalError.UnresolvedImplicitParams
            || node is EvalError.WithContext { ErrorContext: ImplicitParameterContext });

    // ── 1. The canonical FA-OQ-1 witness ───────────────────────────────────────

    [Fact]
    public async Task CanonicalWitness_ReportsTheTargetsCardinality_NotUnresolvedImplicitParams()
    {
        const string source = Inc + "K(z) = count({ Inc })\nK(1)";

        var oracle = await OnEveryRouteAsync(source);
        Assert.Equal("err", oracle.Kind);
        Assert.Equal(
            "ArityMismatch: while evaluating call to K: while evaluating call to count: "
            + "Property 'Inc' expects 1 parameter, but was called with 0 arguments. @ [2:16, 2:19)",
            Assert.Single(oracle.Errors));
        Assert.Empty(oracle.HostCalls);

        // The structured error: Inc's own cardinality contract (expected 1, actual 0) under Inc's
        // property frame — nothing names Inc's parameter `x` as an implicit parameter.
        var error = FailureOf(source);
        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(error));
        Assert.Equal((1, 0), (arity.Expected, arity.Actual));
        Assert.True(HasPropertyFrame(error, "Inc"));
        Assert.False(MentionsUnresolvedImplicitParams(error));
        Assert.Equal(KatLangErrorCode.ArityMismatch, KatLangError.FromEvalError(error).Code);
        Assert.Equal("arity", SemanticExplorerHarness.ErrorCategory(error)); // the FORMAL-06 neutral category

        // Located at the written target reference `Inc` inside the block (line 2, columns 16-19).
        Assert.Equal(TargetReferenceSpan(source, "Inc"), SpanOf(oracle.Errors[0]));
    }

    [Fact]
    public async Task CanonicalWitness_AtTheRoot_IsTheSameRuntimeDemand()
    {
        // The root formula `count({ Inc })` lifts nothing (the block is an alias, not a reference
        // the formula could lift), so the root reaches the same runtime demand.
        var oracle = await OnEveryRouteAsync(Inc + "count({ Inc })");
        Assert.Equal(
            "ArityMismatch: while evaluating call to count: Property 'Inc' expects 1 parameter, but was called with 0 arguments. @ [2:9, 2:12)",
            Assert.Single(oracle.Errors));
    }

    // ── 2. Named/inline equivalence ────────────────────────────────────────────

    /// <summary>
    /// Each inline alias renders EXACTLY like the direct reference to its target — the same code,
    /// message and context frames — and only the location differs (the reference inside the
    /// block versus the direct argument). Before FA-OQ-1 only the builtin pair agreed.
    /// </summary>
    [Theory]
    [InlineData(Inc + "K(z) = count({ Inc })\nK(1)", Inc + "K(z) = count(Inc)\nK(1)")]
    [InlineData(Inc + "A = Inc\nK(z) = count({ A })\nK(1)", Inc + "A = Inc\nK(z) = count(A)\nK(1)")]
    [InlineData(Inc + "A = Inc\nB = A\nK(z) = count({ B })\nK(1)", Inc + "A = Inc\nB = A\nK(z) = count(B)\nK(1)")]
    [InlineData("Add(a, b) = a + b\nK(z) = count({ Add })\nK(1)", "Add(a, b) = a + b\nK(z) = count(Add)\nK(1)")]
    [InlineData("K(z) = count({ abs })\nK(1)", "K(z) = count(abs)\nK(1)")]
    [InlineData("K(z) = count({ Math.Abs })\nK(1)", "K(z) = count(Math.Abs)\nK(1)")]
    [InlineData("Lib = {\n    public F(x) = x\n}\nK(z) = count({ Lib.F })\nK(1)", "Lib = {\n    public F(x) = x\n}\nK(z) = count(Lib.F)\nK(1)")]
    [InlineData("E(0) = 0\nE(n) = n\nK(z) = count({ E })\nK(1)", "E(0) = 0\nE(n) = n\nK(z) = count(E)\nK(1)")]
    [InlineData("E(0) = 0\nE(n) = n\nA = E\nK(z) = count({ A })\nK(1)", "E(0) = 0\nE(n) = n\nA = E\nK(z) = count(A)\nK(1)")]
    [InlineData("K(z) = count({ count })\nK(1)", "K(z) = count(count)\nK(1)")]
    public async Task InlineAlias_RendersExactlyLikeTheDirectReference(string inline, string direct)
    {
        var inlineOracle = await OnEveryRouteAsync(inline);
        var directOracle = await OnEveryRouteAsync(direct);

        Assert.Equal("err", inlineOracle.Kind);
        Assert.Equal(directOracle.Kind, inlineOracle.Kind);
        Assert.Equal(WithoutSpan(Assert.Single(directOracle.Errors)), WithoutSpan(Assert.Single(inlineOracle.Errors)));
        Assert.Equal(directOracle.HostCalls, inlineOracle.HostCalls);

        // The neutral observation (FORMAL-06) and the structured payload agree as well.
        var inlineError = FailureOf(inline);
        var directError = FailureOf(direct);
        Assert.Equal(SemanticExplorerHarness.ErrorCategory(directError), SemanticExplorerHarness.ErrorCategory(inlineError));
        Assert.Equal(Payload(Innermost(directError)), Payload(Innermost(inlineError)));
    }

    [Fact]
    public async Task NamedAlias_IsUnchanged()
    {
        // The NAMED alias report predates FA-OQ-1 and is the model the inline alias now follows.
        var oracle = await OnEveryRouteAsync(Inc + "A = Inc\nK(z) = count(A)\nK(1)");
        Assert.Equal(
            "ArityMismatch: while evaluating call to K: while evaluating call to count: Property 'A' expects 1 parameter, but was called with 0 arguments. @ [3:14, 3:15)",
            Assert.Single(oracle.Errors));

        // ... and so is a named alias read through a parameter, and at the root, where the formula
        // lifts the alias's target signature (PAR-07; unrelated to FA-OQ-1).
        Assert.Equal(
            "ArityMismatch: while evaluating call to Id: Property 'A' expects 1 parameter, but was called with 0 arguments. @ [4:4, 4:5)",
            Assert.Single((await OnEveryRouteAsync(Inc + "A = Inc\nId(v) = v\nId(A)")).Errors));
        Assert.StartsWith(
            "UnresolvedImplicitParams: ",
            Assert.Single((await OnEveryRouteAsync(Inc + "A = Inc\ncount(A)")).Errors));
    }

    [Theory]
    [InlineData(Inc + "K(z) = count({ Inc })\nK(1)", Inc + "K(z) = count(Inc)\nK(1)")]
    [InlineData(Inc + "A = Inc\nK(z) = count({ A })\nK(1)", Inc + "A = Inc\nK(z) = count(A)\nK(1)")]
    [InlineData("E(0) = 0\nE(n) = n\nK(z) = count({ E })\nK(1)", "E(0) = 0\nE(n) = n\nK(z) = count(E)\nK(1)")]
    [InlineData("K(z) = count({ Math.Abs })\nK(1)", "K(z) = count(Math.Abs)\nK(1)")]
    public void InlineAliasRejection_ChargesExactlyWhatTheDirectReferenceCharges(string inline, string direct)
    {
        // Both reject before any body is entered; neither is an invocation of its own.
        foreach (var optimized in new[] { false, true })
        {
            var a = Observe(inline, optimized);
            var b = Observe(direct, optimized);
            Assert.True(a.Result.IsError && b.Result.IsError);
            Assert.Equal(
                (b.Budget.ConsumedSteps, b.Budget.ConsumedExpressionCheckpoints, b.Budget.PeakDepth, b.Budget.MaterializedItems),
                (a.Budget.ConsumedSteps, a.Budget.ConsumedExpressionCheckpoints, a.Budget.PeakDepth, a.Budget.MaterializedItems));
        }
    }

    // ── 3. Every VALUE consumer reaches the same law ───────────────────────────

    /// <summary>
    /// The consumer never decides the report: a builtin value slot (collection, value, control,
    /// a loop's initial state, a range bound), an operand, a list element, a selected branch, the
    /// <c>.string</c> receiver, a dot-call fallback receiver, a spread operand, a fixed or
    /// forwarded parameter read, and a collector read all report Inc's property arity at the
    /// reference.
    /// </summary>
    [Theory]
    [InlineData(Inc + "K(z) = count({ Inc })\nK(1)", "while evaluating call to K: while evaluating call to count: ")]
    [InlineData(Inc + "K(z) = sum({ Inc })\nK(1)", "while evaluating call to K: while evaluating call to sum: ")]
    [InlineData(Inc + "K(z) = { Inc } + 1\nK(1)", "while evaluating call to K: ")]
    [InlineData(Inc + "K(z) = [{ Inc }]\nK(1)", "while evaluating call to K: ")]
    [InlineData(Inc + "K(z) = if(true, { Inc }, 0)\nK(1)", "while evaluating call to K: while evaluating call to if: ")]
    [InlineData(Inc + "K(z) = { Inc }.string\nK(1)", "while evaluating call to K: while evaluating dotCall .string of {...}: ")]
    [InlineData(Inc + "K(z) = { Inc }.count\nK(1)", "while evaluating call to K: while evaluating dotCall .count of {...}: ")]
    [InlineData(Inc + "K(z) = [{ Inc }*]\nK(1)", "while evaluating call to K: ")]
    [InlineData(Inc + "K(z) = range(1, { Inc })\nK(1)", "while evaluating call to K: while evaluating call to range: ")]
    [InlineData(Inc + "K(z) = atoms({ Inc })\nK(1)", "while evaluating call to K: while evaluating call to atoms: ")]
    [InlineData(Inc + "Step(n) = n + 1\nK(z) = repeat(Step, 1, { Inc })\nK(1)", "while evaluating call to K: while evaluating call to repeat: ")]
    [InlineData(Inc + "Id(v) = v\nId({ Inc })", "while evaluating call to Id: ")]
    [InlineData(Inc + "F(g) = g\nF({ Inc })", "while evaluating call to F: ")]
    [InlineData(Inc + "Id(v) = v\nFwd(w) = Id(w)\nFwd({ Inc })", "while evaluating call to Fwd: while evaluating call to Id: ")]
    [InlineData(Inc + "Coll(*xs) = xs\nK(z) = Coll({ Inc })\nK(1)", "while evaluating call to K: while evaluating call to Coll: ")]
    [InlineData(Inc + "K(z) = count({ { Inc } })\nK(1)", "while evaluating call to K: while evaluating call to count: ")]
    public async Task EveryValueConsumer_ReportsTheTargetsArityAtTheReference(string source, string frames)
    {
        var oracle = await OnEveryRouteAsync(source);
        Assert.Equal(
            $"ArityMismatch: {frames}Property 'Inc' expects 1 parameter, but was called with 0 arguments. @ {TargetReferenceSpan(source, "Inc")}",
            Assert.Single(oracle.Errors));

        var error = FailureOf(source);
        Assert.Equal("ArityMismatch(1,0)", Payload(Innermost(error)));
        Assert.False(MentionsUnresolvedImplicitParams(error));
    }

    [Fact]
    public async Task ReduceInitialAccumulator_KeepsReducesDedicatedHint()
    {
        // `reduce`'s initial slot reports a rejected callable with reduce's own accumulator hint
        // (HO-04), whatever shape named it — unchanged by FA-OQ-1.
        var oracle = await OnEveryRouteAsync(Inc + "Add(a, b) = a + b\nK(z) = reduce([1, 2], Add, { Inc })\nK(1)");
        var error = Assert.Single(oracle.Errors);
        Assert.StartsWith("ArityMismatch: `reduce` is `reduce(collection, reducer, initial)`", error);
        Assert.Contains("an algorithm that still needs 'x'", error);
    }

    // ── 4. Every target kind keeps its own contract ────────────────────────────

    [Theory]
    [InlineData("Add(a, b) = a + b\nK(z) = count({ Add })\nK(1)", "Add", 2)]
    [InlineData("Head(x, *rest) = x\nK(z) = count({ Head })\nK(1)", "Head", 1)]
    [InlineData("P((x, y)) = x + y\nK(z) = count({ P })\nK(1)", "P", 1)]
    [InlineData(Inc + "A = Inc\nB = A\nK(z) = count({ B })\nK(1)", "B", 1)]
    [InlineData("K(z) = count({ abs })\nK(1)", "abs", 1)]
    [InlineData("open Math\nK(z) = count({ Abs })\nK(1)", "Abs", 1)]
    [InlineData("K(z) = count({ trace })\nK(1)", "trace", 1)]
    [InlineData("K(z) = count({\n    L(y) = y\n    L\n})\nK(1)", "L", 1)]
    public async Task UserMathAndHostTargets_ReportTheirTrueMinimumUnderTheReferencesPropertyFrame(string source, string name, int expected)
    {
        var oracle = await OnEveryRouteAsync(source);
        var reported = Assert.Single(oracle.Errors);
        var plural = expected == 1 ? "parameter" : "parameters";
        Assert.StartsWith("ArityMismatch: ", reported);
        Assert.EndsWith($"Property '{name}' expects {expected} {plural}, but was called with 0 arguments.", WithoutSpan(reported));
        Assert.Empty(oracle.HostCalls); // a rejected host operation is never called

        var error = FailureOf(source);
        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(error));
        Assert.Equal((expected, 0), (arity.Expected, arity.Actual));
        Assert.True(HasPropertyFrame(error, name));
        Assert.False(MentionsUnresolvedImplicitParams(error));
    }

    [Theory]
    [InlineData("K(z) = count({ Math.Abs })\nK(1)", 1)]
    [InlineData("K(z) = count({ Math.Pow })\nK(1)", 2)]
    [InlineData("Lib = {\n    public F(x) = x\n}\nK(z) = count({ Lib.F })\nK(1)", 1)]
    public async Task MemberPathTargets_ReportTheBareArityOfTheNavigatedMember(string source, int expected)
    {
        var oracle = await OnEveryRouteAsync(source);
        Assert.StartsWith("ArityMismatch: ", Assert.Single(oracle.Errors));

        var error = FailureOf(source);
        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(error));
        Assert.Equal((expected, 0), (arity.Expected, arity.Actual));
        Assert.DoesNotContain(Chain(error).OfType<EvalError.WithContext>(), static frame => frame.ErrorContext is PropertyEvaluationContext);
        Assert.False(MentionsUnresolvedImplicitParams(error));
    }

    [Theory]
    [InlineData("E(0) = 0\nE(n) = n\nK(z) = count({ E })\nK(1)", "E")]
    [InlineData("U((0, x)) = x\nU([x, 0]) = x\nK(z) = count({ U })\nK(1)", "U")]
    [InlineData("E(0) = 0\nE(n) = n\nA = E\nK(z) = count({ A })\nK(1)", "A")]
    public async Task FamilyTargets_KeepNoMatchingBranch_NamedByTheReference(string source, string name)
    {
        var oracle = await OnEveryRouteAsync(source);
        Assert.Equal($"NoMatchingBranch: while evaluating call to K: while evaluating call to count: No matching branch for '{name}'", WithoutSpan(Assert.Single(oracle.Errors)));
        Assert.Equal(name, Assert.IsType<EvalError.NoMatchingBranch>(Innermost(FailureOf(source))).AlgorithmName);
    }

    [Theory]
    [InlineData("K(z) = count({ count })\nK(1)", "Callable `count(collection)` expects 1 argument, but was called with 0 arguments.")]
    [InlineData("K(z) = count({ if })\nK(1)", "Callable `if(condition, whenTrue, whenFalse)` expects 3 arguments, but was called with 0 arguments.")]
    public async Task BuiltinTargets_KeepTheBuiltinsOwnArityError(string source, string message)
    {
        // Unchanged: a builtin is not judged by the law at all; its own adapter rejects.
        var oracle = await OnEveryRouteAsync(source);
        Assert.Equal($"ArityMismatch: while evaluating call to K: {message}", WithoutSpan(Assert.Single(oracle.Errors)));
    }

    [Theory]
    [InlineData("Z = 7\nK(z) = { Z } + 1\nK(1)", "8")]
    [InlineData("Only(*xs) = xs\nK(z) = count({ Only })\nK(1)", "0")]
    [InlineData("Only(*xs) = xs\n{ Only }", "L[]")]
    public async Task AcceptedDemands_AreUnchanged(string source, string value)
    {
        // A zero-parameter target is no alias (the block reads it); a collecting-only target
        // accepts the empty supply.
        var oracle = await OnEveryRouteAsync(source);
        Assert.Equal(("ok", value), (oracle.Kind, oracle.Value));
    }

    // ── 5. Negative boundaries ─────────────────────────────────────────────────

    /// <summary>
    /// A written block that is NOT an alias — a formula, a multi-row body, an unresolved name, a
    /// block nested without being the lone reference — owns its inferred parameters, so its
    /// rejected demand stays <see cref="EvalError.UnresolvedImplicitParams"/> over ITS OWN names.
    /// </summary>
    [Theory]
    [InlineData("K(z) = count({x + 1})\nK(1)", "x")]
    [InlineData("count({x + 1})", "x")]
    [InlineData("Plus(f, x) = f + x\nPlus({x + 1}, 5)", "x")]
    [InlineData(Inc + "K(z) = count({ Inc + 0 })\nK(1)", "x")]
    [InlineData(Inc + "K(z) = count({ Inc, 1 })\nK(1)", "x")]
    [InlineData("K(z) = count({ y })\nK(1)", "y")]
    [InlineData("K(z) = count({ { x + 1 } })\nK(1)", "x")]
    public async Task NonAliasBlocks_KeepUnresolvedImplicitParams(string source, string name)
    {
        var oracle = await OnEveryRouteAsync(source);
        Assert.StartsWith("UnresolvedImplicitParams: ", Assert.Single(oracle.Errors));
        Assert.Equal([name], Assert.IsType<EvalError.UnresolvedImplicitParams>(Innermost(FailureOf(source))).ParamNames);
    }

    [Theory]
    [InlineData(Inc + "Ignore(f) = 0\nIgnore({ Inc })", "0")]
    [InlineData(Inc + "K(z) = if(false, { Inc }, 7)\nK(1)", "7")]
    [InlineData("Apply(f) = f(-5)\nApply({ abs })", "5")]
    [InlineData(Inc + "Apply(f, v) = f(v)\nFwd(f) = Apply(f, 3)\nFwd({ Inc })", "4")]
    [InlineData(Inc + "First(f, *rest) = f(2)\nFirst({ Inc }, 9)", "3")]
    [InlineData(Inc + "K(z) = repeat({ Inc }, 2, 0)\nK(1)", "2")]
    [InlineData(Inc + "K(z) = map([1, 2], { Inc })\nK(1)", "L[2, 3]")]
    [InlineData(Inc + "K(z) = count({ Inc(z) })\nK(1)", "1")]
    public async Task UnusedInvokedAndForwardedAliases_AreUnchanged(string source, string value)
    {
        var oracle = await OnEveryRouteAsync(source);
        Assert.Equal(("ok", value), (oracle.Kind, oracle.Value));
    }

    [Theory]
    [InlineData("Apply(f) = f(1)\nApply(5)", "NotAnAlgorithm: ")]
    [InlineData("Z = 7\nApply(f) = f(1)\nApply({ Z })", "ArityMismatch: while evaluating call to Apply: Callable `f` expects 0 arguments, but was called with 1 argument.")]
    [InlineData(Inc + "K(z) = count({ Inc }, trace(1))\nK(1)", "ArityMismatch: while evaluating call to K: Callable `count(collection)` expects 1 argument, but was called with 2 arguments.")]
    public async Task UnrelatedFailures_AreUnchanged(string source, string reported)
    {
        // A value is no callable; a zero-parameter block called with an argument is that block's
        // own call arity; a builtin's cardinality precedes any demand of its argument.
        var oracle = await OnEveryRouteAsync(source);
        Assert.StartsWith(reported, Assert.Single(oracle.Errors));
        Assert.Empty(oracle.HostCalls);
    }

    [Theory]
    [InlineData(Inc + "K(z) = count({ Inc }) + y\nK(1)", "UndeclaredIdentifier: ")]
    [InlineData("F(q) = q * 2\nK(z) = count({\n    A(p) = F\n    A(1)\n})\nK(1)", "UnforwardableParameter: ")]
    public async Task EarlierStaticErrors_StillWin(string source, string reported)
    {
        // The front end rejects the program before any demand can happen.
        var oracle = await OnEveryRouteAsync(source);
        Assert.Equal("parse", oracle.Kind);
        Assert.StartsWith(reported, Assert.Single(oracle.Errors));
    }

    [Fact]
    public async Task AliasBlockWithItsOwnDeclaration_IsStillAnAlias()
    {
        // Ordinary declarations beside the lone row keep the block an alias (FWD-02).
        const string source = Inc + "K(z) = count({\n    k = 1\n    Inc\n})\nK(1)";
        var oracle = await OnEveryRouteAsync(source);
        Assert.Equal(
            "ArityMismatch: while evaluating call to K: while evaluating call to count: Property 'Inc' expects 1 parameter, but was called with 0 arguments. @ [4:5, 4:8)",
            Assert.Single(oracle.Errors));
    }

    // ── 6. Observable effects: nothing is demanded earlier, later or more often ──

    [Theory]
    [InlineData(Inc + "K(z) = trace(1), count({ Inc }), trace(2)\nK(1)", "err", null, new[] { "trace(1)" })]
    [InlineData("Inc(x) = trace(x) + 1\nK(z) = count({ Inc })\nK(1)", "err", null, new string[0])]
    [InlineData(Inc + "Pair(a, b) = b + a\nK(z) = Pair(trace(5), { Inc })\nK(1)", "err", null, new string[0])]
    [InlineData("Inc(x) = trace(x) + 1\nIgnore(f) = 0\nIgnore({ Inc }), tick()", "ok", "S[0, 1]", new[] { "tick#1" })]
    [InlineData("Only(*xs) = tick()\nK(z) = { Only }, { Only }, Only, Only\nK(1)", "ok", "S[1, 2, 3, 3]", new[] { "tick#1", "tick#2", "tick#3" })]
    public async Task HostEffects_KeepTheirOrderAndCount(string source, string kind, string? value, string[] hostCalls)
    {
        // A rejected demand enters no body (Inc's `trace` never runs) and evaluates no other
        // argument first (`Pair` demands `b` before `a`); earlier rows keep their effects; an
        // accepted inline alias demand is the target's fresh zero-supply evaluation each time (an
        // inline block is no property), while the bare name reads its one cache entry.
        var oracle = await OnEveryRouteAsync(source);
        Assert.Equal((kind, value), (oracle.Kind, oracle.Value));
        Assert.Equal(hostCalls, oracle.HostCalls);
    }

    [Fact]
    public void PlannedLoop_InlineAliasStepIsPlanned_AndChargedLikeTheGenericLoop()
    {
        const string source = "Step(n) = n + 1\nK(z) = repeat({ Step }, 5, 0)\nK(1)";
        var generic = Observe(source, optimized: false);
        var optimized = Observe(source, optimized: true);

        Assert.Equal(1, optimized.Loops.OptimizedLoopHits);
        Assert.Equal(5, optimized.Loops.LoopIterations);
        Assert.Equal("5", Neutral(optimized.Result.Value.Value));
        Assert.Equal(Neutral(generic.Result.Value.Value), Neutral(optimized.Result.Value.Value));
        Assert.Equal(
            (generic.Budget.ConsumedSteps, generic.Budget.ConsumedExpressionCheckpoints),
            (optimized.Budget.ConsumedSteps, optimized.Budget.ConsumedExpressionCheckpoints));
    }

    [Fact]
    public void PlannedLoop_InlineAliasValueDemandInsideThePlannedStep_ReportsTheTargetsArity()
    {
        // The planner plans the loop and evaluates the step's `count({ Inc })` generically inside
        // it; both routes report Inc's cardinality and charge the same budget.
        const string source = Inc + "Step(n) = n + count({ Inc })\nK(z) = repeat(Step, 2, 0)\nK(1)";
        var generic = Observe(source, optimized: false);
        var optimized = Observe(source, optimized: true);

        Assert.Equal(1, optimized.Loops.OptimizedLoopHits);
        foreach (var observed in new[] { generic, optimized })
        {
            Assert.True(observed.Result.IsError);
            var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(observed.Result.Error));
            Assert.Equal((1, 0), (arity.Expected, arity.Actual));
            Assert.True(HasPropertyFrame(observed.Result.Error, "Inc"));
        }

        Assert.Equal(
            (generic.Budget.ConsumedSteps, generic.Budget.ConsumedExpressionCheckpoints),
            (optimized.Budget.ConsumedSteps, optimized.Budget.ConsumedExpressionCheckpoints));
    }

    [Fact]
    public void FusedFilterCount_InlineAliasPredicateIsInvoked_NotDemanded()
    {
        const string source = "IsOdd(x) = x mod 2 == 1\nK(z) = count(filter(range(1, 5), { IsOdd }))\nK(1)";
        var generic = Observe(source, optimized: false);
        var optimized = Observe(source, optimized: true);

        Assert.Equal(1, optimized.Sequences.FilterCountFusionHits);
        Assert.Equal("3", Neutral(optimized.Result.Value.Value));
        Assert.Equal(Neutral(generic.Result.Value.Value), Neutral(optimized.Result.Value.Value));
    }
}
