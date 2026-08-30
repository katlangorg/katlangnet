using System.Text;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Sequences;

namespace KatLang.Tests;

/// <summary>
/// Budget cross-talk matrix: a program's behaviour with respect to resource limit
/// <c>L</c> must depend on <c>L</c> and on the resources the program actually
/// consumes — never on which UNRELATED limits happen to be configured.
///
/// <para><b>Why this exists.</b> Optimizer eligibility is decided by which budgets
/// were CONFIGURED, not by what the program does: <c>Evaluator.CreateRootCtx</c>
/// reads <c>EvaluationBudget.HasStepLimit</c>,
/// <c>HasConfiguredStringLimit</c> and <c>HasConfiguredMaterializationLimit</c> and
/// forces the generic strategy when any of them is set. That construction makes an
/// OPT-IN budget strategy-independent (it has no verdict at all while unconfigured,
/// so forcing one strategy once it IS configured settles the question). It does
/// nothing for an ALWAYS-ACTIVE budget — dynamic depth, the per-collection ceiling,
/// the per-string ceiling — which has a verdict on every run and therefore must be
/// EQUALIZED between the strategies instead. The per-collection ceiling already was
/// (<c>EvaluationBudget.CheckCollectionSize</c> on the fused range path); dynamic
/// depth was not, which is the defect this suite was written to find and now pins
/// (<see cref="ConfiguredStringLimit_DoesNotChangeDepthVerdict_OfAFusedSequencePipeline"/>).</para>
///
/// <para><b>How it tests.</b> Purely behaviourally. The harness never consults the
/// production strategy predicate; it builds limits, calls the public evaluator, and
/// compares outcomes. Every "unrelated" configuration is first PROVED non-binding for
/// the program under test by a solo run that must reproduce the unlimited outcome
/// exactly, so a failure can never be explained away as "that limit really did
/// bind".</para>
///
/// <para>Boundaries are discovered per case by bisection over the public API rather
/// than hard-coded, so the corpus keeps testing the real boundary if accounting
/// changes.</para>
/// </summary>
public class BudgetCrossTalkMatrixTests
{
    // ── Limit inventory ──────────────────────────────────────────────────────

    /// <summary>What a configurable limit governs, which decides how it is treated here.</summary>
    internal enum LimitClass
    {
        /// <summary>Bounds evaluation work/recursion; can select an evaluator strategy.</summary>
        RuntimeEvaluation,

        /// <summary>Bounds the program TREE before evaluation begins.</summary>
        PreflightStructural,

        /// <summary>Bounds values the run constructs.</summary>
        Materialization,

        /// <summary>Bounds rendered text only; must never reach evaluation.</summary>
        RenderOnly,
    }

    internal sealed record LimitDimension(
        string Name,
        LimitClass Class,
        Func<EvaluationLimits, long, EvaluationLimits> Configure,
        long MinimumValid,
        long SearchCeiling,
        /// <summary>Values expected to be non-binding for every corpus case; index 0 is the canonical one.</summary>
        IReadOnlyList<long> NonBindingValues,
        /// <summary>The value the DEFAULT configuration effectively enforces, written out explicitly.</summary>
        long ExplicitDefaultValue,
        /// <summary>The structured error this limit reports when it binds, or null when it never binds evaluation.</summary>
        string? LimitErrorKind);

    private static readonly LimitDimension MaxDepthDim = new(
        "MaxDepth", LimitClass.RuntimeEvaluation, (l, v) => l with { MaxDepth = (int)v },
        MinimumValid: 1, SearchCeiling: EvaluationLimits.MaxSupportedDepth,
        NonBindingValues: [EvaluationLimits.MaxSupportedDepth, 96, 64],
        ExplicitDefaultValue: EvaluationLimits.MaxSupportedDepth,
        LimitErrorKind: nameof(EvalError.EvaluationDepthExceeded));

    private static readonly LimitDimension MaxStepsDim = new(
        "MaxSteps", LimitClass.RuntimeEvaluation, (l, v) => l with { MaxSteps = v },
        MinimumValid: 1, SearchCeiling: 4_000_000,
        NonBindingValues: [long.MaxValue, 1_000_000, 200_000],
        ExplicitDefaultValue: long.MaxValue,
        LimitErrorKind: nameof(EvalError.EvaluationStepLimitExceeded));

    private static readonly LimitDimension MaxAstDepthDim = new(
        "MaxAstDepth", LimitClass.PreflightStructural, (l, v) => l with { MaxAstDepth = (int)v },
        MinimumValid: 1, SearchCeiling: EvaluationLimits.MaxSupportedAstDepth,
        NonBindingValues: [EvaluationLimits.MaxSupportedAstDepth, 280, 260],
        ExplicitDefaultValue: EvaluationLimits.MaxSupportedAstDepth,
        LimitErrorKind: nameof(EvalError.AstDepthLimitExceeded));

    private static readonly LimitDimension MaxCollectionItemsDim = new(
        "MaxCollectionItems", LimitClass.Materialization, (l, v) => l with { MaxCollectionItems = (int)v },
        MinimumValid: 1, SearchCeiling: EvaluationLimits.MaxSupportedCollectionItems,
        NonBindingValues: [EvaluationLimits.MaxSupportedCollectionItems, 50_000, 1_000],
        ExplicitDefaultValue: EvaluationLimits.MaxSupportedCollectionItems,
        LimitErrorKind: nameof(EvalError.CollectionSizeLimitExceeded));

    private static readonly LimitDimension MaxMaterializedItemsDim = new(
        "MaxMaterializedItems", LimitClass.Materialization, (l, v) => l with { MaxMaterializedItems = v },
        MinimumValid: 1, SearchCeiling: 4_000_000,
        NonBindingValues: [long.MaxValue, 1_000_000, 50_000],
        ExplicitDefaultValue: long.MaxValue,
        LimitErrorKind: nameof(EvalError.MaterializationLimitExceeded));

    private static readonly LimitDimension MaxStringLengthDim = new(
        "MaxStringLength", LimitClass.Materialization, (l, v) => l with { MaxStringLength = (int)v },
        MinimumValid: 0, SearchCeiling: EvaluationLimits.MaxSupportedStringLength,
        NonBindingValues: [EvaluationLimits.MaxSupportedStringLength, 100_000, 2_000],
        ExplicitDefaultValue: EvaluationLimits.MaxSupportedStringLength,
        LimitErrorKind: nameof(EvalError.StringSizeLimitExceeded));

    private static readonly LimitDimension MaxMaterializedStringCharsDim = new(
        "MaxMaterializedStringChars", LimitClass.Materialization, (l, v) => l with { MaxMaterializedStringChars = v },
        MinimumValid: 0, SearchCeiling: 4_000_000,
        NonBindingValues: [long.MaxValue, 1_000_000, 20_000],
        ExplicitDefaultValue: long.MaxValue,
        LimitErrorKind: nameof(EvalError.StringMaterializationLimitExceeded));

    private static readonly LimitDimension MaxDisplayLengthDim = new(
        "MaxDisplayLength", LimitClass.RenderOnly, (l, v) => l with { MaxDisplayLength = (int)v },
        MinimumValid: 0, SearchCeiling: EvaluationLimits.MaxSupportedDisplayLength,
        NonBindingValues: [EvaluationLimits.MaxSupportedDisplayLength, 100_000, 10_000],
        ExplicitDefaultValue: EvaluationLimits.MaxSupportedDisplayLength,
        LimitErrorKind: null);

    /// <summary>
    /// Every limit the public <see cref="EvaluationLimits"/> surface exposes. All eight
    /// participate as UNRELATED dimensions; the seven with an evaluation verdict also
    /// serve as primaries. Adding a public limit without adding it here leaves a hole,
    /// which <see cref="Inventory_CoversEveryPublicEvaluationLimit"/> refuses.
    /// </summary>
    private static readonly LimitDimension[] AllDimensions =
    [
        MaxDepthDim, MaxStepsDim, MaxAstDepthDim, MaxCollectionItemsDim,
        MaxMaterializedItemsDim, MaxStringLengthDim, MaxMaterializedStringCharsDim, MaxDisplayLengthDim,
    ];

    // ── Verdicts ─────────────────────────────────────────────────────────────

    /// <summary>
    /// One run's observable outcome. <see cref="Kind"/> is the coarse classification
    /// entry points can agree on; <see cref="Payload"/> is the full structured detail
    /// and is only ever compared between runs of the SAME entry point.
    ///
    /// <para><see cref="Value"/> carries the structured result so equality goes through
    /// <see cref="Result.ValueComparer"/>. The record-synthesised equality would compare
    /// a <c>SequenceValue</c>'s item collection by REFERENCE and call two structurally
    /// different sequences equal, which would silently weaken every comparison in this
    /// file.</para>
    /// </summary>
    private readonly record struct Verdict(string Kind, string Payload, Result? Value = null)
    {
        public bool Equals(Verdict other)
            => Kind == other.Kind
                && Payload == other.Payload
                && (Value is null
                    ? other.Value is null
                    : other.Value is not null && Result.ValueComparer.Equals(Value, other.Value));

        public override int GetHashCode() => HashCode.Combine(Kind, Payload);

        public override string ToString() => $"{Kind} [{Payload}]";
    }

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;
        return error;
    }

    private static Verdict Failure(EvalError error)
    {
        var inner = Innermost(error);
        return new Verdict(inner.GetType().Name, (inner with { Span = null }).ToString());
    }

    private static Verdict Ok(string payload) => new("ok", payload);

    private static Verdict Ok(Result value, string suffix = "")
        => new("ok", RenderValue(value) + suffix, value);

    private static Verdict CountedVerdict(EvalResult<Evaluator.CountedResult> result)
        => result.IsError
            ? Failure(result.Error)
            : Ok(result.Value.Value, $"|{result.Value.EmittedCount}");

    /// <summary>
    /// Structural rendering for verdict payloads. <c>Result.ToString()</c> prints the
    /// COLLECTION TYPE for sequences and lists, so it cannot distinguish two different
    /// sequences. Bounded so a pathological corpus value cannot make the matrix quadratic;
    /// the bound is far above anything this corpus produces, and equality additionally
    /// goes through <see cref="Result.ValueComparer"/>.
    /// </summary>
    private const int MaxRenderedPayload = 8_192;

    private static string RenderValue(Result value)
    {
        var builder = new StringBuilder();
        Append(value, builder);
        return builder.ToString();

        static void Append(Result value, StringBuilder builder)
        {
            if (builder.Length > MaxRenderedPayload)
                return;

            switch (value)
            {
                case Result.Atom atom:
                    builder.Append(atom.Value.ToString(System.Globalization.CultureInfo.InvariantCulture));
                    return;
                case Result.Str str:
                    builder.Append('\'').Append(str.Value).Append('\'');
                    return;
                case Result.SequenceValue sequence:
                    AppendItems(sequence.Items, '(', ')', builder);
                    return;
                case Result.ListValue list:
                    AppendItems(list.Items, '[', ']', builder);
                    return;
                default:
                    builder.Append('<').Append(value.GetType().Name).Append('>');
                    return;
            }
        }

        static void AppendItems(IReadOnlyList<Result> items, char open, char close, StringBuilder builder)
        {
            builder.Append(open);
            for (var i = 0; i < items.Count; i++)
            {
                if (i > 0) builder.Append(", ");
                Append(items[i], builder);
            }

            builder.Append(close);
        }
    }

    // ── Entry points ─────────────────────────────────────────────────────────

    private sealed record EntryPoint(string Name, bool RequiresSource, Func<BudgetCase, EvaluationLimits, Verdict> Run);

    private static readonly EntryPoint[] EntryPoints =
    [
        new("Evaluator.Run(limits)", false, static (c, l) =>
        {
            var r = Evaluator.Run(c.Ast, l);
            return r.IsError ? Failure(r.Error) : Ok(r.Value);
        }),
        new("Evaluator.RunFlat(limits)", false, static (c, l) =>
        {
            var r = Evaluator.RunFlat(c.Ast, l);
            return r.IsError ? Failure(r.Error) : Ok(string.Join(",", r.Value));
        }),
        new("Evaluator.RunCounted(cache, limits)", false, static (c, l) =>
        {
            var r = Evaluator.RunCounted(c.Ast, new RunScopedZeroArgPropertyResultCache(), l);
            return r.IsError ? Failure(r.Error) : Ok(r.Value.Value, $"|{r.Value.EmittedCount}");
        }),
        new("Evaluator.RunCountedObserved(optimized)", false, static (c, l) =>
        {
            var (r, _) = Evaluator.RunCountedObserved(c.Ast, l, enableOptimizations: true);
            return r.IsError ? Failure(r.Error) : Ok(r.Value.Value, $"|{r.Value.EmittedCount}");
        }),
        new("Evaluator.RunCountedObserved(unoptimized)", false, static (c, l) =>
        {
            var (r, _) = Evaluator.RunCountedObserved(c.Ast, l, enableOptimizations: false);
            return r.IsError ? Failure(r.Error) : Ok(r.Value.Value, $"|{r.Value.EmittedCount}");
        }),
        new("Evaluator.RunObserved", false, static (c, l) =>
        {
            var r = Evaluator.RunObserved(c.Ast, new EvaluationObservations(), enableOptimizations: true, l);
            return r.IsError ? Failure(r.Error) : Ok(r.Value);
        }),
        new("Evaluator.RunCountedWithTopLevelProperty", false, static (c, l) =>
        {
            var r = Evaluator.RunCountedWithTopLevelProperty(
                c.Ast, c.TopLevelPropertyName, new RunScopedZeroArgPropertyResultCache(), l);
            return r.IsError
                ? Failure(r.Error)
                : Ok(r.Value.Output.Value,
                    $"|{r.Value.Output.EmittedCount}|{(r.Value.TopLevelProperty is { } p ? RenderValue(p.Value) : "<none>")}");
        }),
        new("KatLangEngine.Run", true, static (c, l) => EngineVerdict(c, l)),
        new("KatLangEngine.EvaluateToString", true, static (c, l) =>
            Ok(KatLangEngine.EvaluateToString(c.Source!, new RunOptions { EvaluationLimits = l }))),
    ];

    /// <summary>
    /// The entry points that perform exactly the SAME evaluation work, and therefore must
    /// classify every configuration identically. Three public surfaces are deliberately
    /// outside this set — they are still individually checked for cross-talk:
    /// <list type="bullet">
    ///   <item><c>RunCountedWithTopLevelProperty</c> additionally evaluates a named
    ///   top-level property, so it legitimately charges more and may stop at a budget the
    ///   others clear.</item>
    ///   <item><c>KatLangEngine.EvaluateToString</c> RENDERS failures as text, so it has
    ///   no failure classification to compare.</item>
    ///   <item><c>KatLangEngine.Run</c> reports failures as formatted messages rather than
    ///   structured kinds; it is compared on success/failure only
    ///   (<see cref="EngineAgreesOnSuccessWithTheStructuredSurfaces"/>).</item>
    /// </list>
    /// </summary>
    private static readonly string[] WorkIdenticalEntryPoints =
    [
        "Evaluator.Run(limits)",
        "Evaluator.RunFlat(limits)",
        "Evaluator.RunCounted(cache, limits)",
        "Evaluator.RunCountedObserved(optimized)",
        "Evaluator.RunCountedObserved(unoptimized)",
        "Evaluator.RunObserved",
    ];

    private static Verdict EngineVerdict(BudgetCase c, EvaluationLimits limits)
    {
        var result = KatLangEngine.Run(c.Source!, new RunOptions { EvaluationLimits = limits });
        return result switch
        {
            RunResult.Success s => Ok(s.ToDisplayString()),
            RunResult.NoProgramOutput n => new Verdict("noOutput", n.ToDisplayString()),
            RunResult.ParseFailure p => new Verdict("parseFailure", string.Join("|", p.Errors.Select(e => e.Message))),
            RunResult.EvalFailure e => new Verdict("evalFailure", string.Join("|", e.Errors.Select(x => x.Message))),
            _ => new Verdict("unknown", result.GetType().Name),
        };
    }

    /// <summary>The entry point the presence/value matrices run on: counted, optimized, structured.</summary>
    private static readonly EntryPoint MatrixEntryPoint =
        EntryPoints.Single(e => e.Name == "Evaluator.RunCountedObserved(optimized)");

    // ── Corpus ───────────────────────────────────────────────────────────────

    /// <summary>
    /// One program plus the limits it genuinely exercises. The declared primaries are
    /// matrix METADATA (which boundaries to go looking for), never the oracle for what
    /// the program does — every boundary is measured, and every expectation compared
    /// against a measured baseline.
    /// </summary>
    private sealed class BudgetCase(string name, string? source, Expr ast, params LimitDimension[] primaries)
    {
        public string Name { get; } = name;

        public string? Source { get; } = source;

        public Expr Ast { get; } = ast;

        public IReadOnlyList<LimitDimension> Primaries { get; } = primaries;

        public string TopLevelPropertyName { get; init; } = "Probe";

        public override string ToString() => Name;
    }

    private static Expr FromSource(string source)
        => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

    private static void AssertSameExactDepthBoundary(string source, int minimumFusionHits = 1)
    {
        var ast = FromSource(source);
        var diagnostics = new KatLang.Optimizations.Sequences.SequencePipelineDiagnostics();
        var (optimized, optimizedBudget) = Evaluator.RunCountedObserved(
            ast,
            enableOptimizations: true,
            sequenceDiagnostics: diagnostics);
        var (generic, genericBudget) = Evaluator.RunCountedObserved(ast, enableOptimizations: false);

        Assert.False(optimized.IsError, $"optimized run failed: {(optimized.IsError ? optimized.Error : null)}");
        Assert.False(generic.IsError, $"generic run failed: {(generic.IsError ? generic.Error : null)}");
        Assert.True(Result.ValueComparer.Equals(generic.Value.Value, optimized.Value.Value));
        Assert.Equal(generic.Value.EmittedCount, optimized.Value.EmittedCount);
        Assert.Equal(genericBudget.ConsumedSteps, optimizedBudget.ConsumedSteps);
        Assert.True(
            diagnostics.GetSnapshot().FilterCountFusionHits >= minimumFusionHits,
            "The optimized side did not execute the fused path under test.");
        Assert.Equal(genericBudget.PeakDepth, optimizedBudget.PeakDepth);

        var requiredDepth = optimizedBudget.PeakDepth;
        Assert.True(requiredDepth > 1);
        foreach (var offset in new[] { -1, 0, 1 })
        {
            var limits = new EvaluationLimits { MaxDepth = requiredDepth + offset };
            var optimizedAtBoundary = Evaluator.RunCountedObserved(
                ast,
                limits,
                enableOptimizations: true).Result;
            var genericAtBoundary = Evaluator.RunCountedObserved(
                ast,
                limits,
                enableOptimizations: false).Result;

            Assert.Equal(optimizedAtBoundary.IsError, genericAtBoundary.IsError);
            if (offset < 0)
            {
                Assert.IsType<EvalError.EvaluationDepthExceeded>(Innermost(optimizedAtBoundary.Error));
                Assert.IsType<EvalError.EvaluationDepthExceeded>(Innermost(genericAtBoundary.Error));
            }
            else
            {
                Assert.False(optimizedAtBoundary.IsError);
                Assert.True(Result.ValueComparer.Equals(
                    genericAtBoundary.Value.Value,
                    optimizedAtBoundary.Value.Value));
            }
        }
    }

    private static BudgetCase Source(string name, string source, params LimitDimension[] primaries)
        => new(name, source, FromSource(source), primaries);

    /// <summary>k levels of <c>e = e + e</c> over ONE shared reference: k+1 nodes, 2^k evaluations (F3).</summary>
    private static Expr SharedBinaryDag(int levels)
    {
        Expr e = new Expr.Num(1);
        for (var i = 0; i < levels; i++)
            e = new Expr.Binary(BinaryOp.Add, e, e);
        return e;
    }

    /// <summary>A runtime-trivial tree that is deep only structurally.</summary>
    private static Expr UnarySpine(int depth)
    {
        Expr e = new Expr.Num(1);
        for (var i = 0; i < depth; i++)
            e = new Expr.Unary(UnaryOp.Minus, e);
        return e;
    }

    /// <summary>
    /// A host-built tree that is not reachable from the parser in this exact shape:
    /// a Capture bundle, a Call, a property-style DotCall and an args DotCall, over one
    /// REFERENCE-SHARED subtree, with a structurally deep spine inside.
    /// </summary>
    private static Expr HostShapedProgram()
    {
        var shared = new Expr.Binary(BinaryOp.Add, new Expr.Num(2), UnarySpine(40));
        var capture = new Expr.Capture(OutputBundle.From([shared, shared, new Expr.Num(3)]));
        var listed = new Expr.ListLiteral(OutputBundle.From([capture, shared]));
        var counted = new Expr.DotCall(listed, "count");
        var call = new Expr.Call(new Expr.Resolve("sum"), OutputBundle.From([capture]));
        var taken = new Expr.DotCall(listed, "take", OutputBundle.From([new Expr.Num(1)]));
        var program = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties:
            [
                new Property("Probe", new Algorithm.User(null, [], [], [], [counted])),
            ],
            Output: [new Expr.Binary(BinaryOp.Add, counted, call), new Expr.DotCall(taken, "count")]);
        return new Expr.AlgorithmExpr(program);
    }

    private static Expr LongStringProgram(int length)
        => new Expr.AlgorithmExpr(new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [new Property("Probe", new Algorithm.User(null, [], [], [], [new Expr.Num(1)]))],
            Output: [new Expr.StringLiteral(new string('x', length))]));

    private const string CountDown = "f(0) = 0\nf(n) = f(n - 1)\n";

    private static readonly BudgetCase[] Corpus =
    [
        // Tiny scalar: must be near-invariant under every non-pathological configuration.
        Source("TinyScalar", "Probe = 1\n1"),

        // Step-heavy, shallow, no strings and no collections.
        Source("StepHeavyShallowLoop", "Probe = 1\nInc = x + 1\nInc.repeat(400, 0)", MaxStepsDim),

        // Deep evaluation, tiny result: depth and steps, nothing else.
        Source("DeepRecursionTinyResult", $"Probe = 1\n{CountDown}f(40)", MaxDepthDim, MaxStepsDim),

        // Collection-heavy, tiny string.
        Source("CollectionHeavy", "Probe = 1\nrange(1, 200).count",
            MaxCollectionItemsDim, MaxMaterializedItemsDim),

        // Collection-heavy through a callback (invocation-heavy as well).
        Source("CollectionCallbackHeavy", "Probe = 1\nDbl(a) = a * 2\nrange(1, 60).map(Dbl).sum",
            MaxCollectionItemsDim, MaxMaterializedItemsDim, MaxStepsDim),

        // The fusion-eligible shape whose strategy the unrelated flags select, with a
        // predicate deep enough that the two strategies' depth accounting is decisive.
        Source("FusedFilterCountDeepPredicate",
            $"Probe = 1\n{CountDown}P(x) = f(6) + 1\nrange(1, 3).filter(P).count",
            MaxDepthDim, MaxStepsDim, MaxCollectionItemsDim),

        // Same shape, but the depth lives in the fused RANGE BOUNDS rather than the predicate.
        Source("FusedFilterCountDeepBounds",
            $"Probe = 1\n{CountDown}Q(x) = 1\nrange(1, f(20) + 3).filter(Q).count",
            MaxDepthDim),

        // Shared VALUE DAG (F5): equality/hash over a value with exponential unfolding.
        Source("SharedValueDag", "Probe = 1\nWrap = [x, x]\nD = Wrap.repeat(10, 1)\nD == D",
            MaxMaterializedItemsDim, MaxCollectionItemsDim),

        // A deterministic non-resource failure: its error kind must survive every
        // unrelated configuration untouched.
        Source("SemanticFailure", "Probe = 1\n1 / 0"),

        // Shared EXPRESSION DAG (F3): host-built, charges only bulk expression work.
        new("SharedExpressionDag", null, SharedBinaryDag(15), MaxStepsDim),

        // Structurally deep, runtime-trivial: preflight only.
        new("PreflightDeepSpine", null,
            new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [], [UnarySpine(150)])), MaxAstDepthDim),

        // Host AST exercising Capture / Call / DotCall / args-DotCall over a shared subtree.
        new("HostCaptureCallDotCall", null, HostShapedProgram(), MaxAstDepthDim, MaxCollectionItemsDim),

        // String-heavy, low step count: reachable only through a host-built AST.
        new("HostLongString", null, LongStringProgram(600), MaxStringLengthDim, MaxMaterializedStringCharsDim),
    ];

    // ── Boundary discovery ───────────────────────────────────────────────────

    private static EvaluationLimits Only(LimitDimension dimension, long value)
        => dimension.Configure(EvaluationLimits.Default, value);

    /// <summary>
    /// Smallest value of <paramref name="dimension"/> at which <paramref name="c"/> avoids
    /// that dimension's own limit error, found by bisection over the public entry point.
    /// Behavioural: no production predicate is consulted and no counter is read.
    /// </summary>
    private static long FindBoundary(BudgetCase c, LimitDimension dimension)
    {
        bool Binds(long value) => MatrixEntryPoint.Run(c, Only(dimension, value)).Kind == dimension.LimitErrorKind;

        var high = dimension.SearchCeiling;
        Assert.False(
            Binds(high),
            $"{c.Name}: {dimension.Name} still binds at its search ceiling {high}; the corpus case outgrew the matrix.");

        var low = dimension.MinimumValid;
        if (!Binds(low))
            return low;

        // invariant: Binds(low), !Binds(high)
        while (high - low > 1)
        {
            var mid = low + ((high - low) / 2);
            if (Binds(mid)) low = mid; else high = mid;
        }

        return high;
    }

    /// <summary>
    /// The probes for one primary: the exact boundary (must succeed) and one below it
    /// (must fail with that limit's own error). Cases whose boundary sits at the minimum
    /// valid value contribute the passing probe only.
    /// </summary>
    private static IEnumerable<(LimitDimension Dim, long Value)> PrimaryProbes(BudgetCase c, LimitDimension dimension)
    {
        var boundary = FindBoundary(c, dimension);
        yield return (dimension, boundary);
        if (boundary > dimension.MinimumValid)
            yield return (dimension, boundary - 1);
    }

    // ── Non-binding proof ────────────────────────────────────────────────────

    /// <summary>
    /// Proves that <paramref name="value"/> for <paramref name="dimension"/> is non-binding
    /// for this program: configured ALONE it must reproduce the unlimited outcome exactly.
    /// Every matrix combination is built only from configurations that passed this.
    /// </summary>
    private static void AssertNonBinding(BudgetCase c, LimitDimension dimension, long value)
    {
        var unlimited = MatrixEntryPoint.Run(c, EvaluationLimits.Default);
        var solo = MatrixEntryPoint.Run(c, Only(dimension, value));
        Assert.True(
            unlimited == solo,
            $"""
             Matrix precondition failed: {dimension.Name}={value} BINDS for case {c.Name},
             so it cannot serve as an unrelated dimension.
               default          -> {unlimited}
               {dimension.Name}={value} -> {solo}
             """);
    }

    // ── Matrix execution ─────────────────────────────────────────────────────

    private static EvaluationLimits Compose(
        LimitDimension primary, long primaryValue, IReadOnlyList<(LimitDimension Dim, long Value)> extras)
    {
        var limits = Only(primary, primaryValue);
        foreach (var (dim, value) in extras)
            limits = dim.Configure(limits, value);
        return limits;
    }

    private static string Describe(IReadOnlyList<(LimitDimension Dim, long Value)> extras)
        => extras.Count == 0 ? "<none>" : string.Join(", ", extras.Select(e => $"{e.Dim.Name}={e.Value}"));

    private static void AssertNoCrossTalk(
        BudgetCase c,
        EntryPoint entryPoint,
        LimitDimension primary,
        long primaryValue,
        Verdict baseline,
        IReadOnlyList<(LimitDimension Dim, long Value)> extras,
        List<string> failures)
    {
        var actual = entryPoint.Run(c, Compose(primary, primaryValue, extras));
        if (actual == baseline)
            return;

        failures.Add(
            $"""
             Budget cross-talk failure:
               case:            {c.Name}
               primary:         {primary.Name}={primaryValue}
               other limits:    {Describe(extras)}
               entry point:     {entryPoint.Name}
               baseline:        {baseline}
               actual:          {actual}
             """);
    }

    private static void AssertClean(List<string> failures, int executions)
    {
        Assert.True(
            failures.Count == 0,
            $"{failures.Count} cross-talk failures out of {executions} executions:{Environment.NewLine}"
            + string.Join(Environment.NewLine + Environment.NewLine, failures.Take(12)));
        Assert.True(executions > 0, "The matrix executed nothing; the corpus or dimension table degenerated.");
    }

    // ── Inventory guard ──────────────────────────────────────────────────────

    [Fact]
    public void Inventory_CoversEveryPublicEvaluationLimit()
    {
        var configured = AllDimensions.Select(d => d.Name).OrderBy(n => n, StringComparer.Ordinal).ToArray();
        var declared = typeof(EvaluationLimits)
            .GetProperties()
            .Where(p => p.Name.StartsWith("Max", StringComparison.Ordinal))
            .Select(p => p.Name)
            .OrderBy(n => n, StringComparer.Ordinal)
            .ToArray();

        Assert.Equal(declared, configured);
    }

    // ── A. Presence cross-talk: the full power set ───────────────────────────

    /// <summary>
    /// For every corpus case, every primary limit, and both sides of that limit's exact
    /// boundary: adding any SUBSET of the other seven limits — each at a value already
    /// proved non-binding for this program — must leave the verdict untouched.
    /// The power set is exhaustive (2^7 per probe) rather than pairwise: the whole point
    /// is the combinations that "should not matter".
    /// </summary>
    [Fact]
    public void BudgetConfiguration_UnrelatedLimitPresenceDoesNotChangeVerdict()
    {
        var failures = new List<string>();
        var executions = 0;

        foreach (var c in Corpus)
        {
            foreach (var primary in c.Primaries)
            {
                var others = AllDimensions.Where(d => d != primary).ToArray();
                foreach (var other in others)
                    AssertNonBinding(c, other, other.NonBindingValues[0]);

                foreach (var (dim, value) in PrimaryProbes(c, primary))
                {
                    var baseline = MatrixEntryPoint.Run(c, Only(dim, value));
                    for (var mask = 0; mask < 1 << others.Length; mask++)
                    {
                        var extras = new List<(LimitDimension, long)>();
                        for (var bit = 0; bit < others.Length; bit++)
                        {
                            if ((mask & (1 << bit)) != 0)
                                extras.Add((others[bit], others[bit].NonBindingValues[0]));
                        }

                        executions++;
                        AssertNoCrossTalk(c, MatrixEntryPoint, dim, value, baseline, extras, failures);
                    }
                }
            }
        }

        AssertClean(failures, executions);
    }

    // ── B. Value cross-talk ──────────────────────────────────────────────────

    /// <summary>
    /// Once an unrelated limit IS configured, its VALUE must not matter either, as long
    /// as it stays non-binding. Sweeps every unrelated dimension across its non-binding
    /// probe values, singly and in pairs, on both sides of the primary boundary.
    /// </summary>
    [Fact]
    public void BudgetConfiguration_UnrelatedLimitValueDoesNotChangeVerdict()
    {
        var failures = new List<string>();
        var executions = 0;

        foreach (var c in Corpus)
        {
            foreach (var primary in c.Primaries)
            {
                var others = AllDimensions.Where(d => d != primary).ToArray();
                foreach (var other in others)
                    foreach (var value in other.NonBindingValues)
                        AssertNonBinding(c, other, value);

                foreach (var (dim, value) in PrimaryProbes(c, primary))
                {
                    var baseline = MatrixEntryPoint.Run(c, Only(dim, value));

                    foreach (var other in others)
                    {
                        foreach (var otherValue in other.NonBindingValues)
                        {
                            executions++;
                            AssertNoCrossTalk(c, MatrixEntryPoint, dim, value, baseline, [(other, otherValue)], failures);
                        }
                    }

                    // Pairwise value sweep: two unrelated limits at every combination of
                    // their non-binding values.
                    for (var i = 0; i < others.Length; i++)
                    {
                        for (var j = i + 1; j < others.Length; j++)
                        {
                            foreach (var vi in others[i].NonBindingValues)
                            {
                                foreach (var vj in others[j].NonBindingValues)
                                {
                                    executions++;
                                    AssertNoCrossTalk(
                                        c, MatrixEntryPoint, dim, value, baseline,
                                        [(others[i], vi), (others[j], vj)], failures);
                                }
                            }
                        }
                    }
                }
            }
        }

        AssertClean(failures, executions);
    }

    // ── C. Configured-but-non-binding, and explicitly-default ────────────────

    /// <summary>
    /// The most important presence case: a limit that is UNSET versus the same limit
    /// configured to exactly the value the default already enforces. If "configuredness"
    /// were semantic state, these would differ — and before the fix they did, because
    /// writing out <c>MaxStringLength = MaxSupportedStringLength</c> switched the
    /// sequence-pipeline optimizer off for the whole run.
    /// </summary>
    [Fact]
    public void BudgetConfiguration_ExplicitDefaultValueBehavesLikeUnset()
    {
        var failures = new List<string>();
        var executions = 0;

        foreach (var c in Corpus)
        {
            foreach (var entryPoint in EntryPoints)
            {
                if (entryPoint.RequiresSource && c.Source is null)
                    continue;

                var unset = entryPoint.Run(c, EvaluationLimits.Default);
                foreach (var dimension in AllDimensions)
                {
                    executions++;
                    var explicitDefault = entryPoint.Run(c, Only(dimension, dimension.ExplicitDefaultValue));
                    if (explicitDefault == unset)
                        continue;

                    failures.Add(
                        $"""
                         Explicit-default cross-talk:
                           case:        {c.Name}
                           entry point: {entryPoint.Name}
                           limit:       {dimension.Name} written out as {dimension.ExplicitDefaultValue}
                           unset:       {unset}
                           explicit:    {explicitDefault}
                         """);
                }
            }
        }

        AssertClean(failures, executions);
    }

    /// <summary>
    /// The opposite direction: a MINIMAL unrelated limit on a resource the program does
    /// not use at all must also be inert. A scalar program does not become a collection
    /// error because <c>MaxCollectionItems</c> is 1.
    /// </summary>
    [Fact]
    public void BudgetConfiguration_MinimalLimitOnAnUnusedResourceIsInert()
    {
        var scalar = Source("ScalarOnly", "Probe = 1\n2 + 3");
        var baseline = MatrixEntryPoint.Run(scalar, EvaluationLimits.Default);

        (LimitDimension Dim, long Value)[] minimal =
        [
            (MaxCollectionItemsDim, 1),
            (MaxMaterializedItemsDim, 1),
            (MaxStringLengthDim, 0),
            (MaxMaterializedStringCharsDim, 0),
            (MaxDisplayLengthDim, 0),
        ];

        foreach (var (dim, value) in minimal)
        {
            Assert.True(
                MatrixEntryPoint.Run(scalar, Only(dim, value)) == baseline,
                $"{dim.Name}={value} changed a scalar program that consumes none of that resource.");
        }

        // …and all of them at once, on top of a binding-adjacent step budget.
        var all = minimal.Aggregate(Only(MaxStepsDim, 8), (limits, m) => m.Dim.Configure(limits, m.Value));
        Assert.Equal(MatrixEntryPoint.Run(scalar, Only(MaxStepsDim, 8)), MatrixEntryPoint.Run(scalar, all));
    }

    // ── D. Entry-point parity ────────────────────────────────────────────────

    /// <summary>
    /// Two separate claims about the guarded public entry points.
    ///
    /// <para>(1) EVERY entry point is individually free of cross-talk: adding unrelated
    /// non-binding limits leaves that surface's own outcome unchanged. This is what
    /// catches "one overload treats <i>configured</i> differently from another".</para>
    ///
    /// <para>(2) The entry points that perform identical work
    /// (<see cref="WorkIdenticalEntryPoints"/>) classify every configuration identically,
    /// which is what catches "one overload bypasses a guard".</para>
    /// </summary>
    [Fact]
    public void BudgetConfiguration_EntryPointsAgreeAcrossLimitSubsets()
    {
        var failures = new List<string>();
        var executions = 0;

        foreach (var c in Corpus)
        {
            var applicable = EntryPoints.Where(e => !e.RequiresSource || c.Source is not null).ToArray();
            var workIdentical = applicable.Where(e => WorkIdenticalEntryPoints.Contains(e.Name)).ToArray();

            foreach (var primary in c.Primaries)
            {
                var others = AllDimensions.Where(d => d != primary).ToArray();

                foreach (var (dim, value) in PrimaryProbes(c, primary))
                {
                    // One configuration per unrelated dimension, plus none and all.
                    var configurations = new List<(LimitDimension Dim, long Value)[]>
                    {
                        Array.Empty<(LimitDimension, long)>(),
                        others.Select(o => (o, o.NonBindingValues[0])).ToArray(),
                    };
                    configurations.AddRange(others.Select(o => new[] { (o, o.NonBindingValues[0]) }));

                    var baselines = applicable.ToDictionary(
                        e => e.Name, e => e.Run(c, Only(dim, value)));

                    foreach (var extras in configurations)
                    {
                        var limits = Compose(dim, value, extras);

                        foreach (var entryPoint in applicable)
                        {
                            executions++;
                            AssertNoCrossTalk(
                                c, entryPoint, dim, value, baselines[entryPoint.Name], extras, failures);
                        }

                        var kinds = workIdentical
                            .Select(e => (e.Name, Kind: SucceededKind(e.Run(c, limits))))
                            .ToArray();
                        if (kinds.Select(k => k.Kind).Distinct().Count() <= 1)
                            continue;

                        failures.Add(
                            $"""
                             Entry-point divergence on identical work:
                               case:         {c.Name}
                               primary:      {dim.Name}={value}
                               other limits: {Describe(extras)}
                               {string.Join(Environment.NewLine + "  ", kinds.Select(k => $"{k.Name} -> {k.Kind}"))}
                             """);
                    }
                }
            }
        }

        AssertClean(failures, executions);
    }

    private static string SucceededKind(Verdict verdict)
        => verdict.Kind == "ok" ? "ok" : "stopped:" + verdict.Kind;

    /// <summary>
    /// <see cref="KatLangEngine"/> reports failures as formatted messages, so it can only
    /// be held to the coarse claim: it succeeds exactly when the structured evaluator
    /// surfaces do, under every limit subset.
    /// </summary>
    [Fact]
    public void EngineAgreesOnSuccessWithTheStructuredSurfaces()
    {
        var failures = new List<string>();
        var executions = 0;

        foreach (var c in Corpus.Where(c => c.Source is not null))
        {
            foreach (var primary in c.Primaries)
            {
                var others = AllDimensions.Where(d => d != primary).ToArray();
                foreach (var (dim, value) in PrimaryProbes(c, primary))
                {
                    for (var mask = 0; mask < 1 << others.Length; mask++)
                    {
                        var extras = new List<(LimitDimension, long)>();
                        for (var bit = 0; bit < others.Length; bit++)
                        {
                            if ((mask & (1 << bit)) != 0)
                                extras.Add((others[bit], others[bit].NonBindingValues[0]));
                        }

                        executions++;
                        var limits = Compose(dim, value, extras);
                        var structured = MatrixEntryPoint.Run(c, limits).Kind == "ok";
                        var engine = EngineVerdict(c, limits).Kind == "ok";
                        if (structured == engine)
                            continue;

                        failures.Add(
                            $"""
                             Engine/evaluator divergence:
                               case:         {c.Name}
                               primary:      {dim.Name}={value}
                               other limits: {Describe(extras.Select(e => (e.Item1, e.Item2)).ToArray())}
                               evaluator succeeded: {structured}
                               engine succeeded:    {engine}
                             """);
                    }
                }
            }
        }

        AssertClean(failures, executions);
    }

    /// <summary>
    /// The no-limits overloads are not a separate policy: they must behave exactly like
    /// the same call with <see cref="EvaluationLimits.Default"/> written out.
    /// </summary>
    [Fact]
    public void NoLimitOverloads_MatchExplicitDefaultLimits()
    {
        foreach (var c in Corpus)
        {
            var run = Evaluator.Run(c.Ast);
            var runWithDefault = Evaluator.Run(c.Ast, EvaluationLimits.Default);
            Assert.Equal(run.IsError, runWithDefault.IsError);
            if (!run.IsError)
                Assert.True(Result.ValueComparer.Equals(run.Value, runWithDefault.Value), c.Name);

            var flat = Evaluator.RunFlat(c.Ast);
            var flatWithDefault = Evaluator.RunFlat(c.Ast, EvaluationLimits.Default);
            Assert.Equal(flat.IsError, flatWithDefault.IsError);
            if (!flat.IsError)
                Assert.Equal(flat.Value, flatWithDefault.Value);

            var counted = Evaluator.RunCounted(c.Ast);
            var countedWithDefault = Evaluator.RunCounted(
                c.Ast, new RunScopedZeroArgPropertyResultCache(), EvaluationLimits.Default);
            Assert.Equal(counted.IsError, countedWithDefault.IsError);
            if (!counted.IsError)
                Assert.True(Result.ValueComparer.Equals(counted.Value.Value, countedWithDefault.Value.Value), c.Name);
        }
    }

    // ── E. Error-kind stability ──────────────────────────────────────────────

    /// <summary>
    /// A program that deterministically exceeds ONE limit must keep reporting that
    /// limit's error however many unrelated budgets are added around it. A different
    /// resource winning would mean the added configuration changed what the run did.
    /// </summary>
    [Fact]
    public void BudgetConfiguration_ErrorKindIsStableUnderUnrelatedLimits()
    {
        var failures = new List<string>();
        var executions = 0;

        foreach (var c in Corpus)
        {
            foreach (var primary in c.Primaries)
            {
                var boundary = FindBoundary(c, primary);
                if (boundary <= primary.MinimumValid)
                    continue;

                var failing = boundary - 1;
                var expected = MatrixEntryPoint.Run(c, Only(primary, failing));
                Assert.Equal(primary.LimitErrorKind, expected.Kind);

                var others = AllDimensions.Where(d => d != primary).ToArray();
                for (var mask = 0; mask < 1 << others.Length; mask++)
                {
                    var extras = new List<(LimitDimension, long)>();
                    for (var bit = 0; bit < others.Length; bit++)
                    {
                        if ((mask & (1 << bit)) != 0)
                            extras.Add((others[bit], others[bit].NonBindingValues[0]));
                    }

                    executions++;
                    var actual = MatrixEntryPoint.Run(c, Compose(primary, failing, extras));
                    if (actual.Kind == primary.LimitErrorKind)
                        continue;

                    failures.Add(
                        $"""
                         Error-kind cross-talk:
                           case:         {c.Name}
                           primary:      {primary.Name}={failing}
                           other limits: {Describe(extras.Select(e => (e.Item1, e.Item2)).ToArray())}
                           expected:     {primary.LimitErrorKind}
                           actual:       {actual}
                         """);
                }
            }
        }

        AssertClean(failures, executions);
    }

    // ── F. Strategy independence, observed behaviourally ─────────────────────

    /// <summary>
    /// The root invariant behind the whole family, stated without reference to any
    /// configuration flag: the OPTIMIZED and GENERIC strategies must consume the same
    /// dynamic depth. Depth is always active, so unlike the opt-in step and cumulative
    /// budgets it cannot be protected by forcing one strategy — and because strategy
    /// selection is driven by which unrelated budgets were configured, any depth
    /// difference here is directly a cross-talk defect.
    /// </summary>
    [Fact]
    public void OptimizedAndGenericStrategies_ConsumeIdenticalDynamicDepth()
    {
        var mismatches = new List<string>();

        foreach (var c in Corpus)
        {
            var (optimized, optimizedBudget) = Evaluator.RunCountedObserved(c.Ast, enableOptimizations: true);
            var (generic, genericBudget) = Evaluator.RunCountedObserved(c.Ast, enableOptimizations: false);

            Assert.Equal(optimized.IsError, generic.IsError);
            if (optimizedBudget.PeakDepth == genericBudget.PeakDepth)
                continue;

            mismatches.Add(
                $"{c.Name}: optimized PeakDepth={optimizedBudget.PeakDepth}, "
                + $"generic PeakDepth={genericBudget.PeakDepth}");
        }

        Assert.True(
            mismatches.Count == 0,
            "Optimizer strategy changed dynamic depth consumption, so an unrelated configured budget "
            + $"decides a MaxDepth verdict:{Environment.NewLine}{string.Join(Environment.NewLine, mismatches)}");
    }

    /// <summary>
    /// The behavioural form of the same claim, at the points where it is decidable: at
    /// every primary limit's exact boundary — and with each unrelated limit configured on
    /// top — the optimized and generic strategies must produce the SAME verdict, value and
    /// structured error payload. This is what a caller actually observes when a configured
    /// unrelated budget silently switches strategy underneath them.
    /// </summary>
    [Fact]
    public void OptimizedAndGenericStrategies_AgreeAtEveryPrimaryLimitBoundary()
    {
        var optimized = EntryPoints.Single(e => e.Name == "Evaluator.RunCountedObserved(optimized)");
        var generic = EntryPoints.Single(e => e.Name == "Evaluator.RunCountedObserved(unoptimized)");
        var failures = new List<string>();
        var executions = 0;

        foreach (var c in Corpus)
        {
            foreach (var primary in c.Primaries)
            {
                var others = AllDimensions.Where(d => d != primary).ToArray();

                foreach (var (dim, value) in PrimaryProbes(c, primary))
                {
                    var configurations = new List<(LimitDimension Dim, long Value)[]>
                    {
                        Array.Empty<(LimitDimension, long)>(),
                        others.Select(o => (o, o.NonBindingValues[0])).ToArray(),
                    };
                    configurations.AddRange(others.Select(o => new[] { (o, o.NonBindingValues[0]) }));

                    foreach (var extras in configurations)
                    {
                        executions++;
                        var limits = Compose(dim, value, extras);
                        var optimizedVerdict = optimized.Run(c, limits);
                        var genericVerdict = generic.Run(c, limits);
                        if (optimizedVerdict == genericVerdict)
                            continue;

                        failures.Add(
                            $"""
                             Optimizer strategy is observable:
                               case:         {c.Name}
                               primary:      {dim.Name}={value}
                               other limits: {Describe(extras)}
                               optimized:    {optimizedVerdict}
                               generic:      {genericVerdict}
                             """);
                    }
                }
            }
        }

        AssertClean(failures, executions);
    }

    /// <summary>
    /// The same invariant swept across the fusion-eligible spellings and source shapes,
    /// including the ones only reachable when the pipeline's depth lives in its range
    /// BOUNDS rather than its predicate.
    /// </summary>
    [Theory]
    [InlineData("range(1, 3).filter(P).count", 1)]
    [InlineData("count(range(1, 3).filter(P))", 1)]
    [InlineData("count(filter(range(1, 3), P))", 1)]
    [InlineData("A.filter(P).count", 1)]
    [InlineData("count(A.filter(P))", 1)]
    [InlineData("count(filter(A, P))", 0)]
    [InlineData("range(1, f(6) + 3).filter(P).count", 1)]
    [InlineData("count(filter(range(1, f(6) + 3), P))", 1)]
    [InlineData("Src.filter(P).count", 1)]
    [InlineData("count(Src.filter(P))", 1)]
    public void FusedAndGenericSequencePipelines_ConsumeIdenticalDynamicDepth(
        string pipeline,
        int minimumFusionHits)
    {
        var source = $"{CountDown}P(x) = f(6) + 1\nA = (1, 2, 3)\nSrc = (f(6) + 1, 2, 3)\n{pipeline}";
        AssertSameExactDepthBoundary(source, minimumFusionHits);
    }

    [Fact]
    public void NestedFusedPipelines_ConsumeTheSameExactDynamicDepth_InMixedStrategies()
    {
        string[] sources =
        [
            // optimized/optimized versus generic/generic
            "P(x) = 1\nInner(x) = range(1, x).filter(P).count > 0\nrange(1, 3).filter(Inner).count",

            // optimized/generic versus generic/generic: the inner plain composition
            // has a non-range source and deliberately falls back.
            "P(x) = 1\nA = (1, 2, 3)\nInner(x) = count(filter(A, P)) > 0\nrange(1, 3).filter(Inner).count",

            // generic/optimized versus generic/generic: the outer plain composition
            // has a non-range source while each callback's direct range still fuses.
            "P(x) = 1\nInner(x) = range(1, x).filter(P).count > 0\nA = (1, 2, 3)\ncount(filter(A, Inner))",
        ];

        foreach (var source in sources)
            AssertSameExactDepthBoundary(source);
    }

    [Fact]
    public void RangeAndCallbackFailures_HaveIdenticalDepthAndStructuredErrors()
    {
        string[] sources =
        [
            "Bad = 1 / 0\nP(x) = 1\nrange(Bad, 3).filter(P).count",
            "Bad = 1 / 0\nP(x) = 1\nrange(1, Bad).filter(P).count",
            "P(x) = 1\nrange('bad', 3).filter(P).count",
            "P(x) = 1 / 0\nrange(1, 3).filter(P).count",
        ];

        foreach (var source in sources)
        {
            var ast = FromSource(source);
            var (optimized, optimizedBudget) = Evaluator.RunCountedObserved(ast, enableOptimizations: true);
            var (generic, genericBudget) = Evaluator.RunCountedObserved(ast, enableOptimizations: false);

            Assert.True(optimized.IsError);
            Assert.True(generic.IsError);
            Assert.Equal(Failure(generic.Error), Failure(optimized.Error));
            Assert.Equal(genericBudget.PeakDepth, optimizedBudget.PeakDepth);
        }
    }

    [Fact]
    public void PreCommitOptimizerFallback_DoesNotChargeDynamicDepth()
    {
        var filter = new Expr.DotCall(
            new Expr.Resolve("Data"),
            "filter",
            OutputBundle.From([new Expr.Resolve("Predicate")]));
        var invocation = SequencePipelineInvocation.DotCall(new Expr.DotCall(filter, "count"));
        var semanticServiceReached = false;
        var services = new SequencePipelineEvaluationServices(
            GetDotCallLexicalBuiltinFallbackReason: (_, _) => "count does not resolve to builtin",
            EvaluateDotReceiverIterationItems: _ =>
            {
                semanticServiceReached = true;
                return EvalResult<IReadOnlyList<Evaluator.CountedResult>>.Ok([]);
            },
            EvaluateSequenceIterationItems: _ =>
            {
                semanticServiceReached = true;
                return EvalResult<IReadOnlyList<Evaluator.CountedResult>>.Ok([]);
            },
            ResolveArgumentAlgorithms: _ =>
            {
                semanticServiceReached = true;
                return EvalResult<IReadOnlyList<Algorithm>>.Ok([]);
            },
            ResolveAlgorithm: _ =>
            {
                semanticServiceReached = true;
                return EvalResult<Algorithm>.Ok(new Algorithm.Builtin(BuiltinId.@range));
            },
            EvaluateRangeCallArguments: (_, _, _) =>
            {
                semanticServiceReached = true;
                return EvalResult<Evaluator.InclusiveRange>.Ok(new Evaluator.InclusiveRange(1, 1));
            });

        foreach (var optimizationEnabled in new[] { false, true })
        {
            semanticServiceReached = false;
            var ctx = Evaluator.EvalCtx.Empty with
            {
                EnableSequencePipelineOptimization = optimizationEnabled,
            };
            var handled = SequencePipelineOptimizer.TryExecute(
                invocation,
                services,
                ctx,
                [],
                diagnostics: null,
                out _);

            Assert.False(handled);
            Assert.False(semanticServiceReached);
            Assert.Equal(0, ctx.Budget.PeakDepth);
        }
    }

    [Fact]
    public void FailedOptimizerCommitDepthEnter_IsNonMutatingAndDoesNotEvaluateSource()
    {
        var range = new Expr.Call(
            new Expr.Resolve("range"),
            OutputBundle.From([new Expr.Num(1), new Expr.Num(3)]));
        var filter = new Expr.DotCall(
            range,
            "filter",
            OutputBundle.From([new Expr.Resolve("Predicate")]));
        var invocation = SequencePipelineInvocation.DotCall(new Expr.DotCall(filter, "count"));
        var sourceEvaluated = false;
        var predicate = new Algorithm.User(
            null, [new ParameterDeclaration("x")], [], [], [new Expr.Num(1)]);
        var services = new SequencePipelineEvaluationServices(
            GetDotCallLexicalBuiltinFallbackReason: (_, _) => null,
            EvaluateDotReceiverIterationItems: _ =>
            {
                sourceEvaluated = true;
                return EvalResult<IReadOnlyList<Evaluator.CountedResult>>.Ok([]);
            },
            EvaluateSequenceIterationItems: _ =>
                throw new Xunit.Sdk.XunitException("plain source evaluation must not run"),
            ResolveArgumentAlgorithms: _ => EvalResult<IReadOnlyList<Algorithm>>.Ok([predicate]),
            ResolveAlgorithm: _ => EvalResult<Algorithm>.Ok(new Algorithm.Builtin(BuiltinId.@range)),
            EvaluateRangeCallArguments: (_, _, _) =>
            {
                sourceEvaluated = true;
                return EvalResult<Evaluator.InclusiveRange>.Ok(new Evaluator.InclusiveRange(1, 3));
            });

        var budget = EvaluationBudget.Create(new EvaluationLimits { MaxDepth = 1 });
        var ctx = Evaluator.EvalCtx.Empty with { Budget = budget };
        Assert.Null(budget.TryEnterArgumentEvaluation());

        var handled = SequencePipelineOptimizer.TryExecute(
            invocation,
            services,
            ctx,
            [],
            diagnostics: null,
            out _);

        Assert.False(handled);
        Assert.False(sourceEvaluated);
        budget.ExitInvocation();
        Assert.Null(budget.TryEnterArgumentEvaluation());
        Assert.Equal(1, budget.PeakDepth);
        budget.ExitInvocation();
    }

    [Fact]
    public void CommittedSourceFailure_ReleasesOptimizerDepthExactlyOnce()
    {
        var range = new Expr.Call(
            new Expr.Resolve("range"),
            OutputBundle.From([new Expr.Num(1), new Expr.Num(3)]));
        var filter = new Expr.DotCall(
            range,
            "filter",
            OutputBundle.From([new Expr.Resolve("Predicate")]));
        var invocation = SequencePipelineInvocation.DotCall(new Expr.DotCall(filter, "count"));
        var predicate = new Algorithm.User(
            null, [new ParameterDeclaration("x")], [], [], [new Expr.Num(1)]);
        var services = new SequencePipelineEvaluationServices(
            GetDotCallLexicalBuiltinFallbackReason: (_, _) => null,
            EvaluateDotReceiverIterationItems: _ =>
                throw new Xunit.Sdk.XunitException("generic source evaluation must not run for a direct range"),
            EvaluateSequenceIterationItems: _ =>
                throw new Xunit.Sdk.XunitException("plain source evaluation must not run"),
            ResolveArgumentAlgorithms: _ => EvalResult<IReadOnlyList<Algorithm>>.Ok([predicate]),
            ResolveAlgorithm: _ => EvalResult<Algorithm>.Ok(new Algorithm.Builtin(BuiltinId.@range)),
            EvaluateRangeCallArguments: (_, _, _) => new EvalError.DivByZero());

        var budget = EvaluationBudget.Create(new EvaluationLimits { MaxDepth = 2 });
        var ctx = Evaluator.EvalCtx.Empty with { Budget = budget };
        var handled = SequencePipelineOptimizer.TryExecute(
            invocation,
            services,
            ctx,
            [],
            diagnostics: null,
            out var result);

        Assert.True(handled);
        Assert.True(result.IsError);
        Assert.IsType<EvalError.DivByZero>(Innermost(result.Error));
        Assert.Equal(1, budget.PeakDepth);

        // Both levels remain available. A leaked outer enter would allow only one;
        // a double exit would corrupt this exact capacity check in the other direction.
        Assert.Null(budget.TryEnterArgumentEvaluation());
        Assert.Null(budget.TryEnterArgumentEvaluation());
        Assert.IsType<EvalError.EvaluationDepthExceeded>(budget.TryEnterArgumentEvaluation());
        budget.ExitInvocation();
        budget.ExitInvocation();
    }

    // ── G. The named regression for the defect this suite found ──────────────

    /// <summary>
    /// Minimal reproducer for the defect. <c>range(1, 3).filter(P).count</c> creates no
    /// string at all, so <c>MaxStringLength</c> is non-binding by construction — yet
    /// configuring it selected the generic sequence strategy, which consumed one more
    /// level of dynamic depth than the fused strategy, and the program's <c>MaxDepth</c>
    /// verdict flipped from success to <see cref="EvalError.EvaluationDepthExceeded"/>.
    /// </summary>
    [Fact]
    public void ConfiguredStringLimit_DoesNotChangeDepthVerdict_OfAFusedSequencePipeline()
    {
        var ast = FromSource($"{CountDown}P(x) = f(6) + 1\nrange(1, 3).filter(P).count");

        // The program creates no language string, so every string budget is non-binding.
        var (_, unlimitedBudget) = Evaluator.RunCountedObserved(ast);
        Assert.Equal(0, unlimitedBudget.MaterializedStringChars);

        var boundary = unlimitedBudget.PeakDepth;

        foreach (var stringLimit in new EvaluationLimits?[]
                 {
                     null,
                     new EvaluationLimits { MaxStringLength = EvaluationLimits.MaxSupportedStringLength },
                     new EvaluationLimits { MaxStringLength = 1 },
                     new EvaluationLimits { MaxMaterializedStringChars = long.MaxValue },
                     new EvaluationLimits { MaxMaterializedItems = long.MaxValue },
                     new EvaluationLimits { MaxSteps = long.MaxValue },
                 })
        {
            var atBoundary = stringLimit is null
                ? new EvaluationLimits { MaxDepth = boundary }
                : stringLimit with { MaxDepth = boundary };
            var belowBoundary = atBoundary with { MaxDepth = boundary - 1 };

            var passing = Evaluator.Run(ast, atBoundary);
            Assert.False(
                passing.IsError,
                $"MaxDepth={boundary} must succeed with unrelated limits {atBoundary}; got {(passing.IsError ? passing.Error : null)}");

            var failing = Evaluator.Run(ast, belowBoundary);
            Assert.IsType<EvalError.EvaluationDepthExceeded>(Innermost(failing.Error));
        }
    }

    // ── H. Multi-limit precedence (legitimate competition, not cross-talk) ───

    /// <summary>
    /// When two limits genuinely bind, which one wins is decided by evaluation ORDER,
    /// not by strategy selection: the first resource the run actually exhausts reports.
    /// This is the control for the cross-talk tests — it documents the one way adding a
    /// limit may legitimately change an error kind.
    /// </summary>
    [Fact]
    public void MultipleBindingLimits_ResolveByFirstExhaustedResource()
    {
        // Six user invocations happen before the 200-item collection is reserved, so the
        // step budget is exhausted first and reports even though the collection ceiling
        // would also bind.
        var staged = FromSource("Probe = 1\nf(0) = range(1, 200)\nf(n) = f(n - 1)\nf(5).count");
        var stepsFirst = Evaluator.Run(staged, new EvaluationLimits { MaxSteps = 3, MaxCollectionItems = 1 });
        Assert.IsType<EvalError.EvaluationStepLimitExceeded>(Innermost(stepsFirst.Error));

        // With steps generous, the collection ceiling is the first thing that run
        // actually exhausts — the change of error kind is the ORDER of exhaustion
        // changing, not a strategy switch.
        var collectionFirst = Evaluator.Run(staged, new EvaluationLimits { MaxSteps = 10_000, MaxCollectionItems = 1 });
        Assert.IsType<EvalError.CollectionSizeLimitExceeded>(Innermost(collectionFirst.Error));

        // Depth is charged at the dot-call's collection-argument funnel, before `range`
        // reserves anything, so it precedes the collection ceiling.
        var direct = FromSource("Probe = 1\nrange(1, 200).count");
        var depthFirst = Evaluator.Run(direct, new EvaluationLimits { MaxDepth = 1, MaxCollectionItems = 1 });
        Assert.IsType<EvalError.EvaluationDepthExceeded>(Innermost(depthFirst.Error));

        // Builtin calls charge no step, so a tight step budget does NOT preempt the
        // collection ceiling for the direct spelling. Documented here because it is the
        // reason "steps always win" is not the precedence rule.
        var noStepsCharged = Evaluator.Run(direct, new EvaluationLimits { MaxSteps = 1, MaxCollectionItems = 1 });
        Assert.IsType<EvalError.CollectionSizeLimitExceeded>(Innermost(noStepsCharged.Error));

        // The structural preflight runs before any evaluation-budget counter can move,
        // so it always precedes every runtime limit regardless of how tight those are.
        var deep = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [], [UnarySpine(400)]));
        var structuralFirst = Evaluator.Run(deep, new EvaluationLimits { MaxSteps = 1, MaxDepth = 1, MaxAstDepth = 4 });
        Assert.IsType<EvalError.AstDepthLimitExceeded>(Innermost(structuralFirst.Error));
    }

    // ── I. Configuration construction ────────────────────────────────────────

    /// <summary>
    /// <see cref="EvaluationLimits"/> is an immutable record, so two orders of the same
    /// <c>with</c> updates must produce equal configuration AND equal behaviour. Verified
    /// rather than assumed, because a configuredness flag computed during construction
    /// could in principle depend on order.
    /// </summary>
    [Fact]
    public void LimitConfiguration_IsIndependentOfConstructionOrder()
    {
        var forward = EvaluationLimits.Default with { MaxSteps = 5_000 };
        forward = forward with { MaxStringLength = 1_000 };
        forward = forward with { MaxCollectionItems = 500 };

        var reverse = EvaluationLimits.Default with { MaxCollectionItems = 500 };
        reverse = reverse with { MaxStringLength = 1_000 };
        reverse = reverse with { MaxSteps = 5_000 };

        Assert.Equal(forward, reverse);

        foreach (var c in Corpus)
            Assert.Equal(MatrixEntryPoint.Run(c, forward), MatrixEntryPoint.Run(c, reverse));
    }

    // ── J. Cache and run isolation across configurations ─────────────────────

    /// <summary>
    /// Limit configuration must not leak between runs through the shared zero-argument
    /// property cache: a run stopped by a tight budget must not poison a later generous
    /// run that reuses the same cache, in either order.
    /// </summary>
    [Fact]
    public void LimitConfiguration_DoesNotLeakThroughASharedPropertyCache()
    {
        foreach (var c in Corpus)
        {
            var reference = Evaluator.RunCounted(c.Ast, new RunScopedZeroArgPropertyResultCache());

            var shared = new RunScopedZeroArgPropertyResultCache();
            var starved = Evaluator.RunCounted(c.Ast, shared, new EvaluationLimits { MaxSteps = 1, MaxDepth = 1 });
            var afterStarved = Evaluator.RunCounted(c.Ast, shared, EvaluationLimits.Default);

            Assert.Equal(CountedVerdict(reference), CountedVerdict(afterStarved));

            // …and the reverse order: a completed generous run must not make the tight
            // one succeed by handing it cached work it never paid for.
            var reused = new RunScopedZeroArgPropertyResultCache();
            _ = Evaluator.RunCounted(c.Ast, reused, EvaluationLimits.Default);
            var starvedAfter = Evaluator.RunCounted(c.Ast, reused, new EvaluationLimits { MaxSteps = 1, MaxDepth = 1 });
            Assert.Equal(CountedVerdict(starved), CountedVerdict(starvedAfter));
        }
    }

    /// <summary>
    /// A run stopped by a limit must leave no residue: the immediately following run of
    /// the same program under a different configuration observes exactly what it would
    /// have observed first.
    /// </summary>
    [Fact]
    public void AFailedRunLeavesNoResidueForTheNextConfiguration()
    {
        foreach (var c in Corpus)
        {
            var pristine = MatrixEntryPoint.Run(c, EvaluationLimits.Default);

            foreach (var starving in new[]
                     {
                         new EvaluationLimits { MaxSteps = 1 },
                         new EvaluationLimits { MaxDepth = 1 },
                         new EvaluationLimits { MaxCollectionItems = 1 },
                         new EvaluationLimits { MaxMaterializedItems = 1 },
                         new EvaluationLimits { MaxStringLength = 0 },
                     })
            {
                _ = MatrixEntryPoint.Run(c, starving);
                Assert.Equal(pristine, MatrixEntryPoint.Run(c, EvaluationLimits.Default));
            }
        }
    }

    // ── K. Render-only limits never reach evaluation ─────────────────────────

    /// <summary>
    /// <c>MaxDisplayLength</c> is a rendering policy. Even at zero it must not change a
    /// structured evaluation result, on any entry point that returns one.
    /// </summary>
    [Fact]
    public void DisplayLimit_NeverChangesAStructuredEvaluationResult()
    {
        foreach (var c in Corpus)
        {
            foreach (var entryPoint in EntryPoints)
            {
                if (entryPoint.RequiresSource)
                    continue;

                var unset = entryPoint.Run(c, EvaluationLimits.Default);
                foreach (var value in new long[] { 0, 1, 10_000, EvaluationLimits.MaxSupportedDisplayLength })
                    Assert.Equal(unset, entryPoint.Run(c, Only(MaxDisplayLengthDim, value)));
            }
        }
    }
}
