using System.Reflection;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Sequences;
using static KatLang.Tests.LoopDiagnosticParityAssertions;

namespace KatLang.Tests;

/// <summary>
/// Fused filter→count over a DOTTED RECEIVER whose elements include the empty sequence value <c>()</c>
/// (investigation of 2026-11-17). The fused source adapter
/// (<c>EvaluateDotReceiverIterationItemsForSequenceOptimizer</c>) returns the generic binding's own view
/// (<c>CollectionIterationItems</c>) since 2026-11-18, so every receiver element, a <c>()</c> element
/// included, carries emitted count 1 on both strategies. Until then the adapter copied the elements with
/// the emitted count <c>item.ValueCount()</c>, so a <c>()</c> element carried 0 there and 1 in generic
/// binding. That difference was NOT observable, by
/// construction: the fused executor reads only the number of source items and passes each item to the
/// ONE predicate funnel the generic <c>filter</c> uses (<c>EvalFilterPredicateTruth</c>). That funnel
/// renders the item's value for its diagnostic context and hands the item to the callback through
/// <c>CountedSequenceCallbackItem</c> — the value-boundary re-count, which rebuilds the count from the
/// value and discards the incoming one — and callback binding then makes ONE supplied cell per item, so
/// a <c>()</c> element is one argument on both strategies. The kept count is the number of true
/// predicate results on both. These witnesses observe the element through <c>count</c>, spreading,
/// collecting and fixed arity, a pattern, <c>map</c>, <c>filter</c> and <c>first</c> inside the
/// predicate, an error, a non-Boolean result and a step charge, over every fused form, and are kept as
/// parity tests: outcome, error tree, budget counters and every limit verdict agree with fusion ON and OFF.
/// </summary>
public class FilterCountReceiverEmptyElementParityTests
{
    private const string CommonDefinitions = """
        V = (), 1, ()
        W = [(), 2, ()]
        E = ()
        Maybe(n) = if(n == 2, 1, ())
        IsEmpty(x) = x.count == 0
        Cnt(y) = y.count
        Two(a, b) = true
        Boom(x) = if(x.count == 0, 1 / 0, true)
        Deep(0) = true
        Deep(n) = Deep(n - 1)
        """;

    // Predicate text and its own definitions.
    private static readonly Dictionary<string, (string Text, string Definitions)> Predicates = new()
    {
        ["count"] = ("IsEmpty", ""),
        ["implicit"] = ("IsEmptyImplicit", "IsEmptyImplicit = x.count == 0"),
        ["spread"] = ("SpreadEmpty", "SpreadEmpty(x) = [x*].count == 0"),
        ["collectNone"] = ("CollectNone", "CollectNone(*xs) = xs.count == 0"),
        ["collectOne"] = ("CollectOne", "CollectOne(*xs) = xs.count == 1"),
        ["arity2"] = ("Two", ""),
        ["spreadArity"] = ("SpreadTwo", "SpreadTwo(x) = Two(x*)"),
        ["zeroParam"] = ("Zero", "Zero = true"),
        ["block"] = ("{true}", ""),
        ["pattern"] = ("Pat", "Pat(()) = true\nPat(x) = false"),
        ["error"] = ("Boom", ""),
        ["notBool"] = ("Same", "Same(x) = x"),
        ["map"] = ("MapIn", "MapIn(x) = [x].map(Cnt).sum == 0"),
        ["filter"] = ("FilterIn", "FilterIn(x) = [x].filter(IsEmpty).count == 1"),
        ["charge"] = ("Charge", "Charge(x) = Deep(x.count + 3)"),
        ["selectFirst"] = ("FirstEmpty", "FirstEmpty(x) = [x].first.count == 0"),
    };

    private static readonly (string Name, string Text)[] Receivers =
    [
        ("seqProperty", "V"),
        ("listProperty", "W"),
        ("listLiteral", "[(), 1, ()]"),
        ("seqLiteral", "((), 1, ())"),
        ("mapped", "[1, 2, 3].map(Maybe)"),
        ("filtered", "[(), 1, ()].filter(IsEmpty)"),
        ("spreadGroup", "(V*)"),
        ("singleEmpty", "[()]"),
        ("nestedEmpties", "[((), ()), ()]"),
        ("emptySource", "E"),
    ];

    // Every filter→count form the optimizer fuses, a parameter as the dotted receiver, two fused
    // pipelines in one program (error order), and the plain form, which falls back for a non-range
    // source (its generic composition is the control).
    private static readonly (string Name, Func<string, string, string> Pipeline, string Definition, bool Fuses)[] Forms =
    [
        ("dotFilterDotCount", static (r, p) => $"{r}.filter({p}).count", "", true),
        ("plainCountDotFilter", static (r, p) => $"count({r}.filter({p}))", "", true),
        ("parameterReceiver", static (r, p) => $"Via({r})", "Via(xs) = xs.filter({P}).count", true),
        ("twoPipelines", static (r, p) => $"({r}.filter({p}).count, count({r}.filter(Boom)))", "", true),
        ("plainCountPlainFilter", static (r, p) => $"count(filter({r}, {p}))", "", false),
    ];

    public static TheoryData<string> PredicateNames()
    {
        var data = new TheoryData<string>();
        foreach (var name in Predicates.Keys)
            data.Add(name);
        return data;
    }

    private static string Program(string predicate, string receiver, int form)
    {
        var (text, definitions) = Predicates[predicate];
        var shape = Forms[form];
        return CommonDefinitions
            + (definitions.Length > 0 ? "\n" + definitions : "")
            + (shape.Definition.Length > 0 ? "\n" + shape.Definition.Replace("{P}", text, StringComparison.Ordinal) : "")
            + "\n" + shape.Pipeline(receiver, text) + "\n";
    }

    private sealed record Budget(long Steps, long Checkpoints, int PeakDepth, long MaterializedItems, long MaterializedStringChars, long StructuralWork, int PeakTransient);

    private sealed record Observed(string Outcome, Budget Budget);

    private static string Outcome(EvalResult<Evaluator.CountedResult> result)
        => result.IsError
            ? $"err {DescribeErrorTree(result.Error)}| {KatLangError.FromEvalError(result.Error).Message}"
            : $"ok {SixRouteAgreement.Neutral(result.Value.Value)} emitted {result.Value.EmittedCount}";

    // Counted run with its budget. The programs contain no loop, so enableOptimizations switches only
    // the sequence-pipeline strategy here.
    private static Observed Observe(Expr ast, EvaluationLimits? limits, bool fusion)
    {
        var (result, budget) = Evaluator.RunCountedObserved(ast, limits, enableOptimizations: fusion);
        return new Observed(
            Outcome(result),
            new Budget(budget.ConsumedSteps, budget.ConsumedExpressionCheckpoints, budget.PeakDepth, budget.MaterializedItems,
                budget.MaterializedStringChars, budget.ConsumedStructuralWorkUnits, budget.PeakTransientExpansion));
    }

    // The switch the optimizer tests and SequencePipelineStage2Benchmarks use: loop optimization on in both
    // modes, only enableSequencePipelineOptimization differs.
    private static (string Outcome, SequencePipelineDiagnosticsSnapshot Stats) RunSwitch(Expr ast, bool fusion)
    {
        var diagnostics = new SequencePipelineDiagnostics();
        var result = Evaluator.Run(ast, new RunScopedZeroArgPropertyResultCache(), enableLoopOptimization: true,
            loopDiagnostics: null, enableSequencePipelineOptimization: fusion, sequenceDiagnostics: diagnostics);
        var outcome = result.IsError
            ? $"err {DescribeErrorTree(result.Error)}| {KatLangError.FromEvalError(result.Error).Message}"
            : $"ok {SixRouteAgreement.Neutral(result.Value)}";
        return (outcome, diagnostics.GetSnapshot());
    }

    [Theory]
    [MemberData(nameof(PredicateNames))]
    public void EveryReceiverAndForm_AgreesWithTheGenericComposition_UnlimitedAndAtEveryLimit(string predicate)
    {
        foreach (var (receiverName, receiver) in Receivers)
        for (var form = 0; form < Forms.Length; form++)
        {
            var id = $"{predicate}/{receiverName}/{Forms[form].Name}";
            var ast = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(Program(predicate, receiver, form)).Root);

            var (genericOutcome, genericStats) = RunSwitch(ast, fusion: false);
            var (fusedOutcome, fusedStats) = RunSwitch(ast, fusion: true);
            Assert.True(genericOutcome == fusedOutcome, $"{id}: generic {genericOutcome} / fused {fusedOutcome}");
            Assert.Equal(0, genericStats.FilterCountFusionHits);
            if (Forms[form].Fuses)
                Assert.True(fusedStats.FilterCountFusionHits > 0, $"{id}: the fused strategy did not run");
            else
                Assert.True(fusedStats.FilterCountFusionFallbacks > 0, $"{id}: the plain form did not fall back");

            var generic = Observe(ast, null, fusion: false);
            var fused = Observe(ast, null, fusion: true);
            Assert.True(generic == fused, $"{id}: generic {generic} / fused {fused}");

            foreach (var (name, limits) in Sweep(generic.Budget))
            {
                var limitedGeneric = Observe(ast, limits, fusion: false);
                var limitedFused = Observe(ast, limits, fusion: true);
                Assert.True(limitedGeneric == limitedFused, $"{id} {name}: generic {limitedGeneric} / fused {limitedFused}");
            }
        }
    }

    // Every depth up to one past the peak, every step budget up to one past the consumption, every
    // cumulative item budget up to one past the materialized total, and small per-collection ceilings.
    private static IEnumerable<(string Name, EvaluationLimits Limits)> Sweep(Budget unlimited)
    {
        for (var depth = 1; depth <= unlimited.PeakDepth + 1; depth++)
            yield return ($"MaxDepth={depth}", new EvaluationLimits { MaxDepth = depth });
        for (var steps = 1L; steps <= unlimited.Steps + 1; steps++)
            yield return ($"MaxSteps={steps}", new EvaluationLimits { MaxSteps = steps });
        for (var items = 1L; items <= unlimited.MaterializedItems + 1; items++)
            yield return ($"MaxMaterializedItems={items}", new EvaluationLimits { MaxMaterializedItems = items });
        for (var items = 1; items <= 4; items++)
            yield return ($"MaxCollectionItems={items}", new EvaluationLimits { MaxCollectionItems = items });
    }

    /// <summary>
    /// The outcomes themselves, on both strategies, so the agreement cannot be vacuous: a <c>()</c>
    /// element counts 0 inside the predicate, spreads to no value, is ONE argument to a collector and to
    /// a fixed arity, matches the <c>()</c> pattern, and is the reported item of a failing predicate.
    /// </summary>
    [Theory]
    [InlineData("count", "V", 0, "ok 2")]
    [InlineData("count", "[((), ()), ()]", 0, "ok 1")]
    [InlineData("count", "[1, 2, 3].map(Maybe)", 0, "ok 2")]
    [InlineData("count", "[(), 1, ()].filter(IsEmpty)", 1, "ok 2")]
    [InlineData("count", "(V*)", 0, "ok 2")]
    [InlineData("count", "E", 0, "ok 0")]
    [InlineData("spread", "V", 0, "ok 2")]
    [InlineData("collectOne", "V", 0, "ok 3")]
    [InlineData("collectNone", "V", 0, "ok 0")]
    [InlineData("pattern", "V", 0, "ok 2")]
    [InlineData("map", "W", 0, "ok 2")]
    [InlineData("filter", "((), 1, ())", 0, "ok 2")]
    [InlineData("selectFirst", "V", 0, "ok 2")]
    [InlineData("charge", "V", 0, "ok 3")]
    [InlineData("implicit", "[(), 1, ()]", 2, "ok 2")]
    [InlineData("arity2", "V", 0, "err Callable `filter predicate(a, b)` expects 2 arguments, but was called with 1 argument.")]
    [InlineData("zeroParam", "[()]", 0, "err Callable `filter predicate` expects 0 arguments, but was called with 1 argument.")]
    [InlineData("spreadArity", "W", 0, "err Callable `Two(a, b)` expects 2 arguments, but was called with 0 arguments.")]
    [InlineData("error", "V", 0, "err while evaluating filter predicate for item 0: ()")]
    [InlineData("notBool", "[()]", 0, "err filter predicate result must be a Boolean value (true or false), but was a sequence value with 0 sequence elements: ()")]
    public void TheEmptyElement_IsObservedIdenticallyByBothStrategies(string predicate, string receiver, int form, string expected)
    {
        var ast = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(Program(predicate, receiver, form)).Root);
        foreach (var fusion in new[] { false, true })
        {
            var (result, _) = Evaluator.RunCountedObserved(ast, enableOptimizations: fusion);
            if (expected.StartsWith("ok ", StringComparison.Ordinal))
            {
                Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : null);
                Assert.Equal(new Result.Atom(int.Parse(expected[3..], System.Globalization.CultureInfo.InvariantCulture)), result.Value.Value, Result.ValueComparer);
            }
            else
            {
                Assert.True(result.IsError, $"fusion {fusion}: expected an error");
                var error = result.Error;
                while (error is EvalError.WithContext context)
                    error = context.Inner;
                var expectedErrorType = predicate switch
                {
                    "arity2" or "zeroParam" or "spreadArity" => typeof(EvalError.ArityMismatch),
                    "error" => typeof(EvalError.DivByZero),
                    "notBool" => typeof(EvalError.TypeMismatch),
                    _ => throw new InvalidOperationException($"No expected error type for predicate '{predicate}'."),
                };
                Assert.IsType(expectedErrorType, error);
                Assert.Contains(expected[4..], KatLangError.FromEvalError(result.Error).Message, StringComparison.Ordinal);
            }
        }
    }

    /// <summary>
    /// The mechanism that made the two counts unobservable: a <c>()</c> item counted 0 (the fused adapter's
    /// until 2026-11-18) and the generic view's (count 1) become the SAME callback item at the one predicate
    /// funnel.
    /// </summary>
    [Fact]
    public void TheCallbackItem_IsRecountedFromItsValue_SoTheIncomingCountIsDiscarded()
    {
        var recount = typeof(Evaluator).GetMethod("CountedSequenceCallbackItem", BindingFlags.NonPublic | BindingFlags.Static)!;
        var empty = new Result.SequenceValue([]);
        var fusedItem = (Evaluator.CountedResult)recount.Invoke(null, [new Evaluator.CountedResult(empty, empty.ValueCount())])!;
        var genericItem = (Evaluator.CountedResult)recount.Invoke(null, [new Evaluator.CountedResult(empty, 1)])!;
        Assert.Equal(0, fusedItem.EmittedCount);
        Assert.Equal(fusedItem, genericItem);
    }
}
