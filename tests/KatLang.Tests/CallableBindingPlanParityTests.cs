using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;

namespace KatLang.Tests;

public class CallableBindingPlanParityTests
{
    private static CallableBindingPlan PlanFor(string source, string name, bool allowErrors = false)
    {
        var parseResult = Parser.Parse(source);
        if (!allowErrors)
        {
            Assert.False(
                parseResult.HasErrors,
                string.Join(Environment.NewLine, parseResult.Diagnostics.Select(static diagnostic => diagnostic.Message)));
        }

        var property = parseResult.Root.Properties.Single(property => property.Name == name);
        return CallableBindingPlan.FromSignature(CallableSignature.FromAlgorithm(name, property.Value));
    }

    private static void AssertEval(string source, params decimal[] expected)
    {
        var parseResult = Parser.Parse(source);
        Assert.False(
            parseResult.HasErrors,
            string.Join(Environment.NewLine, parseResult.Diagnostics.Select(static diagnostic => diagnostic.Message)));

        var result = Evaluator.RunFlat(new Expr.Block(parseResult.Root));
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal(expected, result.Value);
    }

    private static string AssertEvalFails(string source)
    {
        var parseResult = Parser.Parse(source);
        Assert.False(
            parseResult.HasErrors,
            string.Join(Environment.NewLine, parseResult.Diagnostics.Select(static diagnostic => diagnostic.Message)));

        var result = Evaluator.Run(new Expr.Block(parseResult.Root));
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        return KatLangError.FromEvalError(result.Error).Message;
    }

    private static Result EvalResult(string source, bool enableLoopOptimization = true)
    {
        var parseResult = Parser.Parse(source);
        Assert.False(
            parseResult.HasErrors,
            string.Join(Environment.NewLine, parseResult.Diagnostics.Select(static diagnostic => diagnostic.Message)));

        var result = Evaluator.Run(
            new Expr.Block(parseResult.Root),
            new RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        return result.Value;
    }

    private static (Result Result, LoopOptimizationDiagnosticsSnapshot Stats) EvalResultWithLoopDiagnostics(
        string source,
        bool enableLoopOptimization = true)
    {
        var parseResult = Parser.Parse(source);
        Assert.False(
            parseResult.HasErrors,
            string.Join(Environment.NewLine, parseResult.Diagnostics.Select(static diagnostic => diagnostic.Message)));

        var diagnostics = new LoopOptimizationDiagnostics();
        var result = Evaluator.Run(
            new Expr.Block(parseResult.Root),
            new RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization,
            diagnostics);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        return (result.Value, diagnostics.GetSnapshot());
    }

    private static Result ResultFromAtoms(params decimal[] expected)
        => Result.FromItems(expected.Select(static number => new Result.Atom(number)));

    private static void AssertResult(Result expected, Result actual)
        => Assert.True(Result.ValueComparer.Equals(expected, actual), $"Expected {expected} but got {actual}");

    private static void AssertUserCallAndLoopStepParity(string userSource, string loopSource, Result expected)
    {
        var userResult = EvalResult(userSource, enableLoopOptimization: false);
        AssertResult(expected, userResult);

        var genericLoopResult = EvalResult(loopSource, enableLoopOptimization: false);
        AssertResult(expected, genericLoopResult);
        AssertResult(userResult, genericLoopResult);

        var optimizedLoopResult = EvalResult(loopSource, enableLoopOptimization: true);
        AssertResult(expected, optimizedLoopResult);
        AssertResult(userResult, optimizedLoopResult);
    }

    private static void AssertPlanDisplay(CallableBindingPlan plan, string expected)
        => Assert.Equal(expected, plan.DisplayText);

    private static void AssertTopLevelNodes(CallableBindingPlan plan, params string[] expected)
        => Assert.Equal(expected, plan.TopLevelPatternList.Nodes.Select(DescribeNode).ToArray());

    private static void AssertCaptures(CallableBindingPlan plan, params string[] expected)
        => Assert.Equal(expected, plan.Captures.Select(DescribeCapture).ToArray());

    private static void AssertArity(CallableBindingPlan plan, int min, int? max, bool hasTopLevelVariadic)
    {
        Assert.Equal(min, plan.TopLevelPatternList.MinSlotCount);
        Assert.Equal(max, plan.TopLevelPatternList.MaxSlotCount);
        Assert.Equal(hasTopLevelVariadic, plan.TopLevelPatternList.HasVariadicAtThisLevel);
        Assert.Equal(hasTopLevelVariadic ? 1 : 0, plan.TopLevelPatternList.VariadicCountAtThisLevel);
        Assert.Equal(CallableSignatureDiagnostics.GetArityFacts(plan.Signature), plan.ArityFacts);
    }

    private static string DescribeNode(CallableBindingNode node)
        => node switch
        {
            CaptureBindingNode capture => $"Capture({capture.Name}:{capture.Source})",
            VariadicCaptureBindingNode variadic => $"Variadic({variadic.Name}:{variadic.Source}:{(variadic.IsTopLevel ? "top" : "nested")})",
            SequenceValueBindingNode group => $"SequenceValue({DescribePatternList(group.Children)})",
            _ => throw new InvalidOperationException("Unknown binding node."),
        };

    private static string DescribePatternList(PatternListBindingPlan plan)
        => string.Join(", ", plan.Nodes.Select(DescribeNode));

    private static string DescribeCapture(CallableBindingCapture capture)
        => $"{capture.DisplayName}:{capture.Source}";

    [Fact]
    public void ExplicitScalarUserCallShape_MatchesRuntimeBindingExpectation()
    {
        var plan = PlanFor("Add(x, y) = x + y", "Add");

        AssertPlanDisplay(plan, "Add(x, y)");
        AssertTopLevelNodes(plan, "Capture(x:Explicit)", "Capture(y:Explicit)");
        AssertCaptures(plan, "x:Explicit", "y:Explicit");
        AssertArity(plan, min: 2, max: 2, hasTopLevelVariadic: false);

        AssertEval(
            """
            Add(x, y) = x + y
            Add(2, 3)
            """,
            5);
    }

    [Fact]
    public void ImplicitScalarUserCallShape_MatchesRuntimeBindingExpectation()
    {
        var plan = PlanFor("Add = x + y", "Add");

        AssertPlanDisplay(plan, "Add(x, y)");
        AssertTopLevelNodes(plan, "Capture(x:Implicit)", "Capture(y:Implicit)");
        AssertCaptures(plan, "x:Implicit", "y:Implicit");
        AssertArity(plan, min: 2, max: 2, hasTopLevelVariadic: false);

        AssertEval(
            """
            Add = x + y
            Add(2, 3)
            """,
            5);
    }

    [Fact]
    public void SequenceValueExplicitShape_ConsumesOneSlotAndRuntimeRequiresSequenceValueArgument()
    {
        var plan = PlanFor("PairSum((x, y)) = x + y", "PairSum");

        AssertPlanDisplay(plan, "PairSum((x, y))");
        AssertTopLevelNodes(plan, "SequenceValue(Capture(x:Explicit), Capture(y:Explicit))");
        AssertCaptures(plan, "x:Explicit", "y:Explicit");
        AssertArity(plan, min: 1, max: 1, hasTopLevelVariadic: false);

        AssertEval(
            """
            PairSum((x, y)) = x + y
            PairSum((2, 3))
            """,
            5);

        var message = AssertEvalFails(
            """
            PairSum((x, y)) = x + y
            PairSum(2, 3)
            """);
        Assert.Contains("PairSum((x, y))", message, StringComparison.Ordinal);
    }

    [Fact]
    public void TopLevelVariadicShape_MatchesRuntimeVariadicCapture()
    {
        var plan = PlanFor("CountValues(values...) = values.count", "CountValues");

        AssertPlanDisplay(plan, "CountValues(values...)");
        AssertTopLevelNodes(plan, "Variadic(values:Explicit:top)");
        AssertCaptures(plan, "values...:Explicit");
        // Rest-only item supply: no fixed bindings, so min 0 and unbounded max.
        AssertArity(plan, min: 0, max: null, hasTopLevelVariadic: true);
        Assert.NotNull(plan.TopLevelPatternList.VariadicCapture);
        Assert.True(plan.TopLevelPatternList.VariadicCapture.IsTopLevel);

        // Three inline argument slots are collected as the exact list [1, 2, 3];
        // a single grouped `(1, 2, 3)` argument would be one collected item.
        AssertEval(
            """
            CountValues(values...) = values.count
            CountValues(1, 2, 3)
            """,
            3);
    }

    [Fact]
    public void VariadicSuffixShape_MatchesRuntimePrefixVariadicSuffixBinding()
    {
        var plan = PlanFor("Scale(items..., factor) = items.map{n * factor}", "Scale");

        AssertPlanDisplay(plan, "Scale(items..., factor)");
        AssertTopLevelNodes(plan, "Variadic(items:Explicit:top)", "Capture(factor:Explicit)");
        Assert.Empty(plan.TopLevelPatternList.Prefix);
        Assert.NotNull(plan.TopLevelPatternList.VariadicCapture);
        Assert.Equal("items", plan.TopLevelPatternList.VariadicCapture.Name);
        Assert.Equal(["Capture(factor:Explicit)"], plan.TopLevelPatternList.Suffix.Select(DescribeNode).ToArray());
        AssertCaptures(plan, "items...:Explicit", "factor:Explicit");
        // Deconstruction-shaped: the fixed `factor` is the only required slot and
        // the rest collects any number of prefix items as one exact list.
        AssertArity(plan, min: 1, max: null, hasTopLevelVariadic: true);

        AssertEval(
            """
            Scale(items..., factor) = items.map{n * factor}
            Scale((1, 2, 3)..., 10)
            """,
            10, 20, 30);
    }

    [Fact]
    public void SequenceValueVariadicShape_IsNestedAndRuntimeDoesNotTreatItAsTopLevelVariadic()
    {
        var plan = PlanFor("CountSequenceValue((values...)) = values.count", "CountSequenceValue");

        AssertPlanDisplay(plan, "CountSequenceValue((values...))");
        AssertTopLevelNodes(plan, "SequenceValue(Variadic(values:Explicit:nested))");
        AssertCaptures(plan, "values...:Explicit");
        AssertArity(plan, min: 1, max: 1, hasTopLevelVariadic: false);
        Assert.False(plan.TopLevelPatternList.HasVariadicAtThisLevel);
        Assert.True(plan.TopLevelPatternList.HasVariadicInDescendants);

        AssertEval(
            """
            CountSequenceValue((values...)) = values.count
            CountSequenceValue((1, 2, 3))
            """,
            3);

        var message = AssertEvalFails(
            """
            CountSequenceValue((values...)) = values.count
            CountSequenceValue(1, 2, 3)
            """);
        Assert.Contains("CountSequenceValue((values...))", message, StringComparison.Ordinal);
    }

    [Fact]
    public void NestedSequenceValueRecursiveShape_PreservesNestedSequenceValuesAndMatchesRuntimeShape()
    {
        var plan = PlanFor("G(((history...), previous)) = history.count + previous", "G");

        AssertPlanDisplay(plan, "G(((history...), previous))");
        AssertTopLevelNodes(plan, "SequenceValue(SequenceValue(Variadic(history:Explicit:nested)), Capture(previous:Explicit))");
        AssertCaptures(plan, "history...:Explicit", "previous:Explicit");
        AssertArity(plan, min: 1, max: 1, hasTopLevelVariadic: false);
        Assert.True(plan.TopLevelPatternList.HasVariadicInDescendants);

        AssertEval(
            """
            G(((history...), previous)) = history.count + previous
            G(((1, 2, 3), 4))
            """,
            7);
    }

    [Fact]
    public void ExplicitClosedSignaturePlan_ExcludesUnresolvedFreeNames()
    {
        const string source = "F((x, y)) = x + y + z";
        var parseResult = Parser.Parse(source);

        Assert.True(parseResult.HasErrors);
        Assert.Contains(parseResult.Diagnostics, diagnostic =>
            diagnostic.Message.Contains("Explicit parameter lists are closed", StringComparison.Ordinal));

        var property = parseResult.Root.Properties.Single(property => property.Name == "F");
        var plan = CallableBindingPlan.FromSignature(CallableSignature.FromAlgorithm("F", property.Value));

        AssertPlanDisplay(plan, "F((x, y))");
        AssertTopLevelNodes(plan, "SequenceValue(Capture(x:Explicit), Capture(y:Explicit))");
        AssertCaptures(plan, "x:Explicit", "y:Explicit");
        Assert.DoesNotContain(plan.Captures, static capture => capture.Name == "z");
    }

    [Fact]
    public void DotCallReceiverBoundary_IsRuntimeBehaviorOutsideCallableBindingPlan()
    {
        var scalarPlan = PlanFor("Collect(list) = list.count", "Collect");
        AssertTopLevelNodes(scalarPlan, "Capture(list:Explicit)");
        AssertArity(scalarPlan, min: 1, max: 1, hasTopLevelVariadic: false);

        AssertEval(
            """
            Collect(list) = list.count
            Output = (10, 20, 30).Collect
            """,
            3);
        // (fixed parameter: the receiver binds untouched and the collection
        // view opens the lone sequence — count 3)

        var variadicPlan = PlanFor("Collect(list...) = list.count", "Collect");
        AssertTopLevelNodes(variadicPlan, "Variadic(list:Explicit:top)");
        AssertArity(variadicPlan, min: 0, max: null, hasTopLevelVariadic: true);

        // The parenthesized-spread receiver supplies the items to the leading
        // flat variadic; an ordinary receiver would be one collected item.
        AssertEval(
            """
            Collect(list...) = list.count
            Output = ((10, 20, 30)...).Collect
            """,
            3);
    }

    [Fact]
    public void CollectionBuiltinSignatures_HavePlansMatchingBuiltinMetadata()
    {
        AssertBuiltinCollectionPlan(BuiltinId.map, "map(collection, mapper)", controlName: "mapper");
        AssertBuiltinCollectionPlan(BuiltinId.filter, "filter(collection, predicate)", controlName: "predicate");
        AssertBuiltinCollectionPlan(BuiltinId.take, "take(collection, count)", controlName: "count");
        AssertBuiltinCollectionPlan(BuiltinId.skip, "skip(collection, count)", controlName: "count");
        AssertBuiltinCollectionPlan(BuiltinId.count, "count(collection)", controlName: null);
    }

    [Fact]
    public void LoopStepSignatures_HavePlansMatchingGenericLoopBindingShapes()
    {
        var flat = PlanFor("Step(a, b) = b, a + b, 1", "Step");
        AssertTopLevelNodes(flat, "Capture(a:Explicit)", "Capture(b:Explicit)");
        AssertArity(flat, min: 2, max: 2, hasTopLevelVariadic: false);

        var variadic = PlanFor("Step(values...) = values...1", "Step");
        AssertTopLevelNodes(variadic, "Variadic(values:Explicit:top)");
        AssertArity(variadic, min: 0, max: null, hasTopLevelVariadic: true);

        var sequenceValuePlan = PlanFor("Step((x, y)) = x + y, 0", "Step");
        AssertTopLevelNodes(sequenceValuePlan, "SequenceValue(Capture(x:Explicit), Capture(y:Explicit))");
        AssertArity(sequenceValuePlan, min: 1, max: 1, hasTopLevelVariadic: false);

        AssertEval(
            """
            Step(first, rest...) = first...rest
            Step.repeat(1, 1, 2, 3)
            """,
            1, 2, 3);
    }

    // Public-behavior characterization for a future BindingInput data model:
    // shared flat variadic layout, context-specific runtime input construction.
    [Fact]
    public void FlatVariadicPrefixMiddleSuffix_UserCallAndLoopStepPreserveSameObservableLayout()
    {
        // The grouped middle argument/state slot is one collected item in both
        // contexts, so middle.count is 1 for the user call and the loop step.
        AssertUserCallAndLoopStepParity(
            userSource:
            """
            Shape(first, middle..., last) = first, middle.count, last
            Shape(10, (20, 30), 40)
            """,
            loopSource:
            """
            Step(first, middle..., last) = first, middle.count, last
            Step.repeat(1, 10, (20, 30), 40)
            """,
            expected: ResultFromAtoms(10, 1, 40));
    }

    [Fact]
    public void FlatVariadicCountedCapture_UserCallAndLoopStepExposeSameCount()
    {
        // The spread call supplies three slots exactly like the three loop state
        // slots, so both contexts collect the list [7, 8, 9].
        AssertUserCallAndLoopStepParity(
            userSource:
            """
            CountValues(values...) = values.count
            CountValues((7, 8, 9)...)
            """,
            loopSource:
            """
            Step(values...) = values.count
            Step.repeat(1, 7, 8, 9)
            """,
            expected: ResultFromAtoms(3));
    }

    [Fact]
    public void FlatVariadicLoopStep_OptimizationDiagnosticsKeepCurrentFallbackReason()
    {
        var (result, stats) = EvalResultWithLoopDiagnostics(
            """
            Step(values...) = values
            Step.repeat(1, 1, 2, 3)
            """,
            enableLoopOptimization: true);

        // The step returns the rest unspread, so the final state is the one
        // collected list slot [1, 2, 3].
        AssertResult(new Result.ListValue([new Result.Atom(1), new Result.Atom(2), new Result.Atom(3)]), result);
        Assert.Contains(
            stats.FallbackReasons,
            reason => reason.Key == "variadic loop step" && reason.Value >= 1);
    }

    [Fact]
    public void CallbackPlans_MatchCurrentRuntimeCallbackShapes()
    {
        // Sequence callback item projection/counting belongs to runtime; the
        // plan facts below describe only each callback algorithm's shape.
        var flatMap = PlanFor("Double(n) = n * 2", "Double");
        AssertTopLevelNodes(flatMap, "Capture(n:Explicit)");
        AssertCaptures(flatMap, "n:Explicit");
        AssertArity(flatMap, min: 1, max: 1, hasTopLevelVariadic: false);

        AssertEval(
            """
            Double(n) = n * 2
            map((1, 2, 3), Double)
            """,
            2, 4, 6);

        var sequenceValueMap = PlanFor("PairSum((x, y)) = x + y", "PairSum");
        AssertTopLevelNodes(sequenceValueMap, "SequenceValue(Capture(x:Explicit), Capture(y:Explicit))");
        AssertCaptures(sequenceValueMap, "x:Explicit", "y:Explicit");
        AssertArity(sequenceValueMap, min: 1, max: 1, hasTopLevelVariadic: false);

        AssertEval(
            """
            PairSum((x, y)) = x + y
            map(((1, 2), (3, 4)), PairSum)
            """,
            3, 7);

        var sequenceValueReduce = PlanFor("TakeValue((tag, value), acc) = acc + value", "TakeValue");
        AssertTopLevelNodes(sequenceValueReduce, "SequenceValue(Capture(tag:Explicit), Capture(value:Explicit))", "Capture(acc:Explicit)");
        AssertCaptures(sequenceValueReduce, "tag:Explicit", "value:Explicit", "acc:Explicit");
        AssertArity(sequenceValueReduce, min: 2, max: 2, hasTopLevelVariadic: false);

        AssertEval(
            """
            TakeValue((tag, value), acc) = acc + value
            reduce(((1, 10), (2, 20)), TakeValue, 0)
            """,
            30);
    }

    [Fact]
    public void ConditionalBranchMatching_RemainsOutsideCallableBindingPlan()
    {
        var parseResult = Parser.Parse(
            """
            Choose(0) = 10
            Choose(x) = x
            Choose(5)
            """);

        Assert.False(
            parseResult.HasErrors,
            string.Join(Environment.NewLine, parseResult.Diagnostics.Select(static diagnostic => diagnostic.Message)));

        var property = parseResult.Root.Properties.Single(property => property.Name == "Choose");
        var conditional = Assert.IsType<Algorithm.Conditional>(property.Value);
        Assert.Equal(2, conditional.Branches.Count);

        // Conditional branch patterns are not ordinary callable parameter shapes.
        var plan = CallableBindingPlan.FromSignature(CallableSignature.FromAlgorithm("Choose", conditional));
        AssertPlanDisplay(plan, "Choose");
        AssertTopLevelNodes(plan);
        AssertCaptures(plan);
        AssertArity(plan, min: 0, max: 0, hasTopLevelVariadic: false);
    }

    private static void AssertBuiltinCollectionPlan(
        BuiltinId builtin,
        string display,
        string? controlName)
    {
        var plan = CallableBindingPlan.FromSignature(CallableSignature.FromBuiltin(builtin));

        AssertPlanDisplay(plan, display);
        // Fixed collection-object model: one ordinary `collection` capture
        // plus fixed control captures — a flat fixed layout, no variadic.
        Assert.Null(plan.TopLevelPatternList.VariadicCapture);
        var parameterCount = controlName is null ? 1 : 2;
        AssertArity(plan, min: parameterCount, max: parameterCount, hasTopLevelVariadic: false);
        Assert.False(plan.TryGetFlatVariadicLayout(out _, out _, out _));
        Assert.True(plan.TryGetFlatFixedLayout(out var captures));
        Assert.Equal(parameterCount, captures.Count);
        Assert.Equal("collection", captures[0].Name);
        Assert.All(captures, capture => Assert.Equal(CallableParameterSource.Builtin, capture.Source));

        if (controlName is null)
        {
            AssertTopLevelNodes(plan, "Capture(collection:Builtin)");
            AssertCaptures(plan, "collection:Builtin");
            return;
        }

        AssertTopLevelNodes(plan, "Capture(collection:Builtin)", "Capture(" + controlName + ":Builtin)");
        AssertCaptures(plan, "collection:Builtin", controlName + ":Builtin");
    }
}
