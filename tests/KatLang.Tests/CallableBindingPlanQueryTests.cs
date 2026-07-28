namespace KatLang.Tests;

public class CallableBindingPlanQueryTests
{
    private static CallableBindingPlan PlanFor(string source, string name)
    {
        var parseResult = Parser.Parse(source);
        Assert.False(
            parseResult.HasErrors,
            string.Join(Environment.NewLine, parseResult.Diagnostics.Select(static diagnostic => diagnostic.Message)));

        var property = parseResult.Root.Properties.Single(property => property.Name == name);
        return CallableBindingPlan.FromSignature(CallableSignature.FromAlgorithm(name, property.Value));
    }

    private static void AssertFlatFixedLayout(
        CallableBindingPlan plan,
        params (string Name, CallableParameterSource Source)[] expected)
    {
        Assert.True(plan.TryGetFlatFixedLayout(out var captures));
        Assert.Equal(expected.Select(static item => item.Name).ToArray(), captures.Select(static capture => capture.Name).ToArray());
        Assert.Equal(expected.Select(static item => item.Source).ToArray(), captures.Select(static capture => capture.Source).ToArray());
    }

    private static void AssertFlatVariadicLayout(
        CallableBindingPlan plan,
        string[] expectedPrefixNames,
        string variadicName,
        CallableParameterSource variadicSource,
        string[] expectedSuffixNames,
        CallableParameterSource suffixSource)
    {
        Assert.True(plan.TryGetFlatVariadicLayout(out var prefix, out var variadic, out var suffix));
        Assert.Equal(expectedPrefixNames, prefix.Select(static capture => capture.Name).ToArray());
        Assert.Equal(variadicName, variadic.Name);
        Assert.Equal(variadicSource, variadic.Source);
        Assert.True(variadic.IsTopLevel);
        Assert.Equal(expectedSuffixNames, suffix.Select(static capture => capture.Name).ToArray());
        Assert.All(suffix, capture => Assert.Equal(suffixSource, capture.Source));
    }

    private static void AssertTopLevelNodes(CallableBindingPlan plan, params string[] expected)
        => Assert.Equal(expected, plan.TopLevelPatternList.Nodes.Select(DescribeNode).ToArray());

    private static void AssertCaptureNames(CallableBindingPlan plan, params string[] expected)
        => Assert.Equal(expected, plan.Captures.Select(static capture => capture.Name).ToArray());

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

    private static void AssertQueryFacts(
        CallableBindingPlan plan,
        bool requiresPatternedBinding,
        bool hasOnlyFlatTopLevelCaptures,
        bool hasOnlyFlatFixedTopLevelCaptures,
        bool hasTopLevelVariadic,
        bool hasNestedVariadic,
        int min,
        int? max)
    {
        Assert.Equal(requiresPatternedBinding, plan.RequiresPatternedBinding);
        Assert.Equal(hasOnlyFlatTopLevelCaptures, plan.HasOnlyFlatTopLevelCaptures);
        Assert.Equal(hasOnlyFlatFixedTopLevelCaptures, plan.HasOnlyFlatFixedTopLevelCaptures);
        Assert.Equal(hasTopLevelVariadic, plan.HasTopLevelVariadic);
        Assert.Equal(hasNestedVariadic, plan.HasNestedVariadic);
        Assert.Equal(hasTopLevelVariadic, plan.TopLevelVariadicCapture is not null);
        Assert.Equal(min, plan.ArityFacts.MinTopLevelArgumentCount);
        Assert.Equal(max, plan.ArityFacts.MaxTopLevelArgumentCount);
    }

    [Fact]
    public void ExplicitScalarFixedLayout_SucceedsAsFlatFixed()
    {
        var plan = PlanFor("Add(x, y) = x + y", "Add");

        AssertQueryFacts(
            plan,
            requiresPatternedBinding: false,
            hasOnlyFlatTopLevelCaptures: true,
            hasOnlyFlatFixedTopLevelCaptures: true,
            hasTopLevelVariadic: false,
            hasNestedVariadic: false,
            min: 2,
            max: 2);
        AssertFlatFixedLayout(plan, ("x", CallableParameterSource.Explicit), ("y", CallableParameterSource.Explicit));
        Assert.False(plan.TryGetFlatVariadicLayout(out _, out _, out _));
    }

    [Fact]
    public void ImplicitScalarFixedLayout_SucceedsAsFlatFixedWithImplicitSources()
    {
        var plan = PlanFor("Add = x + y", "Add");

        AssertQueryFacts(
            plan,
            requiresPatternedBinding: false,
            hasOnlyFlatTopLevelCaptures: true,
            hasOnlyFlatFixedTopLevelCaptures: true,
            hasTopLevelVariadic: false,
            hasNestedVariadic: false,
            min: 2,
            max: 2);
        AssertFlatFixedLayout(plan, ("x", CallableParameterSource.Implicit), ("y", CallableParameterSource.Implicit));
    }

    [Fact]
    public void SequenceValueExplicitLayout_RequiresPatternedBinding()
    {
        var plan = PlanFor("PairSum((x, y)) = x + y", "PairSum");

        AssertQueryFacts(
            plan,
            requiresPatternedBinding: true,
            hasOnlyFlatTopLevelCaptures: false,
            hasOnlyFlatFixedTopLevelCaptures: false,
            hasTopLevelVariadic: false,
            hasNestedVariadic: false,
            min: 1,
            max: 1);
        Assert.False(plan.TryGetFlatFixedLayout(out _));
        Assert.False(plan.TryGetFlatVariadicLayout(out _, out _, out _));
    }

    [Fact]
    public void TopLevelVariadicLayout_SucceedsAsFlatVariadic()
    {
        var plan = PlanFor("CountValues(values...) = values.count", "CountValues");

        AssertQueryFacts(
            plan,
            requiresPatternedBinding: false,
            hasOnlyFlatTopLevelCaptures: true,
            hasOnlyFlatFixedTopLevelCaptures: false,
            hasTopLevelVariadic: true,
            hasNestedVariadic: false,
            // Lone-variadic item supply: no fixed bindings, so min 0 and unbounded max.
            min: 0,
            max: null);
        Assert.NotNull(plan.TopLevelVariadicCapture);
        Assert.Equal("values", plan.TopLevelVariadicCapture.Name);
        Assert.False(plan.TryGetFlatFixedLayout(out _));
        AssertFlatVariadicLayout(plan, [], "values", CallableParameterSource.Explicit, [], CallableParameterSource.Explicit);
    }

    [Fact]
    public void VariadicSuffixLayout_ReturnsFlatSuffixCaptures()
    {
        var plan = PlanFor("Scale(items..., factor) = items.map{n * factor}", "Scale");

        AssertQueryFacts(
            plan,
            requiresPatternedBinding: false,
            hasOnlyFlatTopLevelCaptures: true,
            hasOnlyFlatFixedTopLevelCaptures: false,
            hasTopLevelVariadic: true,
            hasNestedVariadic: false,
            min: 1,
            max: null);
        AssertFlatVariadicLayout(plan, [], "items", CallableParameterSource.Explicit, ["factor"], CallableParameterSource.Explicit);
    }

    [Fact]
    public void FlatVariadicLayout_OrderMatchesSignatureParameterOrder()
    {
        // Body is incidental to this plan-shape test; comma slots avoid the
        // confusing tight `A.spread B` adjacency.
        var plan = PlanFor("F(first, middle..., last) = first, middle.spread, last", "F");

        Assert.True(plan.TryGetFlatVariadicLayout(out var prefix, out var variadic, out var suffix));
        var layoutNames = prefix
            .Select(static capture => capture.Name)
            .Concat([variadic.Name])
            .Concat(suffix.Select(static capture => capture.Name))
            .ToArray();

        Assert.Equal(["first", "middle", "last"], layoutNames);
        Assert.Equal(plan.Signature.Parameters.Select(static parameter => parameter.Name).ToArray(), layoutNames);
        Assert.Equal(["first", "middle...", "last"], plan.Signature.Parameters.Select(static parameter => parameter.DisplayName).ToArray());
    }

    [Fact]
    public void SequenceValueVariadicLayout_IsNestedNotTopLevel()
    {
        var plan = PlanFor("CountSequenceValue((values...)) = values.count", "CountSequenceValue");

        AssertQueryFacts(
            plan,
            requiresPatternedBinding: true,
            hasOnlyFlatTopLevelCaptures: false,
            hasOnlyFlatFixedTopLevelCaptures: false,
            hasTopLevelVariadic: false,
            hasNestedVariadic: true,
            min: 1,
            max: 1);
        Assert.Null(plan.TopLevelVariadicCapture);
        Assert.False(plan.TryGetFlatFixedLayout(out _));
        Assert.False(plan.TryGetFlatVariadicLayout(out _, out _, out _));
    }

    [Fact]
    public void MixedPatternedAndTopLevelVariadicLayout_RequiresPatternedBindingFirst()
    {
        var plan = PlanFor("F((inner...), outer...) = inner.spread, outer", "F");

        AssertQueryFacts(
            plan,
            requiresPatternedBinding: true,
            hasOnlyFlatTopLevelCaptures: false,
            hasOnlyFlatFixedTopLevelCaptures: false,
            hasTopLevelVariadic: true,
            hasNestedVariadic: true,
            min: 2,
            max: 2);
        Assert.NotNull(plan.TopLevelVariadicCapture);
        Assert.Equal("outer", plan.TopLevelVariadicCapture.Name);
        Assert.False(plan.TryGetFlatFixedLayout(out _));
        Assert.False(plan.TryGetFlatVariadicLayout(out _, out _, out _));
    }

    [Fact]
    public void NestedSequenceValueRecursiveLayout_PreservesNestedVariadicFacts()
    {
        var plan = PlanFor("G(((history...), previous)) = history.count + previous", "G");

        AssertQueryFacts(
            plan,
            requiresPatternedBinding: true,
            hasOnlyFlatTopLevelCaptures: false,
            hasOnlyFlatFixedTopLevelCaptures: false,
            hasTopLevelVariadic: false,
            hasNestedVariadic: true,
            min: 1,
            max: 1);
        Assert.Equal(["history", "previous"], plan.Captures.Select(static capture => capture.Name).ToArray());
        Assert.False(plan.TryGetFlatFixedLayout(out _));
        Assert.False(plan.TryGetFlatVariadicLayout(out _, out _, out _));
    }

    [Fact]
    public void BuiltinMapLayout_SucceedsAsFlatFixedWithBuiltinSources()
    {
        var plan = CallableBindingPlan.FromSignature(CallableSignature.FromBuiltin(BuiltinId.map));

        // Collection builtins are ordinary fixed-arity callables:
        // min = max = parameter count and the layout is flat fixed.
        AssertQueryFacts(
            plan,
            requiresPatternedBinding: false,
            hasOnlyFlatTopLevelCaptures: true,
            hasOnlyFlatFixedTopLevelCaptures: true,
            hasTopLevelVariadic: false,
            hasNestedVariadic: false,
            min: 2,
            max: 2);
        AssertFlatFixedLayout(plan, ("collection", CallableParameterSource.Builtin), ("mapper", CallableParameterSource.Builtin));
        Assert.False(plan.TryGetFlatVariadicLayout(out _, out _, out _));
    }

    [Theory]
    [InlineData(BuiltinId.filter, "predicate")]
    [InlineData(BuiltinId.take, "count")]
    [InlineData(BuiltinId.skip, "count")]
    public void BuiltinControlLayouts_SucceedAsFlatFixedWithOneControl(
        BuiltinId builtin,
        string controlName)
    {
        var plan = CallableBindingPlan.FromSignature(CallableSignature.FromBuiltin(builtin));

        AssertQueryFacts(
            plan,
            requiresPatternedBinding: false,
            hasOnlyFlatTopLevelCaptures: true,
            hasOnlyFlatFixedTopLevelCaptures: true,
            hasTopLevelVariadic: false,
            hasNestedVariadic: false,
            min: 2,
            max: 2);
        AssertFlatFixedLayout(plan, ("collection", CallableParameterSource.Builtin), (controlName, CallableParameterSource.Builtin));
        Assert.False(plan.TryGetFlatVariadicLayout(out _, out _, out _));
    }

    [Theory]
    [InlineData(BuiltinId.count)]
    [InlineData(BuiltinId.sum)]
    public void BuiltinSingleCollectionLayouts_SucceedAsFlatFixed(BuiltinId builtin)
    {
        var plan = CallableBindingPlan.FromSignature(CallableSignature.FromBuiltin(builtin));

        AssertQueryFacts(
            plan,
            requiresPatternedBinding: false,
            hasOnlyFlatTopLevelCaptures: true,
            hasOnlyFlatFixedTopLevelCaptures: true,
            hasTopLevelVariadic: false,
            hasNestedVariadic: false,
            min: 1,
            max: 1);
        AssertFlatFixedLayout(plan, ("collection", CallableParameterSource.Builtin));
        Assert.False(plan.TryGetFlatVariadicLayout(out _, out _, out _));
    }

    [Fact]
    public void LoopStepShapeQueries_IncludePrefixSuffixAndSequenceValueVariadic()
    {
        // These plans inspect only the parameter pattern; the bodies are
        // incidental, so they use comma slots (not tight `A.spread B` adjacency,
        // which reads like a non-existent binary spread) for clarity.
        var flat = PlanFor("Step(first, middle..., last) = first, middle.spread, last, 0", "Step");
        AssertQueryFacts(
            flat,
            requiresPatternedBinding: false,
            hasOnlyFlatTopLevelCaptures: true,
            hasOnlyFlatFixedTopLevelCaptures: false,
            hasTopLevelVariadic: true,
            hasNestedVariadic: false,
            // Deconstruction-shaped: `first` and `last` are the fixed bindings,
            // `middle...` captures any number of middle items.
            min: 2,
            max: null);
        AssertTopLevelNodes(flat, "Capture(first:Explicit)", "Variadic(middle:Explicit:top)", "Capture(last:Explicit)");
        AssertFlatVariadicLayout(flat, ["first"], "middle", CallableParameterSource.Explicit, ["last"], CallableParameterSource.Explicit);

        var sequenceValuePlan = PlanFor("Step((history...), previous) = history.spread, previous, 0", "Step");
        AssertQueryFacts(
            sequenceValuePlan,
            requiresPatternedBinding: true,
            hasOnlyFlatTopLevelCaptures: false,
            hasOnlyFlatFixedTopLevelCaptures: false,
            hasTopLevelVariadic: false,
            hasNestedVariadic: true,
            min: 2,
            max: 2);
        AssertTopLevelNodes(sequenceValuePlan, "SequenceValue(Variadic(history:Explicit:nested))", "Capture(previous:Explicit)");
        AssertCaptureNames(sequenceValuePlan, "history", "previous");
        Assert.False(sequenceValuePlan.TryGetFlatFixedLayout(out _));
        Assert.False(sequenceValuePlan.TryGetFlatVariadicLayout(out _, out _, out _));

        var nested = PlanFor("Step((history..., previous), current) = history.spread, previous, current, 0", "Step");
        AssertQueryFacts(
            nested,
            requiresPatternedBinding: true,
            hasOnlyFlatTopLevelCaptures: false,
            hasOnlyFlatFixedTopLevelCaptures: false,
            hasTopLevelVariadic: false,
            hasNestedVariadic: true,
            min: 2,
            max: 2);
        AssertTopLevelNodes(nested, "SequenceValue(Variadic(history:Explicit:nested), Capture(previous:Explicit))", "Capture(current:Explicit)");
        AssertCaptureNames(nested, "history", "previous", "current");
        Assert.False(nested.TryGetFlatFixedLayout(out _));
        Assert.False(nested.TryGetFlatVariadicLayout(out _, out _, out _));
    }

    [Fact]
    public void CallbackShapeQueries_DescribeOrdinaryCallbackSignatures()
    {
        // Callback item projection/counting is runtime behavior; these plans
        // describe only the callback algorithm's callable shape.
        var flat = PlanFor("Double(n) = n * 2", "Double");
        AssertQueryFacts(
            flat,
            requiresPatternedBinding: false,
            hasOnlyFlatTopLevelCaptures: true,
            hasOnlyFlatFixedTopLevelCaptures: true,
            hasTopLevelVariadic: false,
            hasNestedVariadic: false,
            min: 1,
            max: 1);
        AssertFlatFixedLayout(flat, ("n", CallableParameterSource.Explicit));

        var sequenceValuePlan = PlanFor("PairSum((x, y)) = x + y", "PairSum");
        AssertQueryFacts(
            sequenceValuePlan,
            requiresPatternedBinding: true,
            hasOnlyFlatTopLevelCaptures: false,
            hasOnlyFlatFixedTopLevelCaptures: false,
            hasTopLevelVariadic: false,
            hasNestedVariadic: false,
            min: 1,
            max: 1);
        AssertTopLevelNodes(sequenceValuePlan, "SequenceValue(Capture(x:Explicit), Capture(y:Explicit))");
        AssertCaptureNames(sequenceValuePlan, "x", "y");

        var reducer = PlanFor("AddItemCount(item, acc) = acc + item", "AddItemCount");
        AssertQueryFacts(
            reducer,
            requiresPatternedBinding: false,
            hasOnlyFlatTopLevelCaptures: true,
            hasOnlyFlatFixedTopLevelCaptures: true,
            hasTopLevelVariadic: false,
            hasNestedVariadic: false,
            min: 2,
            max: 2);
        AssertFlatFixedLayout(reducer, ("item", CallableParameterSource.Explicit), ("acc", CallableParameterSource.Explicit));

        var sequenceValueReducer = PlanFor("TakeStats((tag, value), (sum, count)) = sum + value, count + 1", "TakeStats");
        AssertQueryFacts(
            sequenceValueReducer,
            requiresPatternedBinding: true,
            hasOnlyFlatTopLevelCaptures: false,
            hasOnlyFlatFixedTopLevelCaptures: false,
            hasTopLevelVariadic: false,
            hasNestedVariadic: false,
            min: 2,
            max: 2);
        AssertTopLevelNodes(
            sequenceValueReducer,
            "SequenceValue(Capture(tag:Explicit), Capture(value:Explicit))",
            "SequenceValue(Capture(sum:Explicit), Capture(count:Explicit))");
        AssertCaptureNames(sequenceValueReducer, "tag", "value", "sum", "count");
    }
}
