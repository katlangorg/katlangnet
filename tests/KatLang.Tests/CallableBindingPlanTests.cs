namespace KatLang.Tests;

public class CallableBindingPlanTests
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
        var signature = CallableSignature.FromAlgorithm(name, property.Value);
        return CallableBindingPlan.FromSignature(signature);
    }

    private static CaptureBindingNode AssertCapture(
        CallableBindingNode node,
        string name,
        CallableParameterSource source)
    {
        var capture = Assert.IsType<CaptureBindingNode>(node);
        Assert.Equal(name, capture.Name);
        Assert.Equal(ParameterKind.Normal, capture.Kind);
        Assert.Equal(source, capture.Source);
        return capture;
    }

    private static VariadicCaptureBindingNode AssertVariadic(
        CallableBindingNode node,
        string name,
        CallableParameterSource source,
        bool isTopLevel)
    {
        var capture = Assert.IsType<VariadicCaptureBindingNode>(node);
        Assert.Equal(name, capture.Name);
        Assert.Equal(ParameterKind.Variadic, capture.Kind);
        Assert.Equal(source, capture.Source);
        Assert.Equal(isTopLevel, capture.IsTopLevel);
        return capture;
    }

    [Fact]
    public void FromSignature_ExplicitScalarPlan_UsesTwoTopLevelCaptures()
    {
        var plan = PlanFor("Add(x, y) = x + y", "Add");
        var topLevel = plan.TopLevelPatternList;

        Assert.Equal("Add(x, y)", plan.DisplayText);
        Assert.Equal(2, topLevel.Nodes.Count);
        AssertCapture(topLevel.Nodes[0], "x", CallableParameterSource.Explicit);
        AssertCapture(topLevel.Nodes[1], "y", CallableParameterSource.Explicit);
        Assert.Equal(2, topLevel.MinSlotCount);
        Assert.Equal(2, topLevel.MaxSlotCount);
        Assert.False(topLevel.HasVariadicAtThisLevel);
        Assert.Equal(["x", "y"], plan.Captures.Select(static capture => capture.DisplayName).ToArray());
    }

    [Fact]
    public void FromSignature_ImplicitOnlyPlan_UsesImplicitCaptures()
    {
        var plan = PlanFor("Add = x + y", "Add");
        var topLevel = plan.TopLevelPatternList;

        Assert.Equal("Add(x, y)", plan.DisplayText);
        Assert.Equal(2, topLevel.Nodes.Count);
        AssertCapture(topLevel.Nodes[0], "x", CallableParameterSource.Implicit);
        AssertCapture(topLevel.Nodes[1], "y", CallableParameterSource.Implicit);
    }

    [Fact]
    public void FromSignature_SequenceValueExplicitPlan_ConsumesOneTopLevelSlot()
    {
        var plan = PlanFor("PairSum((x, y)) = x + y", "PairSum");
        var topLevel = plan.TopLevelPatternList;

        Assert.Equal("PairSum((x, y))", plan.DisplayText);
        var group = Assert.IsType<SequenceValueBindingNode>(Assert.Single(topLevel.Nodes));
        Assert.Equal(2, group.Children.Nodes.Count);
        AssertCapture(group.Children.Nodes[0], "x", CallableParameterSource.Explicit);
        AssertCapture(group.Children.Nodes[1], "y", CallableParameterSource.Explicit);
        Assert.Equal(1, topLevel.MinSlotCount);
        Assert.Equal(1, topLevel.MaxSlotCount);
        Assert.False(topLevel.HasVariadicAtThisLevel);
        Assert.Equal(["x", "y"], plan.Captures.Select(static capture => capture.Name).ToArray());
    }

    [Fact]
    public void FromSignature_TopLevelVariadicPlan_HasZeroMinimumAndUnboundedMaximum()
    {
        var plan = PlanFor("CountValues(values...) = values.count", "CountValues");
        var topLevel = plan.TopLevelPatternList;

        var values = AssertVariadic(Assert.Single(topLevel.Nodes), "values", CallableParameterSource.Explicit, isTopLevel: true);
        Assert.Same(values, topLevel.VariadicCapture);
        Assert.Empty(topLevel.Prefix);
        Assert.Empty(topLevel.Suffix);
        // Lone-variadic item supply: no fixed bindings, so min 0 and unbounded max.
        Assert.Equal(0, topLevel.MinSlotCount);
        Assert.Null(topLevel.MaxSlotCount);
        Assert.True(topLevel.HasVariadicAtThisLevel);
        Assert.Equal(["values..."], plan.Captures.Select(static capture => capture.DisplayName).ToArray());
    }

    [Fact]
    public void FromSignature_TopLevelVariadicWithSuffixPlan_BindsSuffixFromBack()
    {
        var plan = PlanFor("Scale(items..., factor) = items.map{n * factor}", "Scale");
        var topLevel = plan.TopLevelPatternList;

        Assert.Empty(topLevel.Prefix);
        Assert.NotNull(topLevel.VariadicCapture);
        Assert.Equal("items", topLevel.VariadicCapture.Name);
        Assert.True(topLevel.VariadicCapture.IsTopLevel);
        var suffix = Assert.Single(topLevel.Suffix);
        AssertCapture(suffix, "factor", CallableParameterSource.Explicit);
        // Deconstruction-shaped: the fixed suffix `factor` is the only required
        // slot, and the variadic parameter `items...` may collect any number of prefix items.
        Assert.Equal(1, topLevel.MinSlotCount);
        Assert.Null(topLevel.MaxSlotCount);
        Assert.True(topLevel.HasVariadicAtThisLevel);
    }

    [Fact]
    public void FromSignature_SequenceValueVariadicPlan_IsNestedNotTopLevel()
    {
        var plan = PlanFor("CountSequenceValue((values...)) = values.count", "CountSequenceValue");
        var topLevel = plan.TopLevelPatternList;

        var group = Assert.IsType<SequenceValueBindingNode>(Assert.Single(topLevel.Nodes));
        var values = AssertVariadic(Assert.Single(group.Children.Nodes), "values", CallableParameterSource.Explicit, isTopLevel: false);
        Assert.Same(values, group.Children.VariadicCapture);
        Assert.False(topLevel.HasVariadicAtThisLevel);
        Assert.True(topLevel.HasVariadicInDescendants);
        Assert.Equal(1, topLevel.MinSlotCount);
        Assert.Equal(1, topLevel.MaxSlotCount);
        Assert.Equal(0, plan.ArityFacts.TopLevelVariadicCount);
    }

    [Fact]
    public void FromSignature_NestedSequenceValueRecursivePlan_PreservesNestedStructure()
    {
        var plan = PlanFor("G(((history...), previous)) = history.count + previous", "G");
        var topLevel = plan.TopLevelPatternList;

        var outerGroup = Assert.IsType<SequenceValueBindingNode>(Assert.Single(topLevel.Nodes));
        Assert.Equal(2, outerGroup.Children.Nodes.Count);
        var historyGroup = Assert.IsType<SequenceValueBindingNode>(outerGroup.Children.Nodes[0]);
        AssertVariadic(Assert.Single(historyGroup.Children.Nodes), "history", CallableParameterSource.Explicit, isTopLevel: false);
        AssertCapture(outerGroup.Children.Nodes[1], "previous", CallableParameterSource.Explicit);
        Assert.False(topLevel.HasVariadicAtThisLevel);
        Assert.True(topLevel.HasVariadicInDescendants);
        Assert.Equal(1, topLevel.MinSlotCount);
        Assert.Equal(1, topLevel.MaxSlotCount);
        Assert.Equal(["history...", "previous"], plan.Captures.Select(static capture => capture.DisplayName).ToArray());
    }

    [Fact]
    public void FromSignature_ExplicitClosedPlan_ExcludesUnresolvedFreeName()
    {
        var plan = PlanFor("F((x, y)) = x + y + z", "F", allowErrors: true);

        Assert.Equal("F((x, y))", plan.DisplayText);
        Assert.Equal(["x", "y"], plan.Captures.Select(static capture => capture.Name).ToArray());
        Assert.DoesNotContain(plan.Captures, static capture => capture.Name == "z");
    }

    [Fact]
    public void FromSignature_BuiltinCollectionPlans_AreFlatFixedWithBuiltinSources()
    {
        var map = CallableBindingPlan.FromSignature(CallableSignature.FromBuiltin(BuiltinId.map));
        var take = CallableBindingPlan.FromSignature(CallableSignature.FromBuiltin(BuiltinId.take));
        var count = CallableBindingPlan.FromSignature(CallableSignature.FromBuiltin(BuiltinId.count));

        // Collection builtins are ordinary fixed-arity callables: one fixed
        // `collection` capture plus fixed control captures, no variadic.
        Assert.Equal("map(collection, mapper)", map.DisplayText);
        Assert.Null(map.TopLevelPatternList.VariadicCapture);
        Assert.Equal(2, map.TopLevelPatternList.Nodes.Count);
        AssertCapture(map.TopLevelPatternList.Nodes[0], "collection", CallableParameterSource.Builtin);
        AssertCapture(map.TopLevelPatternList.Nodes[1], "mapper", CallableParameterSource.Builtin);
        Assert.Equal(2, map.TopLevelPatternList.MinSlotCount);
        Assert.Equal(2, map.TopLevelPatternList.MaxSlotCount);
        Assert.False(map.TopLevelPatternList.HasVariadicAtThisLevel);
        Assert.True(map.TryGetFlatFixedLayout(out _));

        Assert.Equal("take(collection, count)", take.DisplayText);
        Assert.Null(take.TopLevelPatternList.VariadicCapture);
        Assert.Equal(2, take.TopLevelPatternList.Nodes.Count);
        AssertCapture(take.TopLevelPatternList.Nodes[0], "collection", CallableParameterSource.Builtin);
        AssertCapture(take.TopLevelPatternList.Nodes[1], "count", CallableParameterSource.Builtin);
        Assert.Equal(2, take.TopLevelPatternList.MinSlotCount);
        Assert.Equal(2, take.TopLevelPatternList.MaxSlotCount);
        Assert.True(take.TryGetFlatFixedLayout(out _));

        Assert.Equal("count(collection)", count.DisplayText);
        AssertCapture(Assert.Single(count.TopLevelPatternList.Nodes), "collection", CallableParameterSource.Builtin);
        Assert.Equal(1, count.TopLevelPatternList.MinSlotCount);
        Assert.Equal(1, count.TopLevelPatternList.MaxSlotCount);
        Assert.False(count.TopLevelPatternList.HasVariadicAtThisLevel);
        Assert.True(count.TryGetFlatFixedLayout(out _));
    }

    [Fact]
    public void FromSignature_ArityFactsAgreeWithCallableSignatureDiagnostics()
    {
        var signatures = new[]
        {
            PlanFor("Add(x, y) = x + y", "Add").Signature,
            PlanFor("PairSum((x, y)) = x + y", "PairSum").Signature,
            PlanFor("CountValues(values...) = values.count", "CountValues").Signature,
            PlanFor("CountSequenceValue((values...)) = values.count", "CountSequenceValue").Signature,
            CallableSignature.FromBuiltin(BuiltinId.map),
            CallableSignature.FromBuiltin(BuiltinId.count),
        };

        foreach (var signature in signatures)
        {
            var plan = CallableBindingPlan.FromSignature(signature);

            Assert.Equal(CallableSignatureDiagnostics.GetArityFacts(signature), plan.ArityFacts);
            Assert.Equal(plan.ArityFacts.MinTopLevelArgumentCount, plan.TopLevelPatternList.MinSlotCount);
            Assert.Equal(plan.ArityFacts.MaxTopLevelArgumentCount, plan.TopLevelPatternList.MaxSlotCount);
            Assert.Equal(plan.ArityFacts.HasTopLevelVariadic, plan.TopLevelPatternList.HasVariadicAtThisLevel);
            Assert.Equal(plan.ArityFacts.TopLevelVariadicCount, plan.TopLevelPatternList.VariadicCountAtThisLevel);
        }
    }
}
