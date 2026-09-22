namespace KatLang.Tests;

/// <summary>
/// The ONE per-level arity rule: at EVERY pattern level, the arity metadata
/// (<see cref="CallableArityFacts"/>, <see cref="PatternListBindingPlan.MinSlotCount"/> /
/// <see cref="PatternListBindingPlan.MaxSlotCount"/>) describes exactly the supply the
/// BINDER accepts there —
/// <c>min = patterns at this level - (1 if this level holds a collecting capture)</c>
/// (<c>ParameterPattern.MinimumSuppliedSlots</c>, the rule <c>BindParameterPatternList</c>
/// itself enforces) and <c>max = unbounded iff this level holds a collecting capture</c>.
///
/// <para>The classification used to be "one collector AND no grouped pattern anywhere at
/// this level", which disagreed with the binder for every signature mixing a group with a
/// collector: <c>G((a, b), *rest)</c> was reported as fixed arity 2 while <c>G()</c> is
/// rejected with the binder's minimum 1 and <c>G((1, 2), 3, 4)</c> binds happily. The
/// nested half was worse still — the rule was gated on <c>isTopLevel</c>, so the nested
/// list of <c>P((x, *r))</c> claimed exact arity 2 where the binder accepts one value or
/// more.</para>
/// </summary>
public class CallableArityFactsPerLevelTests
{
    private static CallableSignature SignatureFor(string source, string name)
        => CallableSignature.FromAlgorithm(name, PropertyFor(source, name));

    private static CallableBindingPlan PlanFor(string source, string name)
        => CallableBindingPlan.FromSignature(SignatureFor(source, name));

    private static Algorithm PropertyFor(string source, string name)
        => SourceProvenance.ParseValid(source).Root.Properties.Single(property => property.Name == name).Value;

    private static CallableSignature HostSignature(string name, params ParameterPattern[] parameterPatterns)
        => CallableSignature.FromAlgorithm(
            name,
            new Algorithm.User(
                Parent: null,
                ParameterPatterns: parameterPatterns,
                Opens: [],
                Properties: [],
                Output: [new Expr.Num(0)]));

    /// <summary>
    /// Every level's facts, in written order, depth first: the top-level list followed by
    /// each sequence-value group's own list. Used to state the per-level invariant without
    /// hand-walking the plan at each call site.
    /// </summary>
    private static IReadOnlyList<(string Path, int Min, int? Max)> LevelArities(CallableBindingPlan plan)
    {
        var levels = new List<(string, int, int?)>();
        Walk(plan.TopLevelPatternList, plan.DisplayText);
        return levels;

        void Walk(PatternListBindingPlan level, string path)
        {
            levels.Add((path, level.MinSlotCount, level.MaxSlotCount));
            foreach (var node in level.Nodes)
            {
                if (node is SequenceValueBindingNode group)
                    Walk(group.Children, $"{path} > ({string.Join(", ", group.Children.Captures.Select(static capture => capture.DisplayName))})");
            }
        }
    }

    private static PatternListBindingPlan NestedLevel(CallableBindingPlan plan, int topLevelIndex)
        => Assert.IsType<SequenceValueBindingNode>(plan.TopLevelPatternList.Nodes[topLevelIndex]).Children;

    private static void AssertTopLevelFacts(CallableSignature signature, int min, int? max, int collectingCount)
    {
        var facts = signature.ArityFacts;
        Assert.Equal(min, facts.MinTopLevelArgumentCount);
        Assert.Equal(max, facts.MaxTopLevelArgumentCount);
        Assert.Equal(collectingCount > 0, facts.HasTopLevelCollecting);
        Assert.Equal(collectingCount, facts.TopLevelCollectingCount);

        // AcceptsItemCount is the public projection of the same two numbers.
        for (var count = 0; count <= (max ?? min) + 3; count++)
        {
            var expected = count >= min && (max is null || count <= max.Value);
            Assert.Equal(expected, signature.AcceptsItemCount(count));
        }
    }

    // ---------------------------------------------------------------------
    // Top level: a grouped pattern beside a collector is still item supply.
    // ---------------------------------------------------------------------

    [Fact]
    public void ArityFacts_GroupThenCollector_IsBinderMinimumWithUnboundedMax()
    {
        var signature = SignatureFor("G((a, b), *rest) = a", "G");

        Assert.Equal("G((a, b), *rest)", signature.DisplayText);
        Assert.True(signature.HasSequenceValueParameterPattern);
        // The grouped pattern consumes one supplied slot; the collector consumes none.
        AssertTopLevelFacts(signature, min: 1, max: null, collectingCount: 1);
        Assert.False(signature.AcceptsItemCount(0));
        Assert.True(signature.AcceptsItemCount(1));
        Assert.True(signature.AcceptsItemCount(2));
        Assert.True(signature.AcceptsItemCount(50));

        // ...and that is exactly what the binder does.
        AssertCallRejectedByTopLevelArity("G((a, b), *rest) = a\nG()", expectedMinimum: 1, actual: 0);
        AssertCallSucceeds("G((a, b), *rest) = a\nG((1, 2))", 1);
        AssertCallSucceeds("G((a, b), *rest) = a\nG((1, 2), 3, 4)", 1);
    }

    [Fact]
    public void ArityFacts_CollectorThenGroup_IsBinderMinimumWithUnboundedMax()
    {
        var signature = SignatureFor("H(*rest, (a, b)) = a", "H");

        Assert.Equal("H(*rest, (a, b))", signature.DisplayText);
        AssertTopLevelFacts(signature, min: 1, max: null, collectingCount: 1);
        Assert.False(signature.AcceptsItemCount(0));
        Assert.True(signature.AcceptsItemCount(1));
        Assert.True(signature.AcceptsItemCount(7));

        AssertCallRejectedByTopLevelArity("H(*rest, (a, b)) = a\nH()", expectedMinimum: 1, actual: 0);
        AssertCallSucceeds("H(*rest, (a, b)) = a\nH((1, 2))", 1);
        AssertCallSucceeds("H(*rest, (a, b)) = a\nH(9, (1, 2))", 1);
    }

    [Fact]
    public void ArityFacts_NestedCollectorBesideTopLevelCollector_IsDecidedAtEachLevel()
    {
        // The top level holds a group AND a collector; the group's own level holds only the
        // nested collector. Both levels are min 1 / unbounded and min 0 / unbounded
        // respectively — the two decisions are independent.
        var plan = PlanFor("F((*inner), *outer) = inner*, outer", "F");

        AssertTopLevelFacts(plan.Signature, min: 1, max: null, collectingCount: 1);
        Assert.Equal(1, plan.TopLevelPatternList.MinSlotCount);
        Assert.Null(plan.TopLevelPatternList.MaxSlotCount);

        var nested = NestedLevel(plan, 0);
        Assert.Equal(0, nested.MinSlotCount);
        Assert.Null(nested.MaxSlotCount);

        AssertCallRejectedByTopLevelArity("F((*inner), *outer) = inner*, outer\nF()", expectedMinimum: 1, actual: 0);
    }

    // ---------------------------------------------------------------------
    // Nested levels: the rule is per level, never gated on "top level".
    // ---------------------------------------------------------------------

    [Fact]
    public void NestedPlan_GroupContainingCollector_IsUnboundedWhileTheCallableStaysExact()
    {
        var plan = PlanFor("P((x, *r)) = x", "P");

        // The callable itself takes exactly ONE argument: one top-level grouped pattern.
        AssertTopLevelFacts(plan.Signature, min: 1, max: 1, collectingCount: 0);
        Assert.Equal(1, plan.TopLevelPatternList.MinSlotCount);
        Assert.Equal(1, plan.TopLevelPatternList.MaxSlotCount);
        Assert.False(plan.HasTopLevelCollecting);
        Assert.True(plan.HasNestedCollecting);

        // The group's OWN level holds one fixed pattern and one collector.
        var nested = NestedLevel(plan, 0);
        Assert.Equal(1, nested.MinSlotCount);
        Assert.Null(nested.MaxSlotCount);
        Assert.True(nested.HasCollectingAtThisLevel);
        Assert.Equal(1, nested.CollectingCountAtThisLevel);

        Assert.Equal(
            [("P((x, *r))", 1, (int?)1), ("P((x, *r)) > (x, *r)", 1, null)],
            LevelArities(plan));

        // Runtime: one supplied argument that opens to zero nested items reaches the nested
        // minimum, and the structured payload and the rendered message report the same 1.
        var nestedFailure = SourceProvenance.ParseValid("P((x, *r)) = x\nP(())");
        var structured = nestedFailure.ExpectEvaluationError<EvalError.ArityMismatch>();
        Assert.Equal(1, structured.Expected);
        Assert.Equal(0, structured.Actual);
        Assert.Equal(
            "Sequence-value parameter pattern `(x, *r)` expects at least 1 value, but received 0 values.",
            RenderEvaluationError(nestedFailure));

        // ...and one or more nested items bind.
        AssertCallSucceeds("P((x, *r)) = x\nP((7, 8, 9))", 7);
        AssertCallSucceeds("P((x, *r)) = x\nP(5)", 5);
    }

    [Fact]
    public void NestedPlan_DoublyNestedGroup_DecidesEachLevelSeparately()
    {
        // `((x, *r))` is a group holding a group: the middle level has no collector
        // (exactly one pattern), the innermost one does.
        var plan = PlanFor("F(((x, *r))) = x", "F");

        Assert.Equal("F(((x, *r)))", plan.DisplayText);
        Assert.Equal(
            [
                ("F(((x, *r)))", 1, (int?)1),
                ("F(((x, *r))) > (x, *r)", 1, 1),
                ("F(((x, *r))) > (x, *r) > (x, *r)", 1, null),
            ],
            LevelArities(plan));

        var middle = NestedLevel(plan, 0);
        Assert.Equal(1, middle.MinSlotCount);
        Assert.Equal(1, middle.MaxSlotCount);
        Assert.False(middle.HasCollectingAtThisLevel);

        var innermost = Assert.IsType<SequenceValueBindingNode>(Assert.Single(middle.Nodes)).Children;
        Assert.Equal(1, innermost.MinSlotCount);
        Assert.Null(innermost.MaxSlotCount);
        Assert.True(innermost.HasCollectingAtThisLevel);

        // The middle level's exact-one expectation is what the binder enforces.
        var middleFailure = SourceProvenance.ParseValid("F(((x, *r))) = x\nF((1, 2, 3))");
        var structured = middleFailure.ExpectEvaluationError<EvalError.ArityMismatch>();
        Assert.Equal(1, structured.Expected);
        Assert.Equal(3, structured.Actual);
        Assert.Equal(
            "Sequence-value parameter pattern `((x, *r))` expects 1 value, but received 3 values.",
            RenderEvaluationError(middleFailure));

        // One outer item that itself opens reaches the innermost collecting level.
        AssertCallSucceeds("F(((x, *r))) = x\nF([(1, 2, 3)])", 1);
    }

    [Fact]
    public void NestedPlan_LoneNestedCollector_AcceptsAnyNestedSupply()
    {
        var plan = PlanFor("CountSequenceValue((*values)) = values.count", "CountSequenceValue");

        AssertTopLevelFacts(plan.Signature, min: 1, max: 1, collectingCount: 0);
        var nested = NestedLevel(plan, 0);
        Assert.Equal(0, nested.MinSlotCount);
        Assert.Null(nested.MaxSlotCount);

        // The nested level really does accept an empty supply.
        AssertCallSucceeds("CountSequenceValue((*values)) = values.count\nCountSequenceValue(())", 0);
        AssertCallSucceeds("CountSequenceValue((*values)) = values.count\nCountSequenceValue((1, 2, 3))", 3);
    }

    [Fact]
    public void NestedPlan_RecursiveGroups_KeepPerLevelFacts()
    {
        var plan = PlanFor("G(((*history), previous)) = history.count + previous", "G");

        AssertTopLevelFacts(plan.Signature, min: 1, max: 1, collectingCount: 0);
        Assert.Equal(
            [
                ("G(((*history), previous))", 1, (int?)1),
                // The outer group binds `(*history)` and `previous`: two fixed patterns.
                ("G(((*history), previous)) > (*history, previous)", 2, 2),
                ("G(((*history), previous)) > (*history, previous) > (*history)", 0, null),
            ],
            LevelArities(plan));

        AssertCallSucceeds("G(((*history), previous)) = history.count + previous\nG(((1, 2, 3), 4))", 7);
    }

    // ---------------------------------------------------------------------
    // The invariant itself: binder minimum = facts minimum = plan minimum.
    // ---------------------------------------------------------------------

    public static TheoryData<string, string, int, int?> PerLevelShapes()
    {
        // name, declaration, top-level min, top-level max (null = unbounded)
        var data = new TheoryData<string, string, int, int?>
        {
            { "F", "F(x) = x", 1, 1 },
            { "F", "F(x, y) = x", 2, 2 },
            { "F", "F(*r) = r", 0, null },
            { "F", "F(x, *r) = x", 1, null },
            { "F", "F(*r, z) = z", 1, null },
            { "F", "F(x, *r, z) = x", 2, null },
            { "F", "F((x, y)) = x", 1, 1 },
            { "F", "F((x, y), *r) = x", 1, null },
            { "F", "F(*r, (x, y)) = x", 1, null },
            { "F", "F((x, *r)) = x", 1, 1 },
            { "F", "F(((x, *r))) = x", 1, 1 },
            { "F", "F((*inner), *outer) = outer", 1, null },
            { "F", "F((a, b), (c, d)) = a", 2, 2 },
            { "F", "F((a, b), *r, (c, d)) = a", 2, null },
        };
        return data;
    }

    [Theory]
    [MemberData(nameof(PerLevelShapes))]
    public void ArityFacts_MatchTheBinderAndTheBindingPlan(string name, string declaration, int min, int? max)
    {
        var signature = SignatureFor(declaration, name);
        var plan = CallableBindingPlan.FromSignature(signature);

        // 1. The metadata states the claimed arity...
        AssertTopLevelFacts(signature, min, max, plan.TopLevelPatternList.CollectingCountAtThisLevel);

        // 2. ...the plan agrees (FromSignature also fails loudly if it does not)...
        Assert.Equal(min, plan.TopLevelPatternList.MinSlotCount);
        Assert.Equal(max, plan.TopLevelPatternList.MaxSlotCount);
        Assert.Equal(signature.ArityFacts, plan.ArityFacts);

        // 3. ...and the binder accepts exactly those supplied counts. Every supplied slot is
        // the well-shaped `(1, 2)`, so a rejection at any count is a TOP-LEVEL arity
        // decision rather than an incidental nested-shape failure.
        for (var count = 0; count <= (max ?? min) + 2; count++)
        {
            var call = $"{name}({string.Join(", ", Enumerable.Repeat("(1, 2)", count))})";
            var accepted = signature.AcceptsItemCount(count);
            Assert.Equal(accepted, !IsTopLevelArityRejection($"{declaration}\n{call}", out var expected, out var actual));

            if (accepted)
                continue;

            Assert.Equal(min, expected);
            Assert.Equal(count, actual);
        }
    }

    [Fact]
    public void ArityFacts_HostBuiltPatterns_FollowTheSamePerLevelRule()
    {
        // Shapes source syntax does not naturally produce.

        // A captureless group beside a collector: one slot for the group, none for `*r`.
        var capturelessGroupThenCollector = HostSignature(
            "Host",
            new SequenceValueParameterPattern([]),
            new CaptureParameterPattern("r", Kind: ParameterKind.Collecting));
        AssertTopLevelFacts(capturelessGroupThenCollector, min: 1, max: null, collectingCount: 1);
        Assert.Equal(
            ParameterPattern.MinimumSuppliedSlots(capturelessGroupThenCollector.ParameterPatterns),
            capturelessGroupThenCollector.ArityFacts.MinTopLevelArgumentCount);

        // A collector nested two levels down never reaches the outer levels.
        var deeplyNestedCollector = HostSignature(
            "Host",
            new SequenceValueParameterPattern(
                [new SequenceValueParameterPattern([new CaptureParameterPattern("r", Kind: ParameterKind.Collecting)])]));
        AssertTopLevelFacts(deeplyNestedCollector, min: 1, max: 1, collectingCount: 0);
        var deepPlan = CallableBindingPlan.FromSignature(deeplyNestedCollector);
        Assert.Equal(
            [("Host(((*r)))", 1, (int?)1), ("Host(((*r))) > (*r)", 1, 1), ("Host(((*r))) > (*r) > (*r)", 0, null)],
            LevelArities(deepPlan));

        // An empty top-level group list is the degenerate exact-zero level.
        var noPatterns = HostSignature("Host");
        AssertTopLevelFacts(noPatterns, min: 0, max: 0, collectingCount: 0);

        // A lone captureless group is one required slot.
        var capturelessGroup = HostSignature("Host", new SequenceValueParameterPattern([]));
        AssertTopLevelFacts(capturelessGroup, min: 1, max: 1, collectingCount: 0);
    }

    [Fact]
    public void ArityFacts_MultipleCollectingCaptures_StayInvalid()
    {
        // Correcting the arity numbers must not make a malformed signature look legal.
        var multipleCollecting = new CallableSignature(
            "Bad",
            [
                new CallableParameter("a", ParameterKind.Collecting),
                new CallableParameter("b", ParameterKind.Collecting),
            ]);

        Assert.Equal(2, multipleCollecting.ArityFacts.TopLevelCollectingCount);
        Assert.True(multipleCollecting.ArityFacts.HasMultipleTopLevelCollectingCaptures);
        Assert.False(multipleCollecting.HasAtMostOneCollectingParameter);
        Assert.Equal(
            "Callable signature `Bad(*a, *b)` cannot contain more than one collecting parameter.",
            multipleCollecting.ValidateMessage());
        Assert.IsType<EvalError.IllegalInEval>(multipleCollecting.Validate());

        // The binding plan still refuses to represent it.
        var planFailure = Assert.Throws<InvalidOperationException>(() => CallableBindingPlan.FromSignature(multipleCollecting));
        Assert.Equal(
            "Callable binding plans cannot contain more than one collecting capture at the same pattern-list level.",
            planFailure.Message);

        // And so does the binder, whatever count is supplied.
        var doubleCollector = HostSignature(
            "Bad",
            new CaptureParameterPattern("a", Kind: ParameterKind.Collecting),
            new CaptureParameterPattern("b", Kind: ParameterKind.Collecting));
        Assert.NotNull(doubleCollector.ValidateMessage());
    }

    // ---------------------------------------------------------------------
    // Rendering: the message and the structured payload report one minimum.
    // ---------------------------------------------------------------------

    [Theory]
    [InlineData("G((a, b), *rest) = a", "G()", "Callable `G((a, b), *rest)` expects at least 1 argument, but was called with 0 arguments.")]
    [InlineData("H(*rest, (a, b)) = a", "H()", "Callable `H(*rest, (a, b))` expects at least 1 argument, but was called with 0 arguments.")]
    [InlineData("F((*inner), *outer) = outer", "F()", "Callable `F((*inner), *outer)` expects at least 1 argument, but was called with 0 arguments.")]
    [InlineData("F((a, b), *r, (c, d)) = a", "F((1, 2))", "Callable `F((a, b), *r, (c, d))` expects at least 2 arguments, but was called with 1 argument.")]
    public void ArityDiagnostic_GroupWithCollector_RendersTheStructuredMinimum(
        string declaration,
        string call,
        string expectedMessage)
    {
        var source = $"{declaration}\n{call}";
        var provenance = SourceProvenance.ParseValid(source);
        var structured = provenance.ExpectEvaluationError<EvalError.ArityMismatch>();

        Assert.Equal(expectedMessage, RenderEvaluationError(provenance));

        // The rendered minimum is the structured one, which is the facts minimum, which is
        // the binder's own MinimumSuppliedSlots.
        var name = declaration[..declaration.IndexOf('(', StringComparison.Ordinal)];
        var signature = SignatureFor(declaration, name);
        Assert.Equal(signature.ArityFacts.MinTopLevelArgumentCount, structured.Expected);
        Assert.Equal(
            ParameterPattern.MinimumSuppliedSlots(signature.ParameterPatterns),
            structured.Expected);
        Assert.Contains(
            $"at least {structured.Expected}",
            CallableSignatureDiagnostics.FormatExpectedArgumentCount(signature.ArityFacts),
            StringComparison.Ordinal);
    }

    // ---------------------------------------------------------------------
    // Helpers
    // ---------------------------------------------------------------------

    private static string RenderEvaluationError(SourceProvenance provenance)
    {
        var result = provenance.Evaluate();
        if (!result.IsError)
            Assert.Fail($"Expected an evaluation failure but got: {result.Value}");

        return KatLangError.FromEvalError(result.Error).Message;
    }

    private static void AssertCallSucceeds(string source, params double[] expected)
    {
        var result = Evaluator.RunFlat(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root));
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {KatLangError.FromEvalError(result.Error).Message}");

        Assert.Equal(expected.Length, result.Value.Count);
        for (var index = 0; index < expected.Length; index++)
            Assert.Equal(expected[index].ToString(System.Globalization.CultureInfo.InvariantCulture), result.Value[index].ToString());
    }

    private static void AssertCallRejectedByTopLevelArity(string source, int expectedMinimum, int actual)
    {
        Assert.True(
            IsTopLevelArityRejection(source, out var expected, out var actualCount),
            $"Expected a top-level arity rejection for:{Environment.NewLine}{source}");
        Assert.Equal(expectedMinimum, expected);
        Assert.Equal(actual, actualCount);
    }

    /// <summary>
    /// Whether evaluating <paramref name="source"/> fails with a TOP-LEVEL call-arity
    /// rejection — an <see cref="EvalError.ArityMismatch"/> or
    /// <see cref="EvalError.VariadicArityMismatch"/> that is NOT attributed to a nested
    /// sequence-value pattern group (those carry
    /// <see cref="SequenceValueParameterBindingContext"/>, which is the group's own level
    /// and therefore a different decision).
    /// </summary>
    private static bool IsTopLevelArityRejection(string source, out int expected, out int actual)
    {
        expected = -1;
        actual = -1;

        var result = Evaluator.Run(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root));
        if (!result.IsError)
            return false;

        var error = result.Error;
        while (error is EvalError.WithContext context)
        {
            if (context.ErrorContext is SequenceValueParameterBindingContext)
                return false;

            error = context.Inner;
        }

        switch (error)
        {
            case EvalError.ArityMismatch mismatch:
                expected = mismatch.Expected;
                actual = mismatch.Actual;
                return true;
            case EvalError.VariadicArityMismatch variadic:
                expected = variadic.ExpectedMinimum;
                actual = variadic.Actual;
                return true;
            default:
                return false;
        }
    }
}
