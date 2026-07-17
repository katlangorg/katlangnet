using KatLang.Semantics;

namespace KatLang.Tests;

public class CallableSignatureTests
{
    private static CallableSignature SignatureFor(string source, string name, bool allowErrors = false)
    {
        var parseResult = Parser.Parse(source);
        if (!allowErrors)
        {
            Assert.False(
                parseResult.HasErrors,
                string.Join(Environment.NewLine, parseResult.Diagnostics.Select(static diagnostic => diagnostic.Message)));
        }

        var property = parseResult.Root.Properties.Single(property => property.Name == name);
        return CallableSignature.FromAlgorithm(name, property.Value);
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

    private static string FormatEvalError(string source)
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

    [Fact]
    public void FromAlgorithm_ImplicitOnlySignature_MarksParametersImplicit()
    {
        var signature = SignatureFor("Add = x + y", "Add");

        Assert.Equal("Add(x, y)", signature.DisplayText);
        Assert.False(signature.HasExplicitParameterList);
        Assert.Equal(["x", "y"], signature.Parameters.Select(static parameter => parameter.Name).ToList());
        Assert.Equal(
            [CallableParameterSource.Implicit, CallableParameterSource.Implicit],
            signature.Parameters.Select(static parameter => parameter.Source).ToList());
    }

    [Fact]
    public void FromAlgorithm_ExplicitScalarSignature_MarksParametersExplicit()
    {
        var signature = SignatureFor("Add(x, y) = x + y", "Add");

        Assert.Equal("Add(x, y)", signature.DisplayText);
        Assert.True(signature.HasExplicitParameterList);
        Assert.Equal(["x", "y"], signature.Parameters.Select(static parameter => parameter.Name).ToList());
        Assert.Equal(
            [CallableParameterSource.Explicit, CallableParameterSource.Explicit],
            signature.Parameters.Select(static parameter => parameter.Source).ToList());
        Assert.All(signature.Parameters, parameter => Assert.NotNull(parameter.DeclaringPattern));
    }

    [Fact]
    public void ArityFacts_ScalarExplicit_UsesFlatTopLevelSlots()
    {
        var signature = SignatureFor("Add(x, y) = x + y", "Add");
        var facts = signature.ArityFacts;

        Assert.Equal(2, facts.MinTopLevelArgumentCount);
        Assert.Equal(2, facts.MaxTopLevelArgumentCount);
        Assert.False(facts.HasTopLevelVariadic);
        Assert.Equal(0, facts.TopLevelVariadicCount);
        Assert.Equal("Add(x, y)", CallableSignatureDiagnostics.FormatExpectedSignature(signature));
    }

    [Fact]
    public void FromAlgorithm_SequenceValueExplicitSignature_PreservesSequenceValueDisplay()
    {
        var signature = SignatureFor("PairSum((x, y)) = x + y", "PairSum");

        Assert.Equal("PairSum((x, y))", signature.DisplayText);
        Assert.NotEqual("PairSum(x, y)", signature.DisplayText);
        Assert.Equal(["(x, y)"], signature.ParameterPatterns.Select(static pattern => pattern.DisplayName).ToList());
        Assert.Equal(["x", "y"], signature.Parameters.Select(static parameter => parameter.Name).ToList());
        Assert.All(signature.Parameters, parameter => Assert.Equal(CallableParameterSource.Explicit, parameter.Source));
    }

    [Fact]
    public void ArityFacts_SequenceValueExplicit_CountsGroupAsOneTopLevelSlot()
    {
        var signature = SignatureFor("PairSum((x, y)) = x + y", "PairSum");
        var facts = signature.ArityFacts;

        Assert.Equal(1, facts.MinTopLevelArgumentCount);
        Assert.Equal(1, facts.MaxTopLevelArgumentCount);
        Assert.False(facts.HasTopLevelVariadic);
        Assert.Equal("PairSum((x, y))", signature.DisplayText);
    }

    [Fact]
    public void RuntimeArityDiagnostic_SequenceValueExplicit_UsesCallableSignatureDisplay()
    {
        var message = FormatEvalError(
            """
            PairSum((x, y)) = x + y
            PairSum(1, 2)
            """);

        Assert.Contains("PairSum((x, y))", message, StringComparison.Ordinal);
        Assert.DoesNotContain("PairSum(x, y)", message, StringComparison.Ordinal);
    }

    [Fact]
    public void FromAlgorithm_ExplicitSequenceValueSignature_RemainsClosed()
    {
        const string source = "F((x, y)) = x + y + z";
        var parseResult = Parser.Parse(source);
        Assert.True(parseResult.HasErrors);
        Assert.Contains(parseResult.Diagnostics, diagnostic =>
            diagnostic.Severity == DiagnosticSeverity.Error
            && diagnostic.Message.Contains("Explicit parameter lists are closed", StringComparison.Ordinal));

        var property = parseResult.Root.Properties.Single(property => property.Name == "F");
        var signature = CallableSignature.FromAlgorithm("F", property.Value);

        Assert.Equal("F((x, y))", signature.DisplayText);
        Assert.Equal(["x", "y"], signature.Parameters.Select(static parameter => parameter.Name).ToList());
        Assert.DoesNotContain(signature.Parameters, parameter => parameter.Name == "z");
    }

    [Fact]
    public void FromAlgorithm_TopLevelVariadicSignature_PreservesTopLevelVariadicDisplay()
    {
        var signature = SignatureFor("CountValues(values...) = values.count", "CountValues");
        var facts = signature.ArityFacts;

        Assert.Equal("CountValues(values...)", signature.DisplayText);
        Assert.False(signature.HasSequenceValueParameterPattern);
        Assert.Equal(1, signature.TopLevelParameterCount);
        Assert.Equal(1, signature.VariadicParameterCount);
        // Rest-only is the degenerate item-supply case: min 0, unbounded max.
        Assert.Equal(0, facts.MinTopLevelArgumentCount);
        Assert.Null(facts.MaxTopLevelArgumentCount);
        Assert.True(facts.HasTopLevelVariadic);
        var parameter = Assert.Single(signature.Parameters);
        Assert.Equal("values", parameter.Name);
        Assert.Equal("values...", parameter.DisplayName);
    }

    [Fact]
    public void ArityFacts_TopLevelVariadicWithSuffix_IsDeconstructionWithUnboundedMax()
    {
        var signature = SignatureFor("Scale(items..., factor) = items.map{n * factor}", "Scale");
        var facts = signature.ArityFacts;

        // Deconstruction-shaped: `factor` is the one fixed binding and `items...`
        // captures zero or more prefix items, so the arity is min 1, max unbounded.
        Assert.Equal("Scale(items..., factor)", signature.DisplayText);
        Assert.Equal(1, facts.MinTopLevelArgumentCount);
        Assert.Null(facts.MaxTopLevelArgumentCount);
        Assert.True(facts.HasTopLevelVariadic);
        Assert.Equal(1, facts.TopLevelVariadicCount);
    }

    [Fact]
    public void ArityFacts_DeconstructionShapes_ReportFixedMinimumAndUnboundedMax()
    {
        var middleRest = SignatureFor("F(x, y..., z) = x + y.sum + z", "F").ArityFacts;
        Assert.Equal(2, middleRest.MinTopLevelArgumentCount);
        Assert.Null(middleRest.MaxTopLevelArgumentCount);
        Assert.True(middleRest.HasTopLevelVariadic);

        var trailingRest = SignatureFor("F(first, tail...) = first", "F").ArityFacts;
        Assert.Equal(1, trailingRest.MinTopLevelArgumentCount);
        Assert.Null(trailingRest.MaxTopLevelArgumentCount);

        var leadingRest = SignatureFor("F(head..., last) = last", "F").ArityFacts;
        Assert.Equal(1, leadingRest.MinTopLevelArgumentCount);
        Assert.Null(leadingRest.MaxTopLevelArgumentCount);

        // Without a rest the count is exact.
        var noRest = SignatureFor("F(x, y) = x + y", "F").ArityFacts;
        Assert.Equal(2, noRest.MinTopLevelArgumentCount);
        Assert.Equal(2, noRest.MaxTopLevelArgumentCount);
        Assert.False(noRest.HasTopLevelVariadic);

        // A lone rest-only parameter is the degenerate item-supply case: min 0,
        // unbounded max (empty calls are accepted).
        var restOnly = SignatureFor("Sum(values...) = values.sum", "Sum").ArityFacts;
        Assert.Equal(0, restOnly.MinTopLevelArgumentCount);
        Assert.Null(restOnly.MaxTopLevelArgumentCount);
        Assert.True(restOnly.HasTopLevelVariadic);
    }

    [Fact]
    public void FromAlgorithm_SequenceValueVariadicSignature_DoesNotBecomeTopLevelVariadic()
    {
        var signature = SignatureFor("CountSequenceValue((values...)) = values.count", "CountSequenceValue");
        var facts = signature.ArityFacts;

        Assert.Equal("CountSequenceValue((values...))", signature.DisplayText);
        Assert.NotEqual("CountSequenceValue(values...)", signature.DisplayText);
        Assert.True(signature.HasSequenceValueParameterPattern);
        Assert.Equal(1, facts.MinTopLevelArgumentCount);
        Assert.Equal(1, facts.MaxTopLevelArgumentCount);
        Assert.False(facts.HasTopLevelVariadic);
        Assert.Equal(0, facts.TopLevelVariadicCount);
        Assert.Equal(["(values...)"], signature.ParameterPatterns.Select(static pattern => pattern.DisplayName).ToList());
        Assert.Equal(["values..."], signature.Parameters.Select(static parameter => parameter.DisplayName).ToList());
    }

    [Fact]
    public void FromAlgorithm_NestedRecursivePatternSignature_PreservesNestedShape()
    {
        var signature = SignatureFor("G(((history...), previous)) = history.count + previous", "G");
        var facts = signature.ArityFacts;

        Assert.Equal("G(((history...), previous))", signature.DisplayText);
        Assert.True(signature.HasSequenceValueParameterPattern);
        Assert.Equal(1, facts.MinTopLevelArgumentCount);
        Assert.Equal(1, facts.MaxTopLevelArgumentCount);
        Assert.False(facts.HasTopLevelVariadic);
        Assert.Equal(["((history...), previous)"], signature.ParameterPatterns.Select(static pattern => pattern.DisplayName).ToList());
        Assert.Equal(["history...", "previous"], signature.Parameters.Select(static parameter => parameter.DisplayName).ToList());
    }

    [Fact]
    public void ArityFacts_BuiltinCollectionSignatures_AreOrdinaryFixed()
    {
        var map = CallableSignature.FromBuiltin(BuiltinId.map);
        var take = CallableSignature.FromBuiltin(BuiltinId.take);
        var count = CallableSignature.FromBuiltin(BuiltinId.count);

        // Collection builtins are ordinary fixed-arity callables:
        // min = max = parameter count and there is no variadic parameter.
        Assert.Equal("map(collection, mapper)", map.DisplayText);
        Assert.Equal(0, map.VariadicParameterCount);
        Assert.Equal(2, map.ArityFacts.MinTopLevelArgumentCount);
        Assert.Equal(2, map.ArityFacts.MaxTopLevelArgumentCount);
        Assert.False(map.ArityFacts.HasTopLevelVariadic);

        Assert.Equal("take(collection, count)", take.DisplayText);
        Assert.Equal(0, take.VariadicParameterCount);
        Assert.Equal(2, take.ArityFacts.MinTopLevelArgumentCount);
        Assert.Equal(2, take.ArityFacts.MaxTopLevelArgumentCount);
        Assert.False(take.ArityFacts.HasTopLevelVariadic);

        Assert.Equal("count(collection)", count.DisplayText);
        Assert.Equal(0, count.VariadicParameterCount);
        Assert.Equal(1, count.ArityFacts.MinTopLevelArgumentCount);
        Assert.Equal(1, count.ArityFacts.MaxTopLevelArgumentCount);
        Assert.False(count.ArityFacts.HasTopLevelVariadic);
    }

    [Fact]
    public void PropertyInfo_DisplaySignature_UsesCallableSignatureDisplayText()
    {
        const string source = "PairSum((x, y)) = x + y";
        var parseResult = Parser.Parse(source);
        Assert.False(
            parseResult.HasErrors,
            string.Join(Environment.NewLine, parseResult.Diagnostics.Select(static diagnostic => diagnostic.Message)));

        var property = parseResult.Root.Properties.Single(property => property.Name == "PairSum");
        var signature = CallableSignature.FromAlgorithm("PairSum", property.Value);
        var model = SemanticModelBuilder.Build(parseResult);
        var propertyInfo = Assert.Single(model.FindProperties("PairSum"));

        Assert.Equal(signature.DisplayText, propertyInfo.DisplaySignature);
        Assert.Equal(signature.DisplayText, propertyInfo.GetDisplaySignature(PropertyCallStyle.Plain));
    }

    [Fact]
    public void ImplicitResolver_VariadicForwardingBehavior_RemainsUnchanged()
    {
        AssertEval(
            """
            CountItems(items...) = items.count
            Use(values...) = CountItems
            Use((1, 2, 3))
            """,
            3);

        AssertEval(
            """
            CountSequenceValue((items...)) = items.count
            Use(values...) = CountSequenceValue
            Use((1, 2, 3))
            """,
            3);
    }
}
