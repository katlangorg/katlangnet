using System.Collections;
using System.Reflection;
using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// Keeps evaluator, semantic-model, and parameter-detector wiring aligned with
/// the canonical internal <see cref="BuiltinRegistry"/>.
/// </summary>
public class BuiltinRegistryParityTests
{
    [Fact]
    public void RegistryPreludeInventory_StaysAlignedAcrossRuntimeAndSemantics()
    {
        AssertSetParity(
            BuiltinRegistry.BuiltinNames,
            BuiltinRegistryParitySnapshot.RuntimePreludeBuiltinNames(),
            "Builtins present in BuiltinRegistry but missing from runtime prelude",
            "Builtins exposed by the runtime prelude but missing from BuiltinRegistry");

        AssertSetParity(
            BuiltinRegistry.BuiltinNames,
            BuiltinRegistryParitySnapshot.SemanticPreludeBuiltinNames(),
            "Builtins present in BuiltinRegistry but missing from semantic prelude",
            "Builtins exposed by the semantic prelude but missing from BuiltinRegistry");

        AssertSetParity(
            BuiltinRegistry.RuntimePreludeExtraNames,
            BuiltinRegistryParitySnapshot.RuntimePreludeExtraNames(),
            "Expected runtime-prelude non-builtin names are missing",
            "Unexpected non-builtin names exposed by runtime prelude");

        AssertSetParity(
            BuiltinRegistry.SemanticPreludeExtraNames,
            BuiltinRegistryParitySnapshot.SemanticPreludeExtraNames(),
            "Expected semantic-prelude non-builtin names are missing",
            "Unexpected non-builtin names exposed by semantic prelude");
    }

    [Fact]
    public void RegistrySequenceMetadata_StaysAlignedWithEvaluatorDispatch()
    {
        var failures = new List<string>();

        foreach (var builtin in BuiltinRegistry.AllBuiltins)
        {
            var hasRuntimeMetadata = BuiltinRegistryParitySnapshot.TryGetRuntimeSequenceSignature(builtin.Id, out var runtimeSequence);

            if (builtin.SequenceMetadata is { } sequenceMetadata)
            {
                if (!hasRuntimeMetadata)
                {
                    failures.Add($"Evaluator sequence metadata is missing builtin '{builtin.Name}'.");
                }
                else
                {
                    var expectedSuffixNames = sequenceMetadata.SuffixArgs
                        .Select(static descriptor => descriptor.Name)
                        .ToArray();
                    if (!expectedSuffixNames.SequenceEqual(runtimeSequence.SuffixParameterNames, StringComparer.Ordinal))
                    {
                        failures.Add(
                            $"Evaluator sequence metadata for builtin '{builtin.Name}' has suffix names {FormatParameterList(runtimeSequence.SuffixParameterNames)}, but BuiltinRegistry expects {FormatParameterList(expectedSuffixNames)}.");
                    }
                }
            }
            else if (hasRuntimeMetadata)
            {
                failures.Add($"Evaluator unexpectedly exposes sequence metadata for fixed-arity builtin '{builtin.Name}'.");
            }

            foreach (var argumentCount in Enumerable.Range(0, 16))
            {
                var expected = builtin.AcceptsArity(argumentCount);
                var actual = BuiltinRegistryParitySnapshot.RuntimeBuiltinAcceptsArity(builtin.Id, argumentCount);
                if (actual != expected)
                {
                    failures.Add(
                        $"Evaluator arity acceptance for builtin '{builtin.Name}' at {argumentCount} argument(s) was {actual}, but BuiltinRegistry expects {expected}.");
                }
            }
        }

        AssertNoFailures(failures);
    }

    [Fact]
    public void RegistryBuiltinMetadata_DrivesSemanticBuiltinSignatures()
    {
        var failures = new List<string>();

        foreach (var builtin in BuiltinRegistry.AllBuiltins)
        {
            var semanticPlain = BuiltinRegistryParitySnapshot.SemanticBuiltinParameterNames(builtin.Id, PropertyCallStyle.Plain);
            var semanticDot = BuiltinRegistryParitySnapshot.SemanticBuiltinParameterNames(builtin.Id, PropertyCallStyle.Dot);
            var expectedPlain = builtin.ToolingPlainSignature.Parameters
                .Select(static parameter => parameter.DisplayName)
                .ToArray();
            var expectedDot = builtin.ToolingDotSignature.Parameters
                .Select(static parameter => parameter.DisplayName)
                .ToArray();

            if (!expectedPlain.SequenceEqual(semanticPlain, StringComparer.Ordinal))
            {
                failures.Add(
                    $"Semantic plain-call metadata for builtin '{builtin.Name}' does not match BuiltinRegistry's tooling surface. Expected: {FormatParameterList(expectedPlain)}. Actual: {FormatParameterList(semanticPlain)}.");
            }

            if (!expectedDot.SequenceEqual(semanticDot, StringComparer.Ordinal))
            {
                failures.Add(
                    $"Semantic dot-call metadata for builtin '{builtin.Name}' does not match BuiltinRegistry's tooling surface. Expected: {FormatParameterList(expectedDot)}. Actual: {FormatParameterList(semanticDot)}.");
            }
        }

        AssertNoFailures(failures);
    }

    [Fact]
    public void RegistryBuiltinCallableSignatures_ValidateSuccessfully()
    {
        var failures = new List<string>();

        foreach (var builtin in BuiltinRegistry.AllBuiltins)
        {
            AddValidationFailure(failures, builtin.PlainSignature);
            AddValidationFailure(failures, builtin.DotSignature);
            AddValidationFailure(failures, builtin.ToolingPlainSignature);
            AddValidationFailure(failures, builtin.ToolingDotSignature);
        }

        AssertNoFailures(failures);
    }

    [Fact]
    public void RegistryBuiltinCallableParameterNames_AreIdentifierLike()
    {
        var failures = new List<string>();

        foreach (var builtin in BuiltinRegistry.AllBuiltins)
        {
            foreach (var parameter in builtin.PlainParameters.Concat(builtin.DotParameters))
            {
                if (!IsIdentifierLike(parameter.Name))
                {
                    failures.Add(
                        $"Builtin '{builtin.Name}' has non-identifier callable parameter name '{parameter.Name}'.");
                }
            }
        }

        AssertNoFailures(failures);
    }

    [Fact]
    public void CallableSignatureValidation_RejectsInvalidMetadata()
    {
        var multipleCollecting = new CallableSignature(
            "Bad",
            [
                new CallableParameter("a", ParameterKind.Collecting),
                new CallableParameter("b", ParameterKind.Collecting),
            ]);
        Assert.Equal(2, multipleCollecting.CollectingParameterCount);
        Assert.False(multipleCollecting.HasAtMostOneCollectingParameter);
        AssertValidationReason(
            multipleCollecting,
            "Callable signature `Bad(*a, *b)` cannot contain more than one collecting parameter.");

        AssertValidationReason(
            new CallableSignature("Bad", [new CallableParameter("")]),
            "Callable signature `Bad` contains an empty parameter name.");

        AssertValidationReason(
            new CallableSignature("Bad", [new CallableParameter("initial accumulator")]),
            "Callable signature `Bad` contains invalid parameter name `initial accumulator`.");

        AssertValidationReason(
            new CallableSignature("Bad", [new CallableParameter("x"), new CallableParameter("x")]),
            "Callable signature `Bad` contains duplicate parameter name `x`.");
    }

    [Fact]
    public void RegistryCollectionBuiltinSignatures_DisplayExpectedNames()
    {
        var expected = ExpectedCollectionBuiltins();
        Assert.Equal(
            expected.Keys.OrderBy(static id => id.ToString(), StringComparer.Ordinal).ToArray(),
            BuiltinRegistry.AllBuiltins
                .Where(static builtin => builtin.SequenceMetadata is not null)
                .Select(static builtin => builtin.Id)
                .OrderBy(static id => id.ToString(), StringComparer.Ordinal)
                .ToArray());

        foreach (var (builtinId, expectation) in expected)
        {
            var builtin = BuiltinRegistry.GetBuiltin(builtinId);

            Assert.Equal(expectation.PlainSignatureDisplay, builtin.PlainSignature.DisplayText);
            Assert.Equal(expectation.DotParameterNames, builtin.PlainParameters.Skip(1).Select(static parameter => parameter.Name).ToArray());
            // Fixed collection-object model: an ordinary fixed `collection`
            // parameter leads, followed by the fixed control parameters.
            Assert.Equal("collection", builtin.PlainParameters[0].Name);
            Assert.All(builtin.PlainParameters, parameter => Assert.Equal(CallableParameterSource.Builtin, parameter.Source));
            Assert.All(builtin.PlainParameters, parameter => Assert.Equal(ParameterKind.Normal, parameter.Kind));
        }
    }

    [Fact]
    public void RegistryCollectionBuiltinDotParameters_ExposeOnlyControlParameters()
    {
        var expected = ExpectedCollectionBuiltins();

        foreach (var (builtinId, expectation) in expected)
        {
            var builtin = BuiltinRegistry.GetBuiltin(builtinId);
            var metadata = builtin.SequenceMetadata!.Value;

            Assert.Equal(expectation.DotParameterNames, builtin.DotParameterNames);
            Assert.Equal(expectation.DotParameterNames, builtin.DotParameters.Select(static parameter => parameter.Name).ToArray());
            Assert.Equal(expectation.DotParameterNames, metadata.SuffixArgs.Select(static descriptor => descriptor.Name).ToArray());
            Assert.All(builtin.DotParameters, parameter => Assert.Equal(CallableParameterSource.Builtin, parameter.Source));
            Assert.All(builtin.DotParameters, parameter => Assert.Equal(ParameterKind.Normal, parameter.Kind));
        }
    }

    [Fact]
    public void CollectionBuiltinPlan_IsFlatFixedAndRoundTripsControlMetadata()
    {
        foreach (var builtin in BuiltinRegistry.AllBuiltins.Where(static builtin => builtin.SequenceMetadata is not null))
        {
            var metadata = builtin.SequenceMetadata!.Value;
            var plan = CallableBindingPlan.FromSignature(builtin.PlainSignature);

            // Collection builtins bind like every other fixed callable: a flat
            // fixed layout (`collection` + controls), never a variadic one.
            Assert.False(plan.TryGetFlatCollectingLayout(out _, out _, out _));
            Assert.True(plan.TryGetFlatFixedLayout(out var captures));
            Assert.Equal("collection", captures[0].Name);

            var controlNames = captures.Skip(1).Select(static capture => capture.Name).ToArray();
            Assert.Equal(metadata.SuffixArgs.Select(static descriptor => descriptor.Name).ToArray(), controlNames);
            Assert.Equal(builtin.DotParameters.Select(static parameter => parameter.Name).ToArray(), controlNames);
            Assert.All(captures, capture => Assert.Equal(ParameterKind.Normal, capture.Kind));
            Assert.All(captures, capture => Assert.Equal(CallableParameterSource.Builtin, capture.Source));
        }
    }

    [Fact]
    public void RegistryBuiltinCallableSignature_ExposesKnownOwnerMemberMetadataOnly()
    {
        Assert.True(BuiltinRegistry.TryGetBuiltinCallableSignature("Math", "Round", out var roundSignature));
        Assert.Equal("Round(value, digits)", roundSignature!.DisplayText);
        Assert.Equal(["value", "digits"], roundSignature.ParameterNames);

        Assert.True(BuiltinRegistry.TryGetBuiltinCallableSignature("Math", "Abs", out var absSignature));
        Assert.Equal("Abs(x)", absSignature!.DisplayText);
        Assert.Equal(["x"], absSignature.ParameterNames);

        // Atan2 follows the conventional atan2(y, x) argument order (the runtime
        // forwards the first argument as y), so its signature must not fall back
        // to the default binary names (x, y).
        Assert.True(BuiltinRegistry.TryGetBuiltinCallableSignature("Math", "Atan2", out var atan2Signature));
        Assert.Equal("Atan2(y, x)", atan2Signature!.DisplayText);
        Assert.Equal(["y", "x"], atan2Signature.ParameterNames);

        Assert.True(BuiltinRegistry.TryGetBuiltinCallableSignature("Math", "Random", out var randomSignature));
        Assert.Equal("Random(start, end)", randomSignature!.DisplayText);
        Assert.Equal(["start", "end"], randomSignature.ParameterNames);

        Assert.True(BuiltinRegistry.TryGetBuiltinCallableSignature("Math", "RandomInt", out var randomIntSignature));
        Assert.Equal("RandomInt(start, end)", randomIntSignature!.DisplayText);
        Assert.Equal(["start", "end"], randomIntSignature.ParameterNames);

        Assert.False(BuiltinRegistry.TryGetBuiltinCallableSignature("Math", "Pi", out var constantSignature));
        Assert.Null(constantSignature);

        Assert.False(BuiltinRegistry.TryGetBuiltinCallableSignature("Other", "Round", out var unknownOwnerSignature));
        Assert.Null(unknownOwnerSignature);
    }

    [Fact]
    public void RegistryMathInventory_StaysAlignedAcrossRuntimeAndSemantics()
    {
        var expectedMath = BuiltinRegistry.MathMembers.ToDictionary(
            static member => member.Name,
            static member => member.Arity,
            StringComparer.Ordinal);
        var runtimeMath = BuiltinRegistryParitySnapshot.RuntimeMathMembers();
        var semanticMath = BuiltinRegistryParitySnapshot.SemanticMathMembers();

        AssertSetParity(
            expectedMath.Keys,
            runtimeMath.Keys,
            "Math members present in BuiltinRegistry but missing from the runtime prelude",
            "Math members exposed by the runtime prelude but missing from BuiltinRegistry");

        AssertSetParity(
            expectedMath.Keys,
            semanticMath.Keys,
            "Math members present in BuiltinRegistry but missing from the semantic model",
            "Math members exposed by the semantic model but missing from BuiltinRegistry");

        var failures = new List<string>();
        foreach (var name in expectedMath.Keys.Intersect(runtimeMath.Keys, StringComparer.Ordinal).OrderBy(static name => name, StringComparer.Ordinal))
        {
            if (runtimeMath[name].Count != expectedMath[name])
            {
                failures.Add(
                    $"Runtime Math member '{name}' has arity {runtimeMath[name].Count}, but BuiltinRegistry expects {expectedMath[name]}.");
            }
        }

        foreach (var name in expectedMath.Keys.Intersect(semanticMath.Keys, StringComparer.Ordinal).OrderBy(static name => name, StringComparer.Ordinal))
        {
            if (semanticMath[name].Count != expectedMath[name])
            {
                failures.Add(
                    $"Semantic Math member '{name}' has arity {semanticMath[name].Count}, but BuiltinRegistry expects {expectedMath[name]}.");
            }
        }

        // Parameter names are runtime binding metadata (NativeCall resolves them
        // positionally), so the runtime prelude, the semantic prelude, and the
        // public callable-signature metadata must agree on the exact name order.
        foreach (var name in runtimeMath.Keys.Intersect(semanticMath.Keys, StringComparer.Ordinal).OrderBy(static name => name, StringComparer.Ordinal))
        {
            if (!runtimeMath[name].SequenceEqual(semanticMath[name], StringComparer.Ordinal))
            {
                failures.Add(
                    $"Math member '{name}' binds runtime parameters ({string.Join(", ", runtimeMath[name])}), but the semantic model exposes ({string.Join(", ", semanticMath[name])}).");
            }

            if (BuiltinRegistry.TryGetBuiltinCallableSignature("Math", name, out var signature)
                && !signature!.ParameterNames.SequenceEqual(runtimeMath[name], StringComparer.Ordinal))
            {
                failures.Add(
                    $"Math member '{name}' reports signature parameters ({string.Join(", ", signature.ParameterNames)}), but binds runtime parameters ({string.Join(", ", runtimeMath[name])}).");
            }
        }

        AssertNoFailures(failures);
    }

    [Fact]
    public void RegistryPreludeNames_AreExcludedByParameterDetector()
    {
        foreach (var name in BuiltinRegistry.ParameterDetectorPreludeNames)
        {
            var (root, diagnostics) = DetectSingleResolve(name);

            Assert.Empty(diagnostics);
            Assert.Empty(root.Params);

            var resolve = Assert.IsType<Expr.Resolve>(Assert.Single(root.Output));
            Assert.Equal(name, resolve.Name);
        }
    }

    [Fact]
    public void RegistryMathMembers_AreExcludedByParameterDetector_WhenMathIsOpened()
    {
        foreach (var name in BuiltinRegistry.MathMemberNames)
        {
            var (root, diagnostics) = DetectSingleResolve(name, opens: [new Expr.Resolve("Math")]);

            Assert.Empty(diagnostics);
            Assert.Empty(root.Params);

            var resolve = Assert.IsType<Expr.Resolve>(Assert.Single(root.Output));
            Assert.Equal(name, resolve.Name);
        }
    }

    private static void AssertSetParity(
        IEnumerable<string> expected,
        IEnumerable<string> actual,
        string missingMessage,
        string extraMessage)
    {
        var expectedSet = ToSortedSet(expected);
        var actualSet = ToSortedSet(actual);

        var missing = expectedSet.Where(name => !actualSet.Contains(name)).ToArray();
        var extra = actualSet.Where(name => !expectedSet.Contains(name)).ToArray();

        if (missing.Length == 0 && extra.Length == 0)
            return;

        var failures = new List<string>();
        if (missing.Length > 0)
            failures.Add($"{missingMessage}: {string.Join(", ", missing)}");
        if (extra.Length > 0)
            failures.Add($"{extraMessage}: {string.Join(", ", extra)}");

        Assert.Fail(string.Join(Environment.NewLine, failures));
    }

    private static void AssertNoFailures(IReadOnlyList<string> failures)
    {
        if (failures.Count == 0)
            return;

        Assert.Fail(string.Join(Environment.NewLine, failures));
    }

    private static void AddValidationFailure(ICollection<string> failures, CallableSignature signature)
    {
        if (signature.Validate() is EvalError.IllegalInEval error)
            failures.Add(error.Reason);
    }

    private static void AssertValidationReason(CallableSignature signature, string expectedReason)
    {
        var error = Assert.IsType<EvalError.IllegalInEval>(signature.Validate());
        Assert.Equal(expectedReason, error.Reason);
    }

    private static SortedSet<string> ToSortedSet(IEnumerable<string> names)
        => new(names, StringComparer.Ordinal);

    private static string FormatParameterList(IEnumerable<string> parameters)
    {
        var items = parameters.ToArray();
        return items.Length == 0 ? "(none)" : string.Join(", ", items);
    }

    private static IReadOnlyDictionary<BuiltinId, CollectionBuiltinExpectation> ExpectedCollectionBuiltins()
        => new Dictionary<BuiltinId, CollectionBuiltinExpectation>
        {
            [BuiltinId.map] = new("map(collection, mapper)", ["mapper"]),
            [BuiltinId.filter] = new("filter(collection, predicate)", ["predicate"]),
            [BuiltinId.reduce] = new("reduce(collection, reducer, initial)", ["reducer", "initial"]),
            [BuiltinId.take] = new("take(collection, count)", ["count"]),
            [BuiltinId.skip] = new("skip(collection, count)", ["count"]),
            [BuiltinId.contains] = new("contains(collection, item)", ["item"]),
            [BuiltinId.count] = new("count(collection)", []),
            [BuiltinId.sum] = new("sum(collection)", []),
            [BuiltinId.min] = new("min(collection)", []),
            [BuiltinId.max] = new("max(collection)", []),
            [BuiltinId.avg] = new("avg(collection)", []),
            [BuiltinId.first] = new("first(collection)", []),
            [BuiltinId.last] = new("last(collection)", []),
            [BuiltinId.order] = new("order(collection)", []),
            [BuiltinId.orderDesc] = new("orderDesc(collection)", []),
            [BuiltinId.distinct] = new("distinct(collection)", []),
        };

    private static bool IsIdentifierLike(string name)
    {
        if (name.Length == 0 || (!char.IsLetter(name[0]) && name[0] != '_'))
            return false;

        return name.Skip(1).All(static c => char.IsLetterOrDigit(c) || c == '_');
    }

    private static (Algorithm.User Root, IReadOnlyList<Diagnostic> Diagnostics) DetectSingleResolve(
        string name,
        IReadOnlyList<Expr>? opens = null)
    {
        var root = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: opens ?? Array.Empty<Expr>(),
            Properties: [],
            Output: [new Expr.Resolve(name)]);

        var (processed, diagnostics) = ParameterDetector.Detect(root);
        return (Assert.IsType<Algorithm.User>(processed), diagnostics);
    }

    private static class BuiltinRegistryParitySnapshot
    {
        private static readonly BindingFlags StaticNonPublic = BindingFlags.Static | BindingFlags.NonPublic;
        private static readonly BindingFlags InstanceAny = BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic;

        private static readonly Type SemanticBuilderType = typeof(SemanticModelBuilder).GetNestedType("Builder", BindingFlags.NonPublic)
            ?? throw new InvalidOperationException("SemanticModelBuilder.Builder was not found.");

        private static readonly MethodInfo SemanticCreateBuiltinParametersMethod = RequireMethod(
            SemanticBuilderType,
            "CreateBuiltinParameters",
            StaticNonPublic);

        private static readonly MethodInfo RuntimeGetSequenceBuiltinMetadataMethod = RequireMethod(
            typeof(Evaluator),
            "GetSequenceBuiltinMetadata",
            StaticNonPublic);

        private static readonly MethodInfo RuntimeBuiltinAcceptsArityMethod = RequireMethod(
            typeof(Evaluator),
            "BuiltinAcceptsArity",
            StaticNonPublic);

        public static IReadOnlyList<string> RuntimePreludeBuiltinNames()
            => GetUserAlgorithmStaticField(typeof(Evaluator), "PreludeAlg")
                .Properties
                .Where(static property => property.Value is Algorithm.Builtin)
                .Select(static property => property.Name)
                .OrderBy(static name => name, StringComparer.Ordinal)
                .ToArray();

        public static IReadOnlyList<string> RuntimePreludeExtraNames()
            => GetUserAlgorithmStaticField(typeof(Evaluator), "PreludeAlg")
                .Properties
                .Where(static property => property.Value is not Algorithm.Builtin)
                .Select(static property => property.Name)
                .OrderBy(static name => name, StringComparer.Ordinal)
                .ToArray();

        public static IReadOnlyList<string> SemanticPreludeBuiltinNames()
            => SemanticPreludePropertyNames()
                .Where(static name => Enum.TryParse<BuiltinId>(name, ignoreCase: false, out _))
                .OrderBy(static name => name, StringComparer.Ordinal)
                .ToArray();

        public static IReadOnlyList<string> SemanticPreludeExtraNames()
            => SemanticPreludePropertyNames()
                .Where(static name => !Enum.TryParse<BuiltinId>(name, ignoreCase: false, out _))
                .OrderBy(static name => name, StringComparer.Ordinal)
                .ToArray();

        public static IReadOnlyList<string> SemanticBuiltinParameterNames(BuiltinId builtin, PropertyCallStyle callStyle)
        {
            var parameters = InvokeStatic<IReadOnlyList<PropertyParameterInfo>>(
                SemanticCreateBuiltinParametersMethod,
                builtin.ToString(),
                new Algorithm.Builtin(builtin),
                callStyle);

            return parameters.Select(static parameter => parameter.DisplayName).ToArray();
        }

        public static bool TryGetRuntimeSequenceSignature(BuiltinId builtin, out RuntimeSequenceSignature signature)
        {
            var metadata = RuntimeGetSequenceBuiltinMetadataMethod.Invoke(null, [builtin]);
            if (metadata is null)
            {
                signature = default;
                return false;
            }

            var suffixArgs = GetEnumerablePropertyValues(metadata, "SuffixArgs")
                .Select(static suffixArg => GetStringPropertyValue(suffixArg, "Name"))
                .ToArray();

            signature = new RuntimeSequenceSignature(suffixArgs);
            return true;
        }

        public static bool RuntimeBuiltinAcceptsArity(BuiltinId builtin, int argumentCount)
            => InvokeStatic<bool>(RuntimeBuiltinAcceptsArityMethod, builtin, argumentCount);

        public static IReadOnlyDictionary<string, IReadOnlyList<string>> RuntimeMathMembers()
            => GetAlgorithmPropertyParameters(GetUserAlgorithmStaticField(typeof(Evaluator), "MathAlgorithm"));

        public static IReadOnlyDictionary<string, IReadOnlyList<string>> SemanticMathMembers()
            => GetAlgorithmPropertyParameters(GetUserAlgorithmStaticField(SemanticBuilderType, "MathAlgorithm"));

        private static IReadOnlyList<string> SemanticPreludePropertyNames()
        {
            var preludeScope = GetStaticFieldValue(SemanticBuilderType, "PreludeScope");
            var properties = GetPropertyValue(preludeScope, "Properties");
            return GetStringEnumerable(properties, "Keys")
                .OrderBy(static name => name, StringComparer.Ordinal)
                .ToArray();
        }

        private static IReadOnlyDictionary<string, IReadOnlyList<string>> GetAlgorithmPropertyParameters(Algorithm.User algorithm)
        {
            var parameters = new SortedDictionary<string, IReadOnlyList<string>>(StringComparer.Ordinal);
            foreach (var property in algorithm.Properties)
            {
                if (property.Value is not Algorithm.User user)
                    throw new InvalidOperationException($"Expected '{property.Name}' to be backed by an Algorithm.User for parity inspection.");

                parameters[property.Name] = user.Params;
            }

            return parameters;
        }

        private static Algorithm.User GetUserAlgorithmStaticField(Type type, string fieldName)
        {
            var value = GetStaticFieldValue(type, fieldName);
            return value as Algorithm.User
                ?? throw new InvalidOperationException($"Expected {type.FullName}.{fieldName} to be an Algorithm.User.");
        }

        private static object GetStaticFieldValue(Type type, string fieldName)
        {
            var field = RequireField(type, fieldName, StaticNonPublic);
            return field.GetValue(null)
                ?? throw new InvalidOperationException($"{type.FullName}.{fieldName} returned null.");
        }

        private static T InvokeStatic<T>(MethodInfo method, params object?[] args)
        {
            var result = method.Invoke(null, args);
            if (result is null)
                throw new InvalidOperationException($"{method.DeclaringType?.FullName}.{method.Name} returned null.");

            return (T)result;
        }

        private static FieldInfo RequireField(Type type, string name, BindingFlags bindingFlags)
            => type.GetField(name, bindingFlags)
                ?? throw new InvalidOperationException($"Field {type.FullName}.{name} was not found.");

        private static MethodInfo RequireMethod(Type type, string name, BindingFlags bindingFlags)
            => type.GetMethod(name, bindingFlags)
                ?? throw new InvalidOperationException($"Method {type.FullName}.{name} was not found.");

        private static object GetPropertyValue(object instance, string propertyName)
        {
            var property = instance.GetType().GetProperty(propertyName, InstanceAny)
                ?? throw new InvalidOperationException($"Property {instance.GetType().FullName}.{propertyName} was not found.");

            return property.GetValue(instance)
                ?? throw new InvalidOperationException($"Property {instance.GetType().FullName}.{propertyName} returned null.");
        }

        private static IReadOnlyList<object> GetEnumerablePropertyValues(object instance, string propertyName)
            => ((IEnumerable)GetPropertyValue(instance, propertyName)).Cast<object>().ToArray();

        private static IReadOnlyList<string> GetStringEnumerable(object instance, string propertyName)
            => ((IEnumerable)GetPropertyValue(instance, propertyName)).Cast<string>().ToArray();

        private static string GetStringPropertyValue(object instance, string propertyName)
            => (string)GetPropertyValue(instance, propertyName);
    }

    private readonly record struct RuntimeSequenceSignature(
        IReadOnlyList<string> SuffixParameterNames);

    private readonly record struct CollectionBuiltinExpectation(
        string PlainSignatureDisplay,
        IReadOnlyList<string> DotParameterNames);
}
