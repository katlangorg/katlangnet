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
                    if (sequenceMetadata.LeadingSequenceArity.MinCount != runtimeSequence.LeadingMinCount
                        || sequenceMetadata.LeadingSequenceArity.MaxCount != runtimeSequence.LeadingMaxCount)
                    {
                        failures.Add(
                            $"Evaluator sequence metadata for builtin '{builtin.Name}' has leading arity {runtimeSequence.LeadingArityDescription}, but BuiltinRegistry expects {DescribeLeadingArity(sequenceMetadata.LeadingSequenceArity)}.");
                    }

                    var expectedTrailingLabels = sequenceMetadata.TrailingArgs
                        .Select(static descriptor => descriptor.Label)
                        .ToArray();
                    if (!expectedTrailingLabels.SequenceEqual(runtimeSequence.TrailingParameterLabels, StringComparer.Ordinal))
                    {
                        failures.Add(
                            $"Evaluator sequence metadata for builtin '{builtin.Name}' has trailing labels {FormatParameterList(runtimeSequence.TrailingParameterLabels)}, but BuiltinRegistry expects {FormatParameterList(expectedTrailingLabels)}.");
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

            if (!builtin.PlainParameterNames.SequenceEqual(semanticPlain, StringComparer.Ordinal))
            {
                failures.Add(
                    $"Semantic plain-call metadata for builtin '{builtin.Name}' does not match BuiltinRegistry. Expected: {FormatParameterList(builtin.PlainParameterNames)}. Actual: {FormatParameterList(semanticPlain)}.");
            }

            if (!builtin.DotParameterNames.SequenceEqual(semanticDot, StringComparer.Ordinal))
            {
                failures.Add(
                    $"Semantic dot-call metadata for builtin '{builtin.Name}' does not match BuiltinRegistry. Expected: {FormatParameterList(builtin.DotParameterNames)}. Actual: {FormatParameterList(semanticDot)}.");
            }
        }

        AssertNoFailures(failures);
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
            if (runtimeMath[name] != expectedMath[name])
            {
                failures.Add(
                    $"Runtime Math member '{name}' has arity {runtimeMath[name]}, but BuiltinRegistry expects {expectedMath[name]}.");
            }
        }

        foreach (var name in expectedMath.Keys.Intersect(semanticMath.Keys, StringComparer.Ordinal).OrderBy(static name => name, StringComparer.Ordinal))
        {
            if (semanticMath[name] != expectedMath[name])
            {
                failures.Add(
                    $"Semantic Math member '{name}' has arity {semanticMath[name]}, but BuiltinRegistry expects {expectedMath[name]}.");
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

    private static SortedSet<string> ToSortedSet(IEnumerable<string> names)
        => new(names, StringComparer.Ordinal);

    private static string FormatParameterList(IEnumerable<string> parameters)
    {
        var items = parameters.ToArray();
        return items.Length == 0 ? "(none)" : string.Join(", ", items);
    }

    private static string DescribeLeadingArity(SequenceBuiltinLeadingArity arity)
        => arity.MaxCount is { } maxCount ? $"{arity.MinCount}..{maxCount}" : $"{arity.MinCount}+";

    private static (Algorithm.User Root, IReadOnlyList<Diagnostic> Diagnostics) DetectSingleResolve(
        string name,
        IReadOnlyList<Expr>? opens = null)
    {
        var root = new Algorithm.User(
            Parent: null,
            Params: [],
            Opens: opens ?? Array.Empty<Expr>(),
            Properties: [],
            Output: [new Expr.Resolve(name)])
        {
            IsParametrized = true,
        };

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

            return parameters.Select(static parameter => parameter.Name).ToArray();
        }

        public static bool TryGetRuntimeSequenceSignature(BuiltinId builtin, out RuntimeSequenceSignature signature)
        {
            var metadata = RuntimeGetSequenceBuiltinMetadataMethod.Invoke(null, [builtin]);
            if (metadata is null)
            {
                signature = default;
                return false;
            }

            var leadingArity = GetPropertyValue(metadata, "LeadingSequenceArity");
            var minCount = GetIntPropertyValue(leadingArity, "MinCount");
            var maxCount = GetNullableIntPropertyValue(leadingArity, "MaxCount");
            var trailingArgs = GetEnumerablePropertyValues(metadata, "TrailingArgs")
                .Select(static trailingArg => GetStringPropertyValue(trailingArg, "Label"))
                .ToArray();

            signature = new RuntimeSequenceSignature(minCount, maxCount, trailingArgs);
            return true;
        }

        public static bool RuntimeBuiltinAcceptsArity(BuiltinId builtin, int argumentCount)
            => InvokeStatic<bool>(RuntimeBuiltinAcceptsArityMethod, builtin, argumentCount);

        public static IReadOnlyDictionary<string, int> RuntimeMathMembers()
            => GetAlgorithmPropertyArities(GetUserAlgorithmStaticField(typeof(Evaluator), "MathAlgorithm"));

        public static IReadOnlyDictionary<string, int> SemanticMathMembers()
            => GetAlgorithmPropertyArities(GetUserAlgorithmStaticField(SemanticBuilderType, "MathAlgorithm"));

        private static IReadOnlyList<string> SemanticPreludePropertyNames()
        {
            var preludeScope = GetStaticFieldValue(SemanticBuilderType, "PreludeScope");
            var properties = GetPropertyValue(preludeScope, "Properties");
            return GetStringEnumerable(properties, "Keys")
                .OrderBy(static name => name, StringComparer.Ordinal)
                .ToArray();
        }

        private static IReadOnlyDictionary<string, int> GetAlgorithmPropertyArities(Algorithm.User algorithm)
        {
            var arities = new SortedDictionary<string, int>(StringComparer.Ordinal);
            foreach (var property in algorithm.Properties)
            {
                if (property.Value is not Algorithm.User user)
                    throw new InvalidOperationException($"Expected '{property.Name}' to be backed by an Algorithm.User for parity inspection.");

                arities[property.Name] = user.Params.Count;
            }

            return arities;
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

        private static int GetIntPropertyValue(object instance, string propertyName)
            => Convert.ToInt32(GetPropertyValue(instance, propertyName));

        private static int? GetNullableIntPropertyValue(object instance, string propertyName)
        {
            var value = instance.GetType().GetProperty(propertyName, InstanceAny)?.GetValue(instance);
            return value is null ? null : Convert.ToInt32(value);
        }

        private static string GetStringPropertyValue(object instance, string propertyName)
            => (string)GetPropertyValue(instance, propertyName);
    }

    private readonly record struct RuntimeSequenceSignature(
        int LeadingMinCount,
        int? LeadingMaxCount,
        IReadOnlyList<string> TrailingParameterLabels)
    {
        public string LeadingArityDescription
            => LeadingMaxCount is { } maxCount ? $"{LeadingMinCount}..{maxCount}" : $"{LeadingMinCount}+";
    }
}