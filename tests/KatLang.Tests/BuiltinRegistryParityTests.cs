using System.Collections;
using System.Reflection;
using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// Keeps the duplicated builtin registries in the C# front-end/runtime stack aligned
/// until registration is centralized. These tests compare the actual runtime,
/// semantic-model, and ParameterDetector sources so drift is caught early.
/// </summary>
public class BuiltinRegistryParityTests
{
    [Fact]
    public void BuiltinInventory_StaysAlignedAcrossRuntimeSemanticsAndParameterDetection()
    {
        var builtinNames = BuiltinRegistryParitySnapshot.CanonicalBuiltinNames();

        AssertSetParity(
            builtinNames,
            BuiltinRegistryParitySnapshot.RuntimePreludeBuiltinNames(),
            "Builtins present in BuiltinId but missing from runtime prelude",
            "Builtins present in runtime prelude but missing from BuiltinId");

        AssertSetParity(
            builtinNames,
            BuiltinRegistryParitySnapshot.SemanticPreludeBuiltinNames(),
            "Builtins present in BuiltinId but missing from semantic prelude",
            "Builtins present in semantic prelude but missing from BuiltinId");

        AssertSetParity(
            builtinNames,
            BuiltinRegistryParitySnapshot.ParameterDetectorBuiltinNames(),
            "Builtins present in BuiltinId but missing from ParameterDetector exclusions",
            "Builtins excluded in ParameterDetector but not present in BuiltinId");

        AssertSetParity(
            new[] { "Math" },
            BuiltinRegistryParitySnapshot.RuntimePreludeExtraNames(),
            "Expected runtime-prelude non-builtin names are missing",
            "Unexpected non-builtin names exposed by runtime prelude");

        AssertSetParity(
            new[] { "Math", "load" },
            BuiltinRegistryParitySnapshot.SemanticPreludeExtraNames(),
            "Expected semantic-prelude non-builtin names are missing",
            "Unexpected non-builtin names exposed by semantic prelude");

        AssertSetParity(
            new[] { "Math", "load" },
            BuiltinRegistryParitySnapshot.ParameterDetectorPreludeExtraNames(),
            "Expected ParameterDetector prelude exclusions are missing",
            "Unexpected non-builtin names excluded in ParameterDetector");
    }

    [Fact]
    public void SemanticBuiltinMetadata_StaysAlignedWithRuntimeArityAndSequenceLabels()
    {
        var failures = new List<string>();

        foreach (var builtin in Enum.GetValues<BuiltinId>())
        {
            var name = builtin.ToString();
            var semanticPlain = BuiltinRegistryParitySnapshot.SemanticBuiltinParameterNames(name, builtin, PropertyCallStyle.Plain);
            var semanticDot = BuiltinRegistryParitySnapshot.SemanticBuiltinParameterNames(name, builtin, PropertyCallStyle.Dot);

            if (BuiltinRegistryParitySnapshot.TryGetRuntimeSequenceSignature(builtin, out var runtimeSequence))
            {
                if (!runtimeSequence.SupportsSemanticItemsSurface)
                {
                    failures.Add(
                        $"Runtime sequence metadata for builtin '{name}' uses leading arity {runtimeSequence.LeadingArityDescription}; update the parity test helper before changing semantic signature expectations.");
                    continue;
                }

                var expectedPlain = runtimeSequence.ExpectedPlainSemanticParameters();
                var expectedDot = runtimeSequence.ExpectedDotSemanticParameters();

                if (!expectedPlain.SequenceEqual(semanticPlain, StringComparer.Ordinal))
                {
                    failures.Add(
                        $"Semantic plain-call metadata for builtin '{name}' does not match runtime sequence metadata. Expected: {FormatParameterList(expectedPlain)}. Actual: {FormatParameterList(semanticPlain)}.");
                }

                if (!expectedDot.SequenceEqual(semanticDot, StringComparer.Ordinal))
                {
                    failures.Add(
                        $"Semantic dot-call metadata for builtin '{name}' does not match runtime sequence metadata. Expected: {FormatParameterList(expectedDot)}. Actual: {FormatParameterList(semanticDot)}.");
                }

                continue;
            }

            // Fixed-arity runtime metadata only exposes exact arity, not a parallel
            // parameter-label table, so parity here checks coverage/count only.
            var expectedArity = BuiltinRegistryParitySnapshot.RuntimeFixedBuiltinArity(builtin);
            if (semanticPlain.Count != expectedArity)
            {
                failures.Add(
                    $"Semantic plain-call metadata for builtin '{name}' has {semanticPlain.Count} parameter(s), but runtime expects arity {expectedArity}. Semantic parameters: {FormatParameterList(semanticPlain)}.");
            }

            if (!semanticPlain.SequenceEqual(semanticDot, StringComparer.Ordinal))
            {
                failures.Add(
                    $"Semantic dot-call metadata for fixed-arity builtin '{name}' should match plain-call metadata. Plain: {FormatParameterList(semanticPlain)}. Dot: {FormatParameterList(semanticDot)}.");
            }
        }

        AssertNoFailures(failures);
    }

    [Fact]
    public void MathPreludeInventory_StaysAlignedAcrossRuntimeSemanticsAndParameterDetection()
    {
        var runtimeMath = BuiltinRegistryParitySnapshot.RuntimeMathMembers();
        var semanticMath = BuiltinRegistryParitySnapshot.SemanticMathMembers();
        var parameterDetectorMath = BuiltinRegistryParitySnapshot.ParameterDetectorMathNames();

        AssertSetParity(
            runtimeMath.Keys,
            semanticMath.Keys,
            "Math members present in runtime prelude but missing from semantic model",
            "Math members present in semantic model but missing from runtime prelude");

        AssertSetParity(
            runtimeMath.Keys,
            parameterDetectorMath,
            "Math members present in runtime prelude but missing from ParameterDetector exclusions",
            "Math members excluded in ParameterDetector but not present in runtime Math registry");

        var failures = new List<string>();
        foreach (var name in runtimeMath.Keys.Intersect(semanticMath.Keys, StringComparer.Ordinal).OrderBy(static name => name, StringComparer.Ordinal))
        {
            if (runtimeMath[name] != semanticMath[name])
            {
                failures.Add(
                    $"Math member '{name}' has runtime arity {runtimeMath[name]} but semantic-model arity {semanticMath[name]}.");
            }
        }

        AssertNoFailures(failures);
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

    private static string FormatParameterList(IReadOnlyList<string> parameters)
        => parameters.Count == 0 ? "(none)" : string.Join(", ", parameters);

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

        public static IReadOnlyList<string> CanonicalBuiltinNames()
            => Enum.GetValues<BuiltinId>()
                .Select(static builtin => builtin.ToString())
                .OrderBy(static name => name, StringComparer.Ordinal)
                .ToArray();

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

        public static IReadOnlyList<string> ParameterDetectorBuiltinNames()
            => GetStringSetStaticField(typeof(ParameterDetector), "PreludeNames")
                .Where(static name => Enum.TryParse<BuiltinId>(name, ignoreCase: false, out _))
                .OrderBy(static name => name, StringComparer.Ordinal)
                .ToArray();

        public static IReadOnlyList<string> ParameterDetectorPreludeExtraNames()
            => GetStringSetStaticField(typeof(ParameterDetector), "PreludeNames")
                .Where(static name => !Enum.TryParse<BuiltinId>(name, ignoreCase: false, out _))
                .OrderBy(static name => name, StringComparer.Ordinal)
                .ToArray();

        public static IReadOnlyList<string> SemanticBuiltinParameterNames(string name, BuiltinId builtin, PropertyCallStyle callStyle)
        {
            var parameters = InvokeStatic<IReadOnlyList<PropertyParameterInfo>>(
                SemanticCreateBuiltinParametersMethod,
                name,
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

        public static int RuntimeFixedBuiltinArity(BuiltinId builtin)
        {
            if (TryGetRuntimeSequenceSignature(builtin, out _))
                throw new InvalidOperationException($"Builtin '{builtin}' is sequence-based, not fixed-arity.");

            var acceptedArities = Enumerable.Range(0, 16)
                .Where(argumentCount => InvokeStatic<bool>(RuntimeBuiltinAcceptsArityMethod, builtin, argumentCount))
                .ToArray();

            return acceptedArities.Length switch
            {
                1 => acceptedArities[0],
                0 => throw new InvalidOperationException($"Runtime builtin '{builtin}' did not report any accepted arity."),
                _ => throw new InvalidOperationException($"Runtime builtin '{builtin}' unexpectedly reported multiple fixed arities: {string.Join(", ", acceptedArities)}."),
            };
        }

        public static IReadOnlyDictionary<string, int> RuntimeMathMembers()
            => GetAlgorithmPropertyArities(GetUserAlgorithmStaticField(typeof(Evaluator), "MathAlgorithm"));

        public static IReadOnlyDictionary<string, int> SemanticMathMembers()
            => GetAlgorithmPropertyArities(GetUserAlgorithmStaticField(SemanticBuilderType, "MathAlgorithm"));

        public static IReadOnlyList<string> ParameterDetectorMathNames()
            => GetStringSetStaticField(typeof(ParameterDetector), "MathPropertyNames")
                .OrderBy(static name => name, StringComparer.Ordinal)
                .ToArray();

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

        private static IReadOnlyList<string> GetStringSetStaticField(Type type, string fieldName)
            => ((IEnumerable<string>)GetStaticFieldValue(type, fieldName))
                .OrderBy(static name => name, StringComparer.Ordinal)
                .ToArray();

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
        public bool SupportsSemanticItemsSurface
            => LeadingMinCount == 1 && LeadingMaxCount is null;

        public string LeadingArityDescription
            => LeadingMaxCount is { } maxCount ? $"{LeadingMinCount}..{maxCount}" : $"{LeadingMinCount}+";

        public IReadOnlyList<string> ExpectedPlainSemanticParameters()
        {
            var parameters = new List<string> { "items..." };
            parameters.AddRange(TrailingParameterLabels);
            return parameters;
        }

        public IReadOnlyList<string> ExpectedDotSemanticParameters()
            => TrailingParameterLabels.ToArray();
    }
}