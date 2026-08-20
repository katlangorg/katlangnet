using System.Numerics;

namespace KatLang;

internal enum BuiltinCallStyle
{
    Plain,
    Dot,
}

internal enum SequenceBuiltinSuffixArgKind
{
    Algorithm,
    Value,
    WholeNumber,
}

internal readonly record struct SequenceBuiltinSuffixArgDescriptor(
    string Name,
    SequenceBuiltinSuffixArgKind Kind = SequenceBuiltinSuffixArgKind.Algorithm);

internal enum SequenceBuiltinEmptyPolicy
{
    AllowEmpty,
    RequireAnyItem,
    RequireEachInputNonEmpty,
}

internal enum SequenceBuiltinItemShapeConstraint
{
    Any,
    SingleNumeric,
}

internal readonly record struct SequenceBuiltinMetadata(
    IReadOnlyList<SequenceBuiltinSuffixArgDescriptor> SuffixArgs,
    SequenceBuiltinEmptyPolicy EmptyPolicy,
    SequenceBuiltinItemShapeConstraint ItemShapeConstraint)
{
    // A collection builtin is an ordinary fixed-arity callable: exactly one
    // fixed `collection` parameter followed by its fixed control parameters
    // (`count(collection)`, `take(collection, count)`). The bound collection
    // value is interpreted through the one-level builtin collection view only
    // AFTER binding; argument boundaries are never altered before binding.
    public IReadOnlyList<CallableParameter> Parameters { get; } = CreateParameters(SuffixArgs);

    private static IReadOnlyList<CallableParameter> CreateParameters(
        IReadOnlyList<SequenceBuiltinSuffixArgDescriptor> suffixArgs)
    {
        var parameters = new List<CallableParameter>(suffixArgs.Count + 1)
        {
            new("collection", Source: CallableParameterSource.Builtin),
        };

        parameters.AddRange(suffixArgs.Select(static descriptor => new CallableParameter(
            descriptor.Name,
            Source: CallableParameterSource.Builtin)));
        return parameters;
    }
}

internal enum MathMemberKind
{
    Constant,
    UnaryFunction,
    BinaryFunction,
}

internal readonly record struct MathMemberDescriptor(
    string Name,
    MathMemberKind Kind,
    Decimal128 ConstantValue = default,
    IReadOnlyList<string>? ParameterNames = null)
{
    public int Arity => Kind switch
    {
        MathMemberKind.Constant => 0,
        MathMemberKind.UnaryFunction => 1,
        MathMemberKind.BinaryFunction => 2,
        _ => throw new InvalidOperationException($"Unsupported Math member kind '{Kind}'."),
    };
}

internal sealed class BuiltinDescriptor
{
    public BuiltinDescriptor(
        BuiltinId id,
        int? fixedArity,
        IReadOnlyList<CallableParameter> plainParameters,
        IReadOnlyList<CallableParameter> dotParameters,
        SequenceBuiltinMetadata? sequenceMetadata = null)
    {
        Id = id;
        Name = id.ToString();
        FixedArity = fixedArity;
        PlainParameters = plainParameters;
        DotParameters = dotParameters;
        PlainParameterNames = plainParameters.Select(static parameter => parameter.DisplayName).ToArray();
        DotParameterNames = dotParameters.Select(static parameter => parameter.DisplayName).ToArray();
        PlainSignature = new CallableSignature(Name, plainParameters);
        DotSignature = new CallableSignature(Name, dotParameters);
        PlainSignature.ValidateOrThrow();
        DotSignature.ValidateOrThrow();
        SequenceMetadata = sequenceMetadata;
    }

    public BuiltinId Id { get; }

    public string Name { get; }

    public int? FixedArity { get; }

    public CallableSignature PlainSignature { get; }

    public CallableSignature DotSignature { get; }

    public IReadOnlyList<CallableParameter> PlainParameters { get; }

    public IReadOnlyList<CallableParameter> DotParameters { get; }

    public IReadOnlyList<string> PlainParameterNames { get; }

    public IReadOnlyList<string> DotParameterNames { get; }

    public SequenceBuiltinMetadata? SequenceMetadata { get; }

    public bool AcceptsArity(int count)
    {
        if (Id == BuiltinId.@while)
            return count >= 2;

        if (Id == BuiltinId.@repeat)
            return count >= 3;

        // Collection builtins are ordinary fixed-arity callables
        // (`count(collection)` is exactly 1, `take(collection, count)` is
        // exactly 2), the same rule as every other fixed builtin.
        return FixedArity == count;
    }

    public string DescribeArity()
    {
        if (SequenceMetadata is { } metadata)
        {
            var totalArgCountDesc = BuiltinRegistry.DescribeSequenceBuiltinTotalArgs(PlainSignature);
            if (metadata.SuffixArgs.Count == 0)
                return totalArgCountDesc;

            return $"{totalArgCountDesc} arguments ({PlainSignature.DisplayText})";
        }

        return Id switch
        {
            BuiltinId.@while => "at least 2",
            BuiltinId.@repeat => "at least 3",
            _ => FixedArity?.ToString() ?? "?",
        };
    }

    public IReadOnlyList<string> GetParameterNames(BuiltinCallStyle callStyle)
        => callStyle == BuiltinCallStyle.Dot ? DotParameterNames : PlainParameterNames;

    public IReadOnlyList<CallableParameter> GetParameters(BuiltinCallStyle callStyle)
        => callStyle == BuiltinCallStyle.Dot ? DotParameters : PlainParameters;

    public CallableSignature GetSignature(BuiltinCallStyle callStyle)
        => callStyle == BuiltinCallStyle.Dot ? DotSignature : PlainSignature;
}

internal enum MathAlgorithmFlavor
{
    Runtime,
    SignatureOnly,
}

internal static class BuiltinRegistry
{
    private static readonly SequenceBuiltinMetadata FilterSequenceMetadata =
        new([new("predicate")], SequenceBuiltinEmptyPolicy.AllowEmpty, SequenceBuiltinItemShapeConstraint.Any);

    private static readonly SequenceBuiltinMetadata MapSequenceMetadata =
        new([new("mapper")], SequenceBuiltinEmptyPolicy.AllowEmpty, SequenceBuiltinItemShapeConstraint.Any);

    private static readonly SequenceBuiltinMetadata OrderSequenceMetadata =
        new([], SequenceBuiltinEmptyPolicy.AllowEmpty, SequenceBuiltinItemShapeConstraint.SingleNumeric);

    private static readonly SequenceBuiltinMetadata OrderDescSequenceMetadata =
        new([], SequenceBuiltinEmptyPolicy.AllowEmpty, SequenceBuiltinItemShapeConstraint.SingleNumeric);

    private static readonly SequenceBuiltinMetadata CountSequenceMetadata =
        new([], SequenceBuiltinEmptyPolicy.AllowEmpty, SequenceBuiltinItemShapeConstraint.Any);

    private static readonly SequenceBuiltinMetadata ContainsSequenceMetadata =
        new([new("item", SequenceBuiltinSuffixArgKind.Value)], SequenceBuiltinEmptyPolicy.AllowEmpty, SequenceBuiltinItemShapeConstraint.Any);

    private static readonly SequenceBuiltinMetadata FirstSequenceMetadata =
        new([], SequenceBuiltinEmptyPolicy.RequireAnyItem, SequenceBuiltinItemShapeConstraint.Any);

    private static readonly SequenceBuiltinMetadata LastSequenceMetadata =
        new([], SequenceBuiltinEmptyPolicy.RequireAnyItem, SequenceBuiltinItemShapeConstraint.Any);

    private static readonly SequenceBuiltinMetadata DistinctSequenceMetadata =
        new([], SequenceBuiltinEmptyPolicy.AllowEmpty, SequenceBuiltinItemShapeConstraint.Any);

    private static readonly SequenceBuiltinMetadata TakeSequenceMetadata =
        new([new("count", SequenceBuiltinSuffixArgKind.WholeNumber)], SequenceBuiltinEmptyPolicy.AllowEmpty, SequenceBuiltinItemShapeConstraint.Any);

    private static readonly SequenceBuiltinMetadata SkipSequenceMetadata =
        new([new("count", SequenceBuiltinSuffixArgKind.WholeNumber)], SequenceBuiltinEmptyPolicy.AllowEmpty, SequenceBuiltinItemShapeConstraint.Any);

    private static readonly SequenceBuiltinMetadata MinSequenceMetadata =
        new([], SequenceBuiltinEmptyPolicy.RequireAnyItem, SequenceBuiltinItemShapeConstraint.SingleNumeric);

    private static readonly SequenceBuiltinMetadata MaxSequenceMetadata =
        new([], SequenceBuiltinEmptyPolicy.RequireAnyItem, SequenceBuiltinItemShapeConstraint.SingleNumeric);

    private static readonly SequenceBuiltinMetadata SumSequenceMetadata =
        new([], SequenceBuiltinEmptyPolicy.AllowEmpty, SequenceBuiltinItemShapeConstraint.SingleNumeric);

    private static readonly SequenceBuiltinMetadata AvgSequenceMetadata =
        new([], SequenceBuiltinEmptyPolicy.RequireAnyItem, SequenceBuiltinItemShapeConstraint.SingleNumeric);

    private static readonly SequenceBuiltinMetadata ReduceSequenceMetadata =
        new([new("reducer"), new("initial")], SequenceBuiltinEmptyPolicy.AllowEmpty, SequenceBuiltinItemShapeConstraint.Any);

    private static readonly BuiltinDescriptor[] Builtins =
    [
        Fixed(BuiltinId.@if, "condition", "whenTrue", "whenFalse"),
        Fixed(BuiltinId.@while, "step", "initialState"),
        Fixed(BuiltinId.@repeat, "step", "count", "initialState"),
        Fixed(BuiltinId.@atoms, "value"),
        Fixed(BuiltinId.@range, "start", "stop"),
        Sequence(BuiltinId.@filter, FilterSequenceMetadata),
        Sequence(BuiltinId.@map, MapSequenceMetadata),
        Sequence(BuiltinId.@order, OrderSequenceMetadata),
        Sequence(BuiltinId.@orderDesc, OrderDescSequenceMetadata),
        Sequence(BuiltinId.@count, CountSequenceMetadata),
        Sequence(BuiltinId.@contains, ContainsSequenceMetadata),
        Sequence(BuiltinId.@first, FirstSequenceMetadata),
        Sequence(BuiltinId.@last, LastSequenceMetadata),
        Sequence(BuiltinId.@distinct, DistinctSequenceMetadata),
        Sequence(BuiltinId.@take, TakeSequenceMetadata),
        Sequence(BuiltinId.@skip, SkipSequenceMetadata),
        Sequence(BuiltinId.@min, MinSequenceMetadata),
        Sequence(BuiltinId.@max, MaxSequenceMetadata),
        Sequence(BuiltinId.@sum, SumSequenceMetadata),
        Sequence(BuiltinId.@avg, AvgSequenceMetadata),
        Sequence(BuiltinId.@reduce, ReduceSequenceMetadata),
    ];

    private static readonly IReadOnlyDictionary<BuiltinId, BuiltinDescriptor> BuiltinsById =
        Builtins.ToDictionary(static descriptor => descriptor.Id);

    private static readonly MathMemberDescriptor[] MathMemberDescriptors =
    [
        // Constants come from Decimal128's own correctly-rounded 34-digit sources —
        // never from double, System.Math, or a narrower decimal literal.
        new("Pi", MathMemberKind.Constant, Decimal128.Pi),
        new("E", MathMemberKind.Constant, Decimal128.E),
        new("Abs", MathMemberKind.UnaryFunction),
        new("Ceil", MathMemberKind.UnaryFunction),
        new("Floor", MathMemberKind.UnaryFunction),
        new("Round", MathMemberKind.BinaryFunction),
        new("Sign", MathMemberKind.UnaryFunction),
        new("Sqrt", MathMemberKind.UnaryFunction),
        new("Ln", MathMemberKind.UnaryFunction),
        new("Lg", MathMemberKind.UnaryFunction),
        new("Sin", MathMemberKind.UnaryFunction),
        new("Asin", MathMemberKind.UnaryFunction),
        new("Cos", MathMemberKind.UnaryFunction),
        new("Acos", MathMemberKind.UnaryFunction),
        new("Tan", MathMemberKind.UnaryFunction),
        new("Atan", MathMemberKind.UnaryFunction),
        new("Atan2", MathMemberKind.BinaryFunction, ParameterNames: ["y", "x"]),
        new("Pow", MathMemberKind.BinaryFunction),
        new("Log", MathMemberKind.BinaryFunction),
        new("Random", MathMemberKind.BinaryFunction, ParameterNames: ["start", "end"]),
        new("RandomInt", MathMemberKind.BinaryFunction, ParameterNames: ["start", "end"]),
    ];

    public static IReadOnlyList<BuiltinDescriptor> AllBuiltins => Builtins;

    public static IReadOnlyList<string> BuiltinNames { get; } = Builtins
        .Select(static descriptor => descriptor.Name)
        .ToArray();

    public static IReadOnlyList<string> RuntimePreludeExtraNames { get; } = ["Math"];

    public static IReadOnlyList<string> SemanticPreludeExtraNames { get; } = ["Math", "load"];

    public static IReadOnlyList<string> ParameterDetectorPreludeNames { get; } =
        BuiltinNames.Concat(SemanticPreludeExtraNames).ToArray();

    public static IReadOnlyList<MathMemberDescriptor> MathMembers => MathMemberDescriptors;

    public static IReadOnlyList<string> MathMemberNames { get; } = MathMemberDescriptors
        .Select(static member => member.Name)
        .ToArray();

    public static bool IsMathFunctionMember(string name)
        => MathMemberDescriptors.Any(member => member.Name == name && member.Kind != MathMemberKind.Constant);

    public static bool TryGetBuiltinCallableSignature(
        string ownerName,
        string memberName,
        [System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out CallableSignature? signature)
    {
        if (ownerName == "Math")
            return TryGetMathFunctionSignature(memberName, out signature);

        signature = null;
        return false;
    }

    private static bool TryGetMathFunctionSignature(
        string name,
        [System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out CallableSignature? signature)
    {
        foreach (var member in MathMemberDescriptors)
        {
            if (member.Name == name && member.Kind != MathMemberKind.Constant)
            {
                signature = CallableSignature.FromAlgorithm(
                    member.Name,
                    CreateMathMemberAlgorithm(member, MathAlgorithmFlavor.SignatureOnly));
                return true;
            }
        }

        signature = null;
        return false;
    }

    public static IReadOnlyList<string> LoadParameterNames { get; } = ["url"];

    public static BuiltinDescriptor GetBuiltin(BuiltinId builtin)
        => BuiltinsById[builtin];

    public static bool TryGetSequenceMetadata(BuiltinId builtin, out SequenceBuiltinMetadata metadata)
    {
        if (GetBuiltin(builtin).SequenceMetadata is { } sequenceMetadata)
        {
            metadata = sequenceMetadata;
            return true;
        }

        metadata = default;
        return false;
    }

    public static IReadOnlyList<string> GetBuiltinParameterNames(BuiltinId builtin, BuiltinCallStyle callStyle)
        => GetBuiltin(builtin).GetParameterNames(callStyle);

    public static IReadOnlyList<CallableParameter> GetBuiltinParameters(BuiltinId builtin, BuiltinCallStyle callStyle)
        => GetBuiltin(builtin).GetParameters(callStyle);

    public static Algorithm.User CreateMathAlgorithm(MathAlgorithmFlavor flavor)
        => new(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: MathMemberDescriptors.Select(member => CreateMathProperty(member, flavor)).ToList(),
            Output: []);

    public static Algorithm.User CreateRuntimePreludeAlgorithm(Algorithm.User? mathAlgorithm = null)
        => CreatePreludeAlgorithm(includeLoad: false, mathAlgorithm ?? CreateMathAlgorithm(MathAlgorithmFlavor.Runtime));

    public static Algorithm.User CreateSemanticPreludeAlgorithm(Algorithm.User? mathAlgorithm = null)
        => CreatePreludeAlgorithm(includeLoad: true, mathAlgorithm ?? CreateMathAlgorithm(MathAlgorithmFlavor.SignatureOnly));

    private static Property CreateMathProperty(MathMemberDescriptor member, MathAlgorithmFlavor flavor)
        => new(member.Name, CreateMathMemberAlgorithm(member, flavor), IsPublic: true);

    private static Algorithm.User CreateMathMemberAlgorithm(MathMemberDescriptor member, MathAlgorithmFlavor flavor)
    {
        var parameterNames = CreateMathParameterNames(member);

        return flavor switch
        {
            MathAlgorithmFlavor.Runtime when member.Kind == MathMemberKind.Constant => new Algorithm.User(
                Parent: null,
                Parameters: Algorithm.NormalParameters(parameterNames),
                Opens: [],
                Properties: [],
                Output: [new Expr.Num(member.ConstantValue)]),
            MathAlgorithmFlavor.Runtime => new Algorithm.User(
                Parent: null,
                Parameters: Algorithm.NormalParameters(parameterNames),
                Opens: [],
                Properties: [],
                Output: [new Expr.NativeCall(member.Name, parameterNames)]),
            MathAlgorithmFlavor.SignatureOnly => new Algorithm.User(
                Parent: null,
                Parameters: Algorithm.NormalParameters(parameterNames),
                Opens: [],
                Properties: [],
                Output: []),
            _ => throw new InvalidOperationException($"Unsupported Math algorithm flavor '{flavor}'."),
        };
    }

    private static Algorithm.User CreateLoadAlgorithm()
        => new(Parent: null, Parameters: Algorithm.NormalParameters(LoadParameterNames), Opens: [], Properties: [], Output: []);

    private static Algorithm.User CreatePreludeAlgorithm(bool includeLoad, Algorithm.User mathAlgorithm)
    {
        var properties = new List<Property>(Builtins.Length + (includeLoad ? 2 : 1));
        foreach (var builtin in Builtins)
            properties.Add(new Property(builtin.Name, new Algorithm.Builtin(builtin.Id), IsPublic: true));

        if (includeLoad)
            properties.Add(new Property("load", CreateLoadAlgorithm(), IsPublic: true));

        properties.Add(new Property("Math", mathAlgorithm, IsPublic: true));

        return new Algorithm.User(Parent: null, Parameters: [], Opens: [], Properties: properties, Output: []);
    }

    private static IReadOnlyList<string> CreateMathParameterNames(MathMemberDescriptor member)
    {
        var parameterNames = member.ParameterNames ?? CreateDefaultMathParameterNames(member.Arity);
        if (parameterNames.Count != member.Arity)
            throw new InvalidOperationException(
                $"Math member '{member.Name}' declares {parameterNames.Count} parameter names for arity {member.Arity}.");

        return parameterNames;
    }

    private static string[] CreateDefaultMathParameterNames(int arity) => arity switch
    {
        0 => [],
        1 => ["x"],
        2 => ["x", "y"],
        _ => throw new InvalidOperationException($"Unsupported Math arity '{arity}'."),
    };

    private static BuiltinDescriptor Fixed(BuiltinId id, params string[] parameterNames)
    {
        var parameters = parameterNames.Select(static name => new CallableParameter(
            name,
            Source: CallableParameterSource.Builtin)).ToArray();
        return new(id, parameterNames.Length, parameters, parameters);
    }

    private static BuiltinDescriptor Sequence(BuiltinId id, SequenceBuiltinMetadata metadata)
        => new(
            id,
            fixedArity: 1 + metadata.SuffixArgs.Count,
            plainParameters: metadata.Parameters,
            dotParameters: CreateSequenceDotParameters(metadata),
            sequenceMetadata: metadata);

    // Dot-call syntax injects the receiver as the fixed `collection` argument,
    // so the dot-visible parameters are exactly the control parameters that
    // follow it (`collection.take(count)`-style hovers show only `count`).
    private static IReadOnlyList<CallableParameter> CreateSequenceDotParameters(SequenceBuiltinMetadata metadata)
        => metadata.Parameters.Skip(1).ToArray();

    internal static string DescribeSequenceBuiltinTotalArgs(CallableSignature signature)
        => CallableSignatureDiagnostics.FormatExpectedArgumentCountWithoutNoun(signature.ArityFacts);
}
