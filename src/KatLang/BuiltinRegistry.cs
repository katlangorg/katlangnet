namespace KatLang;

internal enum BuiltinCallStyle
{
    Plain,
    Dot,
}

internal readonly record struct SequenceBuiltinLeadingArity(int MinCount, int? MaxCount = null)
{
    public static SequenceBuiltinLeadingArity Exact(int count) => new(count, count);

    public bool Accepts(int count)
        => count >= MinCount && (!MaxCount.HasValue || count <= MaxCount.Value);
}

internal enum SequenceBuiltinTrailingArgKind
{
    Algorithm,
    Value,
    WholeNumber,
}

internal readonly record struct SequenceBuiltinTrailingArgDescriptor(
    string Label,
    SequenceBuiltinTrailingArgKind Kind = SequenceBuiltinTrailingArgKind.Algorithm);

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
    SequenceBuiltinLeadingArity LeadingSequenceArity,
    IReadOnlyList<SequenceBuiltinTrailingArgDescriptor> TrailingArgs,
    SequenceBuiltinEmptyPolicy EmptyPolicy,
    SequenceBuiltinItemShapeConstraint ItemShapeConstraint)
{
    public int TrailingArgCount => TrailingArgs.Count;
}

internal enum MathMemberKind
{
    Constant,
    UnaryFunction,
    BinaryFunction,
}

internal readonly record struct MathMemberDescriptor(string Name, MathMemberKind Kind, decimal ConstantValue = 0m)
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
        IReadOnlyList<string> plainParameterNames,
        IReadOnlyList<string> dotParameterNames,
        SequenceBuiltinMetadata? sequenceMetadata = null)
    {
        Id = id;
        Name = id.ToString();
        FixedArity = fixedArity;
        PlainParameterNames = plainParameterNames;
        DotParameterNames = dotParameterNames;
        SequenceMetadata = sequenceMetadata;
    }

    public BuiltinId Id { get; }

    public string Name { get; }

    public int? FixedArity { get; }

    public IReadOnlyList<string> PlainParameterNames { get; }

    public IReadOnlyList<string> DotParameterNames { get; }

    public SequenceBuiltinMetadata? SequenceMetadata { get; }

    public bool AcceptsArity(int count)
    {
        if (SequenceMetadata is { } metadata)
        {
            if (count < metadata.TrailingArgCount)
                return false;

            return metadata.LeadingSequenceArity.Accepts(count - metadata.TrailingArgCount);
        }

        return FixedArity == count;
    }

    public string DescribeArity()
    {
        if (SequenceMetadata is { } metadata)
        {
            var totalArgCountDesc = BuiltinRegistry.DescribeSequenceBuiltinTotalArgs(
                metadata.LeadingSequenceArity,
                metadata.TrailingArgCount);
            if (metadata.TrailingArgs.Count == 0)
                return totalArgCountDesc;

            return $"{totalArgCountDesc} arguments ({BuiltinRegistry.DescribeSequenceBuiltinLeadingArgs(metadata.LeadingSequenceArity)} plus {BuiltinRegistry.DescribeSequenceBuiltinTrailingArgs(metadata.TrailingArgs)})";
        }

        return FixedArity?.ToString() ?? "?";
    }

    public IReadOnlyList<string> GetParameterNames(BuiltinCallStyle callStyle)
        => callStyle == BuiltinCallStyle.Dot ? DotParameterNames : PlainParameterNames;
}

internal enum MathAlgorithmFlavor
{
    Runtime,
    SignatureOnly,
}

internal static class BuiltinRegistry
{
    private static readonly SequenceBuiltinLeadingArity OneOrMoreSequenceArguments = new(1);

    private static readonly SequenceBuiltinMetadata FilterSequenceMetadata =
        new(OneOrMoreSequenceArguments, [new("predicate")], SequenceBuiltinEmptyPolicy.AllowEmpty, SequenceBuiltinItemShapeConstraint.Any);

    private static readonly SequenceBuiltinMetadata MapSequenceMetadata =
        new(OneOrMoreSequenceArguments, [new("transform")], SequenceBuiltinEmptyPolicy.AllowEmpty, SequenceBuiltinItemShapeConstraint.Any);

    private static readonly SequenceBuiltinMetadata OrderSequenceMetadata =
        new(OneOrMoreSequenceArguments, [], SequenceBuiltinEmptyPolicy.AllowEmpty, SequenceBuiltinItemShapeConstraint.SingleNumeric);

    private static readonly SequenceBuiltinMetadata OrderDescSequenceMetadata =
        new(OneOrMoreSequenceArguments, [], SequenceBuiltinEmptyPolicy.AllowEmpty, SequenceBuiltinItemShapeConstraint.SingleNumeric);

    private static readonly SequenceBuiltinMetadata CountSequenceMetadata =
        new(OneOrMoreSequenceArguments, [], SequenceBuiltinEmptyPolicy.AllowEmpty, SequenceBuiltinItemShapeConstraint.Any);

    private static readonly SequenceBuiltinMetadata ContainsSequenceMetadata =
        new(OneOrMoreSequenceArguments, [new("item", SequenceBuiltinTrailingArgKind.Value)], SequenceBuiltinEmptyPolicy.AllowEmpty, SequenceBuiltinItemShapeConstraint.Any);

    private static readonly SequenceBuiltinMetadata FirstSequenceMetadata =
        new(OneOrMoreSequenceArguments, [], SequenceBuiltinEmptyPolicy.RequireAnyItem, SequenceBuiltinItemShapeConstraint.Any);

    private static readonly SequenceBuiltinMetadata LastSequenceMetadata =
        new(OneOrMoreSequenceArguments, [], SequenceBuiltinEmptyPolicy.RequireAnyItem, SequenceBuiltinItemShapeConstraint.Any);

    private static readonly SequenceBuiltinMetadata DistinctSequenceMetadata =
        new(OneOrMoreSequenceArguments, [], SequenceBuiltinEmptyPolicy.AllowEmpty, SequenceBuiltinItemShapeConstraint.Any);

    private static readonly SequenceBuiltinMetadata TakeSequenceMetadata =
        new(OneOrMoreSequenceArguments, [new("count", SequenceBuiltinTrailingArgKind.WholeNumber)], SequenceBuiltinEmptyPolicy.AllowEmpty, SequenceBuiltinItemShapeConstraint.Any);

    private static readonly SequenceBuiltinMetadata SkipSequenceMetadata =
        new(OneOrMoreSequenceArguments, [new("count", SequenceBuiltinTrailingArgKind.WholeNumber)], SequenceBuiltinEmptyPolicy.AllowEmpty, SequenceBuiltinItemShapeConstraint.Any);

    private static readonly SequenceBuiltinMetadata MinSequenceMetadata =
        new(OneOrMoreSequenceArguments, [], SequenceBuiltinEmptyPolicy.RequireAnyItem, SequenceBuiltinItemShapeConstraint.SingleNumeric);

    private static readonly SequenceBuiltinMetadata MaxSequenceMetadata =
        new(OneOrMoreSequenceArguments, [], SequenceBuiltinEmptyPolicy.RequireAnyItem, SequenceBuiltinItemShapeConstraint.SingleNumeric);

    private static readonly SequenceBuiltinMetadata SumSequenceMetadata =
        new(OneOrMoreSequenceArguments, [], SequenceBuiltinEmptyPolicy.AllowEmpty, SequenceBuiltinItemShapeConstraint.SingleNumeric);

    private static readonly SequenceBuiltinMetadata AvgSequenceMetadata =
        new(OneOrMoreSequenceArguments, [], SequenceBuiltinEmptyPolicy.RequireAnyItem, SequenceBuiltinItemShapeConstraint.SingleNumeric);

    private static readonly SequenceBuiltinMetadata ReduceSequenceMetadata =
        new(OneOrMoreSequenceArguments, [new("step"), new("initial accumulator")], SequenceBuiltinEmptyPolicy.AllowEmpty, SequenceBuiltinItemShapeConstraint.Any);

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
        new("Pi", MathMemberKind.Constant, 3.1415926535897932384626433833m),
        new("E", MathMemberKind.Constant, 2.7182818284590452353602874714m),
        new("Abs", MathMemberKind.UnaryFunction),
        new("Ceil", MathMemberKind.UnaryFunction),
        new("Floor", MathMemberKind.UnaryFunction),
        new("Round", MathMemberKind.UnaryFunction),
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
        new("Pow", MathMemberKind.BinaryFunction),
        new("Log", MathMemberKind.BinaryFunction),
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

    public static Algorithm.User CreateMathAlgorithm(MathAlgorithmFlavor flavor)
        => new(
            Parent: null,
            Params: [],
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
        var parameterNames = CreateMathParameterNames(member.Arity);

        return flavor switch
        {
            MathAlgorithmFlavor.Runtime when member.Kind == MathMemberKind.Constant => new Algorithm.User(
                Parent: null,
                Params: parameterNames,
                Opens: [],
                Properties: [],
                Output: [new Expr.Num(member.ConstantValue)]),
            MathAlgorithmFlavor.Runtime => new Algorithm.User(
                Parent: null,
                Params: parameterNames,
                Opens: [],
                Properties: [],
                Output: [new Expr.NativeCall(member.Name, parameterNames)]),
            MathAlgorithmFlavor.SignatureOnly => new Algorithm.User(
                Parent: null,
                Params: parameterNames,
                Opens: [],
                Properties: [],
                Output: []),
            _ => throw new InvalidOperationException($"Unsupported Math algorithm flavor '{flavor}'."),
        };
    }

    private static Algorithm.User CreateLoadAlgorithm()
        => new(Parent: null, Params: LoadParameterNames, Opens: [], Properties: [], Output: []);

    private static Algorithm.User CreatePreludeAlgorithm(bool includeLoad, Algorithm.User mathAlgorithm)
    {
        var properties = new List<Property>(Builtins.Length + (includeLoad ? 2 : 1));
        foreach (var builtin in Builtins)
            properties.Add(new Property(builtin.Name, new Algorithm.Builtin(builtin.Id), IsPublic: true));

        if (includeLoad)
            properties.Add(new Property("load", CreateLoadAlgorithm(), IsPublic: true));

        properties.Add(new Property("Math", mathAlgorithm, IsPublic: true));

        return new Algorithm.User(Parent: null, Params: [], Opens: [], Properties: properties, Output: []);
    }

    private static string[] CreateMathParameterNames(int arity) => arity switch
    {
        0 => [],
        1 => ["x"],
        2 => ["x", "y"],
        _ => throw new InvalidOperationException($"Unsupported Math arity '{arity}'."),
    };

    private static BuiltinDescriptor Fixed(BuiltinId id, params string[] parameterNames)
        => new(id, parameterNames.Length, parameterNames, parameterNames);

    private static BuiltinDescriptor Sequence(BuiltinId id, SequenceBuiltinMetadata metadata)
        => new(
            id,
            fixedArity: null,
            plainParameterNames: CreateSequenceParameterNames(metadata, BuiltinCallStyle.Plain),
            dotParameterNames: CreateSequenceParameterNames(metadata, BuiltinCallStyle.Dot),
            sequenceMetadata: metadata);

    private static string[] CreateSequenceParameterNames(SequenceBuiltinMetadata metadata, BuiltinCallStyle callStyle)
    {
        var names = new List<string>(metadata.TrailingArgs.Count + (callStyle == BuiltinCallStyle.Plain ? 1 : 0));
        if (callStyle == BuiltinCallStyle.Plain)
            names.Add("items...");

        names.AddRange(metadata.TrailingArgs.Select(static descriptor => descriptor.Label));
        return names.ToArray();
    }

    internal static string DescribeSequenceBuiltinLeadingArgs(SequenceBuiltinLeadingArity arity)
    {
        if (arity.MaxCount is { } maxCount)
        {
            if (arity.MinCount == maxCount)
                return arity.MinCount == 1 ? "1 sequence argument" : $"{arity.MinCount} sequence arguments";

            return $"between {arity.MinCount} and {maxCount} sequence arguments";
        }

        return arity.MinCount == 1
            ? "one or more sequence arguments"
            : $"at least {arity.MinCount} sequence arguments";
    }

    internal static string DescribeSequenceBuiltinTrailingArgs(IReadOnlyList<SequenceBuiltinTrailingArgDescriptor> descriptors)
        => string.Join(", ", descriptors.Select(DescribeSequenceBuiltinTrailingArg));

    internal static string DescribeSequenceBuiltinTotalArgs(SequenceBuiltinLeadingArity arity, int trailingArgCount)
    {
        var minTotal = arity.MinCount + trailingArgCount;
        if (arity.MaxCount is { } maxCount)
        {
            var maxTotal = maxCount + trailingArgCount;
            return minTotal == maxTotal ? $"{minTotal}" : $"between {minTotal} and {maxTotal}";
        }

        return $"at least {minTotal}";
    }

    private static string DescribeSequenceBuiltinTrailingArg(SequenceBuiltinTrailingArgDescriptor descriptor)
        => descriptor.Kind switch
        {
            SequenceBuiltinTrailingArgKind.Algorithm => $"{descriptor.Label} algorithm",
            SequenceBuiltinTrailingArgKind.Value => descriptor.Label,
            SequenceBuiltinTrailingArgKind.WholeNumber => $"{descriptor.Label} whole-number value",
            _ => descriptor.Label,
        };
}