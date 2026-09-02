using System.Collections.Frozen;
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
    string PreludeAlias,
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

    /// <summary>
    /// The member's canonical qualified spelling (<c>"Math.Sin"</c>, <c>"Math.Pi"</c>):
    /// the ONE identity string every consumer keys on. It is derived exactly once,
    /// here at descriptor construction, from <see cref="BuiltinRegistry.MathModuleName"/>
    /// and <see cref="Name"/>; <see cref="MathCallableFacts.CanonicalKey"/> (both
    /// spellings' callable facts) and the editor's alias-target metadata carry THIS
    /// instance rather than re-joining the two names, so the relation has one owner.
    /// It can never collide with a user property name because identifiers cannot
    /// contain <c>'.'</c>.
    /// </summary>
    public string CanonicalQualifiedName { get; } = BuiltinRegistry.MathModuleName + "." + Name;
}

/// <summary>
/// Registry-derived callable facts for ONE spelling of a Math function member:
/// the canonical structural spelling (<c>Math.Sin</c>) or its predefined
/// prelude alias (<c>sin</c>). Both spellings project the SAME descriptor, so
/// every consumer that lifts bare references, rewrites implicit calls,
/// processes value-demanding arguments, or orders sibling dependencies through
/// these facts observes identical behavior for the two surfaces.
///
/// <para>The facts are binding-NEUTRAL: they say nothing about whether a
/// particular written name actually resolves to the prelude. Each consumer must
/// first apply its own ordinary-resolution shadow knowledge (visible user
/// properties, parameters) before consulting them — a user-defined <c>sin</c>
/// is an ordinary neutral callable, never a Math member.</para>
/// </summary>
internal sealed class MathCallableFacts
{
    public MathCallableFacts(string spelledName, string canonicalKey, CallableSignature signature)
    {
        SpelledName = spelledName;
        CanonicalKey = canonicalKey;
        Signature = signature;
    }

    /// <summary>The written spelling these facts describe (<c>"Sin"</c> or <c>"sin"</c>).</summary>
    public string SpelledName { get; }

    /// <summary>
    /// Stable canonical identity shared by both spellings (<c>"Math.Sin"</c>) —
    /// the descriptor's own <see cref="MathMemberDescriptor.CanonicalQualifiedName"/>
    /// instance, never reconstructed here. Dependency deduplication keys on this
    /// so a body referencing both <c>Math.Pow</c> and <c>pow</c> lifts ONE
    /// dependency.
    /// </summary>
    public string CanonicalKey { get; }

    /// <summary>Callable signature named by <see cref="SpelledName"/>, with the descriptor's parameter names.</summary>
    public CallableSignature Signature { get; }

    /// <summary>
    /// Math members consume strictly numeric VALUES — the registry proves no
    /// higher-order argument channel exists — so written argument slots are
    /// ordinary value positions (implicit lifting applies). Consumers must
    /// check this rather than assume it, so a future non-strict fact can slot
    /// into the same abstraction.
    /// </summary>
    public bool HasStrictValueArguments => true;
}

internal sealed class BuiltinDescriptor
{
    public BuiltinDescriptor(
        BuiltinId id,
        int? fixedArity,
        IReadOnlyList<CallableParameter> plainParameters,
        IReadOnlyList<CallableParameter> dotParameters,
        SequenceBuiltinMetadata? sequenceMetadata = null,
        IReadOnlyList<CallableParameter>? toolingPlainParameters = null,
        IReadOnlyList<CallableParameter>? toolingDotParameters = null)
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
        ToolingPlainSignature = new CallableSignature(Name, toolingPlainParameters ?? plainParameters);
        ToolingDotSignature = new CallableSignature(Name, toolingDotParameters ?? dotParameters);
        PlainSignature.ValidateOrThrow();
        DotSignature.ValidateOrThrow();
        ToolingPlainSignature.ValidateOrThrow();
        ToolingDotSignature.ValidateOrThrow();
        SequenceMetadata = sequenceMetadata;
    }

    public BuiltinId Id { get; }

    public string Name { get; }

    public int? FixedArity { get; }

    public CallableSignature PlainSignature { get; }

    public CallableSignature DotSignature { get; }

    /// <summary>
    /// Editor-facing callable surfaces. These normally equal the runtime
    /// signatures; loop builtins use a collecting <c>*init</c> display while
    /// retaining their stricter runtime minimum of one initial-state slot.
    /// </summary>
    public CallableSignature ToolingPlainSignature { get; }

    public CallableSignature ToolingDotSignature { get; }

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

    public CallableSignature GetToolingSignature(BuiltinCallStyle callStyle)
        => callStyle == BuiltinCallStyle.Dot ? ToolingDotSignature : ToolingPlainSignature;
}

internal enum MathAlgorithmFlavor
{
    Runtime,
    SignatureOnly,
}

internal static class BuiltinRegistry
{
    /// <summary>
    /// The prelude name of the Math module (<c>Math</c>): the receiver of every
    /// canonical <c>Math.X</c> spelling, the reserved prelude name, and the
    /// prefix of every <see cref="MathMemberDescriptor.CanonicalQualifiedName"/>.
    /// Consumers classify the canonical shape through <c>AstHelpers</c> and read
    /// qualified names from the descriptor, so this literal is written once.
    /// </summary>
    internal const string MathModuleName = "Math";

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
        Loop(BuiltinId.@while, "step"),
        Loop(BuiltinId.@repeat, "step", "count"),
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

    // Every Math member declares its ONE predefined lower-camel-case prelude alias
    // explicitly — never derived by lowercasing — so future collisions, acronyms,
    // exclusions, renames, and deprecations stay deliberate, reviewed decisions.
    // ParameterNames are equally authoritative: they name the member's runtime
    // parameters AND every editor-facing signature (hover, completion, alias
    // target displays), so domain-specific names (`radians`, `digits`) belong
    // here, never in editor layers.
    private static readonly IReadOnlyList<MathMemberDescriptor> MathMemberDescriptors = ValidateMathMemberMetadata(
    [
        // Constants come from Decimal128's own correctly-rounded 34-digit sources —
        // never from double, System.Math, or a narrower decimal literal.
        new("Pi", MathMemberKind.Constant, "pi", Decimal128.Pi),
        new("Exp", MathMemberKind.UnaryFunction, "exp"),
        new("Abs", MathMemberKind.UnaryFunction, "abs"),
        new("Ceil", MathMemberKind.UnaryFunction, "ceil"),
        new("Floor", MathMemberKind.UnaryFunction, "floor"),
        new("Round", MathMemberKind.BinaryFunction, "round", ParameterNames: ["value", "digits"]),
        new("Sign", MathMemberKind.UnaryFunction, "sign"),
        new("Sqrt", MathMemberKind.UnaryFunction, "sqrt"),
        new("Ln", MathMemberKind.UnaryFunction, "ln"),
        new("Lg", MathMemberKind.UnaryFunction, "lg"),
        new("Sin", MathMemberKind.UnaryFunction, "sin", ParameterNames: ["radians"]),
        new("Asin", MathMemberKind.UnaryFunction, "asin"),
        new("Cos", MathMemberKind.UnaryFunction, "cos", ParameterNames: ["radians"]),
        new("Acos", MathMemberKind.UnaryFunction, "acos"),
        new("Tan", MathMemberKind.UnaryFunction, "tan", ParameterNames: ["radians"]),
        new("Atan", MathMemberKind.UnaryFunction, "atan"),
        new("Atan2", MathMemberKind.BinaryFunction, "atan2", ParameterNames: ["y", "x"]),
        new("Pow", MathMemberKind.BinaryFunction, "pow"),
        new("Log", MathMemberKind.BinaryFunction, "log", ParameterNames: ["value", "base"]),
        new("Random", MathMemberKind.BinaryFunction, "random", ParameterNames: ["start", "end"]),
        new("RandomInt", MathMemberKind.BinaryFunction, "randomInt", ParameterNames: ["start", "end"]),
    ]);

    /// <summary>
    /// Fail-loud gate on the hand-maintained Math member table, run while the
    /// registry initializes: canonical names, required aliases, and explicit
    /// parameter names must be valid identifiers and ordinally unique in their
    /// respective scopes; explicit parameter counts must match member arity;
    /// and no alias may collide with a canonical member, builtin name,
    /// <c>Math</c>, or <c>load</c> (the rest of the prelude vocabulary IS the
    /// alias set itself, covered by uniqueness).
    /// </summary>
    private static IReadOnlyList<MathMemberDescriptor> ValidateMathMemberMetadata(MathMemberDescriptor[] members)
    {
        var reservedNames = Builtins
            .Select(static descriptor => descriptor.Name)
            .Append(MathModuleName)
            .Append("load");
        ValidateMathMemberMetadataCore(members, reservedNames);
        return Array.AsReadOnly(members);
    }

    /// <summary>Validation core behind <see cref="ValidateMathMemberMetadata"/>, parameterized for tests.</summary>
    internal static void ValidateMathMemberMetadataCore(
        IReadOnlyList<MathMemberDescriptor> members,
        IEnumerable<string> reservedNames)
    {
        var reserved = new HashSet<string>(reservedNames, StringComparer.Ordinal);
        var seenMemberNames = new HashSet<string>(StringComparer.Ordinal);
        foreach (var member in members)
        {
            if (string.IsNullOrEmpty(member.Name) || !Lexer.IsValidIdentifier(member.Name))
                throw new InvalidOperationException(
                    $"Math member name '{member.Name}' is not a valid KatLang identifier.");

            if (!seenMemberNames.Add(member.Name))
                throw new InvalidOperationException(
                    $"Math member name '{member.Name}' is declared more than once.");

            if (member.ParameterNames is not { } parameterNames)
                continue;

            if (parameterNames.Count != member.Arity)
                throw new InvalidOperationException(
                    $"Math member '{member.Name}' declares {parameterNames.Count} parameter names for arity {member.Arity}.");

            var seenParameterNames = new HashSet<string>(StringComparer.Ordinal);
            foreach (var parameterName in parameterNames)
            {
                if (string.IsNullOrEmpty(parameterName) || !Lexer.IsValidIdentifier(parameterName))
                    throw new InvalidOperationException(
                        $"Math member '{member.Name}' declares parameter name '{parameterName}', which is not a valid KatLang identifier.");

                if (!seenParameterNames.Add(parameterName))
                    throw new InvalidOperationException(
                        $"Math member '{member.Name}' declares parameter name '{parameterName}' more than once.");
            }
        }

        var seenAliases = new HashSet<string>(StringComparer.Ordinal);
        foreach (var member in members)
        {
            if (string.IsNullOrEmpty(member.PreludeAlias) || !Lexer.IsValidIdentifier(member.PreludeAlias))
                throw new InvalidOperationException(
                    $"Math member '{member.Name}' declares prelude alias '{member.PreludeAlias}', which is not a valid KatLang identifier.");

            if (!seenAliases.Add(member.PreludeAlias))
                throw new InvalidOperationException(
                    $"Math member '{member.Name}' declares prelude alias '{member.PreludeAlias}', which another Math member already uses.");

            if (seenMemberNames.Contains(member.PreludeAlias))
                throw new InvalidOperationException(
                    $"Math member '{member.Name}' declares prelude alias '{member.PreludeAlias}', which collides with a canonical Math member name.");

            if (reserved.Contains(member.PreludeAlias))
                throw new InvalidOperationException(
                    $"Math member '{member.Name}' declares prelude alias '{member.PreludeAlias}', which collides with an existing prelude name.");
        }
    }

    /// <summary>
    /// Callable facts for Math FUNCTION members keyed by canonical member name
    /// (<c>"Sin"</c>) and by prelude alias (<c>"sin"</c>). Constants have no
    /// callable facts (zero parameters: nothing lifts and no arguments exist).
    /// </summary>
    private static readonly IReadOnlyDictionary<string, MathCallableFacts> MathFunctionFactsByCanonicalName =
        CreateMathFunctionFacts(byAlias: false);

    private static readonly IReadOnlyDictionary<string, MathCallableFacts> MathFunctionFactsByAliasName =
        CreateMathFunctionFacts(byAlias: true);

    private static IReadOnlyDictionary<string, MathCallableFacts> CreateMathFunctionFacts(bool byAlias)
    {
        var facts = new Dictionary<string, MathCallableFacts>(StringComparer.Ordinal);
        foreach (var member in MathMemberDescriptors)
        {
            if (member.Kind == MathMemberKind.Constant)
                continue;

            var spelledName = byAlias ? member.PreludeAlias : member.Name;
            facts[spelledName] = new MathCallableFacts(
                spelledName,
                canonicalKey: member.CanonicalQualifiedName,
                CallableSignature.FromAlgorithm(
                    spelledName,
                    CreateMathMemberAlgorithm(member, MathAlgorithmFlavor.SignatureOnly)));
        }

        return facts.ToFrozenDictionary(StringComparer.Ordinal);
    }

    public static IReadOnlyList<BuiltinDescriptor> AllBuiltins => Builtins;

    public static IReadOnlyList<string> BuiltinNames { get; } = Builtins
        .Select(static descriptor => descriptor.Name)
        .ToArray();

    /// <summary>
    /// The predefined lower-camel-case prelude aliases, one per Math member, in
    /// descriptor order. Derived from the SAME explicit metadata that drives
    /// prelude construction, host-operation reservation, detector exclusion,
    /// and tooling — never a second hand-maintained list.
    /// </summary>
    public static IReadOnlyList<string> MathAliasNames { get; } = Array.AsReadOnly(MathMemberDescriptors
        .Select(static member => member.PreludeAlias)
        .ToArray());

    public static IReadOnlyList<string> RuntimePreludeExtraNames { get; } = Array.AsReadOnly(
        new[] { MathModuleName }.Concat(MathAliasNames).ToArray());

    public static IReadOnlyList<string> SemanticPreludeExtraNames { get; } = Array.AsReadOnly(
        new[] { MathModuleName, "load" }.Concat(MathAliasNames).ToArray());

    public static IReadOnlyList<string> ParameterDetectorPreludeNames { get; } =
        Array.AsReadOnly(BuiltinNames.Concat(SemanticPreludeExtraNames).ToArray());

    /// <summary>
    /// Whether a semantic-prelude name also exists in the runtime prelude and
    /// can therefore participate in ordinary lexical dot-call fallback.
    /// Front-end-only <c>load</c> deliberately returns false.
    /// </summary>
    public static bool IsRuntimePreludeName(string name)
        => Builtins.Any(descriptor => descriptor.Name == name)
            || RuntimePreludeExtraNames.Contains(name, StringComparer.Ordinal);

    public static IReadOnlyList<MathMemberDescriptor> MathMembers => MathMemberDescriptors;

    /// <summary>
    /// The Math members keyed by their predefined prelude alias, derived from
    /// the SAME explicit per-member metadata as prelude construction — never a
    /// second hand-maintained map. Alias names are validated unique and
    /// disjoint from every canonical member name, builtin name, <c>Math</c>,
    /// and <c>load</c>, so an alias spelling identifies exactly one member.
    /// </summary>
    private static readonly IReadOnlyDictionary<string, MathMemberDescriptor> MathMembersByPreludeAlias =
        MathMemberDescriptors.ToFrozenDictionary(static member => member.PreludeAlias, StringComparer.Ordinal);

    /// <summary>
    /// Resolves a predefined prelude-alias spelling (<c>sin</c>, <c>pi</c>, ...)
    /// to its Math member descriptor. Covers constants and functions alike,
    /// unlike the function-only <see cref="TryGetMathAliasFacts"/>.
    /// Binding-neutral: the caller must first establish through ordinary
    /// resolution that the written name actually reaches the prelude alias.
    /// </summary>
    internal static bool TryGetMathMemberByPreludeAlias(string aliasName, out MathMemberDescriptor member)
        => MathMembersByPreludeAlias.TryGetValue(aliasName, out member);

    public static IReadOnlyList<string> MathMemberNames { get; } = Array.AsReadOnly(MathMemberDescriptors
        .Select(static member => member.Name)
        .ToArray());

    public static bool IsMathFunctionMember(string name)
        => MathFunctionFactsByCanonicalName.ContainsKey(name);

    /// <summary>
    /// Callable facts for the canonical <c>Math.X</c> spelling of a Math
    /// FUNCTION member. Constants yield no facts.
    /// </summary>
    internal static bool TryGetMathMemberFacts(
        string memberName,
        [System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out MathCallableFacts? facts)
        => MathFunctionFactsByCanonicalName.TryGetValue(memberName, out facts);

    /// <summary>
    /// Callable facts for the prelude-alias spelling (<c>sin</c>, <c>pow</c>,
    /// ...) of a Math FUNCTION member. The constant (<c>pi</c>) yields no
    /// facts. Binding-neutral: the caller must first establish through ordinary
    /// resolution that the written name actually reaches the prelude alias.
    /// </summary>
    internal static bool TryGetMathAliasFacts(
        string aliasName,
        [System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out MathCallableFacts? facts)
        => MathFunctionFactsByAliasName.TryGetValue(aliasName, out facts);

    public static bool TryGetBuiltinCallableSignature(
        string ownerName,
        string memberName,
        [System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out CallableSignature? signature)
    {
        if (ownerName == MathModuleName && TryGetMathMemberFacts(memberName, out var facts))
        {
            signature = facts.Signature;
            return true;
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
        var properties = new List<Property>(
            Builtins.Length + MathMemberDescriptors.Count + (includeLoad ? 2 : 1));
        foreach (var builtin in Builtins)
            properties.Add(new Property(builtin.Name, new Algorithm.Builtin(builtin.Id), IsPublic: true));

        if (includeLoad)
            properties.Add(new Property("load", CreateLoadAlgorithm(), IsPublic: true));

        properties.Add(new Property(MathModuleName, mathAlgorithm, IsPublic: true));

        // Each Math member is also visible through ONE predefined lower-camel-case
        // prelude alias (`pi`, `sin`, ...). An alias is an ordinary synthetic
        // prelude property whose value IS the canonical member's algorithm
        // instance from THIS prelude flavor — the same object, never a duplicate
        // constant, native call, or forwarding wrapper — so runtime dispatch,
        // callee identity, and tooling signatures can never drift from `Math.X`.
        // The alias and canonical member remain distinct ordinary PROPERTY
        // bindings, so the evaluator's existing per-binding zero-argument cache
        // keys and the property-style `A` versus explicit-call `A()` distinction
        // apply without an alias-specific cache rule.
        // Sharing is safe because every Math member algorithm is CLOSED: parentless
        // and closed over only its declared parameters and constant/native output.
        // Ordinary ownership-first lookup provides every shadowing rule unchanged;
        // `Math` itself keeps only canonical PascalCase members.
        var mathPropertiesByName = mathAlgorithm.Properties.ToDictionary(
            static property => property.Name,
            StringComparer.Ordinal);
        foreach (var member in MathMemberDescriptors)
        {
            if (!mathPropertiesByName.TryGetValue(member.Name, out var canonicalProperty))
                throw new InvalidOperationException(
                    $"The supplied Math algorithm is missing canonical member '{member.Name}', required by prelude alias '{member.PreludeAlias}'.");

            properties.Add(new Property(member.PreludeAlias, canonicalProperty.Value, IsPublic: true));
        }

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
        return new(id, parameterNames.Length, parameters, parameters.Skip(1).ToArray());
    }

    private static BuiltinDescriptor Loop(BuiltinId id, params string[] fixedParameterNames)
    {
        var runtimeParameters = fixedParameterNames
            .Append("initialState")
            .Select(static name => new CallableParameter(name, Source: CallableParameterSource.Builtin))
            .ToArray();
        var toolingParameters = fixedParameterNames
            .Select(static name => new CallableParameter(name, Source: CallableParameterSource.Builtin))
            .Append(new CallableParameter(
                "init",
                ParameterKind.Collecting,
                CallableParameterSource.Builtin))
            .ToArray();

        return new(
            id,
            runtimeParameters.Length,
            runtimeParameters,
            runtimeParameters.Skip(1).ToArray(),
            toolingPlainParameters: toolingParameters,
            toolingDotParameters: toolingParameters.Skip(1).ToArray());
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
