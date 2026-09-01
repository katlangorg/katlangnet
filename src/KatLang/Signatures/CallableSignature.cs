namespace KatLang;

public enum CallableParameterSource
{
    Explicit,
    Implicit,
    Builtin,
    Synthetic,
}

public sealed record CallableParameter(
    string Name,
    ParameterKind Kind = ParameterKind.Normal,
    CallableParameterSource Source = CallableParameterSource.Explicit,
    ParameterPattern? DeclaringPattern = null)
{
    public string DisplayName => Kind switch
    {
        ParameterKind.Collecting => $"*{Name}",
        _ => Name,
    };
}

public sealed record CallableSignature
{
    public CallableSignature(string name, IReadOnlyList<CallableParameter> parameters)
        : this(
            name,
            CreateFlatParameterPatterns(parameters),
            parameters,
            hasExplicitParameterList: false,
            displayText: null)
    {
    }

    private CallableSignature(
        string name,
        IReadOnlyList<ParameterPattern> parameterPatterns,
        IReadOnlyList<CallableParameter> parameters,
        bool hasExplicitParameterList,
        string? displayText)
    {
        Name = name;
        ParameterPatterns = parameterPatterns.ToArray();
        Parameters = parameters.ToArray();
        HasExplicitParameterList = hasExplicitParameterList;
        ParameterNames = Parameters.Select(static parameter => parameter.Name).ToArray();
        DisplayText = displayText ?? FormatDisplayText(Name, ParameterPatterns);
    }

    public string Name { get; }

    public IReadOnlyList<ParameterPattern> ParameterPatterns { get; }

    public IReadOnlyList<CallableParameter> Parameters { get; }

    public IReadOnlyList<string> ParameterNames { get; }

    public bool HasExplicitParameterList { get; }

    public string DisplayText { get; }

    public int TopLevelParameterCount => ParameterPatterns.Count;

    public int FlattenedParameterCount => Parameters.Count;

    public bool HasSequenceValueParameterPattern => ParameterPatterns.Any(ContainsSequenceValuePattern);

    public CallableArityFacts ArityFacts => CallableSignatureDiagnostics.GetArityFacts(this);

    /// <summary>
    /// Gets the structural count of top-level parameter patterns.
    /// Retained for source and binary compatibility; callable minimum arity is
    /// exposed by <see cref="CallableArityFacts.MinTopLevelArgumentCount"/>.
    /// </summary>
    [Obsolete("Use TopLevelParameterCount for structural shape or ArityFacts.MinTopLevelArgumentCount for callable minimum arity.")]
    public int RequiredNormalParameterCount => ParameterPatterns.Count;

    public int CollectingParameterCount => ArityFacts.TopLevelCollectingCount;

    public bool HasAtMostOneCollectingParameter => !ArityFacts.HasMultipleTopLevelCollectingCaptures;

    public int CollectingParameterIndex => CallableSignatureDiagnostics.TopLevelCollectingIndex(this);

    public bool HasCollectingParameter => CollectingParameterIndex >= 0;

    public bool AcceptsItemCount(int itemCount)
        => ArityFacts.AcceptsArgumentCount(itemCount);

    public static CallableSignature FromAlgorithm(string name, Algorithm algorithm)
        => algorithm switch
        {
            Algorithm.User user => FromUserAlgorithm(name, user),
            Algorithm.Builtin(var builtin) => FromBuiltin(builtin),
            _ => new CallableSignature(name, []),
        };

    public static CallableSignature FromBuiltin(BuiltinId builtin)
        => FromBuiltin(builtin, BuiltinCallStyle.Plain);

    internal static CallableSignature FromBuiltin(BuiltinId builtin, BuiltinCallStyle callStyle)
        => BuiltinRegistry.GetBuiltin(builtin).GetSignature(callStyle);

    internal static CallableSignature FromUserAlgorithm(
        string name,
        Algorithm.User algorithm,
        CallableParameterSource? sourceOverride = null)
    {
        var hasExplicitParameterList = algorithm.ExplicitParameterPatterns.Count > 0;
        var parameterPatterns = hasExplicitParameterList
            ? algorithm.ExplicitParameterPatterns
            : algorithm.ParameterPatterns;
        var source = sourceOverride
            ?? (hasExplicitParameterList ? CallableParameterSource.Explicit : CallableParameterSource.Implicit);
        var parameters = CreateParameters(parameterPatterns, source);

        return new CallableSignature(
            name,
            parameterPatterns,
            parameters,
            hasExplicitParameterList,
            FormatDisplayText(name, parameterPatterns));
    }

    internal static CallableSignature FromParameterDeclarations(
        string name,
        IReadOnlyList<ParameterDeclaration> parameters,
        CallableParameterSource source)
    {
        var callableParameters = parameters
            .Select(parameter => new CallableParameter(parameter.Name, parameter.Kind, source, parameter.ToPattern()))
            .ToArray();
        return new CallableSignature(name, callableParameters);
    }

    public static string FormatDisplayText(string name, IEnumerable<string> parameterDisplayNames)
    {
        var displayNames = parameterDisplayNames.ToArray();
        return displayNames.Length == 0
            ? name
            : $"{name}({string.Join(", ", displayNames)})";
    }

    public string? ValidateMessage()
    {
        if (!HasAtMostOneCollectingParameter)
            return CallableSignatureDiagnostics.FormatMultipleTopLevelCollectingCaptures(this);

        var seen = new HashSet<string>(StringComparer.Ordinal);
        foreach (var parameter in Parameters)
        {
            if (parameter.Name.Length == 0)
                return $"Callable signature `{Name}` contains an empty parameter name.";

            if (!IsIdentifierLike(parameter.Name))
                return $"Callable signature `{Name}` contains invalid parameter name `{parameter.Name}`.";

            if (!seen.Add(parameter.Name))
                return $"Callable signature `{Name}` contains duplicate parameter name `{parameter.Name}`.";
        }

        return null;
    }

    public EvalError? Validate()
        => ValidateMessage() is { } message ? new EvalError.IllegalInEval(message) : null;

    public void ValidateOrThrow()
    {
        if (ValidateMessage() is { } message)
            throw new InvalidOperationException(message);
    }

    private static string FormatDisplayText(string name, IReadOnlyList<ParameterPattern> parameterPatterns)
        => FormatDisplayText(name, parameterPatterns.Select(static parameter => parameter.DisplayName));

    private static IReadOnlyList<ParameterPattern> CreateFlatParameterPatterns(IReadOnlyList<CallableParameter> parameters)
        => parameters
            .Select(static parameter => (ParameterPattern)new CaptureParameterPattern(parameter.Name, Kind: parameter.Kind))
            .ToArray();

    private static IReadOnlyList<CallableParameter> CreateParameters(
        IReadOnlyList<ParameterPattern> parameterPatterns,
        CallableParameterSource source)
    {
        var parameters = new List<CallableParameter>();
        foreach (var parameterPattern in parameterPatterns)
            AddParameters(parameterPattern, source, parameters);
        return parameters;
    }

    private static void AddParameters(
        ParameterPattern parameterPattern,
        CallableParameterSource source,
        ICollection<CallableParameter> parameters)
    {
        switch (parameterPattern)
        {
            case CaptureParameterPattern capture:
                parameters.Add(new CallableParameter(capture.Name, capture.Kind, source, capture));
                break;
            case SequenceValueParameterPattern sequenceValue:
                foreach (var item in sequenceValue.Items)
                    AddParameters(item, source, parameters);
                break;
            default:
                throw new InvalidOperationException("Unknown parameter pattern.");
        }
    }

    private static bool ContainsSequenceValuePattern(ParameterPattern parameterPattern)
        => parameterPattern switch
        {
            SequenceValueParameterPattern => true,
            _ => false,
        };

    /// <summary>
    /// Whether <paramref name="name"/> is identifier-SHAPED under the lexer's one
    /// identifier character policy, with DELIBERATELY no reserved-keyword
    /// exclusion — this mirrors Lean <c>callableParameterNameIsIdentifierLike</c>,
    /// which validates parameter names inside the modeled call binder
    /// (<c>bindCallableArguments</c>). Keywords are a surface-syntax concept the
    /// Lean model does not have, so a keyword spelling such as <c>open</c> stays a
    /// structurally valid parameter name for a host-built AST (parsed source can
    /// never produce one — the lexer refuses to lex it as an identifier). Names
    /// that must be writable in source (host operations, builtin metadata) are
    /// validated with the stricter <see cref="Lexer.IsValidIdentifier"/> instead.
    /// Model boundary: when this validation is reached (currently through the
    /// flat-collecting loop-step binder), Lean's <c>Char.isAlpha</c>/
    /// <c>isAlphanum</c> are ASCII-only while the shipped rule is the lexer's
    /// Unicode per-UTF-16-code-unit rule; the two agree on the ASCII subdomain
    /// (see the identifier row in SEMANTIC-ALIGNMENT.md). This says nothing
    /// about ordinary property/resolve names, which are stored as strings.
    /// </summary>
    private static bool IsIdentifierLike(string name)
        => Lexer.IsIdentifierShaped(name);
}
