namespace KatLang;

internal enum CallableParameterSource
{
    Explicit,
    Implicit,
    Builtin,
    Synthetic,
}

internal sealed record CallableParameter(
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

internal sealed record CallableSignature
{
    // FE-3: the facts DERIVED from the stored patterns (the flat parameter list, the names, the display
    // text, the arity facts) are computed on first read instead of eagerly per signature: implicit
    // lifting builds one signature per owner (and the evaluator one per call), and K owners sharing an
    // L-wide template must not each allocate L parameters, L names, and an L-wide display string. The
    // cache is carried in an equality-transparent slot, so record equality stays that of the stored
    // inputs (name, pattern list, explicit-list bit); every property is get-only, so a `with` copy is
    // identical and may share it.
    private readonly RuntimeStateSlot<DerivedFacts> _derived;

    public CallableSignature(string name, IReadOnlyList<CallableParameter> parameters)
        : this(
            name,
            CreateFlatParameterPatterns(parameters),
            parameters,
            parameterSource: null,
            hasExplicitParameterList: false,
            displayText: null)
    {
    }

    private CallableSignature(
        string name,
        IReadOnlyList<ParameterPattern> parameterPatterns,
        IReadOnlyList<CallableParameter>? parameters,
        CallableParameterSource? parameterSource,
        bool hasExplicitParameterList,
        string? displayText)
    {
        Name = name;
        // A shared implicit-signature template is immutable: it is kept by reference (with its
        // cached facts) instead of being copied per signature. Any other list is caller-owned and
        // snapshotted exactly as before.
        ParameterPatterns = parameterPatterns is ImplicitSignatureTemplate template
            ? template
            : parameterPatterns.ToArray();
        HasExplicitParameterList = hasExplicitParameterList;
        _derived = new(new DerivedFacts(parameters?.ToArray(), parameterSource, displayText));
    }

    public string Name { get; }

    public IReadOnlyList<ParameterPattern> ParameterPatterns { get; }

    public IReadOnlyList<CallableParameter> Parameters => _derived.Value.Parameters(this);

    public IReadOnlyList<string> ParameterNames => _derived.Value.ParameterNames(this);

    public bool HasExplicitParameterList { get; }

    public string DisplayText => _derived.Value.DisplayText(this);

    public int TopLevelParameterCount => ParameterPatterns.Count;

    /// <summary>The flattened capture count, without materializing <see cref="Parameters"/>.</summary>
    public int FlattenedParameterCount => _derived.Value.FlattenedParameterCount(this);

    public bool HasSequenceValueParameterPattern => ParameterPatterns.Any(ContainsSequenceValuePattern);

    public CallableArityFacts ArityFacts => _derived.Value.ArityFacts(this);

    /// <summary>
    /// The lazily derived facts of one signature, published atomically (a signature may be read
    /// concurrently — the builtin registry's are process-wide). Each is a pure function of the
    /// signature's stored inputs, so racing initializers compute equal values.
    /// </summary>
    private sealed class DerivedFacts(
        CallableParameter[]? parameters,
        CallableParameterSource? parameterSource,
        string? displayText)
    {
        private IReadOnlyList<CallableParameter>? _parameters = parameters;
        private IReadOnlyList<string>? _parameterNames;
        private string? _displayText = displayText;
        private CallableArityFacts? _arityFacts;

        public IReadOnlyList<CallableParameter> Parameters(CallableSignature signature)
        {
            var computed = Volatile.Read(ref _parameters);
            if (computed is not null)
                return computed;
            var source = parameterSource ?? CallableParameterSource.Explicit;
            computed = signature.ParameterPatterns is ImplicitSignatureTemplate template
                ? template.Facts.CallableParameters(source)
                : CreateParameters(signature.ParameterPatterns, source);
            return Interlocked.CompareExchange(ref _parameters, computed, null) ?? computed;
        }

        public IReadOnlyList<string> ParameterNames(CallableSignature signature)
        {
            var computed = Volatile.Read(ref _parameterNames);
            if (computed is not null)
                return computed;
            computed = signature.ParameterPatterns is ImplicitSignatureTemplate template
                ? template.Facts.Names
                : Parameters(signature).Select(static parameter => parameter.Name).ToArray();
            return Interlocked.CompareExchange(ref _parameterNames, computed, null) ?? computed;
        }

        public string DisplayText(CallableSignature signature)
        {
            var computed = Volatile.Read(ref _displayText);
            if (computed is not null)
                return computed;
            computed = FormatDisplayText(signature.Name, signature.ParameterPatterns);
            return Interlocked.CompareExchange(ref _displayText, computed, null) ?? computed;
        }

        public int FlattenedParameterCount(CallableSignature signature)
            => Volatile.Read(ref _parameters)?.Count
                ?? (signature.ParameterPatterns is ImplicitSignatureTemplate template
                    ? template.Facts.CaptureCount
                    : ParameterPattern.CountCaptures(signature.ParameterPatterns));

        public CallableArityFacts ArityFacts(CallableSignature signature)
        {
            var computed = Volatile.Read(ref _arityFacts);
            if (computed is not null)
                return computed;
            computed = CallableSignatureDiagnostics.GetArityFacts(signature);
            return Interlocked.CompareExchange(ref _arityFacts, computed, null) ?? computed;
        }
    }

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
            Algorithm.Conditional => new CallableSignature(name, []),
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
        // The ONE stored parameter channel is the signature; whether it was WRITTEN (a closed
        // explicit list) or inferred decides only how its parameters are classified.
        var hasExplicitParameterList = algorithm.HasExplicitParameterList;
        var source = sourceOverride
            ?? (hasExplicitParameterList ? CallableParameterSource.Explicit : CallableParameterSource.Implicit);

        // The flat parameters, names, and display text derive from the stored patterns on first
        // read (a shared template serves them from its facts), never eagerly per signature.
        return new CallableSignature(
            name,
            algorithm.ParameterPatterns,
            parameters: null,
            parameterSource: source,
            hasExplicitParameterList,
            displayText: null);
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

    internal static IReadOnlyList<CallableParameter> CreateParameters(
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
            CaptureParameterPattern => false,
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
