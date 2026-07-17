namespace KatLang;

public sealed record CallableBindingPlan
{
    private CallableBindingPlan(
        CallableSignature signature,
        PatternListBindingPlan topLevelPatternList,
        IReadOnlyList<CallableBindingCapture> captures,
        CallableArityFacts arityFacts)
    {
        Signature = signature;
        TopLevelPatternList = topLevelPatternList;
        Captures = captures.ToArray();
        ArityFacts = arityFacts;
    }

    public CallableSignature Signature { get; }

    public PatternListBindingPlan TopLevelPatternList { get; }

    public IReadOnlyList<CallableBindingCapture> Captures { get; }

    public CallableArityFacts ArityFacts { get; }

    public string DisplayText => Signature.DisplayText;

    public bool RequiresPatternedBinding => !HasOnlyFlatTopLevelCaptures || HasRepeatedCaptureNames;

    public bool HasRepeatedCaptureNames
        => Captures
            .GroupBy(static capture => capture.Name, StringComparer.Ordinal)
            .Any(static captures => captures.Skip(1).Any());

    public bool HasOnlyFlatTopLevelCaptures
        => TopLevelPatternList.Nodes.All(static node => node is CaptureBindingNode or VariadicCaptureBindingNode { IsTopLevel: true });

    public bool HasOnlyFlatFixedTopLevelCaptures
        => TopLevelPatternList.Nodes.All(static node => node is CaptureBindingNode);

    public bool HasTopLevelVariadic => TopLevelPatternList.HasVariadicAtThisLevel;

    public bool HasNestedVariadic => TopLevelPatternList.HasVariadicInDescendants;

    public VariadicCaptureBindingNode? TopLevelVariadicCapture => TopLevelPatternList.VariadicCapture;

    public bool TryGetFlatFixedLayout(out IReadOnlyList<CaptureBindingNode> captures)
    {
        if (RequiresPatternedBinding || !HasOnlyFlatFixedTopLevelCaptures)
        {
            captures = [];
            return false;
        }

        captures = TopLevelPatternList.Nodes.Cast<CaptureBindingNode>().ToArray();
        return true;
    }

    public bool TryGetFlatVariadicLayout(
        out IReadOnlyList<CaptureBindingNode> prefix,
        out VariadicCaptureBindingNode variadic,
        out IReadOnlyList<CaptureBindingNode> suffix)
    {
        prefix = [];
        variadic = null!;
        suffix = [];

        if (RequiresPatternedBinding || !HasOnlyFlatTopLevelCaptures || TopLevelVariadicCapture is not { } topLevelVariadic)
            return false;

        if (!TryCastCaptures(TopLevelPatternList.Prefix, out var prefixCaptures)
            || !TryCastCaptures(TopLevelPatternList.Suffix, out var suffixCaptures))
        {
            return false;
        }

        prefix = prefixCaptures;
        variadic = topLevelVariadic;
        suffix = suffixCaptures;
        return true;
    }

    public static CallableBindingPlan FromSignature(CallableSignature signature)
    {
        ArgumentNullException.ThrowIfNull(signature);

        var parameters = new Queue<CallableParameter>(signature.Parameters);
        var topLevelPatternList = PatternListBindingPlan.FromParameterPatterns(
            signature.ParameterPatterns,
            parameters,
            isTopLevel: true);

        if (parameters.Count != 0)
            throw new InvalidOperationException($"Callable signature `{signature.DisplayText}` contains capture metadata that is not represented by its parameter patterns.");

        var arityFacts = CallableSignatureDiagnostics.GetArityFacts(signature);
        if (arityFacts != topLevelPatternList.ToTopLevelArityFacts())
            throw new InvalidOperationException($"Callable binding plan arity facts do not match signature `{signature.DisplayText}`.");

        return new CallableBindingPlan(
            signature,
            topLevelPatternList,
            topLevelPatternList.Captures,
            arityFacts);
    }

    private static bool TryCastCaptures(
        IReadOnlyList<CallableBindingNode> nodes,
        out IReadOnlyList<CaptureBindingNode> captures)
    {
        var result = new List<CaptureBindingNode>(nodes.Count);
        foreach (var node in nodes)
        {
            if (node is not CaptureBindingNode capture)
            {
                captures = [];
                return false;
            }

            result.Add(capture);
        }

        captures = result.ToArray();
        return true;
    }
}

public sealed record PatternListBindingPlan
{
    private PatternListBindingPlan(
        IReadOnlyList<CallableBindingNode> nodes,
        IReadOnlyList<CallableBindingNode> prefix,
        VariadicCaptureBindingNode? variadicCapture,
        IReadOnlyList<CallableBindingNode> suffix,
        int minSlotCount,
        int? maxSlotCount,
        int variadicCountAtThisLevel)
    {
        Nodes = nodes.ToArray();
        Prefix = prefix.ToArray();
        VariadicCapture = variadicCapture;
        Suffix = suffix.ToArray();
        MinSlotCount = minSlotCount;
        MaxSlotCount = maxSlotCount;
        VariadicCountAtThisLevel = variadicCountAtThisLevel;
        Captures = Nodes.SelectMany(static node => node.Captures).ToArray();
        HasVariadicInDescendants = Nodes.OfType<SequenceValueBindingNode>()
            .Any(static group => group.Children.HasVariadicAtThisLevel || group.Children.HasVariadicInDescendants);
    }

    public IReadOnlyList<CallableBindingNode> Nodes { get; }

    public IReadOnlyList<CallableBindingNode> Prefix { get; }

    public VariadicCaptureBindingNode? VariadicCapture { get; }

    public IReadOnlyList<CallableBindingNode> Suffix { get; }

    public int MinSlotCount { get; }

    public int? MaxSlotCount { get; }

    public bool HasVariadicAtThisLevel => VariadicCapture is not null;

    public int VariadicCountAtThisLevel { get; }

    public bool HasVariadicInDescendants { get; }

    public IReadOnlyList<CallableBindingCapture> Captures { get; }

    internal static PatternListBindingPlan FromParameterPatterns(
        IReadOnlyList<ParameterPattern> parameterPatterns,
        Queue<CallableParameter> parameters,
        bool isTopLevel)
    {
        var nodes = new List<CallableBindingNode>(parameterPatterns.Count);
        var variadicIndex = -1;
        var variadicCount = 0;

        for (var index = 0; index < parameterPatterns.Count; index++)
        {
            var node = CreateNode(parameterPatterns[index], parameters, isTopLevel);
            nodes.Add(node);

            if (node is not VariadicCaptureBindingNode)
                continue;

            variadicCount++;
            if (variadicIndex >= 0)
                throw new InvalidOperationException("Callable binding plans cannot contain more than one variadic capture at the same pattern-list level.");

            variadicIndex = index;
        }

        IReadOnlyList<CallableBindingNode> prefix;
        VariadicCaptureBindingNode? variadicCapture;
        IReadOnlyList<CallableBindingNode> suffix;

        if (variadicIndex >= 0)
        {
            prefix = nodes.Take(variadicIndex).ToArray();
            variadicCapture = (VariadicCaptureBindingNode)nodes[variadicIndex];
            suffix = nodes.Skip(variadicIndex + 1).ToArray();
        }
        else
        {
            prefix = nodes.ToArray();
            variadicCapture = null;
            suffix = [];
        }

        // Mirror CallableSignatureDiagnostics.GetArityFacts: a top-level list with one or
        // more plain captures and one rest (rest-only or comma deconstruction) accepts the
        // fixed captures plus any number of rest items, so it has a fixed-count minimum
        // and an unbounded maximum. Collection builtins have fixed signatures and do not
        // enter this pattern-list branch.
        var isItemSupplyShape = isTopLevel
            && variadicCount == 1
            && nodes.Count >= 1
            && nodes.All(static node => node is CaptureBindingNode or VariadicCaptureBindingNode);

        var minSlotCount = isItemSupplyShape ? nodes.Count - 1 : nodes.Count;
        int? maxSlotCount = isItemSupplyShape ? null : nodes.Count;

        return new PatternListBindingPlan(
            nodes,
            prefix,
            variadicCapture,
            suffix,
            minSlotCount,
            maxSlotCount,
            variadicCount);
    }

    internal CallableArityFacts ToTopLevelArityFacts()
        => new(
            MinSlotCount,
            MaxSlotCount,
            HasVariadicAtThisLevel,
            VariadicCountAtThisLevel);

    private static CallableBindingNode CreateNode(
        ParameterPattern parameterPattern,
        Queue<CallableParameter> parameters,
        bool isTopLevel)
        => parameterPattern switch
        {
            CaptureParameterPattern capture => CreateCaptureNode(capture, parameters, isTopLevel),
            SequenceValueParameterPattern group => new SequenceValueBindingNode(FromParameterPatterns(group.Items, parameters, isTopLevel: false)),
            _ => throw new InvalidOperationException("Unknown callable parameter pattern."),
        };

    private static CallableBindingNode CreateCaptureNode(
        CaptureParameterPattern capture,
        Queue<CallableParameter> parameters,
        bool isTopLevel)
    {
        if (!parameters.TryDequeue(out var parameter))
            throw new InvalidOperationException($"Callable binding plan capture `{capture.DisplayName}` has no matching callable parameter metadata.");

        if (!string.Equals(parameter.Name, capture.Name, StringComparison.Ordinal) || parameter.Kind != capture.Kind)
            throw new InvalidOperationException($"Callable binding plan capture `{capture.DisplayName}` does not match callable parameter metadata `{parameter.DisplayName}`.");

        var bindingCapture = new CallableBindingCapture(
            capture.Name,
            capture.Kind,
            parameter.Source);

        return capture.Kind == ParameterKind.Variadic
            ? new VariadicCaptureBindingNode(bindingCapture, isTopLevel)
            : new CaptureBindingNode(bindingCapture);
    }
}

public sealed record CallableBindingCapture(
    string Name,
    ParameterKind Kind,
    CallableParameterSource Source)
{
    public string DisplayName => Kind == ParameterKind.Variadic ? $"{Name}..." : Name;
}

public abstract record CallableBindingNode
{
    private protected CallableBindingNode() { }

    public abstract IReadOnlyList<CallableBindingCapture> Captures { get; }
}

public sealed record CaptureBindingNode(CallableBindingCapture Capture) : CallableBindingNode
{
    public string Name => Capture.Name;

    public ParameterKind Kind => Capture.Kind;

    public CallableParameterSource Source => Capture.Source;

    public override IReadOnlyList<CallableBindingCapture> Captures { get; } = [Capture];
}

public sealed record VariadicCaptureBindingNode(CallableBindingCapture Capture, bool IsTopLevel) : CallableBindingNode
{
    public string Name => Capture.Name;

    public ParameterKind Kind => Capture.Kind;

    public CallableParameterSource Source => Capture.Source;

    public override IReadOnlyList<CallableBindingCapture> Captures { get; } = [Capture];
}

public sealed record SequenceValueBindingNode(PatternListBindingPlan Children) : CallableBindingNode
{
    public override IReadOnlyList<CallableBindingCapture> Captures => Children.Captures;
}
