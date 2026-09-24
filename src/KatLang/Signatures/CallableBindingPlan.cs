namespace KatLang;

internal sealed record CallableBindingPlan
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
        => TopLevelPatternList.Nodes.All(static node => node is CaptureBindingNode or CollectingCaptureBindingNode { IsTopLevel: true });

    public bool HasOnlyFlatFixedTopLevelCaptures
        => TopLevelPatternList.Nodes.All(static node => node is CaptureBindingNode);

    public bool HasTopLevelCollecting => TopLevelPatternList.HasCollectingAtThisLevel;

    public bool HasNestedCollecting => TopLevelPatternList.HasCollectingInDescendants;

    public CollectingCaptureBindingNode? TopLevelCollectingCapture => TopLevelPatternList.CollectingCapture;

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

    public bool TryGetFlatCollectingLayout(
        out IReadOnlyList<CaptureBindingNode> prefix,
        out CollectingCaptureBindingNode collecting,
        out IReadOnlyList<CaptureBindingNode> suffix)
    {
        prefix = [];
        collecting = null!;
        suffix = [];

        if (RequiresPatternedBinding || !HasOnlyFlatTopLevelCaptures || TopLevelCollectingCapture is not { } topLevelCollecting)
            return false;

        if (!TryCastCaptures(TopLevelPatternList.Prefix, out var prefixCaptures)
            || !TryCastCaptures(TopLevelPatternList.Suffix, out var suffixCaptures))
        {
            return false;
        }

        prefix = prefixCaptures;
        collecting = topLevelCollecting;
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

internal sealed record PatternListBindingPlan
{
    private PatternListBindingPlan(
        IReadOnlyList<CallableBindingNode> nodes,
        IReadOnlyList<CallableBindingNode> prefix,
        CollectingCaptureBindingNode? collectingCapture,
        IReadOnlyList<CallableBindingNode> suffix,
        int minSlotCount,
        int? maxSlotCount,
        int collectingCountAtThisLevel)
    {
        Nodes = nodes.ToArray();
        Prefix = prefix.ToArray();
        CollectingCapture = collectingCapture;
        Suffix = suffix.ToArray();
        MinSlotCount = minSlotCount;
        MaxSlotCount = maxSlotCount;
        CollectingCountAtThisLevel = collectingCountAtThisLevel;
        Captures = Nodes.SelectMany(static node => node.Captures).ToArray();
        HasCollectingInDescendants = Nodes.OfType<SequenceValueBindingNode>()
            .Any(static group => group.Children.HasCollectingAtThisLevel || group.Children.HasCollectingInDescendants);
    }

    public IReadOnlyList<CallableBindingNode> Nodes { get; }

    public IReadOnlyList<CallableBindingNode> Prefix { get; }

    public CollectingCaptureBindingNode? CollectingCapture { get; }

    public IReadOnlyList<CallableBindingNode> Suffix { get; }

    /// <summary>
    /// The MINIMUM number of supplied slots this pattern level accepts, decided at THIS
    /// level alone by the binder's own rule
    /// (<see cref="ParameterPattern.MinimumSuppliedSlots"/>): one slot per pattern, minus one
    /// when this level holds a collecting capture. Nested captures are never flattened into
    /// it: <c>P((x, *r))</c> declares ONE top-level pattern, so the top level is exactly one
    /// slot while the group's own level is one slot or more.
    /// </summary>
    public int MinSlotCount { get; }

    /// <summary>
    /// The MAXIMUM number of supplied slots this pattern level accepts: <c>null</c>
    /// (unbounded) when this level holds a collecting capture — whatever else the level
    /// contains, a grouped pattern included — otherwise the exact pattern count.
    /// </summary>
    public int? MaxSlotCount { get; }

    public bool HasCollectingAtThisLevel => CollectingCapture is not null;

    public int CollectingCountAtThisLevel { get; }

    public bool HasCollectingInDescendants { get; }

    public IReadOnlyList<CallableBindingCapture> Captures { get; }

    internal static PatternListBindingPlan FromParameterPatterns(
        IReadOnlyList<ParameterPattern> parameterPatterns,
        Queue<CallableParameter> parameters,
        bool isTopLevel)
    {
        var nodes = new List<CallableBindingNode>(parameterPatterns.Count);
        var collectingIndex = -1;
        var collectingCount = 0;

        for (var index = 0; index < parameterPatterns.Count; index++)
        {
            var node = CreateNode(parameterPatterns[index], parameters, isTopLevel);
            nodes.Add(node);

            if (node is not CollectingCaptureBindingNode)
                continue;

            collectingCount++;
            if (collectingIndex >= 0)
                throw new InvalidOperationException("Callable binding plans cannot contain more than one collecting capture at the same pattern-list level.");

            collectingIndex = index;
        }

        IReadOnlyList<CallableBindingNode> prefix;
        CollectingCaptureBindingNode? collectingCapture;
        IReadOnlyList<CallableBindingNode> suffix;

        if (collectingIndex >= 0)
        {
            prefix = nodes.Take(collectingIndex).ToArray();
            collectingCapture = (CollectingCaptureBindingNode)nodes[collectingIndex];
            suffix = nodes.Skip(collectingIndex + 1).ToArray();
        }
        else
        {
            prefix = nodes.ToArray();
            collectingCapture = null;
            suffix = [];
        }

        // The ONE per-level arity rule, the same one the binder applies at this level
        // (ParameterPattern.MinimumSuppliedSlots, read by BindParameterPatternList itself):
        // every pattern here consumes ONE supplied slot whatever it contains — a
        // sequence-value group is one slot the binder opens afterwards — and a COLLECTING
        // capture here consumes NONE and lifts the upper bound. The decision is LEVEL-LOCAL:
        // `isTopLevel` classifies the collecting NODE, never the arity, nested captures are
        // never flattened into this level's counts, and a grouped pattern beside a collector
        // does not make the collector fixed. So `G((a, b), *rest)` is min 1 / unbounded at the
        // top level, and the nested list of `P((x, *r))` is min 1 / unbounded while `P` itself
        // stays min 1 / max 1. Collection builtins are flat fixed lists and take the exact arm.
        var minSlotCount = ParameterPattern.MinimumSuppliedSlots(parameterPatterns);
        int? maxSlotCount = collectingIndex >= 0 ? null : nodes.Count;

        return new PatternListBindingPlan(
            nodes,
            prefix,
            collectingCapture,
            suffix,
            minSlotCount,
            maxSlotCount,
            collectingCount);
    }

    /// <summary>
    /// This level's arity facts. Applied by <see cref="CallableBindingPlan.FromSignature"/>
    /// to the TOP-LEVEL list, where it must equal
    /// <see cref="CallableSignatureDiagnostics.GetArityFacts"/> — both state the same
    /// per-level binder rule, so a divergence is a defect and fails loudly there.
    /// </summary>
    internal CallableArityFacts ToTopLevelArityFacts()
        => new(
            MinSlotCount,
            MaxSlotCount,
            HasCollectingAtThisLevel,
            CollectingCountAtThisLevel);

    private static CallableBindingNode CreateNode(
        ParameterPattern parameterPattern,
        Queue<CallableParameter> parameters,
        bool isTopLevel)
        => parameterPattern switch
        {
            CaptureParameterPattern capture => CreateCaptureNode(capture, parameters, isTopLevel),
            SequenceValueParameterPattern group => new SequenceValueBindingNode(FromParameterPatterns(group.Items, parameters, isTopLevel: false)),
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

        return capture.Kind == ParameterKind.Collecting
            ? new CollectingCaptureBindingNode(bindingCapture, isTopLevel)
            : new CaptureBindingNode(bindingCapture);
    }
}

internal sealed record CallableBindingCapture(
    string Name,
    ParameterKind Kind,
    CallableParameterSource Source)
{
    public string DisplayName => Kind == ParameterKind.Collecting ? $"*{Name}" : Name;
}

/// <summary>
/// One node of a callable's binding plan. A C# <c>closed</c> hierarchy:
/// <see cref="CaptureBindingNode"/>, <see cref="CollectingCaptureBindingNode"/>, and
/// <see cref="SequenceValueBindingNode"/> (top-level records of this assembly) are its
/// only variants, no other assembly can derive from it, and a switch EXPRESSION naming
/// all three is compiler-exhaustive with no catch-all arm.
/// </summary>
internal closed record CallableBindingNode
{
    private protected CallableBindingNode() { }

    public abstract IReadOnlyList<CallableBindingCapture> Captures { get; }
}

internal sealed record CaptureBindingNode(CallableBindingCapture Capture) : CallableBindingNode
{
    public string Name => Capture.Name;

    public ParameterKind Kind => Capture.Kind;

    public CallableParameterSource Source => Capture.Source;

    public override IReadOnlyList<CallableBindingCapture> Captures { get; } = [Capture];
}

internal sealed record CollectingCaptureBindingNode(CallableBindingCapture Capture, bool IsTopLevel) : CallableBindingNode
{
    public string Name => Capture.Name;

    public ParameterKind Kind => Capture.Kind;

    public CallableParameterSource Source => Capture.Source;

    public override IReadOnlyList<CallableBindingCapture> Captures { get; } = [Capture];
}

internal sealed record SequenceValueBindingNode(PatternListBindingPlan Children) : CallableBindingNode
{
    public override IReadOnlyList<CallableBindingCapture> Captures => Children.Captures;
}
