namespace KatLang.Semantics;

/// <summary>
/// High-level semantic shape of a property.
/// </summary>
public enum PropertyShape
{
    Ordinary,
    Conditional,
    Builtin,
}

/// <summary>
/// Editor-facing callable surface for a property signature.
/// </summary>
public enum PropertyCallStyle
{
    Plain,
    Dot,
}

/// <summary>
/// Editor-facing classification of one callable property parameter slot.
/// </summary>
public enum PropertyParameterKind
{
    Explicit,
    Implicit,
    ConditionalBinder,
}

/// <summary>
/// Editor-facing metadata for one property parameter slot.
/// For builtins, spans are typically unavailable and remain <see langword="null"/>.
/// </summary>
public sealed record PropertyParameterInfo(string Name, PropertyParameterKind Kind, SourceSpan? Span)
{
    public bool IsCollecting { get; init; }

    public string? DisplayNameOverride { get; init; }

    public string DisplayName => DisplayNameOverride
        ?? (IsCollecting
            ? $"*{Name}"
            : Name);
}

/// <summary>
/// Editor-facing metadata for one callable signature surface.
/// </summary>
public sealed record PropertySignatureInfo
{
    // FE-3: the display text of a signature the semantic model builds for a property whose callable
    // shares a wide implicit-signature template is composed on first read instead of eagerly — the
    // owner name makes it owner-specific, and K owners of one L-wide template would otherwise each
    // hold an L-wide string nobody asked for. Held in an equality-transparent slot; equality below
    // compares the TEXT exactly as the synthesized record equality did.
    private readonly RuntimeStateSlot<Func<string>?> _composeDisplayText;
    private string? _displayText;

    public PropertySignatureInfo(
        PropertyCallStyle CallStyle,
        string DisplayText,
        IReadOnlyList<PropertyParameterInfo> Parameters)
    {
        this.CallStyle = CallStyle;
        _displayText = DisplayText;
        this.Parameters = Snapshot(Parameters);
    }

    /// <summary>A signature whose display text is composed on first read (see the field comment).</summary>
    internal PropertySignatureInfo(
        PropertyCallStyle callStyle,
        Func<string> composeDisplayText,
        IReadOnlyList<PropertyParameterInfo> parameters)
    {
        CallStyle = callStyle;
        _composeDisplayText = new(composeDisplayText);
        Parameters = Snapshot(parameters);
    }

    public PropertyCallStyle CallStyle { get; }

    public string DisplayText
    {
        get
        {
            var text = Volatile.Read(ref _displayText);
            if (text is not null)
                return text;
            text = _composeDisplayText.Value!();
            return Interlocked.CompareExchange(ref _displayText, text, null) ?? text;
        }
    }

    public IReadOnlyList<PropertyParameterInfo> Parameters { get; }

    /// <summary>Record equality over the signature's values (its display text read through, never its lazy state).</summary>
    public bool Equals(PropertySignatureInfo? other)
        => other is not null
            && (ReferenceEquals(this, other)
                || (CallStyle == other.CallStyle
                    && string.Equals(DisplayText, other.DisplayText, StringComparison.Ordinal)
                    && EqualityComparer<IReadOnlyList<PropertyParameterInfo>>.Default.Equals(Parameters, other.Parameters)));

    public override int GetHashCode()
        => HashCode.Combine(
            CallStyle,
            DisplayText,
            EqualityComparer<IReadOnlyList<PropertyParameterInfo>>.Default.GetHashCode(Parameters));

    private static IReadOnlyList<PropertyParameterInfo> Snapshot(
        IReadOnlyList<PropertyParameterInfo> parameters)
        => parameters.Count == 0
            ? Array.Empty<PropertyParameterInfo>()
            : parameters as SharedPropertyParameterList ?? Array.AsReadOnly(parameters.ToArray());
}

/// <summary>
/// FE-3: an immutable parameter-metadata list the semantic model builds ONCE for a shared
/// implicit-signature template and hands to every owner property over it. Its storage is private
/// to the library (no instance can be created, and no element replaced, outside it), so the
/// defensive snapshot copy the metadata records make of a caller-supplied list is skipped for it.
/// It is a <see cref="System.Collections.ObjectModel.ReadOnlyCollection{T}"/> exactly like the
/// snapshots the records store for every other list.
/// </summary>
internal sealed class SharedPropertyParameterList : System.Collections.ObjectModel.ReadOnlyCollection<PropertyParameterInfo>
{
    public SharedPropertyParameterList(PropertyParameterInfo[] parameters)
        : base(parameters)
    {
    }

    private SharedPropertyParameterList(IList<PropertyParameterInfo> parameters)
        : base(parameters)
    {
    }

    /// <summary>
    /// An owner-local head followed by a shared tail list, without copying the tail (a composed
    /// implicit signature's metadata costs its head).
    /// </summary>
    public static SharedPropertyParameterList Concat(PropertyParameterInfo[] head, SharedPropertyParameterList tail)
        => head.Length == 0 ? tail : new(new ConcatenatedParameters(head, tail));

    // Read-only IList over head ++ tail (ReadOnlyCollection wraps an IList; every mutator throws).
    private sealed class ConcatenatedParameters(PropertyParameterInfo[] head, SharedPropertyParameterList tail) : IList<PropertyParameterInfo>
    {
        public PropertyParameterInfo this[int index]
        {
            get => index < head.Length ? head[index] : tail[index - head.Length];
            set => throw new NotSupportedException();
        }

        public int Count => head.Length + tail.Count;

        public bool IsReadOnly => true;

        public bool Contains(PropertyParameterInfo item) => IndexOf(item) >= 0;

        public int IndexOf(PropertyParameterInfo item)
        {
            for (var i = 0; i < Count; i++)
            {
                if (EqualityComparer<PropertyParameterInfo>.Default.Equals(this[i], item))
                    return i;
            }

            return -1;
        }

        public void CopyTo(PropertyParameterInfo[] array, int arrayIndex)
        {
            head.CopyTo(array, arrayIndex);
            tail.CopyTo(array, arrayIndex + head.Length);
        }

        public IEnumerator<PropertyParameterInfo> GetEnumerator()
        {
            foreach (var item in head)
                yield return item;
            foreach (var item in tail)
                yield return item;
        }

        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();

        public void Add(PropertyParameterInfo item) => throw new NotSupportedException();

        public void Clear() => throw new NotSupportedException();

        public void Insert(int index, PropertyParameterInfo item) => throw new NotSupportedException();

        public bool Remove(PropertyParameterInfo item) => throw new NotSupportedException();

        public void RemoveAt(int index) => throw new NotSupportedException();
    }
}

/// <summary>
/// Editor-facing identity of the canonical qualified member behind a predefined
/// prelude alias. <see cref="QualifiedName"/> is the canonical structural
/// spelling (<c>Math.Sin</c>); <see cref="DisplaySignature"/> is that member's
/// declared signature in qualified form (<c>Math.Sin(radians)</c> — for a
/// constant just the qualified name, <c>Math.Pi</c>). Both derive from the same
/// registry metadata that constructs the prelude, so they can never drift from
/// the alias's own callable surface.
/// </summary>
public sealed record PropertyAliasTargetInfo(string QualifiedName, string DisplaySignature);

/// <summary>
/// Editor-facing summary of one conditional branch head.
/// <see cref="HeadSpan"/> is the best available source anchor for the branch
/// head. When the AST only preserves the declared property name span, that
/// exact declaration span is exposed here.
/// </summary>
public sealed record ConditionalBranchInfo
{
    public ConditionalBranchInfo(
        string HeadText,
        SourceSpan? HeadSpan,
        IReadOnlyList<string> BinderNames)
    {
        this.HeadText = HeadText;
        this.HeadSpan = HeadSpan;
        this.BinderNames = BinderNames.Count == 0
            ? Array.Empty<string>()
            : Array.AsReadOnly(BinderNames.ToArray());
    }

    public string HeadText { get; }

    public SourceSpan? HeadSpan { get; }

    public IReadOnlyList<string> BinderNames { get; }
}

/// <summary>
/// Property-centered semantic information for one resolved declaration target.
/// Ordinary properties expose <see cref="Parameters"/>. Conditional properties
/// expose <see cref="ConditionalBranches"/>. Builtins are represented
/// conservatively with <see cref="PropertyShape.Builtin"/>, where
/// <see cref="Parameters"/> reflects the preferred surface for the current
/// usage and <see cref="Signatures"/> retains any alternate callable forms.
/// </summary>
public sealed record PropertyInfo
{
    private IReadOnlyList<PropertyParameterInfo> _parameters;
    private IReadOnlyList<PropertySignatureInfo> _signatures = [];

    public PropertyInfo(
        string Name,
        DeclarationOccurrence? Declaration,
        PropertyShape Shape,
        bool IsPublic,
        PropertyExposure Exposure,
        IReadOnlyList<PropertyParameterInfo> Parameters,
        IReadOnlyList<ConditionalBranchInfo> ConditionalBranches)
    {
        this.Name = Name;
        this.Declaration = Declaration;
        this.Shape = Shape;
        this.IsPublic = IsPublic;
        this.Exposure = Exposure;
        _parameters = Snapshot(Parameters);
        this.ConditionalBranches = ConditionalBranches.Count == 0
            ? Array.Empty<ConditionalBranchInfo>()
            : Array.AsReadOnly(ConditionalBranches.ToArray());
    }

    public string Name { get; }

    /// <summary>
    /// The property's declaration site in the current document, or
    /// <see langword="null"/> when it has none: a builtin
    /// (<see cref="PropertyShape.Builtin"/>), or a property supplied by a
    /// load-elaborated module — a module-provided target is locationless with
    /// respect to the document that imports it (its <see cref="Parameters"/> and
    /// <see cref="ConditionalBranches"/> carry no spans either), because its
    /// coordinates belong to the module's own source text.
    /// A document-owned declaration may reuse an imported callable body in a
    /// host-built AST; its declaration stays local while the imported parameter
    /// spans remain unavailable.
    /// </summary>
    public DeclarationOccurrence? Declaration { get; }

    public PropertyShape Shape { get; }

    public bool IsPublic { get; }

    public PropertyExposure Exposure { get; }

    public IReadOnlyList<PropertyParameterInfo> Parameters
    {
        get => _parameters;
        init => _parameters = Snapshot(value);
    }

    public IReadOnlyList<ConditionalBranchInfo> ConditionalBranches { get; }

    public bool IsExported => Exposure == PropertyExposure.Exported;

    /// <summary>
    /// Whether ordinary lexical dot-call fallback may inject a receiver into
    /// this callable. This is false for zero-parameter properties and for
    /// front-end-only catalog entries such as <c>load</c>. An explicit dot
    /// intrinsic signature is a separate capability.
    /// </summary>
    public bool SupportsLexicalDotCall { get; init; }

    /// <summary>
    /// When this property is a predefined prelude ALIAS for a canonical
    /// qualified member (the lower-camel-case Math bindings — <c>sin</c> for
    /// <c>Math.Sin</c>), the canonical target's identity; otherwise
    /// <see langword="null"/>. Only the synthetic prelude alias bindings carry
    /// this: canonical <c>Math.X</c> members and any source-declared property
    /// that shadows an alias spelling do not, so a non-null value certifies the
    /// resolved symbol IS the prelude alias.
    /// </summary>
    public PropertyAliasTargetInfo? AliasTarget { get; init; }

    public PropertyCallStyle PreferredCallStyle { get; init; } = PropertyCallStyle.Plain;

    public IReadOnlyList<PropertySignatureInfo> Signatures
    {
        get => _signatures;
        init => _signatures = value.Count == 0
            ? Array.Empty<PropertySignatureInfo>()
            : Array.AsReadOnly(value.ToArray());
    }

    public string DisplaySignature => GetDisplaySignature(PreferredCallStyle);

    public PropertySignatureInfo? FindSignature(PropertyCallStyle callStyle)
    {
        foreach (var signature in Signatures)
        {
            if (signature.CallStyle == callStyle)
                return signature;
        }

        return null;
    }

    public IReadOnlyList<PropertyParameterInfo> GetParameters(PropertyCallStyle callStyle)
        => FindSignature(callStyle)?.Parameters ?? Parameters;

    public string GetDisplaySignature(PropertyCallStyle callStyle)
        => FindSignature(callStyle)?.DisplayText
            ?? FormatSignature(Name, GetParameters(callStyle));

    public PropertyInfo WithPreferredCallStyle(PropertyCallStyle callStyle)
    {
        var signature = FindSignature(callStyle);
        if (signature is null)
            return this;

        return this with
        {
            Parameters = signature.Parameters,
            PreferredCallStyle = callStyle,
        };
    }

    private static string FormatSignature(string name, IReadOnlyList<PropertyParameterInfo> parameters)
        => CallableSignature.FormatDisplayText(
            name,
            parameters.Select(static parameter => parameter.DisplayName));

    private static IReadOnlyList<PropertyParameterInfo> Snapshot(
        IReadOnlyList<PropertyParameterInfo> parameters)
        => parameters.Count == 0
            ? Array.Empty<PropertyParameterInfo>()
            : parameters as SharedPropertyParameterList ?? Array.AsReadOnly(parameters.ToArray());
}

internal static class ConditionalBranchHeadFormatter
{
    public static string Format(string propertyName, Pattern pattern)
        => $"{propertyName}({FormatPattern(pattern, nested: false)})";

    private static string FormatPattern(Pattern pattern, bool nested)
        => pattern switch
        {
            Pattern.Bind bind => bind.ParameterKind == ParameterKind.Collecting
                ? $"*{bind.Name}"
                : bind.Name,
            Pattern.LitInt litInt => Rendering.ValueTextRenderer.FormatNumberInvariant(litInt.Value),
            Pattern.LitString litString => $"'{litString.Value}'",
            Pattern.LitBool litBool => Rendering.ValueTextRenderer.FormatBool(litBool.Value),
            Pattern.SequenceValue sequenceValue => FormatSequenceValue(sequenceValue, nested),
        };

    private static string FormatSequenceValue(Pattern.SequenceValue sequenceValue, bool nested)
    {
        var inner = string.Join(", ", sequenceValue.Items.Select(item => FormatPattern(item, nested: true)));
        return nested ? $"({inner})" : inner;
    }
}
