using System.Globalization;

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
    public PropertySignatureInfo(
        PropertyCallStyle CallStyle,
        string DisplayText,
        IReadOnlyList<PropertyParameterInfo> Parameters)
    {
        this.CallStyle = CallStyle;
        this.DisplayText = DisplayText;
        this.Parameters = Snapshot(Parameters);
    }

    public PropertyCallStyle CallStyle { get; }

    public string DisplayText { get; }

    public IReadOnlyList<PropertyParameterInfo> Parameters { get; }

    private static IReadOnlyList<PropertyParameterInfo> Snapshot(
        IReadOnlyList<PropertyParameterInfo> parameters)
        => parameters.Count == 0
            ? Array.Empty<PropertyParameterInfo>()
            : Array.AsReadOnly(parameters.ToArray());
}

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
            : Array.AsReadOnly(parameters.ToArray());
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
            Pattern.LitInt litInt => litInt.Value.ToString(CultureInfo.InvariantCulture),
            Pattern.LitString litString => $"'{litString.Value}'",
            Pattern.SequenceValue sequenceValue => FormatSequenceValue(sequenceValue, nested),
            _ => string.Empty,
        };

    private static string FormatSequenceValue(Pattern.SequenceValue sequenceValue, bool nested)
    {
        var inner = string.Join(", ", sequenceValue.Items.Select(item => FormatPattern(item, nested: true)));
        return nested ? $"({inner})" : inner;
    }
}
