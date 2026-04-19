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
public sealed record PropertyParameterInfo(string Name, PropertyParameterKind Kind, SourceSpan? Span);

/// <summary>
/// Editor-facing metadata for one callable signature surface.
/// </summary>
public sealed record PropertySignatureInfo(
    PropertyCallStyle CallStyle,
    string DisplayText,
    IReadOnlyList<PropertyParameterInfo> Parameters);

/// <summary>
/// Editor-facing summary of one conditional branch head.
/// <see cref="HeadSpan"/> is the best available source anchor for the branch
/// head. When the AST only preserves the declared property name span, that
/// exact declaration span is exposed here.
/// </summary>
public sealed record ConditionalBranchInfo(
    string HeadText,
    SourceSpan? HeadSpan,
    IReadOnlyList<string> BinderNames);

/// <summary>
/// Property-centered semantic information for one resolved declaration target.
/// Ordinary properties expose <see cref="Parameters"/>. Conditional properties
/// expose <see cref="ConditionalBranches"/>. Builtins are represented
/// conservatively with <see cref="PropertyShape.Builtin"/>, where
/// <see cref="Parameters"/> reflects the preferred surface for the current
/// usage and <see cref="Signatures"/> retains any alternate callable forms.
/// </summary>
public sealed record PropertyInfo(
    string Name,
    DeclarationOccurrence? Declaration,
    PropertyShape Shape,
    bool IsPublic,
    PropertyExposure Exposure,
    IReadOnlyList<PropertyParameterInfo> Parameters,
    IReadOnlyList<ConditionalBranchInfo> ConditionalBranches)
{
    public bool IsExported => Exposure == PropertyExposure.Exported;

    public PropertyCallStyle PreferredCallStyle { get; init; } = PropertyCallStyle.Plain;

    public IReadOnlyList<PropertySignatureInfo> Signatures { get; init; } = [];

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
        => parameters.Count == 0
            ? name
            : $"{name}({string.Join(", ", parameters.Select(parameter => parameter.Name))})";
}

internal static class ConditionalBranchHeadFormatter
{
    public static string Format(string propertyName, Pattern pattern)
        => $"{propertyName}({FormatPattern(pattern, nested: false)})";

    private static string FormatPattern(Pattern pattern, bool nested)
        => pattern switch
        {
            Pattern.Bind bind => bind.Name,
            Pattern.LitInt litInt => litInt.Value.ToString(CultureInfo.InvariantCulture),
            Pattern.LitString litString => $"'{litString.Value}'",
            Pattern.Group group => FormatGroup(group, nested),
            _ => string.Empty,
        };

    private static string FormatGroup(Pattern.Group group, bool nested)
    {
        var inner = string.Join(", ", group.Items.Select(item => FormatPattern(item, nested: true)));
        return nested ? $"({inner})" : inner;
    }
}