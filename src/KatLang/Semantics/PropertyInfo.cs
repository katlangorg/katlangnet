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
/// conservatively with <see cref="PropertyShape.Builtin"/> and parameter data
/// only when the callable shape is known.
/// </summary>
public sealed record PropertyInfo(
    string Name,
    DeclarationOccurrence? Declaration,
    PropertyShape Shape,
    bool IsPublic,
    IReadOnlyList<PropertyParameterInfo> Parameters,
    IReadOnlyList<ConditionalBranchInfo> ConditionalBranches);

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