using System.Runtime.CompilerServices;

namespace KatLang;

/// <summary>
/// Diagnostic-only origin of one implicit parameter inferred from an
/// unresolved identifier. This is deliberately internal: public AST and
/// structured-error consumers need the ordinary parameter/error payloads,
/// while only KatLang's diagnostic renderer consumes this implementation
/// metadata.
/// </summary>
internal sealed class ImplicitParameterProvenance
{
    internal ImplicitParameterProvenance(
        string name,
        SourceSpan? span,
        NameSuggestion? suggestion)
    {
        Name = name;
        Span = span;
        Suggestion = suggestion;
    }

    internal string Name { get; }

    internal SourceSpan? Span { get; }

    /// <summary>
    /// The conservative suggestion after any source-defined property involved
    /// in it has received its final exposure classification. Before that
    /// classification, an exposure-dependent suggestion is suppressed.
    /// </summary>
    internal string? SuggestedName => Suggestion?.EligibleName;

    private NameSuggestion? Suggestion { get; }

    internal static IReadOnlyList<ImplicitParameterProvenance>? CollectFrom(
        IReadOnlyList<ParameterDeclaration> parameters)
    {
        List<ImplicitParameterProvenance>? notes = null;
        foreach (var parameter in parameters)
        {
            if (parameter.InferredProvenance is { } provenance)
                (notes ??= []).Add(provenance);
        }

        return notes;
    }
}

/// <summary>
/// A ranked suggestion and, for structural/open candidates, the exact
/// property whose final Exported classification makes the corrected spelling
/// eligible. Direct lexical properties and bound names need no exposure gate.
/// </summary>
internal sealed class NameSuggestion
{
    internal NameSuggestion(string name, Property? requiredExportedProperty)
    {
        Name = name;
        RequiredExportedProperty = requiredExportedProperty;
        if (requiredExportedProperty is not null)
            FinalPropertyExposure.Track(requiredExportedProperty);
    }

    private string Name { get; }

    private Property? RequiredExportedProperty { get; }

    internal string? EligibleName
        => RequiredExportedProperty is null
            || FinalPropertyExposure.IsConfirmedExported(RequiredExportedProperty)
                ? Name
                : null;
}

/// <summary>
/// Weak, diagnostic-only bridge between suggestion collection (which runs
/// during parameter detection) and the later authoritative property-exposure
/// pass. Keys are the exact property records seen by lookup; retaining an AST
/// cannot retain unrelated prior ASTs through this table.
/// </summary>
internal static class FinalPropertyExposure
{
    private sealed class Holder
    {
        internal PropertyExposure? Exposure { get; set; }
    }

    private static readonly ConditionalWeakTable<Property, Holder> ExposureByProperty = new();

    internal static void Track(Property property)
        => _ = ExposureByProperty.GetValue(property, static _ => new Holder());

    private static void Record(Property property, PropertyExposure exposure)
    {
        ExposureByProperty.GetValue(property, static _ => new Holder()).Exposure = exposure;
    }

    internal static void RecordIfTracked(Property property, PropertyExposure exposure)
    {
        if (ExposureByProperty.TryGetValue(property, out var holder))
            holder.Exposure = exposure;
    }

    /// <summary>
    /// Keeps the exposure identity of a property across front-end record
    /// rebuilding before the final exposure pass. Suggestions may hold the
    /// earlier record while the resolver necessarily sees the later one.
    /// </summary>
    internal static void Link(Property source, Property destination)
    {
        var holder = ExposureByProperty.GetValue(source, static _ => new Holder());
        ExposureByProperty.Remove(destination);
        ExposureByProperty.Add(destination, holder);
    }

    internal static bool IsConfirmedExported(Property property)
        => ExposureByProperty.TryGetValue(property, out var holder)
            && holder.Exposure == PropertyExposure.Exported;

    /// <summary>
    /// Prelude/host-operation signature trees are already final and do not run
    /// through PropertyExposureResolver with the source tree. Mark them once so
    /// Math and configured host/prelude candidates remain suggestible.
    /// </summary>
    internal static void MarkTreeFinal(Algorithm algorithm)
        => new FinalExposureMarker().VisitAlgorithm(algorithm);

    /// <summary>
    /// Uses the shared exhaustive AST traversal so algorithms embedded in
    /// output/open/call expressions are finalized too, not only algorithms
    /// reachable through named properties and conditional branches.
    /// </summary>
    private sealed class FinalExposureMarker : AstWalker
    {
        protected override bool VisitsExplicitParameterDeclarations => false;

        protected override void VisitProperty(Property property)
        {
            Record(property, property.Exposure);
            base.VisitProperty(property);
        }
    }
}

/// <summary>
/// Stores diagnostic metadata beside records without adding an instance field.
/// Record equality/hash/printing therefore remain exactly the pre-feature
/// semantic identity. Explicit copy constructors call <see cref="Copy"/> so a
/// user or evaluator <c>with</c> clone retains the diagnostic payload.
/// </summary>
internal static class DiagnosticRecordMetadata<T> where T : class
{
    private sealed class Holder(T value)
    {
        internal T Value { get; } = value;
    }

    private static readonly ConditionalWeakTable<object, Holder> Values = new();

    internal static T? Get(object owner)
        => Values.TryGetValue(owner, out var holder) ? holder.Value : null;

    internal static void Set(object owner, T? value)
    {
        Values.Remove(owner);
        if (value is not null)
            Values.Add(owner, new Holder(value));
    }

    internal static void Copy(object source, object destination)
        => Set(destination, Get(source));
}
