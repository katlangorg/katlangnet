using System.Collections;

namespace KatLang;

/// <summary>Whether an observed property value may be shown to the host.</summary>
public enum PropertyValueStatus
{
    /// <summary>The published value is exposed through <see cref="PropertyValueObservation.Value"/>.</summary>
    Available = 0,

    /// <summary>
    /// The published value contains a run-internal call reference, which never leaves a run, so it
    /// is not exposed: <see cref="PropertyValueObservation.Value"/> is <c>null</c>. The run itself is
    /// unaffected — a program may hold such a value in a property it never outputs.
    /// </summary>
    Withheld = 1,
}

/// <summary>
/// One root property value the run's ordinary evaluation PUBLISHED in its zero-argument property
/// cache (<see cref="RunOptions.ObservePropertyValues"/>): the result of the property's outermost
/// successful property-style read, which every later read of it reused. It is a snapshot of the
/// completed run, not a live evaluator handle, and it is not a calculation history — explicit calls
/// (<c>A()</c>), re-entrant reads under a running owner, and reads whose owner later failed publish
/// nothing and so have no observation.
/// </summary>
public sealed record PropertyValueObservation
{
    internal PropertyValueObservation(
        string name,
        SourceSpan declarationSpan,
        PropertyValueStatus status,
        Result? value,
        int emittedCount)
    {
        Name = name;
        DeclarationSpan = declarationSpan;
        Status = status;
        Value = value;
        EmittedCount = emittedCount;
    }

    /// <summary>The root property's name, unique among the root properties of a valid program.</summary>
    public string Name { get; }

    /// <summary>
    /// The property's canonical declaration anchor — its first declared name occurrence — in the
    /// coordinates of the source that run evaluated. Correlating it with a document version is the
    /// host's responsibility.
    /// </summary>
    public SourceSpan DeclarationSpan { get; }

    /// <summary>Whether <see cref="Value"/> is exposed.</summary>
    public PropertyValueStatus Status { get; }

    /// <summary>
    /// The published value when <see cref="Status"/> is <see cref="PropertyValueStatus.Available"/>;
    /// <c>null</c> when it is <see cref="PropertyValueStatus.Withheld"/>.
    /// </summary>
    public Result? Value { get; }

    /// <summary>
    /// The number of value slots the property's output emitted — its value boundary, like
    /// <see cref="RunResult.Success.OutputRows"/>: <c>P = 1, 2</c> emits two rows that form one
    /// sequence value, while <c>P = (1, 2)</c> emits one row holding that sequence. Kept for withheld
    /// values too.
    /// </summary>
    public int EmittedCount { get; }
}

/// <summary>
/// The immutable, publication-ordered snapshot of a run's root property observations
/// (<see cref="RunResult.PropertyObservations"/>). Order is the order in which the run published
/// the values — dependencies before their dependants in an acyclic chain — not source order.
/// <para>Absence proves nothing: a root property without an observation was not published in this
/// run, which covers an unused property, one only called explicitly, and one whose calculation was
/// never completed by an owning read. It must not be presented as "never calculated".</para>
/// </summary>
public sealed class PropertyObservations : IReadOnlyList<PropertyValueObservation>
{
    internal static PropertyObservations Empty { get; } = new([]);

    private readonly PropertyValueObservation[] _observations;

    internal PropertyObservations(PropertyValueObservation[] observations) => _observations = observations;

    /// <summary>The number of observations.</summary>
    public int Count => _observations.Length;

    /// <summary>The observation at <paramref name="index"/>, in publication order.</summary>
    public PropertyValueObservation this[int index] => _observations[index];

    /// <inheritdoc/>
    public IEnumerator<PropertyValueObservation> GetEnumerator()
        => ((IEnumerable<PropertyValueObservation>)_observations).GetEnumerator();

    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();
}
