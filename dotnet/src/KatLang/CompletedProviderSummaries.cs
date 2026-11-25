using System.Diagnostics.CodeAnalysis;
using System.Runtime.CompilerServices;

namespace KatLang;

/// <summary>
/// COMPLETED PROVIDER SUMMARIES (November 2026; C#-only work sharing, no classification, diagnostic or Lean rule): the
/// requirement summaries of bodies an EARLIER operation of the program completed, kept by the program's loader for the
/// deferred materializations that read them. A deferred branch's materialization is a front-end operation of its own
/// (<see cref="DeferredModuleRegion"/>), with its own exposure resolution and its own
/// <see cref="PropertyDependencyGraphBuilder.SummaryMemo"/>. When its body reads one member of a completed body — a
/// module an enclosing scope opens, a member path through a property that holds a module or an inline block — exposure
/// charges that member's summary seed, and the seed is one entry of the provider body's whole summary: every member's
/// seed and their sibling fixed point. Before this share each materialization computed that summary again, so K selected
/// branches reading one W-member provider cost O(K × W), in a shape no source-processing limit bounds (each branch
/// splices only its own small module) and that evaluation steps do not count.
///
/// <para><b>What is kept.</b> One entry per completed context a materialization asked for by its exact context
/// (<see cref="PropertyDependencyGraphBuilder.GetAlgorithmSummary"/>), under the facts it was asked through: a sealed
/// table of an earlier operation, or the asking unit's own table (which inherits every earlier one). An entry is the
/// finished summary with every anchored reference at the TABLE its origin reads, never at the computing resolution's
/// own requirement view of it (<c>PropertyDependencyGraphBuilder.SummaryMemo.StoredForm</c>).</para>
///
/// <para><b>When a summary is kept (all of these, decided by the computing resolution).</b> The context and every
/// context above it hold a completed, non-provisional body that the asking unit inherited (it did not publish them
/// itself), and the body is the one those facts name. While the summary was computed, the walk entered only bodies
/// whose own facts are sealed, hold that body and are not provisional; it took no summary from the resolution's memo
/// that was computed before it began under a context; and it replaced no context by a representative of a body the
/// resolution's input shares. Such a computation read immutable completed facts and immutable trees only, so every
/// later operation of the program would compute the same summary: a completed body is never rebuilt, a unit overrides
/// only inherited entries that have NO body (<c>StaticStructureOperation.CompleteLookups</c>), and a placeholder inside
/// the body, whose facts a later materialization does replace, taints the computation. Finally every anchored reference
/// the summary carries names sealed facts, or the computing unit's own. A summary that fails any test is simply not
/// kept, and the next materialization computes it as before.</para>
///
/// <para><b>How a summary is reused.</b> A seed names a lookup facts object only through the origins of its anchored
/// references (<see cref="PendingReference.Origin"/>), and a resolution's facts objects are its own: its unit's table
/// and its memo's requirement views of the sealed ones. An adopting resolution therefore receives each seed
/// RE-ANCHORED: the same path, bound owners and selection at the context of the SAME key in the adopter's own facts (the
/// computing unit's table becomes the adopter's unit; a sealed table stays itself, under the adopter's view), which is
/// the reference its own computation would have written. A seed that carries no anchored reference is the same value
/// under every facts object and is handed over as it is. Re-anchoring is per seed and on demand
/// (<see cref="PropertyDependencyGraphBuilder.AlgorithmSummary"/>), so reading one member of an adopted W-member
/// provider costs that member's seed. Everything after the seed (anchoring at the reader, settlement, the frame charge)
/// is the adopter's own work, exactly as before.</para>
///
/// <para><b>Isolation.</b> An attempt reads the entries earlier successful operations published and stages its own
/// (<see cref="Attempt"/>); its entries become visible only when the attempt publishes its unit, together with its
/// module declarations and its structural continuation (<see cref="ModuleUnits.Publish"/>, under the loader's
/// materialization gate and the region's run lock). An attempt that publishes nothing — a load or front-end error, a
/// structural or stack refusal, cancellation, abandonment — leaves nothing here, so nothing of a failed attempt's facts,
/// trees or contexts is retained, and a branch refused at every selection keeps paying for itself only. Entries are
/// facts about COMPLETED content: they hold seeds, the names and owners those seeds carry, keys of the completed
/// tables, and the sealed table of the unit that computed them; no resolution's memo or requirement view, and no
/// branch body, region, attempt, diagnostics list, token, engine or evaluation state. What the share retains is bounded by the completed providers the program's
/// deferred branches read, never by how often branches are selected. Never static: one share belongs to one loader
/// (<see cref="ModuleUnitRegistry"/>), which belongs to one document, and every access happens inside that loader's
/// materialization gate.</para>
/// </summary>
internal sealed class CompletedProviderSummaries
{
    /// <summary>How a materialization uses the share (test seam only; see <see cref="ModeForTesting"/>).</summary>
    internal enum Mode
    {
        /// <summary>The production rule: adopt what earlier operations kept, keep what this one computes.</summary>
        Shared,

        /// <summary>
        /// As <see cref="Shared"/>, and every adopted summary is also computed by the adopting resolution and compared
        /// with it seed by seed (<c>PropertyDependencyGraphBuilder.SummaryMemo.AdoptedSummaryDifference</c>); a
        /// difference throws.
        /// </summary>
        Verified,

        /// <summary>Nothing is adopted or kept: every materialization computes every summary (the reference).</summary>
        Unshared,
    }

    /// <summary>
    /// TEST SEAM (<c>CompletedProviderSummaryTests</c>): the <see cref="Mode"/> of every materialization whose exposure
    /// starts on the calling flow. Never set by production code.
    /// </summary>
    internal static readonly AsyncLocal<Mode> ModeForTesting = new();

    /// <summary>
    /// The context an entry answers: <paramref name="Scope"/> in the sealed table <paramref name="Sealed"/>, or, with no
    /// table, in the asking materialization's own unit (which inherits the context from an earlier operation).
    /// Reference identity on both parts.
    /// </summary>
    internal readonly record struct Key(CompletedStaticStructures? Sealed, StaticScopeKey Scope)
    {
        public bool Equals(Key other) => ReferenceEquals(Sealed, other.Sealed) && ReferenceEquals(Scope, other.Scope);

        public override int GetHashCode()
            => HashCode.Combine(Sealed is null ? 0 : RuntimeHelpers.GetHashCode(Sealed), RuntimeHelpers.GetHashCode(Scope));
    }

    /// <summary>
    /// One kept summary: the summary in its stored form (origins at their tables; never mutated here, never handed to a
    /// reader that could accumulate into it), whether that computation used no context
    /// (<see cref="PropertyDependencyGraphBuilder.SummaryMemo.IndependentAlgorithmSummaries"/>), and the table of the
    /// unit that computed it, which the origins of its anchored references may name.
    /// </summary>
    internal sealed class Entry(PropertyDependencyGraphBuilder.AlgorithmSummary summary, bool independent,
        CompletedStaticStructures computedBy, IReadOnlySet<PropertyDependencyGraphBuilder.SummarySeed> anchoredSeeds)
    {
        internal PropertyDependencyGraphBuilder.AlgorithmSummary Summary => summary;

        internal bool Independent => independent;

        internal CompletedStaticStructures ComputedBy => computedBy;

        /// <summary>
        /// The stored seeds that transitively carry an anchored reference, indexed once before publication.
        /// </summary>
        internal IReadOnlySet<PropertyDependencyGraphBuilder.SummarySeed> AnchoredSeeds => anchoredSeeds;
    }

    private readonly Dictionary<Key, Entry> _published = [];

    /// <summary>The published entries; test-observable, never a decision input.</summary>
    internal int Count => _published.Count;

    /// <summary>One materialization attempt's view: what earlier operations published, and what this one staged.</summary>
    internal Attempt BeginAttempt() => new(this);

    /// <summary>
    /// One materialization attempt's reads and staged entries (see the class remarks, Isolation). An attempt never
    /// reads its own staged entries: its resolution's memo already holds those summaries.
    /// </summary>
    internal sealed class Attempt(CompletedProviderSummaries share)
    {
        private List<(Key Key, Entry Entry)>? _staged;

        /// <summary>Entries staged and not yet published; test-observable, never a decision input.</summary>
        internal int StagedCount => _staged?.Count ?? 0;

        internal bool TryGet(Key key, [NotNullWhen(true)] out Entry? entry) => share._published.TryGetValue(key, out entry);

        internal void Stage(Key key, Entry entry) => (_staged ??= []).Add((key, entry));

        /// <summary>
        /// Publishes the staged entries: call only where the attempt publishes its unit. The first entry of a key
        /// stays (every entry of one key is the same summary, whichever operation computed it).
        /// </summary>
        internal void Publish()
        {
            if (_staged is not { } staged)
                return;
            foreach (var (key, entry) in staged)
                share._published.TryAdd(key, entry);
            _staged = null;
        }
    }
}
