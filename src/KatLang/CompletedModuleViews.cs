using System.Diagnostics.CodeAnalysis;

namespace KatLang;

/// <summary>
/// COMPLETED MODULE VIEWS (November 2026; C#-only work sharing, no value, diagnostic, classification or limit change,
/// no Lean counterpart): the admission facts of the exact module import views the program's operations completed, kept
/// by the program's loader for the deferred materializations that splice those views again. A deferred branch's
/// materialization is a front-end operation of its own (<see cref="DeferredModuleRegion"/>). When its body splices a
/// module an earlier operation completed, the loader hands it the very view object the earlier operation spliced
/// (<see cref="ModuleLoader"/>'s per-URL cache) and every front-end pass receives that module's published declaration
/// (<see cref="ModuleUnitRegistry"/>). Yet the materialization still walked the whole module at every selection: the
/// loader's two structural gates over the composed body and its unresolved-load check, the static admission measure,
/// signature analysis of the module's bodies, and the walk of the module's free reference names behind the resolver's
/// region key of a body that opens or holds it. Those walks read only immutable completed content, so each answered what
/// an earlier one had answered, and K selections of branches that splice one W-member module cost O(K × W) (bounded only
/// by the aggregate source limit, which every splice charges).
///
/// <para><b>What is kept.</b> One <see cref="Facts"/> per completed view, keyed by the view object itself (reference
/// identity: one canonical URL is one view per loader): its weighted height under
/// <see cref="AstConsumerProfile.FullyRecursive"/> (the profile of both composed-body gates), and its
/// <see cref="AdmissionUnit"/>, the view's own part of the static admission measure (its nodes and edges, its open and
/// output-spreading flags, and the module views it splices in turn, which are units of their own). Both are pure
/// functions of the immutable view: the height is the longest weighted path below it, and the unit is what the
/// measure's walk counts below it when it stops at nested module views. A view's own nodes are disjoint from every other
/// view's and from the loading document's, because each view is its own parse's locationless import view and the loader
/// splices it only by reference, so the measure of a composed body is exactly the sum of its own part and its distinct
/// units (<see cref="StaticStructureAdmission.MeasureLoadedBody"/>). Beside them, the free reference names of each
/// completed DETECTED module declaration (the resolution pass's input), kept as names and re-interned by each reader. The
/// verifying test mode checks every reuse against the ordinary walk.</para>
///
/// <para><b>How the facts are reused.</b> A gate meeting a view whose height fits at that occurrence does not walk it
/// (a rejection replays the ordinary walk, so the diagnostic and its span are the established ones). The unresolved-load
/// check does not enter a completed view: the operation that completed it checked it and published nothing it could have
/// flagged. The admission measure adds the view's unit instead of walking it. The resolver re-interns a completed
/// declaration's published free names instead of walking it. Signature analysis needs no fact of its own: a module an
/// earlier operation resolved is not analyzed (<see cref="ModuleUnits.ReceivesEarlierResolution"/>), and its members'
/// signatures are final, read from their published resolved views.</para>
///
/// <para><b>Isolation.</b> An attempt reads what earlier successful materializations published and stages what it
/// computes (<see cref="Attempt"/>); its facts become visible only when the attempt publishes its unit, together with its
/// module declarations, its structural continuation and its provider summaries (<see cref="ModuleUnits.Publish"/>, under
/// the loader's materialization gate and the region's run lock), and only for views the registry then holds as
/// completed units. An attempt that publishes nothing — a load or front-end error, a structural, admission or stack
/// refusal, cancellation, abandonment — leaves nothing here, so a failed attempt never warms a later one. The facts hold
/// counts, flags and references to completed views only: no body, region, attempt, diagnostic list, token or
/// evaluation state. They are bounded by the program's distinct completed module views. Never static: one store belongs
/// to one loader, which belongs to one parse of one document, and every access happens inside that loader's
/// materialization gate.</para>
/// </summary>
internal sealed class CompletedModuleViews
{
    /// <summary>How a materialization uses the store (test seam only; see <see cref="ModeForTesting"/>).</summary>
    internal enum Mode
    {
        /// <summary>The production rule: reuse what earlier materializations published, keep what this one computes.</summary>
        Shared,

        /// <summary>
        /// As <see cref="Shared"/>, and every reuse is checked against the ordinary walk it replaces (the gate's verdict
        /// and height, the load check's verdict and position, the measure's totals, and every reused fact recomputed
        /// from its view); a difference throws.
        /// </summary>
        Verified,

        /// <summary>
        /// Nothing is reused or kept, and signature analysis enters completed modules again: every materialization walks
        /// every spliced view (the reference).
        /// </summary>
        Unshared,
    }

    /// <summary>
    /// TEST SEAM (<c>CompletedModuleSpliceTests</c>): the <see cref="Mode"/> of every materialization whose attempt
    /// starts on the calling flow. Never set by production code.
    /// </summary>
    internal static readonly AsyncLocal<Mode> ModeForTesting = new();

    /// <summary>
    /// A module view's own part of the static admission measure: the nodes the measure's walk reaches from the view
    /// without entering another module view (the view itself included), the children it enumerates from them, whether
    /// one of them declares an <c>open</c> or carries an output-spreading marker, and the other module views it reaches
    /// (each a unit of its own, counted once whichever view or body reaches it).
    /// </summary>
    internal sealed record AdmissionUnit(long Nodes, long Edges, bool HasOpens, bool HasOutputSpreadMarkers, IReadOnlyList<Algorithm.User> Nested)
    {
        /// <summary>Whether two units hold the same counts, flags and nested views (the nested views as a set).</summary>
        internal bool SameAs(AdmissionUnit other)
            => Nodes == other.Nodes && Edges == other.Edges && HasOpens == other.HasOpens
                && HasOutputSpreadMarkers == other.HasOutputSpreadMarkers && Nested.Count == other.Nested.Count
                && Nested.ToHashSet(ReferenceEqualityComparer.Instance).SetEquals(other.Nested);
    }

    /// <summary>The published facts of one completed view.</summary>
    internal sealed record Facts(int Height, AdmissionUnit Unit);

    private readonly Dictionary<Algorithm.User, Facts> _published = new(ReferenceEqualityComparer.Instance);

    // The FREE REFERENCE NAMES of completed DETECTED module declarations (the resolution pass's input, a registry
    // resolution key): what implicit-argument resolution's region keys read of a module reached through an open target or
    // a property (ImplicitArgumentResolver.FreeReferenceNames), a pure function of the immutable declaration. Kept as
    // names, never as one run's canonical set: a reader re-interns them in its own run's interner.
    private readonly Dictionary<Algorithm.User, string[]> _freeNames = new(ReferenceEqualityComparer.Instance);

    /// <summary>The published entries; test-observable, never a decision input.</summary>
    internal int Count => _published.Count;

    /// <summary>Whether facts of <paramref name="view"/> are published; test-observable, never a decision input.</summary>
    internal bool HasPublished(Algorithm view) => view is Algorithm.User user && _published.ContainsKey(user);

    /// <summary>
    /// One materialization attempt's view of the store (see the class remarks, Isolation), in the mode of the calling
    /// flow; <paramref name="observations"/> is the attempt's traversal observer, if any.
    /// </summary>
    internal Attempt BeginAttempt(ModuleUnitRegistry registry, FrontEndTraversalObservations? observations)
        => new(this, registry, ModeForTesting.Value, observations);

    /// <summary>Whether <paramref name="node"/> is a module view the loader spliced: the marked root of a module's import view.</summary>
    internal static bool IsModuleView(object node, [NotNullWhen(true)] out Algorithm.User? view)
    {
        view = node as Algorithm.User;
        return view is { IsModuleElaborated: true };
    }

    /// <summary>
    /// One materialization attempt's reads and staged facts. It reads only what earlier attempts published; what it
    /// computes itself it stages, and uses again within the attempt (a later stage of the same attempt reads the same
    /// immutable view).
    /// </summary>
    internal sealed class Attempt(CompletedModuleViews store, ModuleUnitRegistry registry, Mode mode, FrontEndTraversalObservations? observations)
    {
        private Dictionary<Algorithm.User, int>? _heights;
        private Dictionary<Algorithm.User, AdmissionUnit>? _units;
        private Dictionary<Algorithm.User, string[]>? _freeNames;

        internal Mode Mode => mode;

        /// <summary>Whether published facts are read and computed ones kept (every mode but the reference).</summary>
        internal bool Shares => mode != Mode.Unshared;

        /// <summary>Whether every reuse is also computed the ordinary way and compared (<see cref="Mode.Verified"/>).</summary>
        internal bool Verifies => mode == Mode.Verified;

        internal FrontEndTraversalObservations? Observations => observations;

        /// <summary>The published facts of a completed <paramref name="view"/>, when sharing.</summary>
        internal bool TryGetPublished(Algorithm.User view, [NotNullWhen(true)] out Facts? facts)
        {
            facts = null;
            return Shares && store._published.TryGetValue(view, out facts);
        }

        /// <summary>
        /// The height of <paramref name="view"/> a composed-body gate may take instead of walking it: a published one.
        /// (A height staged by this attempt is never needed: one gate walk per attempt measures every view it meets.)
        /// </summary>
        internal bool TryGetReusableHeight(Algorithm.User view, out int height)
        {
            if (TryGetPublished(view, out var facts))
            {
                height = facts.Height;
                if (Verifies && (AstStructuralPreflight.CheckMeasuringHeight(view, AstStructuralPreflight.RawSyntaxMaxAstDepth,
                        AstConsumerProfile.FullyRecursive, out var walked) is not null || walked != height))
                    throw new InvalidOperationException($"A completed module view's published height {height} differs from its walked height {walked}.");
                return true;
            }

            height = -1;
            return false;
        }

        /// <summary>Stages the height a gate walk measured for a module view it walked.</summary>
        internal void StageHeight(Algorithm.User view, int height)
        {
            if (Shares && !store._published.ContainsKey(view))
                (_heights ??= new(ReferenceEqualityComparer.Instance))[view] = height;
        }

        /// <summary>The admission unit of <paramref name="view"/>: published, or staged earlier in this attempt.</summary>
        internal bool TryGetUnit(Algorithm.User view, [NotNullWhen(true)] out AdmissionUnit? unit, out bool published)
        {
            if (TryGetPublished(view, out var facts))
            {
                unit = facts.Unit;
                published = true;
                return true;
            }

            published = false;
            unit = null;
            return Shares && _units is not null && _units.TryGetValue(view, out unit);
        }

        /// <summary>Stages the admission unit the measure computed for a module view it met.</summary>
        internal void StageUnit(Algorithm.User view, AdmissionUnit unit)
        {
            if (Shares && !store._published.ContainsKey(view))
                (_units ??= new(ReferenceEqualityComparer.Instance))[view] = unit;
        }

        /// <summary>
        /// Whether the post-load check may skip <paramref name="view"/>: a view whose facts are published was spliced by
        /// an operation that completed it and checked it for unresolved loads, and published nothing that check could
        /// flag.
        /// </summary>
        internal bool IsCheckedForLoads(Algorithm.User view) => Shares && store._published.ContainsKey(view);

        /// <summary>
        /// The free reference names of the detected module declaration <paramref name="module"/>, published by an earlier
        /// materialization; null when there are none to reuse.
        /// </summary>
        internal string[]? PublishedFreeNames(Algorithm.User module)
            => Shares && store._freeNames.TryGetValue(module, out var names) ? names : null;

        /// <summary>Stages the free reference names a resolution computed for a detected module declaration.</summary>
        internal void StageFreeNames(Algorithm.User module, string[] names)
        {
            if (Shares && !store._freeNames.ContainsKey(module))
                (_freeNames ??= new(ReferenceEqualityComparer.Instance))[module] = names;
        }

        /// <summary>
        /// Publishes the staged facts: call only where the attempt publishes its unit, after its module declarations are
        /// published. A view is kept only when both facts were staged and the registry holds it as a completed unit; the
        /// first facts of a view stay (every attempt computes the same facts of one immutable view).
        /// </summary>
        internal void Publish()
        {
            if (_heights is { } heights && _units is { } units)
            {
                foreach (var (view, height) in heights)
                {
                    if (units.TryGetValue(view, out var unit) && registry.TryGet(ModuleUnitPass.Detection, view, out _)
                        && store._published.TryAdd(view, new Facts(height, unit)))
                        observations?.RecordCompletedModuleViewPublished();
                }
            }

            if (_freeNames is { } freeNames)
            {
                // A detected declaration is completed once the registry holds its resolved unit.
                foreach (var (module, names) in freeNames)
                {
                    if (registry.TryGet(ModuleUnitPass.Resolution, module, out _))
                        store._freeNames.TryAdd(module, names);
                }
            }

            _heights = null;
            _units = null;
            _freeNames = null;
        }
    }
}
