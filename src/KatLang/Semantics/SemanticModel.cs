namespace KatLang.Semantics;

/// <summary>
/// Syntactic kind of an identifier site in source.
/// </summary>
public enum OccurrenceKind
{
    PropertyDefinition,
    ExplicitParameterDefinition,
    ConditionalBinderDefinition,
    ResolveReference,
    ParameterReference,
    DotMemberReference,
    OpenTargetReference,
    OpenTargetMemberReference,
}

/// <summary>
/// Semantic classification of an identifier occurrence.
/// </summary>
public enum IdentifierClassification
{
    PropertyDefinition,
    PropertyReference,
    ExplicitParameterDefinition,
    ExplicitParameterReference,
    ImplicitParameterReference,
    ConditionalBinderDefinition,
    ConditionalBinderReference,
    Builtin,
    // Value 8 was the retired, never-produced LoadedExternalMemberReference.
    OpenTarget = 9,
    Unresolved,
    /// <summary>
    /// The identifier's meaning cannot be determined without a module the analyzed tree does
    /// not contain: it has no certain lexical resolution, and a module-backed <c>open</c> (or a
    /// <c>X = load('url')</c> receiver of the dot member) whose module was not elaborated sits
    /// in the lookup chain and may supply it or make an ordinary open's candidate ambiguous.
    /// Every situation that leaves a module out of the tree classifies alike: a DEFERRED module
    /// (branch-lazy module loading, B2c), loaded only when its conditional branch is selected,
    /// and a MISSING one whose written <c>load</c> directive the parse kept in place — unavailable
    /// because the parse had no downloader (<see cref="RunOptions.DownloadCode"/>; reported as
    /// <see cref="DiagnosticCode.LoadElaborationUnavailable"/>) or refused by module elaboration
    /// (a failed fetch, a refused target, invalid module source; reported at the load site).
    /// Neither resolved nor known to be invalid — the semantic model never loads a module to
    /// find out — so tooling should treat it as indeterminate rather than as an error,
    /// including in completion results. A name that no such open could supply stays
    /// <see cref="Unresolved"/>.
    /// </summary>
    DeferredModuleReference,
    /// <summary>
    /// A dot member (<see cref="OccurrenceKind.DotMemberReference"/>) whose selection depends on
    /// a valid receiver only the runtime supplies — a parameter such as <c>f</c> in
    /// <c>GetQ(f) = f.Q</c>, a property that transparently refers to one, or a member chain
    /// rooted at either — when no lexical fallback the edge may select instead resolves. The
    /// supplied algorithm's own member is selected at runtime, so the site is indeterminate at
    /// analysis time: tooling should treat it as neither resolved nor an error. It is NOT a
    /// proven lookup — an argument that lacks the member still fails when the call runs — and it
    /// has no declaration target: <see cref="IdentifierResolution.ResolvedDeclaration"/> and
    /// <see cref="IdentifierResolution.ResolvedProperty"/> are <see langword="null"/>, so two such
    /// sites never share an identity merely because their member names match. A receiver that is
    /// unresolved, ambiguous, or statically known to fail, and a statically known receiver that
    /// lacks the member with no resolvable fallback, stay <see cref="Unresolved"/>.
    /// </summary>
    RuntimeMemberReference,
}

/// <summary>
/// A source-backed identifier occurrence with an exact source span.
/// </summary>
public record IdentifierOccurrence(string Name, SourceSpan Span, OccurrenceKind Kind);

/// <summary>
/// A source-backed declaration site.
/// </summary>
public sealed record DeclarationOccurrence(string Name, SourceSpan Span, OccurrenceKind Kind)
    : IdentifierOccurrence(Name, Span, Kind);

/// <summary>
/// Semantic resolution information for one identifier site of the current document.
/// <see cref="ResolvedDeclaration"/> is the document's declaration occurrence the
/// site resolves to, or <see langword="null"/> when the target has no site in this
/// document: a builtin, an implicit parameter, an unresolved or deferred name, a
/// runtime-dependent member (<see cref="IdentifierClassification.RuntimeMemberReference"/>), or a
/// property supplied by a load-elaborated module (a module-provided target keeps its
/// <see cref="ResolvedProperty"/> metadata but is locationless with respect to the
/// importing document — see <see cref="PropertyInfo.Declaration"/>).
/// </summary>
public sealed record IdentifierResolution(
    IdentifierOccurrence Occurrence,
    IdentifierClassification Classification,
    DeclarationOccurrence? ResolvedDeclaration,
    PropertyInfo? ResolvedProperty);

/// <summary>
/// Semantic information derived from a parsed KatLang root algorithm.
/// Only source-backed sites with exact spans in the CURRENT document are
/// included: every listed occurrence, declaration, and resolution site slices the
/// document's text to the identifier written there. A load-elaborated module
/// subtree (<c>open 'url'</c>, <c>load('url')</c>) is positioned in the module's
/// own source text, so it contributes no sites at any nesting depth; document
/// references that bind to its members resolve to locationless module-provided
/// targets, and its public names stay visible through the open. A MISSING module — a
/// load directive the parse kept in place because the module was unavailable or refused —
/// contributes only the directive's own sites, and the names it could supply classify as
/// <see cref="IdentifierClassification.DeferredModuleReference"/>.
/// </summary>
public sealed class SemanticModel
{
    /// <summary>
    /// Creates a semantic model from parts the builder has already made mutually consistent.
    /// Internal: every public model comes from <see cref="SemanticModelBuilder"/>, so its
    /// occurrences, resolutions, property index, and scopes all describe the same root.
    /// </summary>
    internal SemanticModel(
        Algorithm root,
        IReadOnlyList<IdentifierOccurrence> identifierOccurrences,
        IReadOnlyList<DeclarationOccurrence> declarations,
        IReadOnlyList<IdentifierResolution> identifierResolutions,
        IReadOnlyList<PropertyInfo> propertyInfos,
        IReadOnlyDictionary<DeclarationOccurrence, PropertyInfo> propertiesByDeclaration,
        IReadOnlyList<ScopeVisibility>? scopeVisibilities = null)
    {
        Root = root;
        IdentifierOccurrences = SafeReadOnlyCollection.Over(identifierOccurrences.ToArray());
        _declarations = declarations.ToArray();
        Declarations = SafeReadOnlyCollection.Over(_declarations);
        _identifierResolutions = identifierResolutions.ToArray();
        IdentifierResolutions = SafeReadOnlyCollection.Over(_identifierResolutions);
        ResolutionSitesAreMonotone = SitesAreMonotone(_identifierResolutions);
        PropertyInfos = SafeReadOnlyCollection.Over(propertyInfos.ToArray());
        var scopes = (scopeVisibilities ?? [new ScopeVisibility(Span: null, Symbols: [])]).ToArray();
        ScopeVisibilities = SafeReadOnlyCollection.Over(scopes);
        _scopeIndex = ScopePositionIndex.Build(scopes);
        // Declarations are looked up by canonical occurrence identity, never by
        // name/span value: a value-equal DTO (constructed by a consumer, or shared
        // declaration nodes in a host-built tree) is not a key.
        _propertiesByDeclaration = new Dictionary<DeclarationOccurrence, PropertyInfo>(
            propertiesByDeclaration,
            ReferenceEqualityComparer.Instance);
        _propertiesByName = propertyInfos
            .GroupBy(static property => property.Name, StringComparer.Ordinal)
            .ToDictionary(
                static group => group.Key,
                static group => (IReadOnlyList<PropertyInfo>)SafeReadOnlyCollection.Over(group.ToArray()),
                StringComparer.Ordinal);
    }

    private readonly IReadOnlyDictionary<DeclarationOccurrence, PropertyInfo> _propertiesByDeclaration;
    private readonly IReadOnlyDictionary<string, IReadOnlyList<PropertyInfo>> _propertiesByName;

    // The array behind IdentifierResolutions, read in place by position queries.
    private readonly IdentifierResolution[] _identifierResolutions;

    // The array behind Declarations.
    private readonly DeclarationOccurrence[] _declarations;

    // FindResolutions' and FindDeclarations' name indexes. Each is built by its query's first call
    // and published once (null until then, and for a listing with a null entry, which keeps the scan).
    private NameIndex<IdentifierResolution, OrdinalNameHash>? _resolutionsByName;
    private NameIndex<DeclarationOccurrence, OrdinalNameHash>? _declarationsByName;

    /// <summary>
    /// The number of keys in <see cref="FindResolutions"/>' name index, one per resolution with a
    /// name; -1 until a call has built it, and for a listing with a null entry, whose query scans.
    /// </summary>
    internal int ResolutionNameKeys => Volatile.Read(ref _resolutionsByName)?.Keys ?? -1;

    /// <summary>
    /// The number of keys in <see cref="FindDeclarations"/>' name index, one per declaration with a
    /// name; -1 until a call has built it, and for a listing with a null entry, whose query scans.
    /// </summary>
    internal int DeclarationNameKeys => Volatile.Read(ref _declarationsByName)?.Keys ?? -1;

    // FindScopeAt's position index over ScopeVisibilities; null only for a listing with a null entry.
    private readonly ScopePositionIndex? _scopeIndex;

    /// <summary>
    /// The number of intervals in <see cref="FindScopeAt"/>'s position index: at most twice the
    /// number of non-empty scope hulls. -1 when the listing has a null entry and the query scans.
    /// </summary>
    internal int ScopeIndexIntervals => _scopeIndex?.Intervals ?? -1;

    /// <summary>
    /// The work building <see cref="FindScopeAt"/>'s position index took: the candidate comparisons
    /// and expiry checks of its sweep, O(S log S) for S non-empty hulls. A function of the listing
    /// alone, unlike elapsed time. -1 when the listing has a null entry and the query scans.
    /// </summary>
    internal long ScopeIndexBuildSteps => _scopeIndex?.BuildSteps ?? -1;

    /// <summary>
    /// Whether the resolution sites' starts AND ends both never decrease in listing order. The
    /// builder lists sites by start, then end, so this holds whenever no site strictly contains
    /// another — the usual case for a parsed document, whose identifier sites are written names
    /// that do not overlap. Position queries then binary-search the listing; otherwise (for
    /// example a host-built tree with nested sites, or an unordered listing) they scan it.
    /// </summary>
    internal bool ResolutionSitesAreMonotone { get; }

    /// <summary>
    /// Root algorithm the model was built from.
    /// </summary>
    public Algorithm Root { get; }

    /// <summary>
    /// Source-backed identifier references and member occurrences.
    /// Declaration sites are exposed separately through <see cref="Declarations"/>.
    /// </summary>
    public IReadOnlyList<IdentifierOccurrence> IdentifierOccurrences { get; }

    /// <summary>
    /// Source-backed declaration sites of the current document. Declarations
    /// inside a load-elaborated module are sites of the module's text, not of
    /// this document, and are never listed.
    /// </summary>
    public IReadOnlyList<DeclarationOccurrence> Declarations { get; }

    /// <summary>
    /// Semantic classifications for all source-backed identifier sites of the
    /// current document, including declarations. When the occurrence resolves
    /// to a property, <see cref="IdentifierResolution.ResolvedProperty"/>
    /// exposes richer property-centered hover metadata; a module-provided target
    /// has no <see cref="IdentifierResolution.ResolvedDeclaration"/>.
    /// </summary>
    public IReadOnlyList<IdentifierResolution> IdentifierResolutions { get; }

    /// <summary>
    /// All property-centered semantic objects known to this model: every
    /// property declared in the current document, plus the targets its sites
    /// resolve to (referenced builtins and module-provided properties, both
    /// without a <see cref="PropertyInfo.Declaration"/>). Ordinary properties
    /// expose parameter information, conditional properties expose branch-head
    /// summaries, and builtins are represented conservatively when their
    /// callable shape is known.
    /// </summary>
    public IReadOnlyList<PropertyInfo> PropertyInfos { get; }

    /// <summary>
    /// The lexical scope regions of this program with their resolved visible-name
    /// sets, root first. Regions are the source hulls of scope content, so nested
    /// scopes appear as contained spans; each region's symbols already apply
    /// shadowing, open dedup/ambiguity, and direct-beats-open precedence, and
    /// exclude prelude names (see <see cref="PreludeCatalog.Symbols"/>). Scopes share
    /// immutable storage (a symbol seen from several scopes is one
    /// <see cref="VisibleSymbol"/> instance), so enumerating every symbol of every scope
    /// costs what its logical output does while the model retains far less.
    /// </summary>
    public IReadOnlyList<ScopeVisibility> ScopeVisibilities { get; }

    /// <summary>
    /// Finds the innermost scope region containing the supplied position (a region is a
    /// half-open source hull, so a position at the hull's exclusive end is outside it),
    /// falling back to the root scope for positions outside every nested region.
    /// </summary>
    /// <remarks>
    /// Of the regions containing the position, the deepest (<see cref="ScopeVisibility.NestingDepth"/>)
    /// wins; at equal depth the inner hull — the later start, then the earlier end — and of
    /// identical hulls the one listed first in <see cref="ScopeVisibilities"/>. The root is the
    /// first listed scope without a span (a new empty scope when none is listed). The query
    /// binary-searches a position index the model builds once (O(log S) for S scope regions)
    /// instead of inspecting every region.
    /// </remarks>
    public ScopeVisibility FindScopeAt(SourcePosition position)
        => FindScope<UncountedScopeProbes>(position);

    /// <summary>
    /// Test seam: <see cref="FindScopeAt"/>'s own query, which also reports the entries it
    /// inspected. These are the index starts its binary search compared with the position, at
    /// most ⌊log₂ I⌋ + 1 for I = <see cref="ScopeIndexIntervals"/>, or the listed scopes the
    /// fallback scan visited. The count depends only on the listing and the position, unlike
    /// elapsed time. The public query runs the same code with a counter that compiles to nothing.
    /// </summary>
    internal ScopeVisibility FindScopeAtCounted(SourcePosition position, out int probes)
    {
        CountedScopeProbes.Count = 0;
        var scope = FindScope<CountedScopeProbes>(position);
        probes = CountedScopeProbes.Count;
        return scope;
    }

    // The query behind FindScopeAt and its counted seam. It is generic over a struct counter, so
    // the JIT compiles a separate body for each counter. UncountedScopeProbes' empty static calls
    // vanish from the public query, which therefore compiles as it did before the seam.
    private ScopeVisibility FindScope<TProbes>(SourcePosition position)
        where TProbes : struct, IScopeProbes
        => _scopeIndex is { } index
            ? index.Find<TProbes>(position) ?? new ScopeVisibility(Span: null, Symbols: [])
            : ScanScopes<TProbes>(position);

    /// <summary>
    /// Counts the entries a position query inspects (<see cref="FindScopeAtCounted"/>,
    /// <see cref="FindResolutionAtCounted"/>).
    /// </summary>
    private interface IScopeProbes
    {
        static abstract void Probe();
    }

    /// <summary>The public query's counter: it counts nothing, and its calls compile to nothing.</summary>
    private readonly struct UncountedScopeProbes : IScopeProbes
    {
        public static void Probe()
        {
        }
    }

    /// <summary>The seam's counter: one per inspected entry, kept per thread so concurrent queries do not mix.</summary>
    private readonly struct CountedScopeProbes : IScopeProbes
    {
        [ThreadStatic] private static int t_count;

        public static int Count
        {
            get => t_count;
            set => t_count = value;
        }

        public static void Probe() => t_count++;
    }

    /// <summary>
    /// The former query, kept for a listing the index refuses: one with a null entry (only the
    /// internal constructor can receive one), on which every scan throws as it always did. Each
    /// visited scope is one probe.
    /// </summary>
    private ScopeVisibility ScanScopes<TProbes>(SourcePosition position)
        where TProbes : struct, IScopeProbes
    {
        ScopeVisibility? root = null;
        ScopeVisibility? best = null;
        SourceSpan? bestHull = null;
        foreach (var scope in ScopeVisibilities)
        {
            TProbes.Probe();
            if (scope.Span is not { } hull)
            {
                root ??= scope;
                continue;
            }

            if (!hull.Contains(position))
                continue;

            if (best is null
                || scope.NestingDepth > best.NestingDepth
                || (scope.NestingDepth == best.NestingDepth && bestHull is { } current && IsInnerSpan(hull, current)))
            {
                best = scope;
                bestHull = hull;
            }
        }

        return best ?? root ?? new ScopeVisibility(Span: null, Symbols: []);
    }

    /// <summary>
    /// The full effective visible-name set at the supplied position: the innermost
    /// scope's resolved symbols followed by the prelude names they do not shadow.
    /// Dot-only intrinsics (<see cref="PreludeCatalog.DotIntrinsicSymbols"/>) are
    /// not bare-name-visible and are deliberately excluded. The returned read-only list
    /// reads the scope's shared storage in place rather than copying it.
    /// </summary>
    public IReadOnlyList<VisibleSymbol> GetVisibleSymbolsAt(SourcePosition position)
    {
        var scope = FindScopeAt(position);
        if (scope.View is { } view)
        {
            // A builder scope's names are unique and name-indexed: the merged list reads the
            // scope's shared view in place and keeps only the prelude symbols it does not shadow
            // (each checked by one name lookup), instead of copying the scope per query.
            var unshadowed = new List<VisibleSymbol>(PreludeSymbols.Count);
            foreach (var symbol in PreludeSymbols)
            {
                if (view.Find(symbol.Name) is null)
                    unshadowed.Add(symbol);
            }

            return SafeReadOnlyCollection.OverList(
                new MergedVisibleSymbolList(view, unshadowed.ToArray()));
        }

        var result = new List<VisibleSymbol>(scope.Symbols.Count + PreludeSymbols.Count);
        result.AddRange(scope.Symbols);

        var shadowed = new HashSet<string>(StringComparer.Ordinal);
        foreach (var symbol in scope.Symbols)
            shadowed.Add(symbol.Name);

        foreach (var symbol in PreludeSymbols)
        {
            if (!shadowed.Contains(symbol.Name))
                result.Add(symbol);
        }

        return SafeReadOnlyCollection.Over(result.ToArray());
    }

    /// <summary>
    /// The prelude names of the prelude this model resolved against: <see cref="PreludeCatalog.Symbols"/>,
    /// plus the host operations of the parse the model was built from — ambient prelude members
    /// the owner walk reaches exactly like a builtin.
    /// </summary>
    internal IReadOnlyList<VisibleSymbol> PreludeSymbols { get; init; } = PreludeCatalog.Symbols;

    /// <summary>
    /// True when <paramref name="candidate"/> is the more deeply nested of two
    /// containing scope hulls: it starts later, or starts identically and ends
    /// earlier. Well-formed scope hulls nest, so this picks the innermost region.
    /// </summary>
    private static bool IsInnerSpan(SourceSpan candidate, SourceSpan current)
    {
        var byStart = candidate.Start.CompareTo(current.Start);
        return byStart != 0 ? byStart > 0 : candidate.End < current.End;
    }

    /// <summary>
    /// <see cref="FindScopeAt"/>'s position index (KL-05). The starts and ends of the non-empty
    /// hulls cut the document into intervals over which the set of containing hulls is constant,
    /// so one winner — the scope the former scan over every region selected for any position of
    /// the interval — serves the whole interval. A sweep over those boundaries records each
    /// interval's winner, merging neighbors with the same one, and a query binary-searches them.
    /// Building costs O(S log S) time and O(S) storage for S scopes, whatever their nesting,
    /// overlap or ties; the index holds the listing's own instances and copies no symbol.
    /// </summary>
    private sealed class ScopePositionIndex
    {
        // Interval i holds the positions from _starts[i] up to, not including, _starts[i + 1]; the
        // last one, past every hull, has no end. _winners[i] is the interval's scope, or null where
        // no non-empty hull contains it. Positions before _starts[0] are in no hull either.
        private readonly SourcePosition[] _starts;
        private readonly ScopeVisibility?[] _winners;
        private readonly ScopeVisibility? _root;

        private ScopePositionIndex(SourcePosition[] starts, ScopeVisibility?[] winners, ScopeVisibility? root, long buildSteps)
        {
            _starts = starts;
            _winners = winners;
            _root = root;
            BuildSteps = buildSteps;
        }

        public int Intervals => _starts.Length;

        /// <summary>The steps the build's sweep took (<see cref="CandidateOrder"/>).</summary>
        public long BuildSteps { get; }

        /// <summary>
        /// The containing scope the scan selects, else the root; null when the listing has neither.
        /// Each start compared with the position is one probe: at most ⌊log₂ I⌋ + 1 for I intervals.
        /// </summary>
        public ScopeVisibility? Find<TProbes>(SourcePosition position)
            where TProbes : struct, IScopeProbes
        {
            // The number of intervals starting at or before the position; the last of them holds it.
            var starts = _starts;
            var low = 0;
            var high = starts.Length;
            while (low < high)
            {
                TProbes.Probe();
                var middle = low + ((high - low) >> 1);
                if (starts[middle] <= position)
                    low = middle + 1;
                else
                    high = middle;
            }

            return (low > 0 ? _winners[low - 1] : null) ?? _root;
        }

        /// <summary>The index of the listing, or null when an entry is null (the scan's domain).</summary>
        public static ScopePositionIndex? Build(ScopeVisibility[] scopes)
        {
            ScopeVisibility? root = null;
            var hulls = 0;
            foreach (var scope in scopes)
            {
                if (scope is null)
                    return null;
                if (scope.Span is not { } hull)
                    root ??= scope;
                else if (hull.Start < hull.End)
                    hulls++;
            }

            // An empty hull contains no position, so only non-empty hulls enter the sweep: their
            // listing indices by start, and every start and end, where containment can change.
            var byStart = new int[hulls];
            var hullStarts = new SourcePosition[hulls];
            var boundaries = new SourcePosition[2 * hulls];
            var count = 0;
            for (var i = 0; i < scopes.Length; i++)
            {
                if (scopes[i].Span is { } hull && hull.Start < hull.End)
                {
                    byStart[count] = i;
                    hullStarts[count] = hull.Start;
                    boundaries[2 * count] = hull.Start;
                    boundaries[(2 * count) + 1] = hull.End;
                    count++;
                }
            }

            Array.Sort(hullStarts, byStart);
            Array.Sort(boundaries);

            // At each distinct boundary the queue holds every hull starting at or before it, the
            // scan's choice first; a hull ending at or before the boundary no longer contains it
            // and leaves when it surfaces. The first remaining hull then contains the whole
            // interval up to the next boundary and is preferred over every other that does.
            var order = new CandidateOrder(scopes);
            var candidates = new PriorityQueue<int, int>(hulls, order);
            var starts = new SourcePosition[boundaries.Length];
            var winners = new ScopeVisibility?[boundaries.Length];
            var intervals = 0;
            var entered = 0;
            for (var b = 0; b < boundaries.Length; b++)
            {
                var boundary = boundaries[b];
                if (b > 0 && boundaries[b - 1] == boundary)
                    continue;

                for (; entered < hulls && hullStarts[entered] <= boundary; entered++)
                    candidates.Enqueue(byStart[entered], byStart[entered]);
                while (candidates.TryPeek(out var first, out _) && order.HasEnded(first, boundary))
                    candidates.Dequeue();

                var winner = candidates.TryPeek(out var selected, out _) ? scopes[selected] : null;
                if (intervals > 0 && ReferenceEquals(winners[intervals - 1], winner))
                    continue;
                starts[intervals] = boundary;
                winners[intervals] = winner;
                intervals++;
            }

            Array.Resize(ref starts, intervals);
            Array.Resize(ref winners, intervals);
            return new ScopePositionIndex(starts, winners, root, order.Steps);
        }

        /// <summary>
        /// The sweep's only view of its candidates, the listing indices of the non-empty hulls: the
        /// scan's preference between two of them and whether one has ended. Each answer is one step
        /// of the build's work, counted in <see cref="Steps"/>. A hull enters the queue once and
        /// leaves it at most once, at O(log S) comparisons a move, so a build takes O(S log S) steps.
        /// A sweep that revisited every candidate at each boundary would take O(S²) on nested or
        /// overlapping hulls.
        /// </summary>
        private sealed class CandidateOrder(ScopeVisibility[] scopes) : IComparer<int>
        {
            public long Steps { get; private set; }

            /// <summary>Whether the candidate's hull ends at or before the boundary, so it no longer contains it.</summary>
            public bool HasEnded(int candidate, SourcePosition boundary)
            {
                Steps++;
                return scopes[candidate].Span!.Value.End <= boundary;
            }

            /// <summary>
            /// Orders two containing hulls by listing index as the scan prefers them (negative when
            /// <paramref name="left"/> wins): the deeper scope, at equal depth the inner hull
            /// (<see cref="IsInnerSpan"/>), and of identical hulls at one depth the earlier listed —
            /// the scan replaces its choice only by a strictly preferred scope, so it keeps the first.
            /// </summary>
            public int Compare(int left, int right)
            {
                Steps++;
                var leftScope = scopes[left];
                var rightScope = scopes[right];
                if (leftScope.NestingDepth != rightScope.NestingDepth)
                    return leftScope.NestingDepth > rightScope.NestingDepth ? -1 : 1;

                var leftHull = leftScope.Span!.Value;
                var rightHull = rightScope.Span!.Value;
                if (IsInnerSpan(leftHull, rightHull))
                    return -1;
                if (IsInnerSpan(rightHull, leftHull))
                    return 1;
                return left.CompareTo(right);
            }
        }
    }

    /// <summary>
    /// Finds the first identifier resolution whose site contains the supplied position
    /// (half-open: the site's first column is inside, the column just past its last
    /// character is not).
    /// </summary>
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    public IdentifierResolution? FindResolutionAt(SourcePosition position)
        => FindResolution<UncountedScopeProbes>(position);

    /// <summary>
    /// Test seam: <see cref="FindResolutionAt"/>'s own query, which also reports the sites it
    /// inspected. These are the sites its binary search compared with the position, at most
    /// ⌊log₂ R⌋ + 1 for R listed resolutions, or the sites the scan of a listing that is not
    /// monotone visited. The count depends only on the listing and the position, unlike elapsed
    /// time. The public query runs the same code with a counter that compiles to nothing.
    /// </summary>
    internal IdentifierResolution? FindResolutionAtCounted(SourcePosition position, out int probes)
    {
        CountedScopeProbes.Count = 0;
        var resolution = FindResolution<CountedScopeProbes>(position);
        probes = CountedScopeProbes.Count;
        return resolution;
    }

    // The query behind FindResolutionAt and its counted seam, generic over a struct counter like
    // FindScope. It is inlined into both, and the public query is not inlined into its callers,
    // as the pre-seam method (469 bytes) never was. So callers call it exactly as before, and its
    // body is the pre-seam body (UncountedScopeProbes' calls vanish) except that its three returns
    // share one epilogue: 453 bytes (measured 2026-11-21, Release, tiering off). Behind a one-line
    // wrapper that callers inline, every caller re-packed the position for the call instead.
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)]
    private IdentifierResolution? FindResolution<TProbes>(SourcePosition position)
        where TProbes : struct, IScopeProbes
    {
        var resolutions = _identifierResolutions;
        if (!ResolutionSitesAreMonotone)
        {
            foreach (var resolution in resolutions)
            {
                TProbes.Probe();
                if (resolution.Occurrence.Span.Contains(position))
                    return resolution;
            }

            return null;
        }

        // With starts and ends both non-decreasing, the sites containing the position are one
        // contiguous run: every site before the first one that ends after the position ends at or
        // before it, and every site from there on starts no earlier than that first one. So the
        // first containing site in listing order is that first one, when it starts at or before
        // the position, and there is none otherwise.
        var low = 0;
        var high = resolutions.Length;
        while (low < high)
        {
            TProbes.Probe();
            var middle = low + ((high - low) >> 1);
            if (resolutions[middle].Occurrence.Span.End > position)
                high = middle;
            else
                low = middle + 1;
        }

        return low < resolutions.Length && resolutions[low].Occurrence.Span.Start <= position
            ? resolutions[low]
            : null;
    }

    /// <summary>
    /// Whether the sites' starts and ends both never decrease in listing order, which makes
    /// <see cref="FindResolutionAt"/> a binary search. A null entry fails the check, so the query
    /// keeps the plain scan for it.
    /// </summary>
    private static bool SitesAreMonotone(IdentifierResolution[] resolutions)
    {
        SourceSpan? previous = null;
        foreach (var resolution in resolutions)
        {
            if (resolution?.Occurrence is not { } occurrence)
                return false;

            var span = occurrence.Span;
            if (previous is { } last && (span.Start < last.Start || span.End < last.End))
                return false;
            previous = span;
        }

        return true;
    }

    /// <summary>
    /// Finds all identifier resolutions with the supplied name.
    /// </summary>
    /// <remarks>
    /// Names compare ordinally. The resolutions come in <see cref="IdentifierResolutions"/> order, in
    /// a new read-only list for each call that finds any. The first call indexes the resolutions by
    /// name. Subsequent calls binary-search the index and inspect the sites with the requested hash.
    /// </remarks>
    public IReadOnlyList<IdentifierResolution> FindResolutions(string name)
    {
        ArgumentNullException.ThrowIfNull(name);
        return ResolutionsNamed<UncountedNameProbes>(name);
    }

    /// <summary>
    /// Finds all declaration occurrences with the supplied name.
    /// </summary>
    /// <remarks>
    /// Names compare ordinally. The declarations come in <see cref="Declarations"/> order, in a new
    /// read-only list for each call that finds any. The first call indexes the declarations by name,
    /// then subsequent calls binary-search the index and inspect the declarations with the requested hash.
    /// </remarks>
    public IReadOnlyList<DeclarationOccurrence> FindDeclarations(string name)
    {
        ArgumentNullException.ThrowIfNull(name);
        return DeclarationsNamed<UncountedNameProbes>(name);
    }

    /// <summary>
    /// Counts the comparisons that locate the query's hash run. The binary search makes at most
    /// ⌊log₂ K⌋ + 1 comparisons for K = <see cref="ResolutionNameKeys"/> greater than zero. It then
    /// compares each hash in the run and the following hash, if present. The count depends only on
    /// the listing, the name and the process's string hashing, unlike elapsed time. The public query
    /// runs the same code with a counter that compiles to nothing.
    /// </summary>
    internal IReadOnlyList<IdentifierResolution> FindResolutionsCounted(string name, out int probes)
    {
        ArgumentNullException.ThrowIfNull(name);
        CountedNameProbes.Count = 0;
        var found = ResolutionsNamed<CountedNameProbes>(name);
        probes = CountedNameProbes.Count;
        return found;
    }

    /// <summary>
    /// Counts hash-run search comparisons as in <see cref="FindResolutionsCounted"/>, over
    /// <see cref="DeclarationNameKeys"/> keys.
    /// </summary>
    internal IReadOnlyList<DeclarationOccurrence> FindDeclarationsCounted(string name, out int probes)
    {
        ArgumentNullException.ThrowIfNull(name);
        CountedNameProbes.Count = 0;
        var found = DeclarationsNamed<CountedNameProbes>(name);
        probes = CountedNameProbes.Count;
        return found;
    }

    /// <summary>
    /// Test seam: <see cref="FindResolutions"/>' query through a new index whose hash is the name's
    /// length, so that all names of one length share a hash and its key run. String hashes differ
    /// between processes and rarely collide, so this is how tests reach the shared-hash path:
    /// flagged runs, names compared item by item, and a run that another name owns alone. Null
    /// when the listing has a null entry.
    /// </summary>
    internal IReadOnlyList<IdentifierResolution>? FindResolutionsByLengthHash(string name)
    {
        ArgumentNullException.ThrowIfNull(name);
        return NameIndex<IdentifierResolution, LengthNameHash>.Build<ResolutionNames>(_identifierResolutions)
            ?.Find<ResolutionNames, UncountedNameProbes>(name);
    }

    /// <summary>Test seam: <see cref="FindDeclarations"/>' query through a new length-hashed index (see <see cref="FindResolutionsByLengthHash"/>).</summary>
    internal IReadOnlyList<DeclarationOccurrence>? FindDeclarationsByLengthHash(string name)
    {
        ArgumentNullException.ThrowIfNull(name);
        return NameIndex<DeclarationOccurrence, LengthNameHash>.Build<DeclarationNames>(_declarations)
            ?.Find<DeclarationNames, UncountedNameProbes>(name);
    }

    // The queries behind FindResolutions, FindDeclarations and their counted seams, generic over a
    // struct counter like FindScope. A listing with a null entry gets no index and keeps the former
    // scan, which throws on that entry as it always did.
    private IReadOnlyList<IdentifierResolution> ResolutionsNamed<TProbes>(string name)
        where TProbes : struct, INameProbes
    {
        var index = Volatile.Read(ref _resolutionsByName)
            ?? Publish(ref _resolutionsByName, NameIndex<IdentifierResolution, OrdinalNameHash>.Build<ResolutionNames>(_identifierResolutions));
        return index is not null ? index.Find<ResolutionNames, TProbes>(name) : ScanResolutions(name);
    }

    private IReadOnlyList<DeclarationOccurrence> DeclarationsNamed<TProbes>(string name)
        where TProbes : struct, INameProbes
    {
        var index = Volatile.Read(ref _declarationsByName)
            ?? Publish(ref _declarationsByName, NameIndex<DeclarationOccurrence, OrdinalNameHash>.Build<DeclarationNames>(_declarations));
        return index is not null ? index.Find<DeclarationNames, TProbes>(name) : ScanDeclarations(name);
    }

    // The former queries, verbatim. Their lambdas capture the name, so they live apart from the
    // indexed path, which would otherwise allocate the closure on every call.
    private IReadOnlyList<IdentifierResolution> ScanResolutions(string name)
        => SafeReadOnlyCollection.Over(IdentifierResolutions.Where(resolution => resolution.Occurrence.Name == name).ToArray());

    private IReadOnlyList<DeclarationOccurrence> ScanDeclarations(string name)
        => SafeReadOnlyCollection.Over(Declarations.Where(declaration => declaration.Name == name).ToArray());

    /// <summary>
    /// Publishes a name index built by a query's first call. When calls race, the first published
    /// index wins and every caller uses it. A refused (null) index is not kept, so its query scans.
    /// </summary>
    private static NameIndex<T, OrdinalNameHash>? Publish<T>(ref NameIndex<T, OrdinalNameHash>? field, NameIndex<T, OrdinalNameHash>? built)
        where T : class
        => built is null ? null : Interlocked.CompareExchange(ref field, built, null) ?? built;

    /// <summary>How a <see cref="NameIndex{T, THash}"/> hashes names. Equal names must hash alike.</summary>
    private interface INameHash
    {
        static abstract int Of(string name);
    }

    /// <summary>The models' hash: the ordinal string hash.</summary>
    private readonly struct OrdinalNameHash : INameHash
    {
        public static int Of(string name) => name.GetHashCode();
    }

    /// <summary>The test seams' hash: the name's length (<see cref="FindResolutionsByLengthHash"/>).</summary>
    private readonly struct LengthNameHash : INameHash
    {
        public static int Of(string name) => name.Length;
    }

    /// <summary>Counts the index keys a name query inspects (<see cref="FindResolutionsCounted"/>).</summary>
    private interface INameProbes
    {
        static abstract void Probe();
    }

    /// <summary>The public queries' counter: it counts nothing, and its calls compile to nothing.</summary>
    private readonly struct UncountedNameProbes : INameProbes
    {
        public static void Probe()
        {
        }
    }

    /// <summary>The seams' counter: one per inspected key, kept per thread so concurrent queries do not mix.</summary>
    private readonly struct CountedNameProbes : INameProbes
    {
        [ThreadStatic] private static int t_count;

        public static int Count
        {
            get => t_count;
            set => t_count = value;
        }

        public static void Probe() => t_count++;
    }

    /// <summary>How a <see cref="NameIndex{T, THash}"/> reads the name of a listed item.</summary>
    private interface INamedItems<T>
    {
        /// <summary>
        /// The item's name. False for an item the former scan could not read, which made it throw:
        /// a null entry, or a resolution without an occurrence.
        /// </summary>
        static abstract bool TryGetName(T item, out string? name);
    }

    private readonly struct ResolutionNames : INamedItems<IdentifierResolution>
    {
        public static bool TryGetName(IdentifierResolution item, out string? name)
        {
            name = item?.Occurrence?.Name;
            return item?.Occurrence is not null;
        }
    }

    private readonly struct DeclarationNames : INamedItems<DeclarationOccurrence>
    {
        public static bool TryGetName(DeclarationOccurrence item, out string? name)
        {
            name = item?.Name;
            return item is not null;
        }
    }

    /// <summary>
    /// The name index of <see cref="FindResolutions"/> or <see cref="FindDeclarations"/>: one key for
    /// each listed item with a name, sorted. A key holds the hash of the item's name in its high half
    /// (<typeparamref name="THash"/>: the ordinal string hash, except in a test seam) and the item's
    /// listing position in its low half, so the items of one hash lie
    /// together in listing order. A query binary-searches its name's hash and reads only the keys
    /// with that hash, taking O(log N + H) key inspections for N keys and H entries with that hash. Nearly
    /// always, one name owns its hash. Then the query compares the name of the run's first item
    /// and copies the run. When the build finds two names with one hash, it flags that run's keys,
    /// and the query compares the name of each item in the run. The index stores 8 bytes per item
    /// and nothing per name, and reads the items from the model's own listing. A build hashes each
    /// name once, sorts the keys (O(N log N)) and compares the names within each run. Because only
    /// a query's first call builds the index, a model that is never queried by name stores and
    /// builds nothing. An item whose name is null gets no key. The former scan never matched such
    /// an item, because a null query name is refused.
    /// </summary>
    private sealed class NameIndex<T, THash>
        where T : class
        where THash : struct, INameHash
    {
        // The low half of a key: the listing position in bits 0-30 (a position is below 2^31), and in
        // bit 31 the flag of a run whose hash more than one name shares. Every key of such a run has
        // the flag, so the run keeps its listing order and its place among the other hashes.
        private const long PositionBits = 0x7FFF_FFFF;
        private const long SharedHash = 0x8000_0000;

        private readonly T[] _listing;
        private readonly long[] _keys;

        private NameIndex(T[] listing, long[] keys)
        {
            _listing = listing;
            _keys = keys;
        }

        public int Keys => _keys.Length;

        /// <summary>
        /// The items named <paramref name="name"/>, in listing order, in a new list (the shared empty
        /// one when none). Each comparison to locate the start or end of the hash run is one probe.
        /// </summary>
        public IReadOnlyList<T> Find<TNames, TProbes>(string name)
            where TNames : struct, INamedItems<T>
            where TProbes : struct, INameProbes
        {
            // The first key with the name's hash: the hash in the high half, zero in the low half.
            var hash = THash.Of(name);
            var first = (long)hash << 32;
            var keys = _keys;
            var low = 0;
            var high = keys.Length;
            while (low < high)
            {
                TProbes.Probe();
                var middle = low + ((high - low) >> 1);
                if (keys[middle] < first)
                    low = middle + 1;
                else
                    high = middle;
            }

            var end = low;
            while (end < keys.Length)
            {
                TProbes.Probe();
                if ((int)(keys[end] >> 32) != hash)
                    break;
                end++;
            }

            if (end == low)
                return SafeReadOnlyCollection<T>.Empty;

            var listing = _listing;
            T[] found;
            if ((keys[low] & SharedHash) == 0)
            {
                // One name owns the hash: the run is that name's items, or none of the query's.
                if (!HasName<TNames>(listing[(int)(keys[low] & PositionBits)], name))
                    return SafeReadOnlyCollection<T>.Empty;
                found = new T[end - low];
                var run = keys.AsSpan(low, found.Length);
                var target = found.AsSpan(0, run.Length);
                for (var i = 0; i < run.Length; i++)
                    target[i] = listing[(int)(run[i] & PositionBits)];
                return SafeReadOnlyCollection.Over(found);
            }

            // Count matches before allocating. A shared hash can have many sites even on a miss.
            var count = 0;
            for (var i = low; i < end; i++)
            {
                if (HasName<TNames>(listing[(int)(keys[i] & PositionBits)], name))
                    count++;
            }

            if (count == 0)
                return SafeReadOnlyCollection<T>.Empty;

            found = new T[count];
            var next = 0;
            for (var i = low; i < end; i++)
            {
                var item = listing[(int)(keys[i] & PositionBits)];
                if (HasName<TNames>(item, name))
                    found[next++] = item;
            }
            return SafeReadOnlyCollection.Over(found);
        }

        /// <summary>The index of the listing, or null when an item is unreadable (the scan's domain).</summary>
        public static NameIndex<T, THash>? Build<TNames>(T[] listing)
            where TNames : struct, INamedItems<T>
        {
            var keys = new long[listing.Length];
            var named = 0;
            for (var position = 0; position < listing.Length; position++)
            {
                if (!TNames.TryGetName(listing[position], out var name))
                    return null;
                if (name is not null)
                    keys[named++] = ((long)THash.Of(name) << 32) | (uint)position;
            }

            if (named < keys.Length)
                Array.Resize(ref keys, named);
            Array.Sort(keys);

            // Flag every run in which an item's name differs from the name of the run's first item.
            for (var start = 0; start < keys.Length;)
            {
                var hash = (int)(keys[start] >> 32);
                TNames.TryGetName(listing[(int)(keys[start] & PositionBits)], out var runName);
                var shared = false;
                var end = start + 1;
                for (; end < keys.Length && (int)(keys[end] >> 32) == hash; end++)
                    shared |= !HasName<TNames>(listing[(int)(keys[end] & PositionBits)], runName!);
                if (shared)
                {
                    for (var i = start; i < end; i++)
                        keys[i] |= SharedHash;
                }

                start = end;
            }

            return new NameIndex<T, THash>(listing, keys);
        }

        private static bool HasName<TNames>(T item, string name)
            where TNames : struct, INamedItems<T>
        {
            TNames.TryGetName(item, out var itemName);
            return string.Equals(itemName, name, StringComparison.Ordinal);
        }
    }

    /// <summary>
    /// Finds the first property-centered semantic object whose identifier site
    /// contains the supplied position.
    /// </summary>
    public PropertyInfo? FindPropertyAt(SourcePosition position)
        => FindResolutionAt(position)?.ResolvedProperty;

    /// <summary>
    /// Finds the property-centered semantic object associated with a specific
    /// declaration occurrence. The occurrence must be the canonical instance
    /// returned by this model; a value-equal occurrence constructed elsewhere is
    /// not a declaration identity.
    /// </summary>
    public PropertyInfo? FindPropertyByDeclaration(DeclarationOccurrence declaration)
    {
        ArgumentNullException.ThrowIfNull(declaration);
        return _propertiesByDeclaration.TryGetValue(declaration, out var property)
            ? property
            : null;
    }

    /// <summary>
    /// Finds all known property-centered semantic objects with the supplied name.
    /// </summary>
    public IReadOnlyList<PropertyInfo> FindProperties(string name)
    {
        ArgumentNullException.ThrowIfNull(name);
        return _propertiesByName.TryGetValue(name, out var properties)
            ? properties
            : [];
    }
}
