using System.Collections.Immutable;

namespace KatLang;

/// <summary>
/// AUTOMATIC PARAMETER FORWARDING: rewrites bare value-position references to algorithms that
/// REQUIRE supplied arguments into explicit <see cref="Expr.Call"/> nodes whose arguments hand on
/// the callee's parameters. A reference to an algorithm that accepts zero supplied arguments — no
/// parameters, or only a top-level collecting parameter — is never rewritten: it stays a
/// property-style value demand, which reads the property cache (Q-03, see
/// <see cref="RequiresSuppliedArguments"/>). Must run after <see cref="ParameterDetector"/>, which
/// is NAME RESOLUTION: every written name is decided there, and this pass never re-selects one.
///
/// <para><b>Forwarding preserves existing bindings (Q-04, decided September 28 2026).</b>
/// Automatic parameter forwarding must not change what an existing name refers to, so each
/// callee parameter is supplied by a PARAMETER binding only: the referencing algorithm's own
/// (written, inferred), or — through <see cref="ForwardableParameters"/> — the enclosing
/// parameter binding a written reference of that name already denotes (an ancestor's captured
/// parameter or a clause-branch binder). Properties, opened names, module members and prelude
/// builtins are never forwarded as parameters. Only when no parameter binding exists does an
/// inferring algorithm receive a new parameter, appended to its
/// <see cref="Algorithm.User.ParameterPatterns"/> and marked
/// (<see cref="Algorithm.User.ForwardingParameterStart"/>): it completes the signature for
/// callers and is never what a written name denotes. A closed parameter list receives nothing.</para>
///
/// <para><b>Internal by design (v0.8.187):</b> this is ONE stage of the authoritative
/// front-end pipeline (<see cref="FrontEndPipeline"/>), not a host-composable API — its
/// output still lacks the <see cref="PropertyExposureResolver"/> finalization the
/// evaluator's stored-exposure checks rely on (see
/// <c>FrontEndElaborationBoundaryTests</c>). Hosts elaborate through
/// <see cref="Parser.Parse(string)"/> / <see cref="Parser.ParseAsync"/> or run through
/// <see cref="KatLangEngine"/>, which always execute the complete pass sequence.</para>
/// </summary>
internal static class ImplicitArgumentResolver
{
    /// <summary>
    /// Processes a root algorithm, resolving all implicit arguments throughout the tree.
    /// Returns a new AST where every bare value-position reference to an algorithm that
    /// requires supplied arguments has been rewritten into an explicit call with lifted
    /// parameters.
    ///
    /// <para><b>Host-AST contract:</b> the root may be a preconstructed (host-built)
    /// AST. A non-recursive structural preflight runs BEFORE this pass's recursive
    /// rewriting walk and throws <see cref="ArgumentException"/> for a structurally
    /// unsafe root (structural depth beyond
    /// <see cref="EvaluationLimits.MaxSupportedAstDepth"/> — the shared fat-frame
    /// elaboration ceiling, measured with a ≥2x stack margin for this pass on the
    /// documented 1 MiB thread baseline — or a cyclic node graph), matching the
    /// <see cref="Semantics.SemanticModelBuilder"/> convention, instead of
    /// overflowing the process stack. Roots reaching this pass through the front-end
    /// pipeline are already gated and pass unchanged.</para>
    /// </summary>
    /// <exception cref="ArgumentException">
    /// The root exceeds the structural AST depth limit or contains a reference cycle.
    /// </exception>
    /// <remarks>
    /// Shared subtrees (acyclic DAGs) are legal and DAG-safe: a node referenced from several
    /// parents resolves exactly like the equivalent duplicated tree (dependency collection is
    /// name-deduplicated, so multiplicities never mattered), while every walk of this pass is
    /// reference-identity memoized per constant-context region — traversal work is bounded by
    /// the DISTINCT reachable nodes, never the number of root-to-node paths, and the rewritten
    /// output preserves the input's sharing. Memos are run-local (created per resolution,
    /// garbage afterwards).
    /// </remarks>
    public static Algorithm Resolve(Algorithm root)
    {
        if (AstStructuralPreflight.Check(
                root,
                EvaluationLimits.MaxSupportedAstDepth,
                AstConsumerProfile.FullyRecursive) is { } structuralRejection)
        {
            throw new ArgumentException(
                structuralRejection.Kind == AstStructuralViolation.CycleDetected
                    ? "Implicit-argument resolution requires an acyclic AST: the supplied root reaches itself again through its own children."
                    : "Implicit-argument resolution requires a structurally safe AST: the supplied root exceeds the structural AST depth limit of "
                        + $"{EvaluationLimits.MaxSupportedAstDepth} nodes, which protects the host process from stack overflow.",
                nameof(root));
        }

        return ResolvePrevalidated(root);
    }

    /// <summary>
    /// The resolution core behind <see cref="Resolve"/>, without the structural
    /// preflight. Only for callers that ALREADY gated the tree at the shared
    /// elaboration ceiling (the front-end pipeline's common gate); it must never
    /// become reachable with an unvalidated host tree.
    /// </summary>
    internal static Algorithm ResolvePrevalidated(
        Algorithm root,
        FrontEndTraversalObservations? observations = null,
        DiagnosticBag? diagnostics = null)
    {
        return ProcessAlgorithm(
            root,
            parentParamMap: SignatureMap.Empty(observations),
            ForwardableParameters.None,
            isRoot: true,
            observations,
            diagnostics,
            branchContext: null,
            new ResolutionRun { Observations = observations });
    }

    /// <summary>
    /// Run-scoped state of ONE resolution (a <see cref="ResolvePrevalidated"/> or
    /// <see cref="ElaborateDeferredBranch"/> call), threaded through every algorithm-processing
    /// path so an algorithm reached through several paths of a shared (acyclic) host tree —
    /// a property value shared by several properties, a block literal reached from several
    /// rows, a conditional branch body shared by several families — is rewritten once per
    /// SEMANTIC REGION rather than once per path (M4). Run-local: created per resolution,
    /// garbage afterwards — never static, never ambient.
    /// </summary>
    private sealed class ResolutionRun(SourceSpan? importSite = null)
    {
        /// <summary>
        /// The import site of the module content the walk is currently inside (see
        /// <see cref="KatLang.ImportSite"/>): where a refused strict-value forwarding inside
        /// imported content — which carries no source location — is positioned. Null over
        /// the document's own text; a deferred branch run starts from the site its region
        /// recorded. Walk state only: it decides no rewrite and keys no memo.
        /// </summary>
        public SourceSpan? ImportSite = importSite;

        /// <summary>
        /// Enters the content reached through an import edge: a non-null <paramref name="site"/>
        /// becomes the current site for the scope's duration (a nested view inherits the
        /// enclosing site when its own edge carries none); disposal restores the outer site.
        /// </summary>
        public ImportSiteScope EnterImportSite(SourceSpan? site)
        {
            var saved = ImportSite;
            if (site is not null)
                ImportSite = site;
            return new ImportSiteScope(this, saved);
        }

        public readonly struct ImportSiteScope(ResolutionRun run, SourceSpan? saved) : IDisposable
        {
            public void Dispose() => run.ImportSite = saved;
        }

        /// <summary>
        /// Nested algorithms rewritten so far, by <see cref="AlgorithmRegionKey"/>. A family's
        /// NAME only words a branch body's blocked strict-value diagnostics, so a second
        /// family sharing the body reuses the rewrite and REPLAYS those diagnostics under its
        /// own name (see <see cref="AlgorithmRegion.DiagnosticTemplates"/>).
        /// </summary>
        public Dictionary<AlgorithmRegionKey, AlgorithmRegion>? AlgorithmRegions;

        /// <summary>
        /// The free reference names of every algorithm node computed so far (a pure function
        /// of the node — see <see cref="FreeReferenceNames"/>), by node reference.
        /// </summary>
        public Dictionary<Algorithm, CanonicalNameSet>? FreeReferenceNames;
        /// <summary>
        /// FE-3: the shared signature templates of this run (see <see cref="LiftSignature"/>). Run-local:
        /// a template is shared by the owners of ONE resolution and never across parses.
        /// </summary>
        public ImplicitSignatureTemplateInterner Templates => _templates ??= new(Observations);
        private ImplicitSignatureTemplateInterner? _templates;

        /// <summary>The traversal observations of this run (null when none are recorded).</summary>
        public FrontEndTraversalObservations? Observations;

        /// <summary>
        /// FE-3: synthesized implicit-argument bundles shared ACROSS owners, by the exact inputs a
        /// bundle is a pure function of (see <see cref="SharedBundleKey"/>). FE-2 shared one bundle per
        /// callee within a rewrite region; owners whose rewrite contexts give a callee identical
        /// forwarding share it here too, so K owners lifting one L-wide callee keep one bundle.
        /// </summary>
        public Dictionary<SharedBundleKey, OutputBundle>? SharedBundles;

        /// <summary>The capture-name set of each callee pattern list, by list reference (FE-3).</summary>
        public IReadOnlySet<string> CalleeNamesOf(IReadOnlyList<ParameterPattern> patterns)
        {
            if (patterns is ImplicitSignatureTemplate template)
                return template.Facts.NameSet;
            _calleeNames ??= new(ReferenceEqualityComparer.Instance);
            if (!_calleeNames.TryGetValue(patterns, out var names))
            {
                names = new HashSet<string>(ParameterPattern.EnumerateCaptures(patterns).Select(static capture => capture.Name), StringComparer.Ordinal);
                _calleeNames.Add(patterns, names);
            }

            return names;
        }

        private Dictionary<IReadOnlyList<ParameterPattern>, IReadOnlySet<string>>? _calleeNames;

        /// <summary>
        /// The COLLECTING capture names of each callee pattern list (at any pattern level), by list
        /// reference — usually none or one, so a question about them costs O(1) per reference.
        /// </summary>
        public IReadOnlyList<string> CollectingCaptureNamesOf(IReadOnlyList<ParameterPattern> patterns)
        {
            _collectingCaptureNames ??= new(ReferenceEqualityComparer.Instance);
            if (!_collectingCaptureNames.TryGetValue(patterns, out var names))
            {
                IReadOnlyList<ParameterDeclaration> captures = patterns is ImplicitSignatureTemplate template
                    ? template.Facts.Captures
                    : ParameterPattern.FlattenCaptures(patterns);
                names = captures
                    .Where(static capture => capture.Kind == ParameterKind.Collecting)
                    .Select(static capture => capture.Name)
                    .Distinct(StringComparer.Ordinal)
                    .ToArray();
                _collectingCaptureNames.Add(patterns, names);
            }

            return names;
        }

        private Dictionary<IReadOnlyList<ParameterPattern>, IReadOnlyList<string>>? _collectingCaptureNames;

        /// <summary>
        /// Q-04: whether the lifted TAIL shares a capture name with the enclosing parameter bindings a
        /// forwarding owner reuses, by (bindings, tail) reference: the owners of one body share one
        /// bindings instance, so K siblings lifting one L-wide tail under W bindings pay one
        /// min(L, W) test, never K.
        /// </summary>
        public bool TailMeetsForwardable(ImplicitSignatureTemplate tail, ForwardableParameters forwardable)
        {
            _tailMeetsForwardable ??= new();
            var key = (forwardable, tail);
            if (!_tailMeetsForwardable.TryGetValue(key, out var meets))
            {
                var names = tail.Facts.NameSet;
                meets = names.Count <= forwardable.Count
                    ? names.Any(forwardable.Binds)
                    : forwardable.BoundNames.Any(names.Contains);
                _tailMeetsForwardable.Add(key, meets);
            }

            return meets;
        }

        private Dictionary<(ForwardableParameters, ImplicitSignatureTemplate), bool>? _tailMeetsForwardable;

        /// <summary>
        /// THE EXACT-ALIAS RULE: the call arguments that rebuild one alias signature — the callee's own
        /// parameter-pattern list — from its own bindings (<see cref="BuildSourceArguments"/>), by list
        /// reference. A pure function of the list, so every alias of one callee (whose signature is that
        /// callee's interned list) shares ONE immutable bundle, like the FE-2/FE-3 lifted bundles.
        /// </summary>
        public OutputBundle SourceArguments(IReadOnlyList<ParameterPattern> source)
        {
            _sourceArguments ??= new(ReferenceEqualityComparer.Instance);
            if (!_sourceArguments.TryGetValue(source, out var arguments))
            {
                arguments = OutputBundle.From(BuildSourceArguments(source));
                Observations?.RecordImplicitArgumentBundleBuilt(arguments.Count);
                _sourceArguments.Add(source, arguments);
            }

            return arguments;
        }

        private Dictionary<IReadOnlyList<ParameterPattern>, OutputBundle>? _sourceArguments;

        public readonly NameSetInterner ReferenceNameSets = new();
        public readonly SignatureFootprints Footprints = new();
        public readonly BranchContextInterner BranchContexts = new();
    }

    /// <summary>
    /// The minimal complete semantic context of one nested-algorithm rewrite: the node by
    /// REFERENCE; the <see cref="SignatureFootprints"/> projection of the signatures its FREE reference
    /// names see in the visible map (every signature the rewrite can read — the subtree's own
    /// bindings shadow the map, open targets use fresh maps, stored dot-edge fallbacks are
    /// never rewritten); the enclosing PARAMETER bindings its forwarding may reuse (Q-04: the
    /// canonical <see cref="ForwardableParameters"/> content, names and collecting names — a
    /// synthesized argument carries only a binding's spelling and kind, never its owner); for a
    /// conditional branch body the closed binder specification the pattern imposes, by CONTENT
    /// (<see cref="FrontEndRegionKeys.ClosedBranchSpecification"/>) — the head's whole structure,
    /// literal POSITIONS included, when the body is shaped like a bare-forwarding row
    /// (<see cref="FrontEndRegionKeys.BareForwardingBranchHead"/>, <see cref="HasLoneBareRowShape"/>);
    /// and the reporting mode. Two
    /// reaches with equal keys observe identical inputs, whatever path led to them and whatever
    /// else the property loop rewrote in between.
    /// </summary>
    private sealed record AlgorithmRegionKey(
        Algorithm Node,
        CanonicalNameSet Snapshot,
        CanonicalNameSet ForwardableNames,
        CanonicalNameSet ForwardableCollectingNames,
        int? ClosedSpecification,
        bool ReportsDiagnostics)
    {
        public bool Equals(AlgorithmRegionKey? other)
            => other is not null
                && ReferenceEquals(Node, other.Node)
                && Snapshot.Equals(other.Snapshot)
                && ForwardableNames.Equals(other.ForwardableNames)
                && ForwardableCollectingNames.Equals(other.ForwardableCollectingNames)
                && ClosedSpecification == other.ClosedSpecification
                && ReportsDiagnostics == other.ReportsDiagnostics;

        public override int GetHashCode()
            => HashCode.Combine(
                System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(Node),
                Snapshot.GetHashCode(),
                ForwardableNames.GetHashCode(),
                ForwardableCollectingNames.GetHashCode(),
                ClosedSpecification,
                ReportsDiagnostics);
    }

    /// <summary>
    /// The visible signature map of one rewrite: the signature of every property the algorithm
    /// can see, nearest declaration winning. PERSISTENT (FE-1): a nested algorithm that declares
    /// properties EXTENDS its parent's map with just those names, and a deferred branch keeps an
    /// O(1) snapshot, so a scope seeing W signatures with K such nested algorithms costs O(K)
    /// small extensions — never K copies of the W-entry map. A map is written only by the property
    /// loop of the algorithm that created it (its own local names, after each is processed); a
    /// child reads it, extends it, or snapshots it, and an extension or snapshot is independent of
    /// every later write to the map it came from — exactly the copy-on-entry semantics the former
    /// dictionary copy had.
    /// </summary>
    private sealed class SignatureMap
    {
        private ImmutableDictionary<string, CallableSignature> _entries;
        public SignatureVersion Version { get; private set; }
        private readonly FrontEndTraversalObservations? _observations;

        private SignatureMap(ImmutableDictionary<string, CallableSignature> entries, FrontEndTraversalObservations? observations)
        {
            _entries = entries;
            Version = new(entries, null, []);
            _observations = observations;
        }

        /// <summary>A fresh map with no visible signature (a root, an open-target region).</summary>
        public static SignatureMap Empty(FrontEndTraversalObservations? observations)
            => new(ImmutableDictionary.Create<string, CallableSignature>(StringComparer.Ordinal), observations);

        /// <summary>A map over a recorded <see cref="Snapshot"/> (a deferred branch's demand-time run).</summary>
        public static SignatureMap FromSnapshot(ImmutableDictionary<string, CallableSignature> snapshot, FrontEndTraversalObservations? observations)
            => new(snapshot, observations);

        /// <summary>The current entries, frozen: later writes to this map never reach the snapshot.</summary>
        public ImmutableDictionary<string, CallableSignature> Snapshot => _entries;

        public bool TryGetValue(string name, [System.Diagnostics.CodeAnalysis.MaybeNullWhen(false)] out CallableSignature signature)
            => _entries.TryGetValue(name, out signature);

        public bool ContainsKey(string name) => _entries.ContainsKey(name);

        /// <summary>A NEW map: these entries overlaid with <paramref name="locals"/> (local wins).</summary>
        public SignatureMap Extend(IReadOnlyDictionary<string, CallableSignature> locals)
        {
            var extended = _entries.ToBuilder();
            foreach (var (name, signature) in locals)
            {
                extended[name] = signature;
                _observations?.RecordContextEntryWritten();
            }

            var result = new SignatureMap(extended.ToImmutable(), _observations);
            result.Version = new(result._entries, Version, locals.Keys.ToArray());
            return result;
        }

        /// <summary>Records a processed property's signature in THIS map (its creator's property loop only).</summary>
        public void Set(string name, CallableSignature signature)
        {
            _entries = _entries.SetItem(name, signature);
            Version = new(_entries, Version, [name]);
            _observations?.RecordContextEntryWritten();
        }
    }

    /// <summary>
    /// Q-04 (decided September 28 2026): the PARAMETER bindings automatic parameter forwarding may
    /// reuse inside one body — the answer to "which EXISTING parameter binding can satisfy this
    /// callee parameter?", kept separate from ordinary name resolution on purpose.
    ///
    /// <para>It holds, for every name, the parameter binding the owner walk
    /// (<see cref="ElaboratedScopeLookup.SelectOwnedDeclaration"/>) would select for a WRITTEN
    /// parameter occurrence of that name here: a parameter that an enclosing owner's name
    /// resolution established — written, inferred, a clause-branch binder, or an inferred name of
    /// the never-called root — nearest owner winning, and never a name a NEARER level declares as a
    /// property (the nearer declaration decides; only invalid source or the root's phantom exemption
    /// reach that case). Forwarding therefore hands a callee exactly the binding an existing written
    /// reference of the name already denotes, instead of adding a same-named parameter to the
    /// referencing body that would shadow it: automatic forwarding never changes what an existing
    /// name refers to. Properties, opened names, module members, and prelude builtins are
    /// deliberately absent — they are not forwarded as parameters — and so are the parameters
    /// forwarding itself adds (<see cref="Algorithm.User.ForwardingParameterStart"/>): they exist
    /// only for the callee that needed them.</para>
    ///
    /// <para>PERSISTENT and CANONICAL (FE-1): a body extends its parent's bindings by what it adds,
    /// so K nested bodies under a W-binding owner cost O(K + W); <see cref="Names"/> and
    /// <see cref="CollectingNames"/> are canonical name-set ids of the run's interner, so two
    /// derivations of equal bindings key the resolver's region memo alike.</para>
    /// </summary>
    internal sealed class ForwardableParameters
    {
        private readonly ImmutableDictionary<string, ParameterKind> _kinds;
        private readonly NameSetInterner? _interner;

        private ForwardableParameters(
            ImmutableDictionary<string, ParameterKind> kinds,
            NameSetInterner? interner,
            CanonicalNameSet names,
            CanonicalNameSet collectingNames)
        {
            _kinds = kinds;
            _interner = interner;
            Names = names;
            CollectingNames = collectingNames;
        }

        /// <summary>No parameter binding to reuse (the program root's body, an open-target region).</summary>
        public static ForwardableParameters None { get; } = new(
            ImmutableDictionary.Create<string, ParameterKind>(StringComparer.Ordinal),
            interner: null,
            NameSetInterner.Empty,
            NameSetInterner.Empty);

        /// <summary>The bound names (canonical set of the run's interner).</summary>
        public CanonicalNameSet Names { get; }

        /// <summary>The bound names whose binding is a collecting binding (canonical set).</summary>
        public CanonicalNameSet CollectingNames { get; }

        public bool IsEmpty => _kinds.IsEmpty;

        public int Count => _kinds.Count;

        public IEnumerable<string> BoundNames => _kinds.Keys;

        public bool Binds(string name) => _kinds.ContainsKey(name);

        /// <summary>The binding kind of <paramref name="name"/> when an enclosing parameter binds it.</summary>
        public bool TryGetKind(string name, out ParameterKind kind) => _kinds.TryGetValue(name, out kind);

        /// <summary>
        /// The bindings a body's OWN forwarding may reuse: these, minus every name the body
        /// declares as a property (a nearer declaration decides the owner walk). The same instance
        /// when the body declares none of the bound names.
        /// </summary>
        public ForwardableParameters WithoutProperties(IReadOnlyList<Property> properties, NameSetInterner interner)
        {
            if (_kinds.IsEmpty || properties.Count == 0)
                return this;

            List<string>? shadowed = null;
            foreach (var property in properties)
            {
                if (_kinds.ContainsKey(property.Name))
                    (shadowed ??= []).Add(property.Name);
            }

            if (shadowed is null)
                return this;

            var removed = interner.With(NameSetInterner.Empty, shadowed);
            var rebased = Rebase(interner);
            return new(
                rebased._kinds.RemoveRange(shadowed),
                interner,
                interner.Except(rebased.Names, removed),
                interner.Except(rebased.CollectingNames, removed));
        }

        /// <summary>
        /// The bindings a body's NESTED bodies may reuse: these plus the body's own name-resolution
        /// parameter bindings, which replace same-named outer ones (the nearest owner wins); the first
        /// capture of a repeated name decides its kind, as it does for a caller's own signature.
        /// The same instance when the body binds no parameter.
        /// </summary>
        public ForwardableParameters WithParameters(IEnumerable<ParameterDeclaration> parameters, NameSetInterner interner)
        {
            HashSet<string>? own = null;
            List<string>? collecting = null;
            List<string>? ordinary = null;
            foreach (var parameter in parameters)
            {
                own ??= new HashSet<string>(StringComparer.Ordinal);
                if (own.Add(parameter.Name))
                    (parameter.Kind == ParameterKind.Collecting ? collecting ??= [] : ordinary ??= []).Add(parameter.Name);
            }

            if (own is null)
                return this;

            var rebased = Rebase(interner);
            var kinds = rebased._kinds.ToBuilder();
            foreach (var name in ordinary ?? [])
                kinds[name] = ParameterKind.Normal;
            foreach (var name in collecting ?? [])
                kinds[name] = ParameterKind.Collecting;

            var collectingNames = rebased.CollectingNames;
            if (ordinary is not null)
                collectingNames = interner.Except(collectingNames, interner.With(NameSetInterner.Empty, ordinary));
            if (collecting is not null)
                collectingNames = interner.With(collectingNames, collecting);
            return new(kinds.ToImmutable(), interner, interner.With(rebased.Names, own), collectingNames);
        }

        /// <summary>
        /// These bindings with their canonical keys interned by <paramref name="interner"/>: a snapshot
        /// recorded by one resolution run (a deferred branch's context) is re-keyed once by the run
        /// that reads it, so region keys never compare ids of two different interners.
        /// </summary>
        public ForwardableParameters Rebase(NameSetInterner interner)
        {
            if (ReferenceEquals(_interner, interner) || _kinds.IsEmpty)
                return this;

            var collecting = _kinds.Where(static entry => entry.Value == ParameterKind.Collecting).Select(static entry => entry.Key);
            return new(
                _kinds,
                interner,
                interner.With(NameSetInterner.Empty, _kinds.Keys),
                interner.With(NameSetInterner.Empty, collecting));
        }
    }

    /// <summary>
    /// One immutable map version and the names changed since its parent. Retained only by the
    /// resolution run; deferred regions retain the immutable dictionary alone.
    /// </summary>
    private sealed record SignatureVersion(
        ImmutableDictionary<string, CallableSignature> Entries,
        SignatureVersion? Parent,
        IReadOnlyList<string> ChangedNames);

    /// <summary>
    /// Exact canonical projections of visible signatures onto a body's free names. Version
    /// identity is only a cache over immutable inputs; REGION identity is the canonical set of
    /// (name, signature-reference) tokens. Equal projections reached through different map
    /// histories therefore compare in O(1). A small map delta updates only affected free names.
    /// A first query or a large delta probes the free names directly, never scans a wide map for
    /// a narrow query. Walking back at most that many changes also seeds shared ancestor caches.
    /// </summary>
    private sealed class SignatureFootprints
    {
        private readonly NameSetInterner _tokens = new();
        private readonly Dictionary<string, Dictionary<CallableSignature, CanonicalNameSet>> _bindings = new(StringComparer.Ordinal);
        private readonly Dictionary<int, Dictionary<SignatureVersion, CanonicalNameSet>> _projections = [];
        private int _nextToken;

        private CanonicalNameSet Binding(string name, CallableSignature signature)
        {
            if (!_bindings.TryGetValue(name, out var signatures))
                _bindings.Add(name, signatures = new(ReferenceEqualityComparer.Instance));
            if (!signatures.TryGetValue(signature, out var token))
                signatures.Add(signature, token = _tokens.With(NameSetInterner.Empty,
                    [(++_nextToken).ToString(System.Globalization.CultureInfo.InvariantCulture)]));
            return token;
        }

        public CanonicalNameSet Capture(CanonicalNameSet freeNames, NameSetInterner names,
            SignatureVersion version, FrontEndTraversalObservations? observations)
        {
            if (freeNames.Count == 0)
                return NameSetInterner.Empty;
            if (!_projections.TryGetValue(freeNames.Id, out var cache))
                _projections.Add(freeNames.Id, cache = new(ReferenceEqualityComparer.Instance));
            var pending = new Stack<SignatureVersion>();
            var current = version;
            var work = 0;
            CanonicalNameSet result;
            while (!cache.TryGetValue(current, out result))
            {
                if (current.Parent is null || current.ChangedNames.Count > freeNames.Count - work)
                {
                    result = NameSetInterner.Empty;
                    foreach (var name in freeNames.Names)
                    {
                        observations?.RecordResolverSnapshotBindingProbe();
                        if (current.Entries.TryGetValue(name, out var signature))
                            result = _tokens.Union(result, Binding(name, signature));
                    }
                    cache.Add(current, result);
                    break;
                }
                work += current.ChangedNames.Count;
                pending.Push(current);
                current = current.Parent;
            }
            while (pending.TryPop(out current))
            {
                foreach (var name in current.ChangedNames)
                {
                    observations?.RecordResolverSnapshotBindingProbe();
                    if (!names.Contains(freeNames, name))
                        continue;
                    if (current.Parent!.Entries.TryGetValue(name, out var previous))
                        result = _tokens.Except(result, Binding(name, previous));
                    result = _tokens.Union(result, Binding(name, current.Entries[name]));
                }
                cache.Add(current, result);
            }
            return result;
        }
    }

    /// <summary>
    /// A completed algorithm region: the rewritten algorithm and, for a conditional branch
    /// body, the diagnostics its own rewrite reported whose wording names the family — blocked
    /// strict-value forwarding and unforwardable bare-forwarding parameters — as re-issuable
    /// templates.
    /// </summary>
    private sealed record AlgorithmRegion(Algorithm.User Rewritten, IReadOnlyList<BranchDiagnosticTemplate>? DiagnosticTemplates);

    /// <summary>One branch-body report, minus the family name that words it.</summary>
    private readonly record struct BranchDiagnosticTemplate(
        DiagnosticCode Code,
        Func<string?, string> FormatMessage,
        SourceSpan? Span);

    /// <summary>
    /// The FREE reference names of an algorithm's subtree: every <see cref="Expr.Resolve"/>
    /// name in its output rows and property values (recursively) that the subtree does not
    /// bind itself (a body's property names bind for everything inside it; parameters and
    /// binders are already <see cref="Expr.Param"/>s). These are exactly the names whose
    /// visible-map signatures the rewrite of the subtree can read — bare and called
    /// references, the alias and canonical <c>Math</c> shadow checks, and the sibling-order
    /// channel's shadow predicate all probe the map by a written name — while open targets
    /// (rewritten with fresh maps) and stored dot-edge fallbacks (never rewritten) read
    /// nothing. A pure function of the node: memoized per run, and reference-visited per
    /// subtree so a shared expression contributes its names once.
    /// </summary>
    private sealed class ReferenceNames(NameSetInterner interner)
    {
        public CanonicalNameSet Set { get; private set; }
        public void Add(string name) => Set = interner.With(Set, [name]);
        public void Remove(string name) => Set = interner.Except(Set, interner.With(NameSetInterner.Empty, [name]));
        public void UnionWith(CanonicalNameSet other) => Set = interner.Union(Set, other);
    }

    private static CanonicalNameSet FreeReferenceNames(Algorithm algorithm, ResolutionRun run)
    {
        var memo = run.FreeReferenceNames ??= new(ReferenceEqualityComparer.Instance);
        if (memo.TryGetValue(algorithm, out var cached))
            return cached;

        var names = new ReferenceNames(run.ReferenceNameSets);
        switch (algorithm)
        {
            case Algorithm.User user:
            {
                var visited = new HashSet<Expr>(ReferenceEqualityComparer.Instance);
                foreach (var row in user.Output)
                    CollectReferenceNames(row, names, visited, run);
                foreach (var property in user.Properties)
                    names.UnionWith(FreeReferenceNames(property.Value, run));
                foreach (var property in user.Properties)
                    names.Remove(property.Name);
                break;
            }

            case Algorithm.Conditional conditional:
                foreach (var branch in conditional.Branches)
                    names.UnionWith(FreeReferenceNames(branch.Body, run));
                break;

            case Algorithm.Builtin:
                break;

            default:
                throw new InvalidOperationException(
                    $"Unhandled Algorithm variant in {nameof(ImplicitArgumentResolver)}.{nameof(FreeReferenceNames)}: {algorithm.GetType().Name}.");
        }

        memo[algorithm] = names.Set;
        return names.Set;
    }

    private static void CollectReferenceNames(Expr expr, ReferenceNames names, HashSet<Expr> visited, ResolutionRun run)
    {
        if (AstTraversalDagSafety.HasTraversableExprChildren(expr) && !visited.Add(expr))
            return;

        switch (expr)
        {
            case Expr.Resolve(var name):
                names.Add(name);
                break;

            case Expr.Call(var function, var args):
                CollectReferenceNames(function, names, visited, run);
                foreach (var arg in args)
                    CollectReferenceNames(arg, names, visited, run);
                break;

            case Expr.Binary(_, var left, var right):
                CollectReferenceNames(left, names, visited, run);
                CollectReferenceNames(right, names, visited, run);
                break;

            case Expr.Comparison(var first, var links):
                CollectReferenceNames(first, names, visited, run);
                foreach (var link in links)
                    CollectReferenceNames(link.Operand, names, visited, run);
                break;

            case Expr.Unary(_, var operand):
                CollectReferenceNames(operand, names, visited, run);
                break;

            case Expr.Index(var target, var selector):
                CollectReferenceNames(target, names, visited, run);
                CollectReferenceNames(selector, names, visited, run);
                break;

            case Expr.SequenceSpread(var operand):
                CollectReferenceNames(operand, names, visited, run);
                break;

            case Expr.SequenceConstruct(var left, var right):
                CollectReferenceNames(left, names, visited, run);
                CollectReferenceNames(right, names, visited, run);
                break;

            case Expr.ListLiteral(var items):
                foreach (var item in items)
                    CollectReferenceNames(item, names, visited, run);
                break;

            case Expr.DotCall dotCall:
                // The target is read (a bare `Math` receiver is a shadow check, a called
                // receiver is a name); the stored lexical fallback is never rewritten.
                CollectReferenceNames(dotCall.Target, names, visited, run);
                if (dotCall.Args is { } dotArgs)
                {
                    foreach (var arg in dotArgs)
                        CollectReferenceNames(arg, names, visited, run);
                }

                break;

            case Expr.Grace(var inner, _):
                CollectReferenceNames(inner, names, visited, run);
                break;

            case Expr.AlgorithmExpr(var nested):
                names.UnionWith(FreeReferenceNames(nested, run));
                break;

            case Expr.Capture(var rows):
                foreach (var row in rows)
                    CollectReferenceNames(row, names, visited, run);
                break;

            // Intentional leaves: no written name the resolver could look up.
            case Expr.Param:
            case Expr.Num:
            case Expr.StringLiteral:
            case Expr.BoolLiteral:
            case Expr.EmptySequence:
            case Expr.NativeCall:
                break;

            // Runtime exhaustiveness guard (statement-form collector, which the closed Expr
            // hierarchy cannot make compiler-exhaustive — see AstWalker.VisitExpr): a new Expr
            // variant must be classified above rather than silently keeping its names out of
            // the region key.
            default:
                throw new InvalidOperationException(
                    $"Unhandled Expr variant in {nameof(ImplicitArgumentResolver)}.{nameof(CollectReferenceNames)}: {expr.GetType().Name}. " +
                    "Classify the new variant explicitly as a recursive case or an intentional leaf.");
        }
    }

    /// <summary>
    /// The CALLER-dependent configuration one algorithm's implicit-call rewriting runs under:
    /// the enclosing algorithm's parameter patterns, the source binding kinds derived from
    /// them, and its closed-explicit-list gate. Every rewrite decision that is not a property
    /// of the node itself or of the visible signature map reads this record, so it must travel
    /// unchanged into every sub-context of the same algorithm — including value-demanding
    /// (Math) argument bundles, which are ordinary value positions of the SAME caller.
    ///
    /// <para>Bundling the values is deliberate: they are one semantic unit, and the
    /// defect this record replaces was exactly a call site that supplied some of them
    /// degenerately and silently defaulted the others away
    /// (see <see cref="ProcessValueDemandingArgumentBundle"/>).</para>
    /// </summary>
    /// <param name="CallerParameterPatterns">
    /// The enclosing algorithm's parameter patterns — the forwarding SOURCE shape.
    /// </param>
    /// <param name="SourceBindingKinds">
    /// Caller capture name to binding kind, so re-spread decisions read the source binding
    /// (see <see cref="BuildSourceBindingKinds"/>).
    /// </param>
    /// <param name="ClosedParameterNames">
    /// Non-null inside an algorithm whose parameter list is CLOSED — a written explicit
    /// parameter list, or a conditional branch pattern — carrying that list's declared
    /// capture names: nothing may be lifted that would need a capture the list does not
    /// already declare. Null when the list is OPEN and lifting may add captures. The
    /// presence of the set IS the closed state; there is no separate flag to keep in step.
    /// </param>
    /// <param name="ConditionalBranchName">
    /// Non-null when the closed specification is a conditional BRANCH PATTERN rather than a
    /// written explicit parameter list: the family's property name, used only to word the
    /// blocked strict-value diagnostic in the branch's own terms.
    /// </param>
    /// <remarks>
    /// A reference type, allocated EXACTLY ONCE per rewrite region and forwarded by reference
    /// through the whole walk: that makes the region's memo-soundness guard one reference
    /// comparison (<see cref="ResolverWalkMemos.PinRewriteContext"/>) instead of a per-node
    /// field-by-field comparison, and keeps the recursion spine passing one reference rather
    /// than copying several values.
    /// </remarks>
    private sealed record ImplicitRewriteContext(
        IReadOnlyList<ParameterPattern> CallerParameterPatterns,
        IReadOnlyDictionary<string, ParameterKind> SourceBindingKinds,
        IReadOnlySet<string>? ClosedParameterNames,
        string? ConditionalBranchName = null)
    {
        /// <summary>
        /// FE-3: for an OPEN (liftable) context, the owner's final signature — the list whose facts
        /// <see cref="SourceBindingKinds"/> are — so a bundle can be shared with every other owner
        /// whose forwarding inputs are identical (<see cref="SharedBundleKey"/>). Null for a closed
        /// context (a written explicit list or a branch pattern), whose bundles stay region-local.
        /// </summary>
        public IReadOnlyList<ParameterPattern>? FinalSignature { get; init; }

        /// <summary>
        /// Q-04: the ENCLOSING parameter bindings this owner's forwarding reuses for a callee
        /// capture its own parameters do not bind — the source of that capture's synthesized
        /// argument and, for a re-spread decision, of its binding kind. A name they bind is never
        /// lifted into an open owner and is never missing from a closed one.
        /// </summary>
        public ForwardableParameters Forwardable { get; init; } = ForwardableParameters.None;

        /// <summary>
        /// The forwarding SOURCE kind of <paramref name="name"/>: the owner's own binding (its
        /// signature, lifted captures included), else the enclosing parameter binding forwarding
        /// reuses, else none (the name is about to be lifted as a copy of the callee's capture).
        /// </summary>
        public bool TryGetSourceBindingKind(string name, out ParameterKind kind)
            => SourceBindingKinds.TryGetValue(name, out kind) || Forwardable.TryGetKind(name, out kind);
    }

    /// <summary>
    /// FE-3: the EXACT inputs of <see cref="BuildImplicitCallArguments"/> for one callee in one open
    /// rewrite context, by reference: the callee's pattern list; the caller's single collecting
    /// stream (the only way the caller's OWN patterns enter the bundle — its forwarding source), or
    /// <see cref="NoForwardedStream"/>; and the list whose first-occurrence binding kinds are read for
    /// the callee's capture names — a composed owner signature's shared TAIL when none of those names
    /// is in the owner-local head (the kinds then come from the tail alone), otherwise the owner's
    /// whole signature. Owners with equal keys build byte-identical bundles, so they share one.
    /// </summary>
    private readonly record struct SharedBundleKey(object Callee, object ForwardedStream, object Kinds)
    {
        public bool Equals(SharedBundleKey other)
            => ReferenceEquals(Callee, other.Callee)
                && ReferenceEquals(ForwardedStream, other.ForwardedStream)
                && ReferenceEquals(Kinds, other.Kinds);

        public override int GetHashCode()
            => HashCode.Combine(
                System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(Callee),
                System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(ForwardedStream),
                System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(Kinds));
    }

    private static readonly object NoForwardedStream = new();

    /// <summary>
    /// The conditional branch a body belongs to, threaded into
    /// <see cref="ProcessAlgorithm"/> so the body resolves under the CLOSED branch-pattern
    /// rule: its pattern binders are its only inputs, exactly like a written explicit
    /// parameter list, and its <see cref="Algorithm.User.Parameters"/> stay empty.
    /// </summary>
    private sealed record ConditionalBranchContext(string BranchName, Pattern Pattern);

    /// <summary>
    /// Reference-identity memo state for the walks of ONE constant rewrite context region —
    /// either one algorithm's output-rewrite phase (its visible signature map is final once
    /// the property loop completed, and its <see cref="ImplicitRewriteContext"/> is one fixed
    /// value for every row and every sub-context below them) or one algorithm's open-target
    /// region (fresh empty signature maps throughout; open targets never reach the rewrite
    /// maps at all). Maps are keyed by the ORIGINAL node reference and split by the ONE
    /// context dimension that legitimately changes a node's rewrite within the region: call
    /// position (a callee <see cref="Expr.Resolve"/> stays bare where a value-position one
    /// lifts). Shared input therefore rewrites once per distinct (node, position) and stays
    /// shared in the output. Strict-value diagnostic observation is tracked separately: it
    /// changes no rewrite, but a neutral memo hit must not suppress a later strict reach.
    /// <see cref="Algorithms"/> memoizes nested-algorithm processing so two distinct
    /// <see cref="Expr.AlgorithmExpr"/> wrappers over ONE shared algorithm resolve it once
    /// (same signature map for every such call inside the region).
    ///
    /// <para><b>Memo soundness invariant:</b> node reference plus call position is a complete
    /// key ONLY because the region's <see cref="ImplicitRewriteContext"/> is invariant. That
    /// is not a comment but a checked fact: <see cref="PinRewriteContext"/> records the first
    /// context the region rewrites under and throws on any later divergence, so a future
    /// caller that reintroduces a sub-context with its own configuration fails loudly here
    /// instead of silently serving another caller's rewrite. This is what made the
    /// pre-fix value-demanding sub-context safe to unify AND what made it wrong: it unified
    /// by ERASING the caller's configuration rather than by preserving it.</para>
    /// </summary>
    private sealed class ResolverWalkMemos(
        ResolutionRun run,
        FrontEndTraversalObservations? observations,
        DiagnosticBag? diagnostics)
    {
        private ImplicitRewriteContext? _pinnedRewriteContext;

        /// <summary>The resolution this region belongs to (its algorithm region memo).</summary>
        public readonly ResolutionRun Run = run;

        /// <summary>
        /// Q-04: the enclosing parameter bindings a block written in this region's rows may reuse
        /// for its own forwarding — the region owner's forwardable bindings plus its own
        /// name-resolution parameters (<see cref="ForwardableParameters.None"/> for an open-target
        /// region, whose targets are rooted at the prelude).
        /// </summary>
        public ForwardableParameters NestedForwarding { get; init; } = ForwardableParameters.None;

        /// <summary>
        /// Non-null only for a conditional branch body's own output-rewrite region: the
        /// templates of the diagnostics it issues that name the branch (blocked strict-value and
        /// unforwardable-parameter reports), kept on the region so a further family sharing the
        /// body re-issues them under its own name (M4).
        /// </summary>
        public List<BranchDiagnosticTemplate>? BranchDiagnosticTemplates;

        private static readonly string RewriteContextViolationMessage =
            $"{nameof(ImplicitArgumentResolver)} memo soundness violation: one rewrite region observed two "
            + "different caller rewrite contexts. The reference-identity rewrite memo is keyed by node and call "
            + "position only, which is complete solely while the region's caller configuration (parameter "
            + "patterns, source binding kinds, closed-explicit-list gate) stays fixed. Allocate the region's "
            + $"{nameof(ImplicitRewriteContext)} once and forward that instance; a sub-context that genuinely "
            + "needs its own configuration needs its own region memo.";

        public Dictionary<Expr, Expr>? ValueRewrites;

        public Dictionary<Expr, Expr>? CalleeRewrites;

        public Dictionary<Expr, Expr>? OpenRewrites;

        public Dictionary<Expr, Expr>? NestedRewrites;

        public Dictionary<Algorithm, Algorithm>? Algorithms;

        /// <summary>
        /// Nodes whose strict-value diagnostic walk has completed in this region. Kept
        /// separate from rewrite maps so a neutral-first memo hit can replay diagnostic
        /// observation once without changing or duplicating the rewritten node.
        /// </summary>
        public HashSet<Expr>? StrictValueDiagnosticVisits;

        public readonly FrontEndTraversalObservations? Observations = observations;

        /// <summary>
        /// The pass-wide diagnostic sink, threaded beside <see cref="Observations"/> so
        /// every region of one resolution appends to the SAME list. Null for the
        /// standalone entry points that only rewrite. A blocked lift returns the same
        /// reference either way, so rewrite maps never depend on this field; the separate
        /// strict-visit set above tracks the reporting side effect.
        /// </summary>
        public readonly DiagnosticBag? Diagnostics = diagnostics;

        /// <summary>
        /// Fail-loud guard for the memo soundness invariant above. One reference comparison,
        /// because a region allocates its <see cref="ImplicitRewriteContext"/> once and every
        /// walk below forwards that instance. Deliberately stricter than value equality: an
        /// equal-but-freshly-built context also trips, which can only over-report (never let an
        /// unsound reuse through) and points at the right fix — hoist the allocation.
        /// </summary>
        public void PinRewriteContext(ImplicitRewriteContext context)
        {
            if (_pinnedRewriteContext is null)
            {
                _pinnedRewriteContext = context;
                return;
            }

            if (!ReferenceEquals(_pinnedRewriteContext, context))
                throw new InvalidOperationException(RewriteContextViolationMessage);
        }

        // The closed-list forwarding verdict per callee pattern list, under the one context it was
        // computed for: every reference to one callable in the region asks the same question —
        // the closed-list gate for each, the blocked-forwarding report for each blocked one — so
        // it is answered once. Answering it per reference cost O(K × L) for K references to a
        // callable of L parameters (and the former list-scan dedup made each answer O(L²)).
        private Dictionary<IReadOnlyList<ParameterPattern>, IReadOnlyList<string>>? _missingForwardingNames;
        private ImplicitRewriteContext? _missingForwardingNamesContext;

        public IReadOnlyList<string> MissingForwardingNames(
            IReadOnlyList<ParameterPattern> calleePatterns,
            ImplicitRewriteContext context,
            IReadOnlySet<string> closedParameterNames)
        {
            // The verdict depends on the caller's patterns and closed list, which the region's
            // pinned context fixes; any other context instance is answered without the memo.
            _missingForwardingNamesContext ??= context;
            if (!ReferenceEquals(_missingForwardingNamesContext, context))
            {
                Observations?.RecordResolverForwardingVerdict();
                return MissingClosedListForwardingNames(calleePatterns, context.CallerParameterPatterns, closedParameterNames, context.Forwardable);
            }

            _missingForwardingNames ??= new(ReferenceEqualityComparer.Instance);
            if (!_missingForwardingNames.TryGetValue(calleePatterns, out var missing))
            {
                Observations?.RecordResolverForwardingVerdict();
                missing = MissingClosedListForwardingNames(calleePatterns, context.CallerParameterPatterns, closedParameterNames, context.Forwardable);
                _missingForwardingNames.Add(calleePatterns, missing);
            }

            return missing;
        }

        // FE-2: the synthesized implicit-argument bundle per callee pattern list, under the one context
        // it was built for. A bundle is a pure function of the callee's parameter patterns and the
        // caller configuration (BuildImplicitCallArguments reads nothing else), and the region pins that
        // configuration, so every lifted reference to one callable in the region forwards the SAME
        // arguments: K references share ONE immutable bundle of L synthesized slots instead of K copies.
        // The bundle is syntax, not activation state — spanless reads of the caller's own bindings that
        // every call evaluates afresh in its own activation — and each reference keeps its own call node,
        // which carries its span and its origin entry. Region-local, so it never outlives the run.
        private Dictionary<IReadOnlyList<ParameterPattern>, OutputBundle>? _implicitArguments;
        private ImplicitRewriteContext? _implicitArgumentsContext;

        public OutputBundle ImplicitArguments(IReadOnlyList<ParameterPattern> calleePatterns, ImplicitRewriteContext context)
        {
            // Any other context instance is answered without the memo, exactly like the forwarding verdict.
            _implicitArgumentsContext ??= context;
            if (!ReferenceEquals(_implicitArgumentsContext, context))
                return BuildImplicitArgumentBundle(calleePatterns, context);

            _implicitArguments ??= new(ReferenceEqualityComparer.Instance);
            if (!_implicitArguments.TryGetValue(calleePatterns, out var arguments))
            {
                // FE-3: an OPEN context shares the bundle with every owner whose forwarding inputs are
                // identical (SharedBundleKey); a closed context keeps the region-local FE-2 bundle, and
                // so does a bundle whose re-spread decision reads an ENCLOSING binding's kind (Q-04) —
                // an input the shared key does not carry.
                if (context.FinalSignature is { } finalSignature
                    && !ReadsForwardableBindingKind(calleePatterns, context))
                {
                    var key = SharedBundleKeyOf(calleePatterns, context, finalSignature);
                    Run.SharedBundles ??= new();
                    if (!Run.SharedBundles.TryGetValue(key, out arguments))
                    {
                        arguments = BuildImplicitArgumentBundle(calleePatterns, context);
                        Run.SharedBundles.Add(key, arguments);
                    }
                }
                else
                {
                    arguments = BuildImplicitArgumentBundle(calleePatterns, context);
                }

                _implicitArguments.Add(calleePatterns, arguments);
            }

            return arguments;
        }

        /// <summary>
        /// Q-04: whether a synthesized bundle for this callee reads the KIND of an enclosing binding
        /// its owner's forwarding reuses — only a COLLECTING callee capture decides a re-spread, and
        /// only when the owner itself does not bind its name. Such a bundle depends on the enclosing
        /// bindings, which <see cref="SharedBundleKey"/> does not carry, so it stays region-local.
        /// </summary>
        private bool ReadsForwardableBindingKind(IReadOnlyList<ParameterPattern> calleePatterns, ImplicitRewriteContext context)
        {
            if (context.Forwardable.IsEmpty)
                return false;

            foreach (var name in Run.CollectingCaptureNamesOf(calleePatterns))
            {
                if (!context.SourceBindingKinds.ContainsKey(name) && context.Forwardable.Binds(name))
                    return true;
            }

            return false;
        }

        /// <summary>
        /// The <see cref="SharedBundleKey"/> of one callee under one open context: the caller's own
        /// patterns enter only as a single forwarded collecting stream, and the binding kinds of the
        /// callee's capture names come from a composed signature's shared tail exactly when no such
        /// name is in the owner-local head (the head is small, so the test costs the head).
        /// </summary>
        private SharedBundleKey SharedBundleKeyOf(
            IReadOnlyList<ParameterPattern> calleePatterns,
            ImplicitRewriteContext context,
            IReadOnlyList<ParameterPattern> finalSignature)
        {
            object forwardedStream = TryGetSingleTopLevelCollectingCapture(context.CallerParameterPatterns, out _)
                ? context.CallerParameterPatterns
                : NoForwardedStream;
            object kinds = finalSignature;
            // A forwarded stream reads the kind of the CALLER's own collecting name (in the head), so
            // only a bundle without one may take the tail's kinds.
            if (ReferenceEquals(forwardedStream, NoForwardedStream)
                && finalSignature is ImplicitSignatureTemplate { Tail: { } tail } composed)
            {
                var calleeNames = Run.CalleeNamesOf(calleePatterns);
                var headTouchesCallee = false;
                foreach (var capture in ParameterPattern.EnumerateCaptures(composed.Head))
                {
                    if (calleeNames.Contains(capture.Name))
                    {
                        headTouchesCallee = true;
                        break;
                    }
                }

                if (!headTouchesCallee)
                    kinds = tail;
            }

            return new SharedBundleKey(calleePatterns, forwardedStream, kinds);
        }

        private OutputBundle BuildImplicitArgumentBundle(IReadOnlyList<ParameterPattern> calleePatterns, ImplicitRewriteContext context)
        {
            if (calleePatterns is ImplicitSignatureTemplate { Tail: { } tail } composed
                && context.FinalSignature is ImplicitSignatureTemplate source
                && ReferenceEquals(source.Tail ?? source, tail))
            {
                // These inputs forward the callee's own kinds unchanged. The local head
                // and shared tail are independent, including collecting/grouped patterns.
                // Every tail name is the owner's own lifted capture, so the tail bundle reads
                // no enclosing binding (Q-04) and stays shareable by every owner.
                var tailContext = context with
                {
                    CallerParameterPatterns = [],
                    SourceBindingKinds = tail.Facts.BindingKinds,
                    FinalSignature = tail,
                    Forwardable = ForwardableParameters.None,
                };
                var tailKey = SharedBundleKeyOf(tail, tailContext, tail);
                Run.SharedBundles ??= new();
                if (!Run.SharedBundles.TryGetValue(tailKey, out var tailArguments))
                {
                    tailArguments = BuildImplicitArgumentBundle(tail, tailContext);
                    Run.SharedBundles.Add(tailKey, tailArguments);
                }
                var head = BuildImplicitCallArguments(composed.Head, [], context.SourceBindingKinds, context.Forwardable);
                Observations?.RecordImplicitArgumentBundleBuilt(head.Count);
                return OutputBundle.Prepend(head, tailArguments);
            }
            var arguments = OutputBundle.From(BuildImplicitCallArguments(
                calleePatterns, context.CallerParameterPatterns, context.SourceBindingKinds, context.Forwardable));
            Observations?.RecordImplicitArgumentBundleBuilt(arguments.Count);
            return arguments;
        }

        /// <summary>One lifted reference's own call edge, observed once per reference.</summary>
        public Expr SynthesizedImplicitCall(Expr call)
        {
            Observations?.RecordImplicitCallSynthesized();
            return call;
        }

        public Dictionary<Expr, Expr> RewriteMapFor(bool inCallPosition)
            => inCallPosition
                ? CalleeRewrites ??= new(ReferenceEqualityComparer.Instance)
                : ValueRewrites ??= new(ReferenceEqualityComparer.Instance);

        public bool TryBeginStrictValueDiagnosticVisit(Expr expr)
        {
            if (Diagnostics is null)
                return false;

            StrictValueDiagnosticVisits ??= new(ReferenceEqualityComparer.Instance);
            return StrictValueDiagnosticVisits.Add(expr);
        }
    }

    /// <summary>
    /// Reference-identity memo for ONE implicit-dependency collection region (one algorithm's
    /// output rows; the signature map and the shared seen/deps accumulators are constant).
    /// Every contribution is seen-set deduplicated, so a revisit of a completed node — split
    /// by call position, which changes what a node contributes — adds nothing and is skipped.
    /// </summary>
    private sealed class DepsWalkMemo(FrontEndTraversalObservations? observations)
    {
        public readonly HashSet<Expr> ValueVisited = new(ReferenceEqualityComparer.Instance);

        public HashSet<Expr>? CalleeVisited;

        public readonly FrontEndTraversalObservations? Observations = observations;
    }

    /// <summary>
    /// Builds a map from property name to its parameter-pattern signature for one level of properties.
    /// </summary>
    private static Dictionary<string, CallableSignature> BuildPropertyParamMap(
        IReadOnlyList<Property> properties)
    {
        var map = new Dictionary<string, CallableSignature>();
        foreach (var prop in properties)
            map[prop.Name] = CallableSignature.FromAlgorithm(prop.Name, prop.Value);
        return map;
    }

    /// <summary>
    /// Processes an algorithm: topologically sorts its properties, recursively processes each,
    /// then collects implicit deps and rewrites the algorithm's own output. Every NESTED
    /// algorithm — a property value, a block literal, an open target, a conditional branch
    /// body — goes through the run's region memo (M4): one rewrite per
    /// <see cref="AlgorithmRegionKey"/>, sharing preserved in the output, and a branch body's
    /// family-worded diagnostics replayed for every further family that shares it.
    /// </summary>
    /// <remarks>
    /// <paramref name="forwardable"/> is what the algorithm's enclosing owners bind as PARAMETERS by
    /// name resolution (Q-04): the bindings its automatic forwarding may reuse instead of lifting a
    /// same-named parameter of its own.
    /// </remarks>
    private static Algorithm ProcessAlgorithm(
        Algorithm alg,
        SignatureMap parentParamMap,
        ForwardableParameters forwardable,
        bool isRoot,
        FrontEndTraversalObservations? observations,
        DiagnosticBag? diagnostics,
        ConditionalBranchContext? branchContext,
        ResolutionRun run) => alg switch
        {
            Algorithm.Builtin => alg,

            Algorithm.Conditional conditional => ProcessConditionalProperty(
                conditional, "<anonymous>", parentParamMap, forwardable, observations, diagnostics, run),

            // A synthetic assignment-deconstruction helper (`x, *y, z = RHS`) is a fully-elaborated
            // leaf: its output is a single bound Param (rewritten by ParameterDetector), it has no
            // properties or opens, and its explicit N-capture pattern lifts nothing. The general path
            // would still build an O(N) existing-parameter set and source-binding-kind map per helper —
            // O(N^2) across a wide deconstruction's N helpers — only to rewrite an output that has no
            // implicit calls. Returning it unchanged is O(1) and identical.
            Algorithm.User { AssignmentDeconstructionTarget: not null } => alg,

            Algorithm.User user => ProcessUserAlgorithmRegion(
                user, parentParamMap, forwardable, isRoot, observations, diagnostics, branchContext, run),
        };

    /// <summary>
    /// The user-algorithm half of <see cref="ProcessAlgorithm"/>: the root is rewritten once
    /// (nothing shares it), every nested body once per <see cref="AlgorithmRegionKey"/>.
    /// </summary>
    private static Algorithm.User ProcessUserAlgorithmRegion(
        Algorithm.User alg,
        SignatureMap parentParamMap,
        ForwardableParameters forwardable,
        bool isRoot,
        FrontEndTraversalObservations? observations,
        DiagnosticBag? diagnostics,
        ConditionalBranchContext? branchContext,
        ResolutionRun run)
    {
        // The root is processed exactly once and keeps its bare-root rule; nothing shares it.
        if (isRoot)
            return ProcessUserAlgorithm(alg, parentParamMap, forwardable, isRoot: true, observations, diagnostics, branchContext: null, run, diagnosticTemplates: null);

        forwardable = forwardable.Rebase(run.ReferenceNameSets);
        var regionKey = new AlgorithmRegionKey(
            alg,
            run.Footprints.Capture(FreeReferenceNames(alg, run), run.ReferenceNameSets, parentParamMap.Version, observations),
            forwardable.Names,
            forwardable.CollectingNames,
            branchContext is null ? null
                : HasLoneBareRowShape(alg) ? run.BranchContexts.BareForwardingHeadId(branchContext.Pattern)
                : run.BranchContexts.ClosedSpecificationId(branchContext.Pattern),
            ReportsDiagnostics: diagnostics is not null);
        var regions = run.AlgorithmRegions ??= new();
        if (regions.TryGetValue(regionKey, out var completedRegion))
        {
            if (branchContext is not null)
                ReplayBranchDiagnostics(completedRegion, branchContext.BranchName, diagnostics);
            return completedRegion.Rewritten;
        }

        if (branchContext is null)
            observations?.RecordResolverAlgorithmRegionExpansion();
        else
            observations?.RecordResolverBranchBodyRegionExpansion();

        var diagnosticTemplates = branchContext is not null && diagnostics is not null
            ? new List<BranchDiagnosticTemplate>()
            : null;
        var rewritten = ProcessUserAlgorithm(alg, parentParamMap, forwardable, isRoot: false, observations, diagnostics, branchContext, run, diagnosticTemplates);
        // Admitted only after the whole body completed (acyclic by the structural preflight).
        regions[regionKey] = new AlgorithmRegion(rewritten, diagnosticTemplates);
        return rewritten;
    }

    private static Algorithm.User ProcessUserAlgorithm(
        Algorithm.User alg,
        SignatureMap parentParamMap,
        ForwardableParameters forwardable,
        bool isRoot,
        FrontEndTraversalObservations? observations,
        DiagnosticBag? diagnostics,
        ConditionalBranchContext? branchContext,
        ResolutionRun run,
        List<BranchDiagnosticTemplate>? diagnosticTemplates)
    {
        var newOpens = ProcessOpenExprs(alg.Opens, observations, run);

        // Q-04: the enclosing PARAMETER bindings this body's own forwarding reuses — those its
        // owners established, minus any name this body declares as a property (the nearer
        // declaration decides) — and, for every body nested in this one (property values, branch
        // bodies, and blocks written in its rows), those plus this body's own name-resolution
        // parameters: its written or inferred ones, or a branch body's binders. Never the
        // parameters forwarding itself adds below: they exist only for the callee that needed them.
        var ownForwarding = forwardable.WithoutProperties(alg.Properties, run.ReferenceNameSets);
        var nestedForwarding = ownForwarding.WithParameters(
            branchContext is null
                ? ParameterPattern.FlattenCaptures(alg.NameResolutionParameterPatterns)
                : ParameterPattern.FlattenCaptures(BranchBinderParameterPatterns(branchContext.Pattern)),
            run.ReferenceNameSets);

        // Build local param map
        var localParamMap = BuildPropertyParamMap(alg.Properties);
        // The sibling-order channel consults the same Math-alias shadow knowledge
        // this pass's own visibleParamMap carries (ancestor property names here,
        // sibling names inside the builder), so dependency ordering and the
        // rewriting below cannot disagree about which calls are alias calls.
        // This pass consumes ONLY the dependency/order channel: the builder's
        // recursive property-summary channel belongs to the exposure resolver
        // and is deliberately never computed here (M17).
        var dependencyGraph = PropertyDependencyGraphBuilder.BuildDependencyOrder(
            alg,
            preludeNameShadowedByCaller: parentParamMap.ContainsKey,
            observations);

        // Visible map = parent + local (local overrides). When there are no local properties —
        // the common leaf case, e.g. every simple property value `A = expr` — nothing overrides
        // the parent map and the per-property loop below (the only writer of visibleParamMap) is
        // empty, so the parent map is shared instead of copied. Cloning this O(P) parent map once
        // per leaf property is what made this pass O(P^2) in the property count.
        var visibleParamMap = localParamMap.Count == 0 ? parentParamMap : parentParamMap.Extend(localParamMap);

        // Topological sort of properties
        var topoOrder = dependencyGraph.TopologicalOrder;

        // Process properties in topological order
        var processedProperties = new Property[alg.Properties.Count];
        foreach (var idx in topoOrder)
        {
            var prop = alg.Properties[idx];

            if (prop.Value is Algorithm.User { IsAssignmentDeconstructionSource: true })
            {
                // Hoisted deconstruction right-hand side: written as rows of THIS body, so it
                // is rewritten in the output phase below with this body's own context and
                // acquires no parameters of its own (see RewriteDeconstructionSourceRows).
                processedProperties[idx] = prop;
            }
            else if (prop.Value is Algorithm.Conditional condAlg)
            {
                processedProperties[idx] = prop.WithValue(ProcessConditionalProperty(
                    condAlg, prop.Name, visibleParamMap, nestedForwarding, observations, diagnostics, run));
            }
            else
            {
                // visibleParamMap is UPDATED after each processed property, so a value shared
                // by two properties could observe different sibling signatures if it were
                // reached between two writes it depends on. The run's region memo keys each
                // value on the signatures its FREE names actually see (M4), so a shared value
                // rewrites once per distinct observation and never once per referencing
                // property — and the dependency order above processes every referenced
                // sibling first, so within an acyclic property graph every reach observes the
                // same, final signatures.
                Algorithm processedBody;
                using (run.EnterImportSite(ImportSite.OfProperty(prop)))
                {
                    processedBody = ProcessAlgorithm(
                        prop.Value, visibleParamMap, nestedForwarding, isRoot: false, observations, diagnostics, branchContext: null, run);
                }

                // Update param maps with the processed, potentially augmented signature.
                var processedSignature = CallableSignature.FromAlgorithm(prop.Name, processedBody);
                visibleParamMap.Set(prop.Name, processedSignature);

                processedProperties[idx] = prop.WithValue(processedBody);
            }
        }

        var newProperties = processedProperties.ToList();

        // ONE memo bundle spans this algorithm's whole output-rewrite phase: the property
        // loop above has completed, so visibleParamMap's contents are final for every
        // rewrite below, and all rows share the exact same context (see ResolverWalkMemos).
        var walkMemos = new ResolverWalkMemos(run, observations, diagnostics)
        {
            BranchDiagnosticTemplates = diagnosticTemplates,
            NestedForwarding = nestedForwarding,
        };

        // A LONE BARE ROW (FWD-02): a body whose ONE written row is a bare reference to a callable
        // that declares parameters is an exact alias (an open body) or bare forwarding (a written
        // parameter list or a clause branch: the callee receives the existing bindings of its
        // parameters' names, never renamed, reshaped or added). Every other body keeps formula
        // lifting below.
        if (!isRoot && TryCompleteLoneCalleeRow(alg, branchContext, visibleParamMap, ownForwarding, walkMemos) is { } completed)
        {
            return completed with
            {
                Opens = newOpens,
                Properties = newProperties,
            };
        }

        if (alg.HasExplicitParameterList || branchContext is not null)
        {
            // Two CLOSED input specifications share one gate: a written explicit parameter
            // list, and a conditional branch pattern. A branch body's only inputs are its
            // pattern binders — bound through valEnv at runtime exactly like declared
            // parameters — and its Parameters stay empty by invariant, so nothing may be
            // lifted that would need a capture the pattern does not already bind. The open
            // implicit-lifting path below would instead invent that capture as a body
            // parameter nothing ever binds (`Unknown name` at runtime).
            var closedPatterns = branchContext is null
                ? alg.ParameterPatterns
                : BranchBinderParameterPatterns(branchContext.Pattern);
            var closedParameterNames = branchContext is null
                ? new HashSet<string>(alg.Params)
                : new HashSet<string>(branchContext.Pattern.BoundNames());
            var explicitContext = new ImplicitRewriteContext(
                closedPatterns,
                BuildSourceBindingKinds(closedPatterns),
                ClosedParameterNames: closedParameterNames,
                branchContext?.BranchName)
            {
                Forwardable = ownForwarding,
            };
            var newOutput = new List<Expr>(alg.Output.Count);
            foreach (var expr in alg.Output)
            {
                newOutput.Add(
                    RewriteImplicitCalls(
                        expr,
                        visibleParamMap,
                        explicitContext,
                        inCallPosition: false,
                        walkMemos));
            }

            AstHelpers.RewriteDeconstructionSourceRows(
                alg,
                newProperties,
                expr => RewriteImplicitCalls(expr, visibleParamMap, explicitContext, inCallPosition: false, walkMemos));

            return alg with
            {
                Opens = newOpens,
                Properties = newProperties,
                Output = newOutput,
            };
        }

        // Collect implicit dependencies from the algorithm's output and lift
        // them into its parameter list. One deps memo spans all rows (they share
        // the seen/deps accumulators, so the walk context is one region).
        var deps = new List<(string Name, CallableSignature Signature)>();
        var seen = new HashSet<string>();
        var depsMemo = new DepsWalkMemo(observations);
        foreach (var expr in AstHelpers.WrittenRows(
            alg, isRoot ? expr => !ShouldPreserveBareRootResolve(expr, visibleParamMap, isRoot: true) : null))
        {
            CollectImplicitDeps(expr, visibleParamMap, seen, deps, inCallPosition: false, depsMemo);
        }

        // Compute lifted parameter patterns: existing patterns first, then new
        // dependency captures with their recursive shape preserved — as a SHARED
        // signature template (FE-3, see LiftSignature). A capture an enclosing
        // parameter binding supplies is reused, never lifted (Q-04).
        var lifting = LiftSignature(alg.ParameterPatterns, deps, ownForwarding, run);
        var finalPatterns = lifting.Patterns;

        // Rewrite output expressions. Source binding kinds come from the
        // LIFTED pattern list: a callee name missing from the original caller
        // parameters binds through the capture lifted above (possibly by an
        // earlier dependency with a different kind), and that lifted capture
        // is the forwarding source — or, for a name an enclosing parameter
        // binding supplies, that reused binding (Q-04).
        var liftedContext = new ImplicitRewriteContext(
            alg.ParameterPatterns,
            lifting.SourceBindingKinds,
            ClosedParameterNames: null)
        {
            FinalSignature = finalPatterns,
            Forwardable = ownForwarding,
        };
        var rewrittenOutput = new List<Expr>(alg.Output.Count);
        foreach (var expr in alg.Output)
        {
            rewrittenOutput.Add(
                ShouldPreserveBareRootResolve(expr, visibleParamMap, isRoot)
                    ? expr
                    : RewriteImplicitCalls(
                        expr,
                        visibleParamMap,
                        liftedContext,
                        inCallPosition: false,
                        walkMemos));
        }

        AstHelpers.RewriteDeconstructionSourceRows(
            alg,
            newProperties,
            expr => RewriteImplicitCalls(expr, visibleParamMap, liftedContext, inCallPosition: false, walkMemos));

        // Lean: withParameterPatterns on the rewritten body — the lifted list replaces the
        // stored channel; Parameters/Params follow it. The patterns forwarding appended are
        // marked (Q-04): they complete the signature for callers, and no written name ever
        // denotes them.
        return alg with
        {
            ParameterPatterns = finalPatterns,
            ForwardingParameterStart = alg.ForwardingParameterStart
                ?? (lifting.Lifted ? alg.ParameterPatterns.Count : null),
            Opens = newOpens,
            Properties = newProperties,
            Output = rewrittenOutput,
        };
    }

    private static IReadOnlyList<Expr> ProcessOpenExprs(
        IReadOnlyList<Expr> opens,
        FrontEndTraversalObservations? observations,
        ResolutionRun run)
    {
        if (opens.Count == 0)
            return opens;

        // One memo bundle per open-target region: every walk below runs with a fresh EMPTY
        // signature map, so the region's rewrite context is constant regardless of which
        // fresh map instance a call site allocates.
        var memos = new ResolverWalkMemos(run, observations, diagnostics: null);
        var processed = new List<Expr>(opens.Count);
        foreach (var open in opens)
            processed.Add(ProcessOpenExpr(open, memos));
        return processed;
    }

    private static Algorithm.Conditional ProcessConditionalProperty(
        Algorithm.Conditional conditional,
        string propertyName,
        SignatureMap parentParamMap,
        ForwardableParameters forwardable,
        FrontEndTraversalObservations? observations,
        DiagnosticBag? diagnostics,
        ResolutionRun run)
    {
        var newOpens = ProcessOpenExprs(conditional.Opens, observations, run);
        var branches = new List<CondBranch>(conditional.Branches.Count);
        foreach (var branch in conditional.Branches)
        {
            if (branch.Body.DeferredRegion is { } region)
            {
                // B2c: a deferred module region is not resolved eagerly (its provisional body
                // is never evaluated, and resolving it could only report false forwarding
                // refusals against names a deferred module provides). This pass's output view
                // of the placeholder carries the region forked with the visible signature map
                // as it stands HERE — a snapshot, since the property loop keeps extending the
                // map — and the enclosing parameter bindings forwarding may reuse (Q-04), one
                // view per family occurrence.
                branches.Add(branch with
                {
                    Body = branch.Body with
                    {
                        DeferredRegion = region.WithResolution(new DeferredBranchContext(
                            parentParamMap.Snapshot,
                            propertyName,
                            branch.Pattern,
                            forwardable)),
                    },
                });
                continue;
            }

            // M4: the body is rewritten through the run's region memo — once per (body,
            // free-name signature snapshot, forwardable parameter bindings, closed binder
            // specification, reporting mode). A body shared by several families under one
            // region is rewritten once (sharing preserved in the output) and only its
            // blocked-forwarding diagnostics, the one thing that names THIS family, are
            // re-issued for the later families.
            var body = ProcessAlgorithm(
                branch.Body, parentParamMap, forwardable, isRoot: false, observations, diagnostics,
                new ConditionalBranchContext(propertyName, branch.Pattern), run);
            branches.Add(branch with { Body = body });
        }

        return conditional with { Opens = newOpens, Branches = branches };
    }

    /// <summary>
    /// Re-issues a completed region's blocked strict-value reports for a further family that
    /// shares the body — same references, same missing names, same spans, worded with THIS
    /// family's name — so per-family diagnostic multiplicity matches a fresh rewrite without
    /// performing one, independent of which family was reached first.
    /// </summary>
    private static void ReplayBranchDiagnostics(AlgorithmRegion region, string branchName, DiagnosticBag? diagnostics)
    {
        if (diagnostics is null || region.DiagnosticTemplates is null)
            return;

        foreach (var template in region.DiagnosticTemplates)
        {
            diagnostics.Add(new Diagnostic(template.FormatMessage(branchName), DiagnosticSeverity.Error, template.Span)
            {
                Code = template.Code,
            });
        }
    }

    /// <summary>
    /// The resolution context of one deferred module region (B2c): the visible signature map
    /// exactly as the eager walk saw it at the branch, plus the closed branch-pattern
    /// specification, so the demand-time run rewrites the detected body under the same
    /// forwarding rules.
    /// </summary>
    internal sealed record DeferredBranchContext(
        ImmutableDictionary<string, CallableSignature> ParentParamMap,
        string BranchName,
        Pattern Pattern,
        ForwardableParameters Forwardable);

    /// <summary>
    /// Demand-time implicit-argument resolution of a deferred region's DETECTED body: the
    /// ordinary closed-branch rewrite, with diagnostics.
    /// </summary>
    internal static Algorithm ElaborateDeferredBranch(
        Algorithm detectedBody,
        DeferredBranchContext context,
        DiagnosticBag diagnostics,
        FrontEndTraversalObservations? observations = null,
        SourceSpan? importSite = null)
    {
        var run = new ResolutionRun(importSite) { Observations = observations };
        return ProcessAlgorithm(
            detectedBody,
            SignatureMap.FromSnapshot(context.ParentParamMap, observations),
            // The eager run recorded these bindings; this run keys them with its own interner.
            context.Forwardable.Rebase(run.ReferenceNameSets),
            isRoot: false,
            observations,
            diagnostics,
            new ConditionalBranchContext(context.BranchName, context.Pattern),
            run);
    }

    private static Expr ProcessOpenExpr(Expr expr, ResolverWalkMemos memos)
    {
        // DAG-safety: a shared node reference rewrites once per open-target region and stays
        // shared in the output. Childless leaves skip the memo.
        if (!AstTraversalDagSafety.HasTraversableExprChildren(expr))
            return ProcessOpenExprCore(expr, memos);

        memos.OpenRewrites ??= new(ReferenceEqualityComparer.Instance);
        if (memos.OpenRewrites.TryGetValue(expr, out var rewritten))
            return rewritten;

        memos.Observations?.RecordResolverRewriteExpansion();
        rewritten = ProcessOpenExprCore(expr, memos);
        memos.OpenRewrites[expr] = rewritten;
        return rewritten;
    }

    private static Expr ProcessOpenExprCore(Expr expr, ResolverWalkMemos memos)
    {
        return expr switch
        {
            Expr.AlgorithmExpr block => block with
            {
                Algorithm = ProcessSharedNestedAlgorithm(block.Algorithm, ImportSite.OfBlock(block), SignatureMap.Empty(memos.Observations), memos),
            },

            // Capture targets own no scope; rows recurse without lifting,
            // with a fresh signature map like every other open target.
            Expr.Capture capture => capture with
            {
                Body = new OutputBundle(
                    capture.Body
                        .Select(row => ProcessExprNested(row, SignatureMap.Empty(memos.Observations), memos))
                        .ToList()),
            },

            // `with` keeps the stored dot-edge facts (member span, lexical
            // fallback) intact.
            Expr.DotCall dotCall => dotCall with
            {
                Target = ProcessOpenExpr(dotCall.Target, memos),
                Args = dotCall.Args is { } dotArgs
                    ? ProcessArgumentBundle(dotArgs, SignatureMap.Empty(memos.Observations), memos)
                    : null,
            },

            Expr.SequenceSpread spread => spread with { Operand = ProcessOpenExpr(spread.Operand, memos) },

            Expr.SequenceConstruct construct => construct with
            {
                Left = ProcessOpenExpr(construct.Left, memos),
                Right = ProcessOpenExpr(construct.Right, memos),
            },

            Expr.ListLiteral list => list with { Items = list.Items.Select(item => ProcessOpenExpr(item, memos)).ToList() },

            Expr.Call call => call with
            {
                Function = ProcessOpenExpr(call.Function, memos),
                Args = ProcessArgumentBundle(call.Args, SignatureMap.Empty(memos.Observations), memos),
            },

            // Operator forms are never valid open targets (open-form validation
            // rejects them: BadOpenForm), but the parser produces them in diagnostic
            // recovery trees, where parameter detection has already elaborated their
            // operands like a capture's rows. Their operands are resolved the same
            // way — the transparent walk with a fresh empty signature map — so a
            // block inside `open -{ ... }` is resolved exactly as one inside
            // `open ({ ... }, 1)`.
            Expr.Unary or Expr.Binary or Expr.Comparison or Expr.Index
                => ProcessExprNestedCore(expr, SignatureMap.Empty(memos.Observations), memos),

            // Intentional leaves: name/literal leaves carry no nested algorithm
            // to process (a bare Resolve IS the ordinary open-target form);
            // Grace cannot survive parameter detection, which runs first, so a
            // host-supplied wrapper passes through untouched.
            Expr.Resolve or Expr.Param or Expr.Num or Expr.StringLiteral or Expr.BoolLiteral or Expr.EmptySequence
                or Expr.NativeCall or Expr.Grace => expr,
        };
    }

    /// <summary>
    /// A bare ROOT output row naming a callable that requires supplied arguments stays an
    /// unlifted reference, so evaluation reports the callable's own zero-argument demand
    /// rejection at the reference instead of lifting its parameters into the never-called
    /// root. A callable that accepts zero supplied arguments is never lifted anywhere
    /// (<see cref="RequiresSuppliedArguments"/>), so it needs no preservation.
    /// </summary>
    private static bool ShouldPreserveBareRootResolve(
        Expr expr,
        SignatureMap paramMap,
        bool isRoot)
        => isRoot
            && expr is Expr.Resolve(var name)
            && paramMap.TryGetValue(name, out var ps)
            && RequiresSuppliedArguments(ps);

    /// <summary>
    /// THE implicit-lifting eligibility rule (Q-03, decided September 28 2026), consulted by
    /// every liftable arm — a bare property reference (<see cref="CollectImplicitDepsCore"/>,
    /// <see cref="RewriteBareReference"/>), a bare Math alias, and the bare canonical
    /// <c>Math.X</c> shape (<see cref="TryGetBareBuiltinCallableSignature"/>) — and by root-row
    /// preservation (<see cref="ShouldPreserveBareRootResolve"/>): a bare value-position
    /// reference lifts to an implicit forwarding call ONLY when its callee REQUIRES supplied
    /// arguments, that is, when an ordinary call supplying zero arguments could NOT bind it.
    ///
    /// <para>A callee that accepts zero supplied arguments — no parameters, or only a top-level
    /// collecting parameter such as <c>Roll(*xs)</c> — is NEVER lifted, whatever position it
    /// stands in (an operator or comparison operand, a list element, an index target, a spread
    /// operand, a strict Math argument, a block body): declaring a parameter does
    /// not by itself make a bare reference a call. The reference stays a property-style value
    /// demand, which the evaluator accepts (<see cref="Evaluator.AcceptsZeroSuppliedArguments"/>
    /// reads the SAME rule, <see cref="ParameterPattern.AcceptsZeroSuppliedSlots"/>) and serves
    /// from the property cache, so <c>Roll == Roll</c> reads ONE value; only a written call
    /// (<c>Roll()</c>, <c>Roll(args)</c>) evaluates afresh. Lifting had judged "declares any
    /// parameter" before, so a collecting-only callee in a lifting position became the fresh
    /// call <c>Roll(xs*)</c> and bypassed the cache (PV-03).</para>
    /// Lean: <c>liftsBareValueReference</c>.
    /// </summary>
    private static bool RequiresSuppliedArguments(CallableSignature signature)
        => !signature.AcceptsZeroSuppliedArguments;

    /// <summary>
    /// The eligibility of the alias and bare-forwarding rules (<see cref="TryCompleteLoneCalleeRow"/>):
    /// the callee declares at least one parameter pattern. Lean: <c>aliasesLoneBareReference</c>.
    /// </summary>
    private static bool DeclaresParameters(CallableSignature signature)
        => signature.ParameterPatterns.Count > 0;

    /// <summary>The outcome of <see cref="LiftSignature"/> for one open owner.</summary>
    private readonly record struct LiftedSignature(
        IReadOnlyList<ParameterPattern> Patterns,
        IReadOnlyDictionary<string, ParameterKind> SourceBindingKinds,
        bool Lifted);

    /// <summary>
    /// FE-3: the lifted signature of one open owner — its own patterns first, then every dependency
    /// capture it does not already bind, in dependency order with recursive shape preserved (the
    /// exact pre-FE-3 order) — built from SHARED signature templates instead of a fresh per-owner copy.
    ///
    /// <para>The dependencies' merged captures (the TAIL) are a function of the dependencies alone,
    /// so they are merged once per distinct dependency sequence and interned
    /// (<see cref="ImplicitSignatureTemplateInterner.LiftedTail"/>). The owner's own patterns (the
    /// HEAD) meet the tail only through their capture names: when none is lifted, the head filters
    /// nothing and the signature is exactly <c>head ++ tail</c> — the tail itself for an owner with
    /// no own parameter (K such owners share ONE template), otherwise a composed signature that costs
    /// the head (<see cref="ImplicitSignatureTemplate.Compose"/>). When an own name IS lifted, the
    /// owner's order is genuinely its own (its capture stays first and the lifted one is filtered),
    /// so that signature is merged per owner exactly as before and held as an immutable template.</para>
    ///
    /// <para>Q-04 (decided September 28 2026): a dependency capture that an ENCLOSING parameter
    /// binding already supplies (<paramref name="forwardable"/> — the binding a written reference of
    /// that name here already denotes) is never lifted: forwarding reuses that exact binding, and
    /// adding a same-named parameter to this owner would make every existing reference of the name
    /// inside it denote the new parameter instead. Only a genuinely unbound dependency becomes a new
    /// (forwarded) parameter. When the lifted tail meets such a binding the signature is merged per
    /// owner, like an owner whose own name is lifted; otherwise the shared templates are used as
    /// before.</para>
    /// </summary>
    private static LiftedSignature LiftSignature(
        IReadOnlyList<ParameterPattern> own,
        List<(string Name, CallableSignature Signature)> deps,
        ForwardableParameters forwardable,
        ResolutionRun run)
    {
        // A dependency whose whole shape the owner's own single collecting stream forwards
        // contributes no capture (the same per-dependency test as always, O(1) each).
        List<IReadOnlyList<ParameterPattern>>? included = null;
        foreach (var (_, signature) in deps)
        {
            if (!CanForwardSingleCollectingStream(own, signature.ParameterPatterns))
                (included ??= []).Add(signature.ParameterPatterns);
        }

        var tail = included is null ? null : run.Templates.LiftedTail(included, MergeLiftedTail);
        if (tail is null)
            return new(own, SourceBindingKindsOf(own), Lifted: false);

        if (!forwardable.IsEmpty && run.TailMeetsForwardable(tail, forwardable))
        {
            var reused = MergeOwnerSignature(own, included!, forwardable);
            if (reused is null)
                return new(own, SourceBindingKindsOf(own), Lifted: false);
            var reusedDistinct = run.Templates.InternFlat(reused);
            run.Observations?.RecordOwnerSignatureMaterialized(reused.Length);
            return new(reusedDistinct, reusedDistinct.Facts.BindingKinds, Lifted: true);
        }

        var tailNames = tail.Facts.NameSet;
        var disjoint = true;
        foreach (var capture in ParameterPattern.EnumerateCaptures(own))
        {
            if (tailNames.Contains(capture.Name))
            {
                disjoint = false;
                break;
            }
        }

        if (disjoint)
        {
            var signature = ImplicitSignatureTemplate.Compose(own.Select(run.Templates.Freeze).ToArray(), tail);
            run.Observations?.RecordOwnerSignatureInstance(own.Count);
            return new(signature, signature.Facts.BindingKinds, Lifted: true);
        }

        var merged = MergeOwnerSignature(own, included!, ForwardableParameters.None);
        if (merged is null)
            return new(own, SourceBindingKindsOf(own), Lifted: false);
        var distinct = run.Templates.InternFlat(merged);
        run.Observations?.RecordOwnerSignatureMaterialized(merged.Length);
        return new(distinct, distinct.Facts.BindingKinds, Lifted: true);
    }

    /// <summary>The first-occurrence binding kinds of an owner's own list (a template's are cached).</summary>
    private static IReadOnlyDictionary<string, ParameterKind> SourceBindingKindsOf(IReadOnlyList<ParameterPattern> patterns)
        => patterns is ImplicitSignatureTemplate template
            ? template.Facts.BindingKinds
            : BuildSourceBindingKinds(patterns);

    /// <summary>The captures of a dependency sequence, first occurrence of each name winning.</summary>
    private static IReadOnlyList<ParameterPattern> MergeLiftedTail(IReadOnlyList<IReadOnlyList<ParameterPattern>> dependencies)
    {
        var existing = new HashSet<string>(StringComparer.Ordinal);
        var merged = new List<ParameterPattern>();
        foreach (var dependency in dependencies)
            AppendMissingPatterns(dependency, existing, merged);
        return merged;
    }

    /// <summary>
    /// One owner's merge when an own name is also lifted, or (Q-04) when an enclosing parameter
    /// binding supplies a dependency capture: exactly the pre-FE-3 loop (own patterns, then each
    /// dependency's captures that neither the owner nor <paramref name="forwardable"/> binds).
    /// Null when nothing is lifted.
    /// </summary>
    private static ParameterPattern[]? MergeOwnerSignature(
        IReadOnlyList<ParameterPattern> own,
        IReadOnlyList<IReadOnlyList<ParameterPattern>> dependencies,
        ForwardableParameters forwardable)
    {
        var existing = new HashSet<string>(ParameterPattern.EnumerateCaptures(own).Select(static capture => capture.Name), StringComparer.Ordinal);
        var merged = new List<ParameterPattern>(own);
        var ownCount = merged.Count;
        foreach (var dependency in dependencies)
            AppendMissingPatterns(dependency, existing, merged, forwardable);
        return merged.Count == ownCount ? null : merged.ToArray();
    }

    /// <summary>
    /// FORMULA LIFTING IS BY BINDING NAME, regardless of how many times a name occurs in a
    /// callee's parameter patterns: the merge walks the captures left to right — across dependencies,
    /// across one dependency's patterns, and inside a group alike — and keeps a capture only when no
    /// earlier capture (the owner's own, an earlier dependency's, or an earlier one of the same
    /// pattern) and no reused enclosing binding already binds its name. So one binding name is ONE
    /// caller parameter: <c>P(x, x)</c> lifts <c>x</c> once exactly as <c>H = F + G</c> with
    /// <c>F(x)</c> and <c>G(x)</c> does, and <c>P((x, x))</c> lifts the bare binder <c>x</c> (a
    /// sequence group left with one binder IS that binder), never a caller pattern that repeats
    /// <c>x</c>. The synthesized call supplies the one binding to every occurrence
    /// (<see cref="BuildImplicitCallArguments"/>). A lone bare row never reaches this merge: it is an
    /// exact alias or bare forwarding, which reuses existing bindings by name and adds none
    /// (<see cref="TryCompleteLoneCalleeRow"/>).
    /// </summary>
    private static void AppendMissingPatterns(
        IReadOnlyList<ParameterPattern> patterns,
        HashSet<string> existing,
        List<ParameterPattern> merged,
        ForwardableParameters? forwardable = null)
    {
        foreach (var pattern in patterns)
        {
            var missingPattern = MissingCapturePattern(pattern, existing, forwardable ?? ForwardableParameters.None);
            if (missingPattern is not null)
                merged.Add(missingPattern);
        }
    }

    /// <summary>
    /// The part of <paramref name="pattern"/> whose captures no earlier capture binds, recording
    /// each kept capture's name in <paramref name="existing"/> as it is kept, so a later occurrence
    /// of the name — in this very pattern too — is skipped.
    /// </summary>
    private static ParameterPattern? MissingCapturePattern(
        ParameterPattern pattern,
        HashSet<string> existing,
        ForwardableParameters forwardable)
        => pattern switch
        {
            CaptureParameterPattern capture
                => forwardable.Binds(capture.Name) || !existing.Add(capture.Name) ? null : capture,
            SequenceValueParameterPattern or ListValueParameterPattern or UnpackingParameterPattern
                => MissingGroupCapturePattern(pattern, existing, forwardable),
        };

    /// <summary>
    /// The part of a structural group whose captures no earlier capture binds. The group keeps
    /// its KIND for the names that are new there (a list group stays a list group, a sequence
    /// group a sequence group), with one consequence of the value model: a SEQUENCE group left
    /// with exactly one non-collecting item IS that item, because there is no one-item sequence
    /// (the singleton rule) — <c>P((x, x))</c> lifts <c>x</c> and <c>P(x, (x, a))</c> lifts
    /// <c>x, a</c>, exactly as a redundant one-slot group is its content (SYN-06). A list group
    /// keeps its brackets at every cardinality (<c>P(x, [x, a])</c> lifts <c>x, [a]</c>), and a
    /// group with no new name contributes no caller parameter.
    /// </summary>
    private static ParameterPattern? MissingGroupCapturePattern(
        ParameterPattern group,
        HashSet<string> existing,
        ForwardableParameters forwardable)
    {
        var groupItems = ParameterPattern.StructuralItems(group)!;
        var missingItems = new List<ParameterPattern>(groupItems.Count);
        var unchanged = true;
        foreach (var item in groupItems)
        {
            var missingItem = MissingCapturePattern(item, existing, forwardable);
            unchanged &= ReferenceEquals(missingItem, item);
            if (missingItem is not null)
                missingItems.Add(missingItem);
        }

        // A group none of whose captures is already bound lifts AS ITSELF — the callee's record,
        // exactly like a lifted capture leaf — so owners lifting it share one record (FE-3).
        if (missingItems.Count == 0)
            return null;
        if (unchanged)
            return group;
        if (group is SequenceValueParameterPattern && ParameterPattern.IsSingletonSequenceItems(missingItems))
            return missingItems[0];
        return ParameterPattern.WithStructuralItems(group, missingItems);
    }

    private static bool TryGetSingleTopLevelCollectingCapture(
        IReadOnlyList<ParameterPattern> patterns,
        [System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out CaptureParameterPattern? capture)
    {
        if (patterns.Count == 1
            && patterns[0] is CaptureParameterPattern { Kind: ParameterKind.Collecting } collecting)
        {
            capture = collecting;
            return true;
        }

        capture = null;
        return false;
    }

    /// <summary>
    /// The callee half of forwarding by shape: a callee whose whole parameter list is ONE
    /// structural group of either kind holding a lone collecting capture (<c>H((*xs))</c>,
    /// <c>H([*xs])</c>), which requires its one supplied slot. A callee whose whole list is a lone TOP-LEVEL collector
    /// (<c>H(*xs)</c>) accepts zero supplied arguments and is therefore never lifted (Q-03,
    /// <see cref="RequiresSuppliedArguments"/>), so it never reaches forwarding at all: a bare
    /// reference to it is a cached value read, and forwarding its caller's items is written
    /// explicitly (<c>H(items*)</c>).
    /// </summary>
    private static bool TryGetSingleForwardableCalleeStream(
        IReadOnlyList<ParameterPattern> patterns,
        [System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out CaptureParameterPattern? capture)
    {
        // A grouped stream of either structural kind — `H((*xs))` or `H([*xs])` — is re-supplied
        // by a caller's lone collecting stream, rebuilt as that group's own kind.
        if (patterns.Count == 1
            && ParameterPattern.StructuralItems(patterns[0]) is [CaptureParameterPattern { Kind: ParameterKind.Collecting } groupedCollecting])
        {
            capture = groupedCollecting;
            return true;
        }

        capture = null;
        return false;
    }

    private static bool TryGetSingleCollectingForwarding(
        IReadOnlyList<ParameterPattern> callerPatterns,
        IReadOnlyList<ParameterPattern> calleePatterns,
        [System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out string? calleeName,
        [System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out string? callerName)
    {
        if (TryGetSingleTopLevelCollectingCapture(callerPatterns, out var callerCapture)
            && TryGetSingleForwardableCalleeStream(calleePatterns, out var calleeCapture))
        {
            calleeName = calleeCapture.Name;
            callerName = callerCapture.Name;
            return true;
        }

        calleeName = null;
        callerName = null;
        return false;
    }

    private static bool CanForwardSingleCollectingStream(
        IReadOnlyList<ParameterPattern> callerPatterns,
        IReadOnlyList<ParameterPattern> calleePatterns)
        => TryGetSingleCollectingForwarding(callerPatterns, calleePatterns, out _, out _);

    /// <summary>
    /// The callee capture names a CLOSED explicit parameter list cannot supply — the ONE
    /// implementation of the closed-list forwarding verdict: <see cref="ClosedListBlocksLifting"/>
    /// blocks exactly when it is non-empty, and <see cref="ReportBlockedStrictValueForwarding"/>
    /// names exactly these (both read it through the region's
    /// <see cref="ResolverWalkMemos.MissingForwardingNames"/>). Forwarding availability and the
    /// names blamed for its absence therefore cannot drift apart: the caller's own forwarded
    /// collecting stream satisfies EVERY capture (so it yields no names at all), and otherwise a
    /// capture is missing exactly when the closed list does not declare it.
    /// <para>Q-04: a capture an ENCLOSING parameter binding supplies (<paramref name="forwardable"/>,
    /// the bindings a written reference of that name in the closed body already denotes) is never
    /// missing — forwarding reuses that binding, exactly as it does for an inferring owner.</para>
    /// <para>Order is <see cref="ParameterPattern.FlattenCaptures"/> order — the callee's
    /// own declaration order — deduplicated first-occurrence-wins, so a diagnostic built
    /// from it is stable and never hash-ordered.</para>
    /// </summary>
    private static IReadOnlyList<string> MissingClosedListForwardingNames(
        IReadOnlyList<ParameterPattern> calleePatterns,
        IReadOnlyList<ParameterPattern> callerPatterns,
        IReadOnlySet<string> existingParameterNames,
        ForwardableParameters forwardable)
    {
        // A single forwarded collecting stream re-supplies the callee's whole parameter
        // shape by binding KIND, not by name, so nothing is missing even though the names
        // differ. Consulting the same helper the forwarding builder uses keeps fixed and
        // collecting bindings from ever being judged interchangeable here.
        if (CanForwardSingleCollectingStream(callerPatterns, calleePatterns))
            return [];

        List<string>? missing = null;
        HashSet<string>? seen = null;
        foreach (var capture in ParameterPattern.FlattenCaptures(calleePatterns))
        {
            if (existingParameterNames.Contains(capture.Name) || forwardable.Binds(capture.Name))
                continue;

            seen ??= new(StringComparer.Ordinal);
            if (seen.Add(capture.Name))
                (missing ??= []).Add(capture.Name);
        }

        return missing ?? (IReadOnlyList<string>)[];
    }

    /// <summary>
    /// The CLOSED-explicit-parameter-list gate, in one place: inside an algorithm that wrote
    /// its own parameter list, a bare reference to a callable that requires supplied arguments
    /// (the only kind that is ever lifted, <see cref="RequiresSuppliedArguments"/>) may lift
    /// only when every capture the synthesized argument list would need is supplied by an
    /// existing parameter binding: declared by that list, the caller's own forwarded collecting
    /// stream, or (Q-04) an enclosing parameter binding a written reference of the name there
    /// already denotes. Lifting anything else would invent a parameter the programmer never wrote.
    ///
    /// <para>Every liftable arm of <see cref="RewriteImplicitCallsCore"/> consults THIS
    /// helper with the region's <see cref="ImplicitRewriteContext"/>, so no expression
    /// position — value-demanding Math arguments included — can be reached under a
    /// weaker gate than the rows around it.</para>
    /// </summary>
    private static bool ClosedListBlocksLifting(
        ImplicitRewriteContext context,
        IReadOnlyList<ParameterPattern> calleePatterns,
        ResolverWalkMemos memos)
        => context.ClosedParameterNames is { } closedParameterNames
            && memos.MissingForwardingNames(calleePatterns, context, closedParameterNames).Count > 0;

    /// <summary>
    /// Reports a STATICALLY IMPOSSIBLE strict value demand: a registry-proven
    /// value-demanding consumer requires this reference's produced value, the reference
    /// resolves to a callable that REQUIRES supplied arguments, and
    /// <see cref="ClosedListBlocksLifting"/> just refused the forwarding that would supply
    /// them. Nothing later in the pipeline can rescue such a position — evaluation would
    /// demand the value with zero arguments and fail — so the front end says so, naming
    /// what the programmer can act on. A callable that accepts zero supplied arguments
    /// (a collecting-only <c>Cnt(*ys)</c>) never reaches this report: it is never lifted, so
    /// nothing is blocked and its demand is legal (Q-03; formerly PV-27).
    ///
    /// <para>Called ONLY from the arms that already decided to leave the reference bare,
    /// and only while <c>inStrictValueDemand</c> holds. Both halves matter: outside a
    /// proven strict-value position the same blocked reference is a legal higher-order
    /// reference (<c>F(x) = A</c>, <c>Apply(A)</c>), and outside a blocked lift there is
    /// nothing wrong at all.</para>
    ///
    /// <para>Conservative by construction — it reports only what it can name: the missing
    /// captures of the closed list (<see cref="ImplicitRewriteContext.ClosedParameterNames"/>,
    /// always present here because only a closed list ever blocks a lift). A blocked
    /// reference whose missing captures cannot be named yields no diagnostic and the
    /// program keeps its ordinary runtime checking.</para>
    /// </summary>
    /// <remarks>
    /// <paramref name="referenceDisplayName"/> is the written callable the program can act on
    /// (<c>A</c>, the alias <c>abs</c>, the canonical <c>Math.Abs</c>) — never the consuming
    /// native's own declared argument name, which belongs to the consumer and not to this
    /// failure.
    /// </remarks>
    private static void ReportBlockedStrictValueForwarding(
        Expr reference,
        string referenceDisplayName,
        IReadOnlyList<ParameterPattern> calleePatterns,
        ImplicitRewriteContext context,
        ResolverWalkMemos memos)
    {
        if (memos.Diagnostics is not { } diagnostics || context.ClosedParameterNames is not { } closedParameterNames)
            return;

        var missing = memos.MissingForwardingNames(calleePatterns, context, closedParameterNames);
        if (missing.Count == 0)
            return;

        // A reference the document wrote is reported at its span; one inside imported
        // content at the import site.
        var span = reference.Span ?? memos.Run.ImportSite;
        diagnostics.Add(new Diagnostic(
            FormatBlockedStrictValueForwarding(referenceDisplayName, missing, context.ConditionalBranchName),
            DiagnosticSeverity.Error,
            span)
        {
            Code = DiagnosticCode.UndeclaredIdentifier,
        });
        // A conditional branch body's own region keeps the report re-issuable for further
        // families sharing the body (M4; see ConditionalBranchContext.DiagnosticTemplates).
        memos.BranchDiagnosticTemplates?.Add(new BranchDiagnosticTemplate(
            DiagnosticCode.UndeclaredIdentifier,
            family => FormatBlockedStrictValueForwarding(referenceDisplayName, missing, family),
            span));
    }

    /// <summary>
    /// Wording for <see cref="ReportBlockedStrictValueForwarding"/>, deliberately parallel
    /// to parameter detection's directly-written counterparts ("Identifier 'z' is used in an
    /// explicitly parameterized algorithm, but it is not declared in the parameter list" /
    /// "Identifier 'z' is used in conditional branch 'F', but it is not declared in the branch
    /// pattern"): the same closed-specification rule, reached one level of indirection away
    /// because the missing name is required by the REFERENCED callable rather than written here.
    /// </summary>
    private static string FormatBlockedStrictValueForwarding(
        string referenceDisplayName,
        IReadOnlyList<string> missingParameterNames,
        string? conditionalBranchName)
    {
        // Reported once per blocked reference, so everything the referenced callable or the
        // family contributes is echoed bounded (ExprNameRenderer's name bound and marker).
        referenceDisplayName = ExprNameRenderer.BoundName(referenceDisplayName);
        conditionalBranchName = conditionalBranchName is null ? null : ExprNameRenderer.BoundName(conditionalBranchName);
        var names = FormatQuotedNameList(missingParameterNames);
        var noun = missingParameterNames.Count == 1 ? "parameter" : "parameters";
        if (conditionalBranchName is not null)
        {
            return string.Join(
                Environment.NewLine,
                $"'{referenceDisplayName}' is required as a value here, but producing that value needs the implicit {noun} {names}, "
                    + $"which the pattern of conditional branch '{conditionalBranchName}' does not bind.",
                $"Conditional branch patterns are closed, so {names} cannot be inferred here. Declare {names} in the branch pattern, "
                    + $"or call '{referenceDisplayName}' with explicit arguments.");
        }

        return string.Join(
            Environment.NewLine,
            $"'{referenceDisplayName}' is required as a value here, but producing that value needs the implicit {noun} {names}, "
                + "which the enclosing explicit parameter list does not declare.",
            $"Explicit parameter lists are closed, so {names} cannot be inferred here. Declare {names} in the parameter list, "
                + $"call '{referenceDisplayName}' with explicit arguments, or remove the explicit parameter list.");
    }

    // `'a'`, `'a' and 'b'`, `'a', 'b', and 'c'` — rendered within the rendered-name bound, reading
    // only the names it shows; text that fits is exactly the unbounded spelling.
    private static string FormatQuotedNameList(IReadOnlyList<string> values)
    {
        var sink = new Rendering.BoundedDiagnosticSink(ExprNameRenderer.MaxRenderedNameLength);
        for (var index = 0; index < values.Count; index++)
        {
            var separator = index == 0 ? ""
                : values.Count == 2 ? " and "
                : index == values.Count - 1 ? ", and "
                : ", ";
            if (!sink.Append(separator) || !sink.Append("'") || !sink.Append(values[index]) || !sink.Append("'"))
                break;
        }

        return sink.Finish();
    }

    /// <summary>
    /// Maps every caller-side capture name (top-level and nested) to its
    /// binding kind. Implicit forwarding consults this map so the decision to
    /// re-spread a forwarded value is made from the SOURCE binding, never from
    /// the destination parameter kind alone.
    /// </summary>
    private static Dictionary<string, ParameterKind> BuildSourceBindingKinds(
        IEnumerable<ParameterPattern> callerPatterns)
    {
        var kinds = new Dictionary<string, ParameterKind>(StringComparer.Ordinal);
        foreach (var capture in ParameterPattern.FlattenCaptures(callerPatterns))
            kinds.TryAdd(capture.Name, capture.Kind);
        return kinds;
    }

    /// <summary>
    /// The binder shape of a conditional branch pattern as caller parameter patterns — the
    /// forwarding SOURCE shape of a branch body, mirroring
    /// <see cref="Pattern.TryGetOrdinaryClauseParameterPatterns"/> but total over mixed
    /// heads: literal items bind nothing, so they contribute no capture,
    /// while binders keep their kind and nested binder groups keep their structural kind
    /// (a sequence pattern stays a sequence pattern, a list pattern a list pattern),
    /// including empty groups. The closed-specification name check consumes only
    /// captures, but single-collecting forwarding also depends on those group boundaries.
    /// Collecting binders in conditional families are host-AST-only; the parser rejects them.
    /// </summary>
    private static IReadOnlyList<ParameterPattern> BranchBinderParameterPatterns(Pattern pattern)
    {
        // A top-level sequence pattern IS the branch's parameter list; any other top-level
        // pattern is one single parameter position.
        var items = pattern is Pattern.SequenceValue(var topLevelItems) ? topLevelItems : [pattern];
        var patterns = new List<ParameterPattern>(items.Count);
        foreach (var item in items)
        {
            if (TryCreateBinderParameterPattern(item, out var parameterPattern))
                patterns.Add(parameterPattern);
        }

        return patterns;
    }

    private static bool TryCreateBinderParameterPattern(
        Pattern pattern,
        [System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out ParameterPattern? parameterPattern)
    {
        switch (pattern)
        {
            case Pattern.Bind binder:
                parameterPattern = new CaptureParameterPattern(binder.Name, binder.NameSpan, binder.ParameterKind)
                {
                    CollectMarkerSpan = binder.CollectMarkerSpan,
                };
                return true;

            case Pattern.SequenceValue(var items):
            {
                parameterPattern = new SequenceValueParameterPattern(BinderChildPatterns(items));
                return true;
            }

            case Pattern.ListValue(var items):
            {
                parameterPattern = new ListValueParameterPattern(BinderChildPatterns(items));
                return true;
            }

            case Pattern.LitInt:
            case Pattern.LitString:
            case Pattern.LitBool:
                parameterPattern = null;
                return false;

            default:
                throw new InvalidOperationException(
                    $"Unhandled Pattern variant in {nameof(BranchBinderParameterPatterns)}: {pattern.GetType().Name}.");
        }

        static List<ParameterPattern> BinderChildPatterns(IReadOnlyList<Pattern> items)
        {
            var childPatterns = new List<ParameterPattern>(items.Count);
            foreach (var item in items)
            {
                if (TryCreateBinderParameterPattern(item, out var childPattern))
                    childPatterns.Add(childPattern);
            }

            return childPatterns;
        }
    }

    /// <summary>
    /// A LONE BARE ROW (FWD-02, decided September 29–30 2026). A NON-ROOT body — a named definition,
    /// a clause branch, or an inline block — whose ONE written row is a bare reference to a callable
    /// that DECLARES parameters (<see cref="DeclaresParameters"/>) is completed here, never by formula
    /// lifting. The row names the callable itself, so the rule reads the callee's DECLARED signature,
    /// not zero-argument acceptance. Declarations and opens beside the row do not change what the row
    /// means.
    /// <list type="bullet">
    ///   <item><b>Exact alias.</b> An OPEN body — no written parameter list, no parameter of its own
    ///   (<c>A = F</c>) — takes the callee's parameter patterns VERBATIM as its signature (repeated
    ///   names, binderless groups, collectors and structural kinds included; interned as one shared
    ///   template, FE-3) and calls the callee with those patterns rebuilt
    ///   (<see cref="BuildSourceArguments"/>), so <c>A(S) ≡ F(S)</c> for every argument supply. Its
    ///   parameters are all forwarded ones (<see cref="Algorithm.User.ForwardingParameterStart"/> = 0):
    ///   no written name denotes them, no enclosing binding is reused, and their names — the callee's
    ///   private binder names — collide with no property
    ///   (<see cref="Algorithm.User.InheritsCalleeSignature"/>).</item>
    ///   <item><b>Bare forwarding.</b> A CLOSED body — a written parameter list (<c>A(p) = F</c>) or a
    ///   clause branch (<c>A(head) = F</c>) — forwards the callee the EXISTING bindings of its
    ///   parameters' names (<see cref="BareForwardingArgument"/>): by name, never by position; nothing
    ///   is renamed and nothing is added to the closed list; and a callee parameter pattern is supplied
    ///   only by a binding that declares the SAME pattern, so a same-named leaf never reshapes an
    ///   argument. A callee parameter that cannot be supplied is the front-end error
    ///   <see cref="DiagnosticCode.UnforwardableParameter"/>, and the row is left as written. When
    ///   nothing is forwarded to a callee that works with no arguments, the row is its bare name —
    ///   Q-03's cached value read, never an invented call. The explicit call <c>A(p) = F(p)</c> is an
    ///   ordinary written call and never reaches this rule.</item>
    /// </list>
    /// Returns null for every other body (formula lifting, <see cref="LiftSignature"/>) and for a
    /// bare-forwarding row that forwards nothing.
    /// </summary>
    private static Algorithm.User? TryCompleteLoneCalleeRow(
        Algorithm.User alg,
        ConditionalBranchContext? branchContext,
        SignatureMap paramMap,
        ForwardableParameters ownForwarding,
        ResolverWalkMemos memos)
    {
        if (!HasLoneBareRowShape(alg))
            return null;

        var run = memos.Run;

        var row = alg.Output[0];
        if (!TryGetLoneCalleeSignature(row, paramMap, out var calleePatterns, out var calleeDisplayName))
            return null;

        if (branchContext is null && !alg.HasExplicitParameterList)
        {
            // An inferring body that already owns parameters (none can come from a lone bare
            // reference, but a host tree may carry them) keeps formula lifting.
            if (alg.ParameterPatterns.Count != 0)
                return null;

            var signature = calleePatterns is ImplicitSignatureTemplate template
                ? template
                : run.Templates.InternFlat(calleePatterns);
            return alg with
            {
                ParameterPatterns = signature,
                ForwardingParameterStart = 0,
                InheritsCalleeSignature = true,
                Output = [memos.SynthesizedImplicitCall(LoneRowCall(row, run.SourceArguments(signature)))],
            };
        }

        var sources = branchContext is null
            ? BareForwardingSources.OfParameterList(alg.ParameterPatterns)
            : BareForwardingSources.OfBranchHead(branchContext.Pattern);
        var forwarded = new List<Expr>(calleePatterns.Count);
        List<(ParameterPattern Parameter, bool DifferentPattern)>? unforwardable = null;
        foreach (var parameter in calleePatterns)
        {
            var verdict = BareForwardingArgument(parameter, sources, ownForwarding);
            if (verdict.Argument is { } argument)
                forwarded.Add(argument);
            else if (verdict.Unforwardable)
                (unforwardable ??= []).Add((parameter, verdict.DifferentPattern));
        }

        if (unforwardable is not null)
        {
            ReportUnforwardableParameters(row, calleeDisplayName, unforwardable, branchContext?.BranchName, memos);
            return alg;
        }

        // Nothing to forward: every callee parameter is a collector that no binding of its name
        // supplies, so the callee works with no arguments and the row is its bare name.
        if (forwarded.Count == 0)
            return null;

        var arguments = OutputBundle.From(forwarded);
        run.Observations?.RecordImplicitArgumentBundleBuilt(arguments.Count);
        return alg with { Output = [memos.SynthesizedImplicitCall(LoneRowCall(row, arguments))] };
    }

    /// <summary>The call a completed lone row makes: the written callee applied to <paramref name="arguments"/>.</summary>
    private static Expr LoneRowCall(Expr row, OutputBundle arguments) => row switch
    {
        Expr.DotCall bareDotCall => bareDotCall with { Args = arguments },
        _ => new Expr.Call(new Expr.Resolve(((Expr.Resolve)row).Name) { Span = row.Span }, arguments) { Span = row.Span },
    };

    /// <summary>
    /// The context-free half of the lone-row rule's eligibility: the body's ONE written row is a bare
    /// name or a bare dot reference (whatever it resolves to; declarations and opens do not count as
    /// rows, while a hoisted deconstruction right-hand side does — <see cref="AstHelpers.WrittenRows"/>
    /// — so a body with a deconstruction beside the bare callee is a formula). A property of the node
    /// alone, so a region key may read it before the body is rewritten.
    /// </summary>
    private static bool HasLoneBareRowShape(Algorithm.User alg)
        => alg.Output.Count == 1
            && alg.Output[0] is Expr.Resolve or Expr.DotCall { Args: null }
            && AstHelpers.WrittenRows(alg).Count == 1;

    /// <summary>
    /// The callee a lone body row names, when that row is a bare reference to a callable that
    /// declares parameters: a property with a parameter-pattern signature, a registry-proven Math
    /// alias, or the bare canonical <c>Math.X</c> shape (the resolution arms of
    /// <see cref="RewriteBareReference"/> and <see cref="TryGetBareBuiltinCallableSignature"/>, in
    /// the same order; every Math function requires its arguments), with the name the program wrote.
    /// A clause family has no parameter-pattern signature and is never an alias or forwarding target
    /// (PV-14).
    /// </summary>
    private static bool TryGetLoneCalleeSignature(
        Expr row,
        SignatureMap paramMap,
        [System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out IReadOnlyList<ParameterPattern>? calleePatterns,
        [System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out string? calleeDisplayName)
    {
        switch (row)
        {
            case Expr.Resolve(var name)
                when paramMap.TryGetValue(name, out var signature) && DeclaresParameters(signature):
                calleePatterns = signature.ParameterPatterns;
                calleeDisplayName = name;
                return true;

            case Expr.Resolve
                when row.TryGetRegistryProvenMathAliasFacts(paramMap.ContainsKey, out var aliasFacts)
                    && DeclaresParameters(aliasFacts.Signature):
                calleePatterns = aliasFacts.Signature.ParameterPatterns;
                calleeDisplayName = aliasFacts.SpelledName;
                return true;

            case Expr.DotCall { Args: null }
                when TryGetBareBuiltinCallableSignature(row, paramMap, out var builtinKey, out var builtinSignature):
                calleePatterns = builtinSignature.ParameterPatterns;
                calleeDisplayName = builtinKey;
                return true;

            default:
                calleePatterns = null;
                calleeDisplayName = null;
                return false;
        }
    }

    /// <summary>
    /// The call arguments that REBUILD a parameter-pattern list from its own bindings — the exact
    /// alias's call (FWD-02): a fixed capture is its binding (<c>x</c>), a collecting capture
    /// re-spreads the items it collected (<c>xs*</c>) at any level, a sequence pattern rebuilds a
    /// sequence and a list pattern a list, of the same shape (<see cref="BuildPatternArgument"/> with
    /// every capture naming its own binding). Binding the rebuilt supply against the same patterns
    /// therefore reproduces the same bindings, which is what makes an alias exact. Lean:
    /// <c>ParameterPattern.sourceArguments</c>.
    /// </summary>
    private static IReadOnlyList<Expr> BuildSourceArguments(IReadOnlyList<ParameterPattern> source)
        => source.Select(BuildSourceArgument).ToList();

    /// <summary>
    /// ONE pattern rebuilt from its own bindings (<see cref="BuildSourceArguments"/>) — also the
    /// argument bare forwarding passes for a structural pattern the body declares with the same
    /// contract. Lean: <c>ParameterPattern.sourceArgument</c>.
    /// </summary>
    private static Expr BuildSourceArgument(ParameterPattern pattern)
        => BuildPatternArgument(
            pattern,
            static capture => capture.Name,
            static capture => capture.Kind == ParameterKind.Collecting);

    /// <summary>
    /// What a CLOSED body's own inputs offer BARE FORWARDING: the kind of every TOP-LEVEL capture it
    /// declares (first occurrence of a repeated name wins, as for a caller's own signature), the
    /// contract of every top-level structural pattern it declares that holds no literal (a clause
    /// head item that holds a literal, <c>[0, x]</c>, declares no literal-free pattern), and every
    /// name it binds at any depth — a name bound only inside a structural pattern is an element of
    /// that pattern, never a whole-value parameter. Lean: the <c>own</c> / <c>ownNames</c> inputs of
    /// <c>bareForwardingArguments</c>.
    /// </summary>
    private sealed class BareForwardingSources
    {
        private BareForwardingSources(
            Dictionary<string, ParameterKind> topLevelCaptureKinds,
            HashSet<ParameterPattern> structuralContracts,
            HashSet<string> boundNames)
        {
            TopLevelCaptureKinds = topLevelCaptureKinds;
            StructuralContracts = structuralContracts;
            BoundNames = boundNames;
        }

        public IReadOnlyDictionary<string, ParameterKind> TopLevelCaptureKinds { get; }

        /// <summary>Every literal-free top-level structural pattern, compared by its complete contract.</summary>
        public IReadOnlySet<ParameterPattern> StructuralContracts { get; }

        public IReadOnlySet<string> BoundNames { get; }

        public static BareForwardingSources OfParameterList(IReadOnlyList<ParameterPattern> patterns)
        {
            var boundNames = new HashSet<string>(StringComparer.Ordinal);
            foreach (var capture in ParameterPattern.FlattenCaptures(patterns))
                boundNames.Add(capture.Name);
            return Of(patterns, boundNames);
        }

        public static BareForwardingSources OfBranchHead(Pattern head)
        {
            // A top-level sequence pattern IS the branch's parameter list; any other top-level
            // pattern is one single parameter position.
            var items = head is Pattern.SequenceValue(var topLevelItems) ? topLevelItems : [head];
            var patterns = new List<ParameterPattern>(items.Count);
            foreach (var item in items)
            {
                // An item that holds a literal at any depth declares no literal-free contract.
                if (Pattern.TryCreateOrdinaryClauseParameterPattern(item, out var pattern))
                    patterns.Add(pattern);
            }

            return Of(patterns, new HashSet<string>(head.BoundNames(), StringComparer.Ordinal));
        }

        private static BareForwardingSources Of(IReadOnlyList<ParameterPattern> topLevelPatterns, HashSet<string> boundNames)
        {
            var captureKinds = new Dictionary<string, ParameterKind>(StringComparer.Ordinal);
            var structuralContracts = new HashSet<ParameterPattern>(ParameterPattern.ContractComparer);
            foreach (var pattern in topLevelPatterns)
            {
                if (pattern is CaptureParameterPattern capture)
                    captureKinds.TryAdd(capture.Name, capture.Kind);
                else
                    structuralContracts.Add(pattern);
            }

            return new(captureKinds, structuralContracts, boundNames);
        }
    }

    /// <summary>BARE FORWARDING's verdict for one callee parameter pattern (<see cref="BareForwardingArgument"/>).</summary>
    private readonly record struct BareForwardingVerdict(Expr? Argument, bool Unforwardable, bool DifferentPattern)
    {
        public static BareForwardingVerdict Supplied(Expr argument) => new(argument, Unforwardable: false, DifferentPattern: false);

        /// <summary>A collector that no binding of its name supplies: it receives no argument.</summary>
        public static BareForwardingVerdict Optional => new(null, Unforwardable: false, DifferentPattern: false);

        public static BareForwardingVerdict Unsupplied(bool differentPattern) => new(null, Unforwardable: true, differentPattern);
    }

    /// <summary>
    /// BARE FORWARDING's verdict for ONE callee parameter pattern (FWD-02): the argument that supplies
    /// it from an EXISTING binding, by name; no argument for a collector that nothing of its name
    /// supplies (a collector accepts none); or unforwardable.
    /// <list type="bullet">
    ///   <item>A capture <c>n</c> reads the binding a written <c>n</c> would denote (Q-04): the body's
    ///   own TOP-LEVEL parameter <c>n</c>, else — when the body binds no <c>n</c> at all — the nearest
    ///   enclosing parameter binding (<paramref name="enclosing"/>). A collecting source re-spreads
    ///   into a collecting destination (FWD-01); every other pair passes the binding as ONE argument,
    ///   unchanged (FWD-02's source-kind rule). A body that binds <c>n</c> only INSIDE one of its
    ///   structural patterns holds an element, not a whole-value parameter: unforwardable.</item>
    ///   <item>A structural pattern is supplied only by one of the body's own top-level patterns with
    ///   the SAME contract — kind, shape, names and collectors — rebuilt as itself, never assembled
    ///   from same-named leaves; captured enclosing bindings are plain named values and supply
    ///   none.</item>
    /// </list>
    /// Lean: <c>bareForwardingArgument</c>.
    /// </summary>
    private static BareForwardingVerdict BareForwardingArgument(
        ParameterPattern parameter,
        BareForwardingSources sources,
        ForwardableParameters enclosing)
    {
        if (parameter is CaptureParameterPattern capture)
        {
            if (sources.TopLevelCaptureKinds.TryGetValue(capture.Name, out var ownKind))
                return BareForwardingVerdict.Supplied(ForwardedBinding(capture, ownKind));
            if (sources.BoundNames.Contains(capture.Name))
                return BareForwardingVerdict.Unsupplied(differentPattern: true);
            if (enclosing.TryGetKind(capture.Name, out var enclosingKind))
                return BareForwardingVerdict.Supplied(ForwardedBinding(capture, enclosingKind));
            return capture.Kind == ParameterKind.Collecting
                ? BareForwardingVerdict.Optional
                : BareForwardingVerdict.Unsupplied(differentPattern: false);
        }

        if (sources.StructuralContracts.Contains(parameter))
            return BareForwardingVerdict.Supplied(BuildSourceArgument(parameter));

        var bindsAName = false;
        foreach (var leaf in ParameterPattern.FlattenCaptures([parameter]))
        {
            if (sources.BoundNames.Contains(leaf.Name) || enclosing.Binds(leaf.Name))
            {
                bindsAName = true;
                break;
            }
        }

        return BareForwardingVerdict.Unsupplied(differentPattern: bindsAName);

        static Expr ForwardedBinding(CaptureParameterPattern destination, ParameterKind sourceKind)
            => destination.Kind == ParameterKind.Collecting && sourceKind == ParameterKind.Collecting
                ? new Expr.SequenceSpread(new Expr.Param(destination.Name))
                : new Expr.Param(destination.Name);
    }

    /// <summary>
    /// Reports every callee parameter bare forwarding cannot supply, once per parameter, at the bare
    /// reference (a row inside imported content at the import site). A conditional branch body's own
    /// region keeps each report re-issuable for further families sharing the body (M4).
    /// </summary>
    private static void ReportUnforwardableParameters(
        Expr row,
        string calleeDisplayName,
        IReadOnlyList<(ParameterPattern Parameter, bool DifferentPattern)> unforwardable,
        string? branchName,
        ResolverWalkMemos memos)
    {
        if (memos.Diagnostics is not { } diagnostics)
            return;

        var span = row.Span ?? memos.Run.ImportSite;
        var reported = new HashSet<ParameterPattern>(ParameterPattern.ContractComparer);
        foreach (var (parameter, differentPattern) in unforwardable)
        {
            if (!reported.Add(parameter))
                continue;
            var parameterDisplayName = parameter.DisplayName;

            string Format(string? family)
                => FormatUnforwardableParameter(calleeDisplayName, parameterDisplayName, differentPattern, family);
            diagnostics.Add(new Diagnostic(Format(branchName), DiagnosticSeverity.Error, span)
            {
                Code = DiagnosticCode.UnforwardableParameter,
            });
            memos.BranchDiagnosticTemplates?.Add(new BranchDiagnosticTemplate(DiagnosticCode.UnforwardableParameter, Format, span));
        }
    }

    /// <summary>
    /// Wording for <see cref="ReportUnforwardableParameters"/>, parallel to the closed-list wording of
    /// <see cref="FormatBlockedStrictValueForwarding"/>: what bare forwarding could not supply, why
    /// (the list is closed; nothing is renamed or reshaped), and the two repairs.
    /// </summary>
    private static string FormatUnforwardableParameter(
        string calleeDisplayName,
        string parameterDisplayName,
        bool differentPattern,
        string? conditionalBranchName)
    {
        calleeDisplayName = ExprNameRenderer.BoundName(calleeDisplayName);
        parameterDisplayName = ExprNameRenderer.BoundName(parameterDisplayName);
        conditionalBranchName = conditionalBranchName is null ? null : ExprNameRenderer.BoundName(conditionalBranchName);
        if (conditionalBranchName is not null)
        {
            return differentPattern
                ? string.Join(
                    Environment.NewLine,
                    $"'{calleeDisplayName}' is forwarded by name here, but the pattern of conditional branch '{conditionalBranchName}' "
                        + $"does not bind its parameter '{parameterDisplayName}' in that form.",
                    "Bare forwarding reuses an existing binding only with the same pattern and never reshapes an argument. "
                        + $"Bind '{parameterDisplayName}' in the branch pattern, or call '{calleeDisplayName}' with explicit arguments.")
                : string.Join(
                    Environment.NewLine,
                    $"'{calleeDisplayName}' is forwarded by name here, but its parameter '{parameterDisplayName}' "
                        + $"is not bound by the pattern of conditional branch '{conditionalBranchName}'.",
                    "Bare forwarding reuses an existing binding only under its own name, and conditional branch patterns are closed, "
                        + $"so '{parameterDisplayName}' is neither renamed nor added. Bind '{parameterDisplayName}' in the branch pattern, "
                        + $"or call '{calleeDisplayName}' with explicit arguments.");
        }

        return differentPattern
            ? string.Join(
                Environment.NewLine,
                $"'{calleeDisplayName}' is forwarded by name here, but the enclosing explicit parameter list "
                    + $"does not declare its parameter '{parameterDisplayName}' in that form.",
                "Bare forwarding reuses an existing parameter only with the same pattern and never reshapes an argument. "
                    + $"Declare the parameter '{parameterDisplayName}', or call '{calleeDisplayName}' with explicit arguments.")
            : string.Join(
                Environment.NewLine,
                $"'{calleeDisplayName}' is forwarded by name here, but its parameter '{parameterDisplayName}' "
                    + "is not a parameter of the enclosing explicit parameter list.",
                "Bare forwarding reuses an existing parameter only under its own name, and explicit parameter lists are closed, "
                    + $"so '{parameterDisplayName}' is neither renamed nor added. Declare '{parameterDisplayName}' in the parameter list, "
                    + $"or call '{calleeDisplayName}' with explicit arguments.");
    }

    /// <summary>
    /// The synthesized forwarding arguments of a lifted call: one slot per callee parameter pattern,
    /// in the callee's declaration order. A PURE function of its inputs — the region memo
    /// <see cref="ResolverWalkMemos.ImplicitArguments"/> shares one result between every lifted
    /// reference to the callee in a rewrite region (FE-2) — so it reads nothing about the reference
    /// site: its nodes are spanless, name only bindings the caller can already reach (its own
    /// parameters, lifted captures included, and — Q-04 — the enclosing parameter bindings
    /// <paramref name="forwardable"/> it reuses), and carry no occurrence identity. A reused
    /// enclosing binding is read through the ordinary captured-parameter read, so the callee receives
    /// the very binding an existing written reference of that name denotes. Forwarding is BY BINDING
    /// NAME: every callee capture receives the caller's binding of its name, so a name the callee
    /// repeats (<c>P(x, x)</c>, <c>P((x, a), x)</c>) receives that one binding at every occurrence —
    /// exactly the call <c>P(x, x)</c> a programmer would write — and the callee's binder then checks
    /// the occurrences as the ordinary independently evaluated argument slots they are (Q-05).
    /// <para>FORWARDING PRESERVES EACH BINDING AND EACH STRUCTURAL KIND (FWD-02, September 2026):
    /// every binding is forwarded as itself — a fixed binding as one <c>Param</c>, a collecting
    /// source into a collecting destination re-spread — never wrapped in a structure of its own;
    /// and a callee structural pattern is rebuilt around those bindings as the SAME kind it
    /// matches (<see cref="BuildPatternArgument"/>): a sequence pattern as a sequence, a list
    /// pattern as a list — never the other kind. So <c>Add((x, y))</c> / <c>A = [Add]:0</c> is
    /// <c>A((x, y)) = [Add((x, y))]:0</c> and <c>Single([x])</c> / <c>B = Single + 0</c> is
    /// <c>B([x]) = Single([x]) + 0</c>. The rebuilt group is the tree the explicit written call
    /// has, so implicit forwarding is observationally the explicit call that writes the same
    /// bindings into the callee's pattern.</para>
    /// </summary>
    private static IReadOnlyList<Expr> BuildImplicitCallArguments(
        IReadOnlyList<ParameterPattern> calleePatterns,
        IReadOnlyList<ParameterPattern> callerPatterns,
        IReadOnlyDictionary<string, ParameterKind> sourceBindingKinds,
        ForwardableParameters forwardable)
    {
        TryGetSingleCollectingForwarding(
            callerPatterns,
            calleePatterns,
            out var forwardedCalleeName,
            out var forwardedCallerName);

        // TryGetSingleCollectingForwarding succeeds only when the callee shape
        // contains exactly one capture: a lone collector inside one structural
        // group (a lone TOP-LEVEL collector accepts zero supplied arguments and is
        // never lifted, Q-03). Consequently there is no second callee capture to
        // discriminate here; when forwarding is active, every reachable capture is
        // the forwarded capture. Expressing that invariant directly avoids an
        // equivalent && -> || mutant.
        string MapCaptureName(CaptureParameterPattern capture)
            => forwardedCalleeName is not null ? forwardedCallerName! : capture.Name;

        // A collecting DESTINATION re-spreads the forwarded value only when the
        // SOURCE binding is itself a collecting binding's exact list: then
        // `callee(rest*)` re-supplies exactly the collected items
        // (spread(collect(xs)) = xs). An ordinary source binding always
        // forwards as ONE argument, even into a collecting destination. The
        // source is the caller's own binding, else the enclosing parameter
        // binding it reuses (Q-04); a name bound by neither is about to be
        // lifted as a copy of the callee's own pattern, so its source kind IS
        // the callee kind.
        bool ForwardAsSpread(CaptureParameterPattern calleeCapture)
        {
            var sourceName = MapCaptureName(calleeCapture);
            return sourceBindingKinds.TryGetValue(sourceName, out var sourceKind)
                || forwardable.TryGetKind(sourceName, out sourceKind)
                    ? sourceKind == ParameterKind.Collecting
                    : calleeCapture.Kind == ParameterKind.Collecting;
        }

        return calleePatterns
            .Select(pattern => BuildPatternArgument(pattern, MapCaptureName, ForwardAsSpread))
            .ToList();
    }

    private static Expr BuildPatternArgument(
        ParameterPattern pattern,
        Func<CaptureParameterPattern, string> mapCaptureName,
        Func<CaptureParameterPattern, bool> forwardAsSpread)
    {
        return pattern switch
        {
            // A collecting destination whose source binding is a collecting binding's
            // exact list forwards through explicit spread so the callee's collecting
            // parameter re-collects exactly the caller's items; every other
            // capture forwards as one argument slot.
            CaptureParameterPattern { Kind: ParameterKind.Collecting } collecting
                when forwardAsSpread(collecting) =>
                new Expr.SequenceSpread(new Expr.Param(mapCaptureName(collecting))),
            CaptureParameterPattern capture => new Expr.Param(mapCaptureName(capture)),
            // A forwarded structural pattern is rebuilt as the SAME kind it matches (FWD-02):
            // STRUCTURAL PATTERN DELIMITERS SELECT THE VALUE KIND THEY DESTRUCTURE, so the only
            // argument the callee pattern can open is a value of its own kind, and
            // reconstruction never converts between sequence and list.
            SequenceValueParameterPattern group
                => BuildSequenceArgument(BuildPatternArgumentOutput(group.Items, mapCaptureName, forwardAsSpread)),
            ListValueParameterPattern list => new Expr.ListLiteral(new OutputBundle(
                BuildPatternArgumentOutput(list.Items, mapCaptureName, forwardAsSpread))),
            // The deconstruction unpacking receiver (never written; only a host-built callee can
            // carry one here) opens a list one level at every cardinality, so the exact list of
            // its items is the argument it re-binds exactly.
            UnpackingParameterPattern unpacking => new Expr.ListLiteral(new OutputBundle(
                BuildPatternArgumentOutput(unpacking.Items, mapCaptureName, forwardAsSpread))),
        };
    }

    /// <summary>
    /// A sequence pattern's rebuilt argument: exactly the tree the explicit written group
    /// <c>(e1, …, en)</c> has — <c>()</c> for no items, the one item itself for a lone non-spread
    /// item (a one-slot group IS its content, SYN-06; there is no one-item sequence), and
    /// otherwise a capture of the slots (a spread slot contributes its items). A valid sequence
    /// pattern matched a sequence of zero or at least two elements, so rebuilding a COPIED
    /// pattern reproduces that very sequence; a lone forwarded binding is the explicit call
    /// <c>C((x))</c>, which is <c>C(x)</c>.
    /// </summary>
    private static Expr BuildSequenceArgument(IReadOnlyList<Expr> items)
        => items switch
        {
            [] => new Expr.EmptySequence(0),
            [var only] when only is not Expr.SequenceSpread => only,
            _ => new Expr.Capture(new OutputBundle(items)),
        };

    private static IReadOnlyList<Expr> BuildPatternArgumentOutput(
        IReadOnlyList<ParameterPattern> patterns,
        Func<CaptureParameterPattern, string> mapCaptureName,
        Func<CaptureParameterPattern, bool> forwardAsSpread)
        => patterns
            .Select(pattern => BuildPatternArgument(pattern, mapCaptureName, forwardAsSpread))
            .ToList();

    /// <summary>
    /// Collects implicit dependencies from an expression: bare value-position
    /// <see cref="Expr.Resolve"/> nodes pointing to visible algorithms that REQUIRE supplied
    /// arguments (<see cref="RequiresSuppliedArguments"/>). A reference to an algorithm that
    /// accepts zero supplied arguments contributes nothing: it is read, never forwarded.
    /// </summary>
    private static void CollectImplicitDeps(
        Expr expr,
        SignatureMap paramMap,
        HashSet<string> seen,
        List<(string Name, CallableSignature Signature)> deps,
        bool inCallPosition,
        DepsWalkMemo memo)
    {
        // DAG-safety: every contribution of this walk is seen-set deduplicated, so a
        // completed node reference reached again — under the same call-position flavor,
        // which is the one context dimension that changes what a node contributes — adds
        // nothing and is skipped. Childless leaves decide in place.
        if (!AstTraversalDagSafety.HasTraversableExprChildren(expr))
        {
            CollectImplicitDepsCore(expr, paramMap, seen, deps, inCallPosition, memo);
            return;
        }

        var visited = inCallPosition
            ? memo.CalleeVisited ??= new(ReferenceEqualityComparer.Instance)
            : memo.ValueVisited;
        if (visited.Contains(expr))
            return;

        memo.Observations?.RecordResolverCollectExpansion();
        CollectImplicitDepsCore(expr, paramMap, seen, deps, inCallPosition, memo);
        visited.Add(expr);
    }

    private static void CollectImplicitDepsCore(
        Expr expr,
        SignatureMap paramMap,
        HashSet<string> seen,
        List<(string Name, CallableSignature Signature)> deps,
        bool inCallPosition,
        DepsWalkMemo memo)
    {
        switch (expr)
        {
            case Expr.Resolve(var name):
                if (inCallPosition)
                    break;

                if (paramMap.TryGetValue(name, out var ps))
                {
                    if (RequiresSuppliedArguments(ps) && seen.Add(name))
                        deps.Add((name, ps));
                }
                else if (expr.TryGetRegistryProvenMathAliasFacts(paramMap.ContainsKey, out var bareAliasFacts)
                    && RequiresSuppliedArguments(bareAliasFacts.Signature)
                    && seen.Add(bareAliasFacts.CanonicalKey))
                {
                    // A bare Math ALIAS in value position lifts exactly like the
                    // bare canonical `Math.X` spelling (the DotCall arm below),
                    // from the same registry facts. The canonical key dedups the
                    // two spellings into ONE lifted dependency. Any visible user
                    // property — even a zero-parameter one — shadows the alias
                    // through the paramMap branch above.
                    //
                    // The resolver's shadow predicate for every Math-shape
                    // classification (this arm, the alias-call arms, and the
                    // canonical `Math.X` arms) is `paramMap.ContainsKey`: the map
                    // carries every visible user property — local or ancestor —
                    // and a parameter reference is an Expr.Param after detection,
                    // so a surviving bare Expr.Resolve outside the map can only
                    // resolve to the prelude. A user-defined `sin` or `Math`
                    // therefore stays an ordinary neutral callable/container.
                    deps.Add((bareAliasFacts.CanonicalKey, bareAliasFacts.Signature));
                }
                break;

            case Expr.Call(var func, var callArgs) call:
                // Every callee is consumed on the algorithm channel, including
                // the qualified native reference in `(Math.Abs)(A)`. Its own
                // parameters are supplied by this call, never implicitly lifted.
                CollectImplicitDeps(func, paramMap, seen, deps, inCallPosition: true, memo);
                if (call.HasRegistryProvenStrictValueArguments(paramMap.ContainsKey))
                {
                    CollectArgumentImplicitDeps(callArgs, paramMap, seen, deps, memo);
                }
                break;

            case Expr.Binary(_, var left, var right):
                CollectImplicitDeps(left, paramMap, seen, deps, false, memo);
                CollectImplicitDeps(right, paramMap, seen, deps, false, memo);
                break;

            case Expr.Comparison(var first, var links):
                CollectImplicitDeps(first, paramMap, seen, deps, false, memo);
                foreach (var link in links)
                    CollectImplicitDeps(link.Operand, paramMap, seen, deps, false, memo);
                break;

            case Expr.Unary(_, var operand):
                CollectImplicitDeps(operand, paramMap, seen, deps, false, memo);
                break;

            case Expr.Index(var target, var selector):
                CollectImplicitDeps(target, paramMap, seen, deps, false, memo);
                CollectImplicitDeps(selector, paramMap, seen, deps, false, memo);
                break;

            case Expr.SequenceSpread(var operand):
                CollectImplicitDeps(operand, paramMap, seen, deps, false, memo);
                break;

            case Expr.SequenceConstruct(var left, var right):
                CollectImplicitDeps(left, paramMap, seen, deps, false, memo);
                CollectImplicitDeps(right, paramMap, seen, deps, false, memo);
                break;

            case Expr.ListLiteral(var listItems):
                foreach (var item in listItems)
                    CollectImplicitDeps(item, paramMap, seen, deps, false, memo);
                break;

            case Expr.DotCall dotCall:
                if (!inCallPosition
                    && TryGetBareBuiltinCallableSignature(dotCall, paramMap, out var callableKey, out var signature))
                {
                    if (seen.Add(callableKey))
                        deps.Add((callableKey, signature));
                }

                // DotCall target is in algorithm position (resolveAlg, not eval) — unless the
                // edge must fall back to a Math member, where it is the leading ARGUMENT of the
                // call `x(receiver, args)` (dotted-call equivalence) and a strict value position.
                var strictFallback = dotCall.HasRegistryProvenStrictValueFallback(paramMap.ContainsKey);
                CollectImplicitDeps(dotCall.Target, paramMap, seen, deps, inCallPosition: !strictFallback, memo);
                if (dotCall.Args is { } dotArgs
                    && (strictFallback || dotCall.HasRegistryProvenStrictValueArguments(paramMap.ContainsKey)))
                {
                    CollectArgumentImplicitDeps(dotArgs, paramMap, seen, deps, memo);
                }
                break;

            case Expr.Grace(var inner, _):
                CollectImplicitDeps(inner, paramMap, seen, deps, inCallPosition, memo);
                break;

            case Expr.AlgorithmExpr or Expr.Capture:
                // A scoped block owns its names; a capture suppresses callable
                // lifting for everything inside it (pre-split behavior for
                // grouped expressions). Neither contributes deps here.
                break;

            // Intentional leaves: no bare callable references to lift.
            case Expr.Num:
            case Expr.Param:
            case Expr.StringLiteral:
            case Expr.BoolLiteral:
            case Expr.EmptySequence:
            case Expr.NativeCall:
                break;

            // Runtime exhaustiveness guard (statement-form collector, which the
            // closed Expr hierarchy cannot make compiler-exhaustive — see
            // AstWalker.VisitExpr): a new Expr variant must be classified above
            // rather than silently contributing no implicit dependencies.
            default:
                throw new InvalidOperationException(
                    $"Unhandled Expr variant in {nameof(ImplicitArgumentResolver)}.{nameof(CollectImplicitDeps)}: {expr.GetType().Name}. " +
                    "Classify the new variant explicitly as a collected case or an intentional leaf.");
        }
    }

    private static void CollectArgumentImplicitDeps(
        OutputBundle args,
        SignatureMap paramMap,
        HashSet<string> seen,
        List<(string Name, CallableSignature Signature)> deps,
        DepsWalkMemo memo)
    {
        foreach (var argExpr in args)
            CollectImplicitDeps(argExpr, paramMap, seen, deps, inCallPosition: false, memo);
    }

    /// <summary>
    /// Rewrites bare <see cref="Expr.Resolve"/> nodes into <see cref="Expr.Call"/> nodes
    /// with lifted parameters. Also recursively processes nested algorithms.
    /// </summary>
    /// <remarks>
    /// <paramref name="inStrictValueDemand"/> is true while this position's produced value is
    /// required by a registry-proven value-demanding consumer — set by
    /// <see cref="ProcessValueDemandingArgumentBundle"/> and carried down only through
    /// positions that compute that same value (operands, index parts, sequence/list
    /// elements, a nested value-demanding bundle). It is DROPPED wherever the walk leaves
    /// that obligation: call/dot-call targets (algorithm position), neutral argument
    /// bundles, capture rows, and nested algorithms. The flag never changes a rewrite —
    /// only whether a refused lift is additionally REPORTED (see
    /// <see cref="ReportBlockedStrictValueForwarding"/>), so it is not part of the rewrite
    /// memo key. A separate strict-visit set makes that reporting side effect independent of
    /// whether a neutral reach populated the rewrite memo first.
    /// </remarks>
    private static Expr RewriteImplicitCalls(
        Expr expr,
        SignatureMap paramMap,
        ImplicitRewriteContext context,
        bool inCallPosition,
        ResolverWalkMemos memos,
        bool inStrictValueDemand = false)
    {
        // DAG-safety: one rewrite per shared node reference per (region, call position); the
        // memo returns the same rewritten node for every later reach, preserving the input's
        // sharing (see ResolverWalkMemos). A Resolve leaf participates because value-position
        // resolution may replace it with a fresh Call. Node plus call position is a complete
        // key only while the region rewrites under ONE caller context — pinned here, not
        // assumed.
        memos.PinRewriteContext(context);

        var hasTraversableChildren = AstTraversalDagSafety.HasTraversableExprChildren(expr);
        if (!hasTraversableChildren && expr is not Expr.Resolve)
            return RewriteImplicitCallsCore(expr, paramMap, context, inCallPosition, memos, inStrictValueDemand);

        var observeStrictValueDemand = inStrictValueDemand
            && memos.TryBeginStrictValueDiagnosticVisit(expr);
        var rewriteMap = memos.RewriteMapFor(inCallPosition);
        if (rewriteMap.TryGetValue(expr, out var rewritten))
        {
            // The cached rewrite is still authoritative. Re-enter the existing traversal
            // only for its first strict diagnostic observation; descendants use the same
            // independent visit set, so each shared written occurrence reports at most once.
            if (observeStrictValueDemand)
                _ = RewriteImplicitCallsCore(expr, paramMap, context, inCallPosition, memos, inStrictValueDemand: true);
            return rewritten;
        }

        if (hasTraversableChildren)
            memos.Observations?.RecordResolverRewriteExpansion();
        rewritten = RewriteImplicitCallsCore(
            expr, paramMap, context, inCallPosition, memos, observeStrictValueDemand);
        rewriteMap[expr] = rewritten;
        return rewritten;
    }

    private static Expr RewriteImplicitCallsCore(
        Expr expr,
        SignatureMap paramMap,
        ImplicitRewriteContext context,
        bool inCallPosition,
        ResolverWalkMemos memos,
        bool inStrictValueDemand)
    {
        // Every child rewrite is a `with` copy of the node: the record copy carries the span
        // (and every other stored fact) inside the copy constructor, so this calibrated
        // recursion frame holds no span temporaries — see ModuleLoader.ProcessExpr.
        return expr switch
        {
            Expr.Resolve(var name) => RewriteBareReference(
                expr, name, paramMap, context, inCallPosition, memos, inStrictValueDemand),

            Expr.Call call => RewriteCall(call, paramMap, context, memos),

            Expr.Binary binary => binary with
            {
                Left = RewriteImplicitCalls(binary.Left, paramMap, context, false, memos, inStrictValueDemand),
                Right = RewriteImplicitCalls(binary.Right, paramMap, context, false, memos, inStrictValueDemand),
            },

            Expr.Comparison comparison => comparison with
            {
                First = RewriteImplicitCalls(comparison.First, paramMap, context, false, memos, inStrictValueDemand),
                Links = AstHelpers.RewriteComparisonLinks(
                    comparison.Links,
                    operand => RewriteImplicitCalls(operand, paramMap, context, false, memos, inStrictValueDemand)),
            },

            Expr.Unary unary => unary with
            {
                Operand = RewriteImplicitCalls(unary.Operand, paramMap, context, false, memos, inStrictValueDemand),
            },

            Expr.Index index => index with
            {
                Target = RewriteImplicitCalls(index.Target, paramMap, context, false, memos, inStrictValueDemand),
                Selector = RewriteImplicitCalls(index.Selector, paramMap, context, false, memos, inStrictValueDemand),
            },

            Expr.SequenceSpread spread => spread with
            {
                Operand = RewriteImplicitCalls(spread.Operand, paramMap, context, false, memos, inStrictValueDemand),
            },

            Expr.SequenceConstruct construct => construct with
            {
                Left = RewriteImplicitCalls(construct.Left, paramMap, context, false, memos, inStrictValueDemand),
                Right = RewriteImplicitCalls(construct.Right, paramMap, context, false, memos, inStrictValueDemand),
            },

            Expr.ListLiteral list => list with
            {
                Items = list.Items.Select(item => RewriteImplicitCalls(item, paramMap, context, false, memos, inStrictValueDemand)).ToList(),
            },

            // A bare argumentless builtin dot shape in value position (`Math.Pow`) lifts
            // like a bare reference to a property that requires supplied arguments.
            Expr.DotCall { Args: null } bareDotCall
                when !inCallPosition
                    && TryGetBareBuiltinCallableSignature(bareDotCall, paramMap, out var bareBuiltinKey, out var builtinSignature)
                => LiftBareBuiltinDotCall(
                    bareDotCall, bareBuiltinKey, builtinSignature, paramMap, context, memos, inStrictValueDemand),

            Expr.DotCall dotCall => RewriteDotCall(dotCall, paramMap, context, memos),

            Expr.Grace(var inner, _) => RewriteImplicitCalls(inner, paramMap, context, inCallPosition, memos, inStrictValueDemand),

            Expr.AlgorithmExpr block => block with
            {
                Algorithm = ProcessSharedNestedAlgorithm(block.Algorithm, ImportSite.OfBlock(block), paramMap, memos),
            },

            // Capture rows recurse without lifting at this level, exactly as
            // the pre-split transparent group algorithm's rows did.
            Expr.Capture capture => capture with
            {
                Body = new OutputBundle(capture.Body.Select(row => ProcessExprNested(row, paramMap, memos)).ToList()),
            },

            // Intentional leaves: nothing to lift or rewrite. (A Param is an
            // already-elaborated parameter reference; the Resolve arm above
            // handled every liftable name shape.)
            Expr.Num or Expr.Param or Expr.StringLiteral or Expr.BoolLiteral or Expr.EmptySequence or Expr.NativeCall => expr,
        };
    }

    /// <summary>
    /// The bare-reference arm of <see cref="RewriteImplicitCallsCore"/>: a value-position
    /// reference to a property that REQUIRES supplied arguments — or to a registry-proven Math
    /// alias — lifts to an explicit implicit-argument call unless the caller's closed explicit
    /// parameter list blocks the forwarding (reported only under strict value demand). Every
    /// other bare reference stays bare — in particular one to a callable that accepts zero
    /// supplied arguments, which is a cached property-style value demand however many
    /// (optional or collecting) parameters it declares (<see cref="RequiresSuppliedArguments"/>).
    /// </summary>
    private static Expr RewriteBareReference(
        Expr expr,
        string name,
        SignatureMap paramMap,
        ImplicitRewriteContext context,
        bool inCallPosition,
        ResolverWalkMemos memos,
        bool inStrictValueDemand)
    {
        if (!inCallPosition
            && paramMap.TryGetValue(name, out var ps)
            && RequiresSuppliedArguments(ps))
        {
            if (ClosedListBlocksLifting(context, ps.ParameterPatterns, memos))
            {
                if (inStrictValueDemand)
                    ReportBlockedStrictValueForwarding(expr, name, ps.ParameterPatterns, context, memos);
                return expr;
            }

            // The arguments are the region's one shared bundle for this callee (FE-2); the call node
            // and its callee name are this reference's own.
            var implicitArgs = memos.ImplicitArguments(ps.ParameterPatterns, context);
            return memos.SynthesizedImplicitCall(
                new Expr.Call(new Expr.Resolve(name) { Span = expr.Span }, implicitArgs) { Span = expr.Span });
        }

        // Bare Math ALIAS in value position: lift exactly like the bare
        // canonical `Math.X` arm, from the same registry facts and under the
        // same eligibility rule (every Math function requires its arguments).
        // The constant (`pi`) carries no facts and stays a bare reference.
        if (!inCallPosition
            && expr.TryGetRegistryProvenMathAliasFacts(paramMap.ContainsKey, out var bareAliasFacts)
            && RequiresSuppliedArguments(bareAliasFacts.Signature))
        {
            if (ClosedListBlocksLifting(context, bareAliasFacts.Signature.ParameterPatterns, memos))
            {
                if (inStrictValueDemand)
                {
                    ReportBlockedStrictValueForwarding(
                        expr, bareAliasFacts.SpelledName, bareAliasFacts.Signature.ParameterPatterns, context, memos);
                }

                return expr;
            }

            var aliasArgs = memos.ImplicitArguments(bareAliasFacts.Signature.ParameterPatterns, context);
            return memos.SynthesizedImplicitCall(
                new Expr.Call(new Expr.Resolve(name) { Span = expr.Span }, aliasArgs) { Span = expr.Span });
        }

        return expr;
    }

    /// <summary>
    /// The Call arm of <see cref="RewriteImplicitCallsCore"/>. Every callee is in algorithm
    /// position. A resolved Math callable, including a qualified native reference used as
    /// an ordinary callee, shares the written <c>Math.X(...)</c> dot shape's strict-value
    /// argument contract, classified by the shared identity helper: its argument slots are
    /// ordinary value positions and lift. Every other call keeps NEUTRAL argument processing
    /// so bare higher-order references survive.
    /// </summary>
    private static Expr RewriteCall(
        Expr.Call call,
        SignatureMap paramMap,
        ImplicitRewriteContext context,
        ResolverWalkMemos memos)
    {
        var newFunc = RewriteImplicitCalls(call.Function, paramMap, context, inCallPosition: true, memos);
        var newArgs = call.HasRegistryProvenStrictValueArguments(paramMap.ContainsKey)
            ? ProcessValueDemandingArgumentBundle(call.Args, paramMap, context, memos)
            : ProcessArgumentBundle(call.Args, paramMap, memos);
        return new Expr.Call(newFunc, newArgs) { Span = call.Span };
    }

    /// <summary>
    /// The DotCall arm of <see cref="RewriteImplicitCallsCore"/>. The target is in algorithm
    /// position (resolveAlg, not eval) and the written arguments are neutral — except where
    /// the edge IS a Math member's call: the canonical <c>Math.X(...)</c> shape makes its
    /// arguments strict value positions, and a lexical fallback that must be selected on a
    /// Math member makes the edge the call <c>x(receiver, args)</c> (dotted-call
    /// equivalence holds through elaboration), so the receiver and the arguments lift and
    /// report exactly as that direct call's arguments do. The stored lexical fallback is a
    /// Resolve/Param leaf and needs no implicit-call rewriting; <c>with</c> carries it
    /// forward.
    /// </summary>
    private static Expr RewriteDotCall(
        Expr.DotCall dotCall,
        SignatureMap paramMap,
        ImplicitRewriteContext context,
        ResolverWalkMemos memos)
    {
        var strictFallback = dotCall.HasRegistryProvenStrictValueFallback(paramMap.ContainsKey);
        return dotCall with
        {
            Target = strictFallback
                ? RewriteImplicitCalls(dotCall.Target, paramMap, context, inCallPosition: false, memos, inStrictValueDemand: true)
                : RewriteImplicitCalls(dotCall.Target, paramMap, context, inCallPosition: true, memos),
            Args = dotCall.Args is { } dotArgs
                ? strictFallback || dotCall.HasRegistryProvenStrictValueArguments(paramMap.ContainsKey)
                    ? ProcessValueDemandingArgumentBundle(dotArgs, paramMap, context, memos)
                    : ProcessArgumentBundle(dotArgs, paramMap, memos)
                : null,
        };
    }

    /// <summary>
    /// The bare-builtin arm of <see cref="RewriteImplicitCallsCore"/>: an argumentless
    /// canonical Math dot shape in value position lifts to an explicit implicit-argument
    /// call unless the caller's closed explicit parameter list blocks the forwarding.
    /// </summary>
    private static Expr LiftBareBuiltinDotCall(
        Expr.DotCall bareDotCall,
        string bareBuiltinKey,
        CallableSignature builtinSignature,
        SignatureMap paramMap,
        ImplicitRewriteContext context,
        ResolverWalkMemos memos,
        bool inStrictValueDemand)
    {
        if (ClosedListBlocksLifting(context, builtinSignature.ParameterPatterns, memos))
        {
            if (inStrictValueDemand)
            {
                ReportBlockedStrictValueForwarding(
                    bareDotCall, bareBuiltinKey, builtinSignature.ParameterPatterns, context, memos);
            }

            return bareDotCall;
        }

        var liftedDotArgs = memos.ImplicitArguments(builtinSignature.ParameterPatterns, context);
        return memos.SynthesizedImplicitCall(bareDotCall with
        {
            Target = RewriteImplicitCalls(bareDotCall.Target, paramMap, context, inCallPosition: true, memos),
            Args = liftedDotArgs,
        });
    }

    /// <summary>
    /// Processes an argument bundle without lifting at this level: each slot
    /// recurses into nested algorithms only, exactly like every other
    /// transparent expression context (capture rows, list elements). Bare
    /// higher-order references such as <c>Apply(Increment)</c> therefore stay
    /// bare argument slots.
    /// </summary>
    private static OutputBundle ProcessArgumentBundle(
        OutputBundle args,
        SignatureMap paramMap,
        ResolverWalkMemos memos)
        => new(args.Select(argExpr => ProcessExprNested(argExpr, paramMap, memos)).ToList());

    /// <summary>
    /// Region-memoized nested-algorithm processing for transparent contexts and value
    /// positions: two distinct <see cref="Expr.AlgorithmExpr"/> wrappers over ONE shared
    /// algorithm resolve it once (the whole region shares one final signature map).
    /// </summary>
    private static Algorithm ProcessSharedNestedAlgorithm(
        Algorithm alg,
        SourceSpan? importSite,
        SignatureMap paramMap,
        ResolverWalkMemos memos)
    {
        memos.Algorithms ??= new(ReferenceEqualityComparer.Instance);
        if (!memos.Algorithms.TryGetValue(alg, out var processed))
        {
            using var site = memos.Run.EnterImportSite(importSite);
            processed = ProcessAlgorithm(
                alg, paramMap, memos.NestedForwarding, isRoot: false, memos.Observations, memos.Diagnostics, branchContext: null, memos.Run);
            memos.Algorithms[alg] = processed;
        }

        return processed;
    }

    /// <summary>
    /// Processes an argument bundle whose consumer is VALUE-DEMANDING: each
    /// slot is an ordinary value position, so bare references to callables
    /// that require supplied arguments lift to implicit calls exactly as they
    /// would in any other value position (binary operands, output rows), and a
    /// callable that accepts zero supplied arguments stays a cached value read
    /// (<see cref="RequiresSuppliedArguments"/>). This is the
    /// deliberate counterpart of <see cref="ProcessArgumentBundle"/>:
    /// ordinary call arguments stay NEUTRAL (no lifting) because an arbitrary
    /// callee may consume an argument on the higher-order algorithm channel,
    /// and lifting would destroy the bare reference. Value-context processing
    /// is a property of the consumer, not of the argument.
    ///
    /// <para>The current value-demanding consumer is the Math member family in
    /// BOTH of its spellings — the written <c>Math.X(...)</c> dot shape
    /// (<see cref="AstHelpers.HasRegistryProvenStrictValueArguments(Expr.DotCall, Func{string, bool}?)"/>)
    /// and an unshadowed prelude-alias call
    /// (<see cref="AstHelpers.HasRegistryProvenStrictValueArguments(Expr.Call, Func{string, bool}?)"/>),
    /// which resolve to the same <see cref="MathCallableFacts"/>: the builtin registry proves every
    /// Math member consumes strictly numeric values, so no higher-order
    /// channel exists to preserve. Other strict builtins (<c>sum</c>,
    /// <c>count</c>, ...) do NOT currently receive value-context lifting —
    /// their unresolved-reference arguments surface as runtime errors instead
    /// (a documented consistency gap; widening lifting to them would be a new
    /// observable semantic surface and is deliberately left as future
    /// work).</para>
    ///
    /// <para><b>Value-demanding is WHERE lifting happens, never HOW.</b> The consumer's
    /// registry-proven strict-value contract decides only that these slots are value
    /// positions; the rewriting itself must then be the ordinary one, under the ENCLOSING
    /// algorithm's <see cref="ImplicitRewriteContext"/> — the same caller parameter patterns,
    /// the same source binding kinds, and the same closed-explicit-list gate as the rows
    /// around the Math call. This method therefore forwards <paramref name="context"/>
    /// unchanged and holds no configuration of its own. Erasing it (as an earlier revision
    /// did, to let a region's value-demanding memo entries unify) made a semantically neutral
    /// <c>Math.Abs(...)</c> wrapper change elaboration: forwarding spread was decided from the
    /// CALLEE's kind, forwarded under the CALLEE's capture name, and a closed explicit
    /// parameter list silently acquired an ancestor's parameter.</para>
    /// </summary>
    private static OutputBundle ProcessValueDemandingArgumentBundle(
        OutputBundle args,
        SignatureMap paramMap,
        ImplicitRewriteContext context,
        ResolverWalkMemos memos)
    {
        var rewritten = new List<Expr>(args.Count);
        foreach (var argExpr in args)
            rewritten.Add(RewriteImplicitCalls(
                argExpr, paramMap, context, inCallPosition: false, memos, inStrictValueDemand: true));

        return new OutputBundle(rewritten);
    }

    private static bool TryGetBareBuiltinCallableSignature(
        Expr expr,
        SignatureMap paramMap,
        [System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out string? callableKey,
        [System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out CallableSignature? signature)
    {
        // `Math~.Pow` reaches this same structural arm: its ordinary receiver
        // Grace is consumed by parameter detection before implicit-call
        // rewriting, so Grace cannot change registry facts. The bare reference
        // is the argumentless canonical shape, classified by the shared helper.
        if (expr is Expr.DotCall { Args: null } dotCall
            && dotCall.TryGetRegistryProvenCanonicalMathFacts(paramMap.ContainsKey, out var facts)
            && RequiresSuppliedArguments(facts.Signature))
        {
            // The canonical spelling and its prelude alias use the SAME
            // descriptor-projected identity and signature. Do not reconstruct
            // the key from text here: that would create a second convention
            // capable of drifting from MathCallableFacts.CanonicalKey.
            callableKey = facts.CanonicalKey;
            signature = facts.Signature;
            return true;
        }

        callableKey = null;
        signature = null;
        return false;
    }

    /// <summary>
    /// Processes an expression in a transparent context (capture rows, list
    /// elements, argument slots): recurse into nested algorithms only (no
    /// lifting at this level).
    /// </summary>
    private static Expr ProcessExprNested(
        Expr expr,
        SignatureMap paramMap,
        ResolverWalkMemos memos)
    {
        // DAG-safety: one rewrite per shared node reference per region's transparent
        // context; the memo returns the same rewritten node for every later reach.
        if (!AstTraversalDagSafety.HasTraversableExprChildren(expr))
            return ProcessExprNestedCore(expr, paramMap, memos);

        memos.NestedRewrites ??= new(ReferenceEqualityComparer.Instance);
        if (memos.NestedRewrites.TryGetValue(expr, out var rewritten))
            return rewritten;

        memos.Observations?.RecordResolverRewriteExpansion();
        rewritten = ProcessExprNestedCore(expr, paramMap, memos);
        memos.NestedRewrites[expr] = rewritten;
        return rewritten;
    }

    private static Expr ProcessExprNestedCore(
        Expr expr,
        SignatureMap paramMap,
        ResolverWalkMemos memos)
    {
        return expr switch
        {
            Expr.AlgorithmExpr block => block with
            {
                Algorithm = ProcessSharedNestedAlgorithm(block.Algorithm, ImportSite.OfBlock(block), paramMap, memos),
            },
            Expr.Capture capture => capture with
            {
                Body = new OutputBundle(
                    capture.Body.Select(row => ProcessExprNested(row, paramMap, memos)).ToList()),
            },
            Expr.Call call => call with
            {
                Function = ProcessExprNested(call.Function, paramMap, memos),
                Args = ProcessArgumentBundle(call.Args, paramMap, memos),
            },
            Expr.Binary binary => binary with
            {
                Left = ProcessExprNested(binary.Left, paramMap, memos),
                Right = ProcessExprNested(binary.Right, paramMap, memos),
            },
            Expr.Comparison comparison => comparison with
            {
                First = ProcessExprNested(comparison.First, paramMap, memos),
                Links = AstHelpers.RewriteComparisonLinks(comparison.Links, operand => ProcessExprNested(operand, paramMap, memos)),
            },
            Expr.Unary unary => unary with { Operand = ProcessExprNested(unary.Operand, paramMap, memos) },
            Expr.Index index => index with
            {
                Target = ProcessExprNested(index.Target, paramMap, memos),
                Selector = ProcessExprNested(index.Selector, paramMap, memos),
            },
            Expr.SequenceSpread spread => spread with { Operand = ProcessExprNested(spread.Operand, paramMap, memos) },
            Expr.SequenceConstruct construct => construct with
            {
                Left = ProcessExprNested(construct.Left, paramMap, memos),
                Right = ProcessExprNested(construct.Right, paramMap, memos),
            },
            Expr.ListLiteral list => list with { Items = list.Items.Select(item => ProcessExprNested(item, paramMap, memos)).ToList() },
            // `with` keeps the stored dot-edge facts (member span, lexical
            // fallback) — a positional rebuild here silently dropped the
            // elaborated fallback identity inside argument bundles, capture
            // rows, and list elements.
            Expr.DotCall dotCall => dotCall with
            {
                Target = ProcessExprNested(dotCall.Target, paramMap, memos),
                Args = dotCall.Args is { } da ? ProcessArgumentBundle(da, paramMap, memos) : null,
            },
            Expr.Grace(var inner, _) => ProcessExprNested(inner, paramMap, memos),
            // Intentional leaves: bare references stay bare in transparent
            // contexts (no lifting at this level, so higher-order references
            // such as Apply(Increment) survive), and literals carry nothing to
            // process.
            Expr.Resolve or Expr.Param or Expr.Num or Expr.StringLiteral or Expr.BoolLiteral
                or Expr.EmptySequence or Expr.NativeCall => expr,
        };
    }
}
