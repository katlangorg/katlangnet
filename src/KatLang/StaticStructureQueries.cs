namespace KatLang;

internal enum StaticFactKind : byte
{
    Unknown, Missing, Bound, Parameter, Declaration, Ambiguous, Structure, Runtime, Absent, Failure,
    Members, Providers, Inputs, Yes, No, Refused, Never, May, Always, ExpansionPending, ExpansionFinal, OpenMatch, NamespaceCoverage,
}

/// <summary>Operation-local immutable facts. Scope and property fields always retain written identity.</summary>
internal sealed record StaticFact(
    StaticFactKind Kind, StaticScopeKey? Scope = null, Property? Property = null, object? Data = null)
{
    internal static readonly StaticFact Unknown = new(StaticFactKind.Unknown);
    internal static readonly StaticFact Missing = new(StaticFactKind.Missing);
    internal static readonly StaticFact Bound = new(StaticFactKind.Bound);
    internal static readonly StaticFact Ambiguous = new(StaticFactKind.Ambiguous);
    internal static readonly StaticFact Yes = new(StaticFactKind.Yes);
    internal static readonly StaticFact No = new(StaticFactKind.No);
    internal static readonly StaticFact Refused = new(StaticFactKind.Refused);
    internal bool IsUnknown => Kind == StaticFactKind.Unknown;
    internal bool HasUnknownSelection => Kind is StaticFactKind.Unknown or StaticFactKind.Bound or StaticFactKind.NamespaceCoverage;
}

internal sealed record StaticOpenMatch(StaticScopeKey? Provider, bool Pending);
internal sealed record StaticProviderTree(StaticProviderTree? Left = null, StaticProviderTree? Right = null, StaticScopeKey[]? Leaves = null);

/// <summary>Q4's one immutable syntax index; public and branch-only surfaces remain distinct.</summary>
internal sealed class StaticMembers
{
    private readonly Dictionary<string, Property> _declared = new(StringComparer.Ordinal);
    private readonly Dictionary<string, Property> _public = new(StringComparer.Ordinal);
    private readonly HashSet<string> _branchOnly = new(StringComparer.Ordinal);
    private Property? _nullDeclared;
    private Property? _nullPublic;

    internal StaticMembers(Algorithm algorithm, CancellationToken cancellationToken = default)
    {
        foreach (var property in algorithm.Properties)
        {
            cancellationToken.ThrowIfCancellationRequested();
            // Malformed host payloads retain the ordered lookup relation, including a null name.
            // Null is not a source-language name and is kept outside the named namespace index.
            if (property.Name is null)
            {
                _nullDeclared ??= property;
                if (property.IsPublic) _nullPublic ??= property;
            }
            else
            {
                _declared.TryAdd(property.Name, property);
                if (property.IsPublic) _public.TryAdd(property.Name, property);
            }
        }
        if (algorithm is Algorithm.Conditional conditional)
            foreach (var branch in conditional.Branches)
                foreach (var property in branch.Body.Properties)
                {
                    cancellationToken.ThrowIfCancellationRequested();
                    _branchOnly.Add(property.Name);
                }
    }

    internal Property? Declared(string name) => name is null ? _nullDeclared : _declared.GetValueOrDefault(name);
    internal Property? Public(string name) => name is null ? _nullPublic : _public.GetValueOrDefault(name);
    internal bool IsBranchOnly(string name) => _branchOnly.Contains(name);
    internal bool HasMembers => _declared.Count != 0 || _nullDeclared is not null || _branchOnly.Count != 0;
    internal bool HasPublicMembers => _public.Count != 0 || _nullPublic is not null;
    internal IEnumerable<Property> PublicProperties => _public.Values;
}

/// <summary>
/// B3-2★ production Q1–Q7 authority. All structural conclusions and implementation projections
/// use this one engine. Phase-aware admission keeps immutable definitions separate from processed
/// views; RawSource permits inference/formation, NameResolved formation only, Resolved neither.
/// StaticStructureOperation publishes completed facts and forks deferred bodies under fresh regions.
/// A changed definition must never be registered under an already completed key.
/// </summary>
internal sealed partial class StaticStructureQueries : IStaticQueryDefinition<StaticQueryKey, StaticFact>
{
    internal sealed class BodySyntax(Algorithm body, CancellationToken cancellationToken)
    {
        internal Algorithm Body { get; } = body;
        internal StaticMembers Members { get; } = new(body, cancellationToken);
        internal IReadOnlySet<string> Parameters { get; } = new HashSet<string>(body is Algorithm.User user
            ? ParameterPattern.FlattenCaptures(user.NameResolutionParameterPatterns).Select(p => p.Name) : body.Params, StringComparer.Ordinal);
        private StaticInputGraph? _graph;
        internal long InputGraphBuilds { get; private set; }
        internal long InputGraphNodeVisits { get; private set; }
        internal long RetainedStorageUnits => 4 + 3L * Body.Properties.Count + 2L * Parameters.Count + (_graph?.RetainedStorageUnits ?? 0);
        internal StaticInputGraph Graph(StaticQueryResourceBudget? budget, CancellationToken token)
        {
            if (_graph is not null) return _graph;
            lock (this)
            {
                if (_graph is not null) return _graph;
                _graph = new(Body is Algorithm.User user ? AstHelpers.WrittenRows(user) : [], budget, token);
                InputGraphBuilds++;
                InputGraphNodeVisits += _graph.Nodes.Count;
                return _graph;
            }
        }
    }

    internal sealed class BodyContext(StaticScopeKey key, BodySyntax syntax, StaticScopeKey? parent, IReadOnlySet<string>? branchBinders = null, StaticQueryResourceBudget? resourceBudget = null, CancellationToken cancellationToken = default)
    {
        internal StaticScopeKey Key { get; } = key;
        internal Algorithm Body => syntax.Body;
        internal StaticScopeKey? Parent { get; } = parent;
        internal StaticMembers Members => syntax.Members;
        internal IReadOnlySet<string> WrittenParameters { get; } = branchBinders ?? syntax.Parameters;
        internal bool AllowsInference { get; init; } = true;
        internal bool AllowsReferenceFormation { get; init; } = true;
        internal bool Infers => AllowsInference && branchBinders is null && Body is Algorithm.User { HasExplicitParameterList: false };
        internal StaticInputGraph Syntax => syntax.Graph(resourceBudget, cancellationToken);
        internal BodyContext Retokenize(StaticQueryResourceBudget? budget, CancellationToken token) => new(Key, syntax, Parent, branchBinders, budget, token) { HasOpens = HasOpens, AllowsInference = AllowsInference, AllowsReferenceFormation = AllowsReferenceFormation };
        internal bool HasOpens { get; init; }
    }

    private readonly Dictionary<StaticScopeKey, BodyContext> _contexts = new(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<Algorithm, BodySyntax> _syntaxSources = new(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<Pattern, IReadOnlySet<string>> _branchNames = new(ReferenceEqualityComparer.Instance);
    private readonly StaticQueryEngine<StaticQueryKey, StaticFact> _engine;
    private readonly CancellationToken _cancellationToken;
    private readonly Snapshot? _snapshot;
    private readonly StaticAstPhase _phase;

    internal StaticStructureQueries(Algorithm root, StaticQueryLimits limits, Algorithm? prelude = null, StaticAstPhase phase = StaticAstPhase.RawSource,
        CancellationToken cancellationToken = default)
    {
        cancellationToken.ThrowIfCancellationRequested();
        _cancellationToken = cancellationToken;
        _phase = phase;
        Keys = new StaticKeyTable();
        var preludeBody = prelude ?? BuiltinRegistry.CreateSemanticPreludeAlgorithm();
        _engine = new(this, limits: limits, cancellationToken: cancellationToken);
        Resources.Metadata(8, cancellationToken: cancellationToken);
        _contexts.Add(Keys.Root, new(Keys.Root, SyntaxOf(preludeBody), null, resourceBudget: Resources, cancellationToken: cancellationToken) { HasOpens = preludeBody.Opens.Count != 0 });
        Root = BodyIn(Keys.Root, root);
    }

    internal StaticKeyTable Keys { get; }
    internal StaticScopeKey Root { get; }
    internal StaticQueryStatistics Statistics => _engine.Statistics;
    internal FrontEndTraversalObservations? Observations { get; set; }
    internal long SyntaxIndexBuilds { get; private set; }
    internal long SyntaxPropertyEntries { get; private set; }
    internal long InputGraphBuilds => _syntaxSources.Values.Sum(syntax => syntax.InputGraphBuilds);
    internal long InputGraphNodeVisits => _syntaxSources.Values.Sum(syntax => syntax.InputGraphNodeVisits);
    internal int LocalContextCount => _contexts.Count;
    internal StaticQueryResourceBudget Resources => _engine.Resources;
    internal CancellationToken OperationToken => _cancellationToken;
    internal IReadOnlySet<string> WrittenParametersOf(StaticScopeKey scope) => ContextOf(scope).WrittenParameters;
    internal IReadOnlyList<string> CandidateNames(StaticScopeKey scope) => ContextOf(scope).Infers ? ContextOf(scope).Syntax.Names : [];
    internal Algorithm BodyOf(StaticScopeKey scope) => ContextOf(scope).Body;
    internal bool IsSourceDefinition(Algorithm body)
        => _syntaxSources.ContainsKey(body) || _snapshot?.Syntax.ContainsKey(body) == true;
    internal void RequireInputPhase(StaticScopeKey scope, StaticAstPhase phase)
    {
        var context = ContextOf(scope);
        if (context.AllowsInference != (phase == StaticAstPhase.RawSource)
            || context.AllowsReferenceFormation != (phase != StaticAstPhase.Resolved))
            throw new ArgumentException("A coherent source admission cannot reinterpret an existing definition in another phase.", nameof(phase));
    }
    internal StaticFact Get(StaticQueryKey key)
    {
        var fact = _engine.Get(key);
        Observations?.RecordStaticQueryRead(key, fact);
        return fact;
    }
    internal void EnsureUsable()
    {
        try { _cancellationToken.ThrowIfCancellationRequested(); }
        catch { Resources.Fail(); throw; }
        _engine.EnsureUsable();
    }

    private bool TryContext(StaticScopeKey key, out BodyContext? context)
    {
        if (_contexts.TryGetValue(key, out context)) return true;
        if (_snapshot is null || !_snapshot.Contexts.TryGetValue(key, out var external)) return false;
        _cancellationToken.ThrowIfCancellationRequested();
        Resources.Metadata(2, cancellationToken: _cancellationToken);
        _contexts.Add(key, context = external.Retokenize(Resources, _cancellationToken));
        return true;
    }

    private BodyContext ContextOf(StaticScopeKey key)
        => TryContext(key, out var context) ? context! : throw new KeyNotFoundException("The static scope was not admitted to this unit.");

    private BodySyntax SyntaxOf(Algorithm body)
    {
        if (!_syntaxSources.TryGetValue(body, out var syntax))
        {
            if (_snapshot is not null && _snapshot.Syntax.TryGetValue(body, out var shared))
            {
                Resources.Metadata(1, cancellationToken: _cancellationToken);
                syntax = shared;
            }
            else
            {
                var parameters = body is Algorithm.User user ? ParameterPattern.CountCaptures(user.NameResolutionParameterPatterns) : body.Params.Count;
                Resources.Metadata(4 + 3L * body.Properties.Count + 2L * parameters,
                    1L + body.Properties.Count + parameters, _cancellationToken);
                syntax = new(body, _cancellationToken);
                SyntaxIndexBuilds++;
                SyntaxPropertyEntries += body.Properties.Count;
                Observations?.RecordStaticSyntaxIndexBuild(body.Properties.Count);
            }
            _syntaxSources.Add(body, syntax);
        }
        return syntax;
    }

    internal StaticScopeKey BodyIn(StaticScopeKey declaring, Algorithm body, object? ownerIdentity = null)
    {
        _cancellationToken.ThrowIfCancellationRequested();
        var key = Keys.DefinitionIn(declaring, body, null, Resources, ownerIdentity, _cancellationToken);
        if (!TryContext(key, out var existing))
        {
            var parent = body.IsModuleRoot ? Keys.Root : declaring;
            Resources.Metadata(8, cancellationToken: _cancellationToken);
            _contexts.Add(key, new(key, SyntaxOf(body), parent, resourceBudget: Resources, cancellationToken: _cancellationToken) { HasOpens = body.Opens.Count != 0 || ContextOf(parent).HasOpens, AllowsInference = _phase == StaticAstPhase.RawSource, AllowsReferenceFormation = _phase != StaticAstPhase.Resolved });
        }
        else if (!ReferenceEquals(existing!.Body, body))
            throw new InvalidOperationException("A static query context cannot change its source definition.");
        return key;
    }

    internal StaticScopeKey BranchBodyIn(StaticScopeKey declaring, Algorithm body, Pattern pattern, object? ownerIdentity = null)
    {
        if (body.IsModuleRoot) return BodyIn(declaring, body);
        _cancellationToken.ThrowIfCancellationRequested();
        var key = Keys.DefinitionIn(declaring, body, pattern, Resources, ownerIdentity, _cancellationToken);
        if (!TryContext(key, out var existing))
        {
            if (!_branchNames.TryGetValue(pattern, out var names))
            {
                var set = new HashSet<string>(StringComparer.Ordinal);
                foreach (var name in pattern.BoundNames()) { Resources.Metadata(1, cancellationToken: _cancellationToken); set.Add(name); }
                _branchNames.Add(pattern, names = set);
            }
            Resources.Metadata(8, cancellationToken: _cancellationToken);
            _contexts.Add(key, new(key, SyntaxOf(body), declaring, names, Resources, _cancellationToken) { HasOpens = body.Opens.Count != 0 || ContextOf(declaring).HasOpens, AllowsInference = _phase == StaticAstPhase.RawSource, AllowsReferenceFormation = _phase != StaticAstPhase.Resolved });
        }
        else if (!ReferenceEquals(existing!.Body, body))
            throw new InvalidOperationException("A branch query context cannot change its source definition.");
        return key;
    }

    public bool IsClosureObserver(StaticQueryKey key) => key.Projection is StaticQueryProjection.OpenMemberAbsence
        or StaticQueryProjection.EmptyOpenNamespace or StaticQueryProjection.FallbackParticipation or StaticQueryProjection.PreservedOpenPresence;

    public StaticFact Initial(StaticQueryKey key) => StaticFact.Unknown;
    public StaticFact PathCycleValue => StaticFact.Refused;
    public bool IsRefinement(StaticFact before, StaticFact after) => before.IsUnknown || ValueEquals(before, after)
        || before.Kind == StaticFactKind.NamespaceCoverage && after.Kind == StaticFactKind.Yes
        || before.Kind == StaticFactKind.Bound && after.Kind is StaticFactKind.Parameter or StaticFactKind.Declaration or StaticFactKind.Ambiguous
        || before.Kind == StaticFactKind.OpenMatch && before.Data is StaticOpenMatch { Pending: true } old
            && (after.Kind == StaticFactKind.Ambiguous || after.Data is StaticOpenMatch next && SameProvider(old.Provider, next.Provider));
    public bool ValueEquals(StaticFact left, StaticFact right)
        => left.Kind == right.Kind && ReferenceEquals(left.Scope, right.Scope) && ReferenceEquals(left.Property, right.Property)
            && (ReferenceEquals(left.Data, right.Data) || (left.Data, right.Data) switch
            {
                (StaticScopeKey[] a, StaticScopeKey[] b) => a.AsSpan().SequenceEqual(b),
                (string[] a, string[] b) => a.AsSpan().SequenceEqual(b),
                (StaticOpenMatch a, StaticOpenMatch b) => a.Pending == b.Pending
                    && (a.Pending ? SameProvider(a.Provider, b.Provider) : ReferenceEquals(a.Provider, b.Provider)),
                (OpenMemberIndex a, OpenMemberIndex b) => a.Same(b),
                (StaticProviderTree a, StaticProviderTree b) => ReferenceEquals(a.Left, b.Left) && ReferenceEquals(a.Right, b.Right) && ReferenceEquals(a.Leaves, b.Leaves),
                _ => false,
            });

    private static StaticQueryKey Project(StaticQueryKind family, StaticScopeKey scope, StaticQueryProjection projection,
        string? name = null, StaticCycleCheck stratum = StaticCycleCheck.Formation, Expr? node = null)
        => StaticQueryKey.Project(family, scope, projection, name, stratum, node);

    public StaticQueryStep<StaticFact> Compute(StaticQueryKey key, StaticQueryReader<StaticQueryKey, StaticFact> reader)
    {
        _cancellationToken.ThrowIfCancellationRequested();
        if (_snapshot is not null && _snapshot.Facts.TryGetValue(key, out var imported))
        {
            Observations?.RecordStaticImportedFactRead();
            return StaticQueryStep.Complete(imported);
        }
        Observations?.RecordStaticQueryEvaluation(key);
        var context = ContextOf(key.Scope);
        if (key.Projection is StaticQueryProjection.OpenMemberAbsence or StaticQueryProjection.EmptyOpenNamespace or StaticQueryProjection.FallbackParticipation or StaticQueryProjection.PreservedOpenPresence
            && reader.Read(key).Kind == StaticFactKind.Yes)
            return StaticQueryStep.Complete(StaticFact.Yes);
        if (key.Kind == StaticQueryKind.TargetWalk && key.Projection == StaticQueryProjection.TargetCycle)
            return Cycle(context, key.Stratum, reader);
        if (key.Kind == StaticQueryKind.TargetWalk && key.Projection == StaticQueryProjection.ReceiverExpansionCycle)
            return ReceiverExpansionCycle(context, key.Stratum, reader);
        if (key.Kind == StaticQueryKind.TargetWalk && key.Projection == StaticQueryProjection.Default)
            return Structure(context, key.Stratum, reader);
        if (key.Kind == StaticQueryKind.TargetWalk && key.Projection == StaticQueryProjection.OpenStructure)
            return Structure(context, key.Stratum, reader, open: true);
        var fact = key.Kind switch
        {
            StaticQueryKind.OpenProviders when key.Projection is StaticQueryProjection.OpenMemberAbsence or StaticQueryProjection.EmptyOpenNamespace =>
                new NamespaceCertificate(this, reader).OpenAbsence(key.Scope, key.Node!, key.Name, key.Stratum),
            StaticQueryKind.MissSelection when key.Projection == StaticQueryProjection.FallbackParticipation =>
                new NamespaceCertificate(this, reader).FallbackParticipation(key.Scope, (Expr.DotCall)key.Node!),
            StaticQueryKind.Members => new StaticFact(StaticFactKind.Members, key.Scope, Data: context.Members),
            StaticQueryKind.Binding when key.Projection == StaticQueryProjection.OpenMatches => OpenMatches(context, key, reader),
            StaticQueryKind.Binding when key.Projection == StaticQueryProjection.OpenPresenceWitnesses => OpenPresenceWitnesses(context, key, reader),
            StaticQueryKind.Binding => Binding(context, key.Name!, key.Stratum, key.Projection, reader),
            StaticQueryKind.TargetWalk when key.Projection == StaticQueryProjection.MemberSelection => MemberSelection(key.Scope, (Expr.DotCall)key.Node!, key.Stratum, reader),
            StaticQueryKind.TargetWalk when key.Projection == StaticQueryProjection.RowTarget => RowTarget(context, key.Stratum, reader),
            StaticQueryKind.TargetWalk when key.Projection == StaticQueryProjection.OpenRowTarget => RowTarget(context, key.Stratum, reader, open: true),
            StaticQueryKind.TargetWalk when key.Projection == StaticQueryProjection.InvocationTarget => InvocationTarget(context, reader),
            StaticQueryKind.TargetWalk when key.Projection == StaticQueryProjection.ReceiverExpansionStep => ReceiverExpansionStep(context, key.Stratum, reader),
            StaticQueryKind.TargetWalk when key.Projection == StaticQueryProjection.Receiver => Receiver(key.Scope, key.Node!, key.Stratum, reader),
            StaticQueryKind.OpenProviders when key.Projection == StaticQueryProjection.ProviderRange => ProviderRange(context, key, reader),
            StaticQueryKind.OpenProviders when key.Projection == StaticQueryProjection.OpenMemberIndex => ClosedOpenMemberIndex(context, key.Stratum, reader),
            StaticQueryKind.OpenProviders when key.Projection == StaticQueryProjection.PreservedOpenPresence =>
                new NamespaceCertificate(this, reader).PreservedOpenPresence(key.Scope, key.Offset, key.Name!, key.Stratum),
            StaticQueryKind.OpenProviders => OpenProviders(context, key.Stratum, key.Node, reader),
            StaticQueryKind.MissSelection => MissSelection(key.Scope, (Expr.DotCall)key.Node!, reader),
            StaticQueryKind.IsInput when key.Projection == StaticQueryProjection.InputUse => Activation(context, key.Node!, reader),
            StaticQueryKind.IsInput when key.Projection == StaticQueryProjection.ActivationRange => ActivationRange(context, key, reader),
            StaticQueryKind.IsInput when key.Projection == StaticQueryProjection.InputRange => InputRange(context, key, reader),
            StaticQueryKind.IsInput when key.Projection == StaticQueryProjection.InputUses => InputUses(context, key, reader),
            StaticQueryKind.IsInput => IsInput(context, key.Name!, reader),
            StaticQueryKind.Inputs => Inputs(context, reader),
            _ => throw new InvalidOperationException($"Unsupported static query projection: {key}"),
        };
        return StaticQueryStep.Complete(fact);
    }

    private StaticFact Binding(BodyContext context, string name, StaticCycleCheck stratum, StaticQueryProjection projection,
        StaticQueryReader<StaticQueryKey, StaticFact> reader)
    {
        if (projection is StaticQueryProjection.OwnedBinding or StaticQueryProjection.OpenHeadBinding)
        {
            var phantomRoot = projection == StaticQueryProjection.OpenHeadBinding && ReferenceEquals(context.Key, Root);
            if (!phantomRoot && context.WrittenParameters.Contains(name)) return new(StaticFactKind.Parameter, context.Key);
            var property = context.Members.Declared(name);
            if (property is not null) return new(StaticFactKind.Declaration, context.Key, property);
            var input = !phantomRoot && context.Infers && context.Syntax.Uses.ContainsKey(name)
                ? reader.Read(StaticQueryKey.IsInput(context.Key, name)) : StaticFact.No;
            if (input.Kind == StaticFactKind.Yes) return new(StaticFactKind.Parameter, context.Key);
            var outer = context.Parent is { } parent
                ? reader.Read(Project(StaticQueryKind.Binding, parent, projection, name, stratum)) : StaticFact.Missing;
            return input.IsUnknown ? outer.Kind is StaticFactKind.Missing or StaticFactKind.Unknown ? StaticFact.Unknown : StaticFact.Bound : outer;
        }
        if (projection == StaticQueryProjection.OpenedBinding)
        {
            if (!context.HasOpens) return StaticFact.Missing;
            var empty = context.Body.Opens.Count == 0 ? StaticFact.Yes
                : reader.Read(Project(StaticQueryKind.OpenProviders, context.Key, StaticQueryProjection.EmptyOpenNamespace, stratum: stratum));
            var matches = empty.Kind == StaticFactKind.Yes ? EmptyMatches : empty.IsUnknown ? StaticFact.Unknown
                : reader.Read(StaticQueryKey.Project(StaticQueryKind.Binding, context.Key, StaticQueryProjection.OpenMatches,
                    name, stratum, length: context.Body.Opens.Count));
            if (matches.Kind == StaticFactKind.Ambiguous) return matches;
            if (matches.IsUnknown)
            {
                var outer = context.Parent is { } unknownParent
                    ? reader.Read(Project(StaticQueryKind.Binding, unknownParent, projection, name, stratum)) : StaticFact.Missing;
                return outer.Kind is StaticFactKind.Missing or StaticFactKind.Unknown ? StaticFact.Unknown : StaticFact.Bound;
            }
            var match = (StaticOpenMatch)matches.Data!;
            if (match.Pending) return StaticFact.Bound;
            if (match.Provider is { } provider)
                return new(StaticFactKind.Declaration, provider, ContextOf(provider).Members.Public(name));
            return context.Parent is { } parent
                ? reader.Read(Project(StaticQueryKind.Binding, parent, projection, name, stratum)) : StaticFact.Missing;
        }
        // This immutable local owner is already conclusive. Subscribing to its still-bottom
        // OwnedBinding key first would unnecessarily demand opens during the initial iteration.
        if (projection == StaticQueryProjection.Default)
        {
            if (context.WrittenParameters.Contains(name)) return new(StaticFactKind.Parameter, context.Key);
            if (context.Members.Declared(name) is { } local) return new(StaticFactKind.Declaration, context.Key, local);
        }
        StaticFact owned;
        if (projection == StaticQueryProjection.InferenceBinding)
        {
            // Availability for this candidate excludes its own inferred binding, not ancestor ownership.
            if (context.WrittenParameters.Contains(name)) return new(StaticFactKind.Parameter, context.Key);
            if (context.Members.Declared(name) is { } property) return new(StaticFactKind.Declaration, context.Key, property);
            owned = context.Parent is { } parent
                ? reader.Read(Project(StaticQueryKind.Binding, parent, StaticQueryProjection.OwnedBinding, name, stratum))
                : StaticFact.Missing;
        }
        else
            owned = reader.Read(Project(StaticQueryKind.Binding, context.Key, StaticQueryProjection.OwnedBinding, name, stratum));
        if (owned.Kind != StaticFactKind.Missing && !owned.IsUnknown) return owned;
        if (!context.HasOpens) return owned;
        var opened = reader.Read(Project(StaticQueryKind.Binding, context.Key, StaticQueryProjection.OpenedBinding, name, stratum));
        return owned.IsUnknown ? opened.Kind is StaticFactKind.Missing or StaticFactKind.Unknown ? StaticFact.Unknown : StaticFact.Bound : opened;
    }

    private StaticFact OpenProviders(BodyContext context, StaticCycleCheck stratum, Expr? target,
        StaticQueryReader<StaticQueryKey, StaticFact> reader)
    {
        if (target is not null)
        {
            var direct = DirectPath(context.Key, target, stratum, reader);
            if (direct.Kind != StaticFactKind.Structure) return direct.IsUnknown ? direct : new(StaticFactKind.Providers, Data: Array.Empty<StaticScopeKey>());
            var structure = reader.Read(Project(StaticQueryKind.TargetWalk, direct.Scope!, StaticQueryProjection.OpenStructure, stratum: stratum));
            if (structure.IsUnknown) return structure;
            var provider = structure.Kind == StaticFactKind.Refused ? direct.Scope : structure.Scope;
            if (provider is null) return new(StaticFactKind.Providers, Data: Array.Empty<StaticScopeKey>());
            // Eligibility diagnostics remain with open validation, as in the existing front end.
            return new(StaticFactKind.Providers, Data: new[] { provider });
        }
        var tree = reader.Read(StaticQueryKey.Project(StaticQueryKind.OpenProviders, context.Key, StaticQueryProjection.ProviderRange,
            stratum: stratum, length: context.Body.Opens.Count));
        if (tree.IsUnknown) return tree;
        using var storage = Resources.Temporary();
        var all = new List<StaticScopeKey>();
        var seen = new HashSet<StaticScopeKey>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<StaticProviderTree>();
        pending.Push((StaticProviderTree)tree.Data!);
        while (pending.TryPop(out var part))
        {
            Resources.Metadata(0, cancellationToken: _cancellationToken);
            if (part.Leaves is { } leaves)
                foreach (var provider in leaves)
                {
                    Resources.Metadata(0, cancellationToken: _cancellationToken);
                    var identity = Keys.ProviderScope(provider, Resources, _cancellationToken);
                    if (seen.Contains(identity)) continue;
                    storage.Add(3, _cancellationToken);
                    seen.Add(identity); all.Add(provider);
                }
            if (part.Right is { } right) pending.Push(right);
            if (part.Left is { } left) pending.Push(left);
        }
        Resources.Metadata(all.Count, cancellationToken: _cancellationToken);
        return new(StaticFactKind.Providers, Data: all.ToArray());
    }

    private StaticFact DirectPath(StaticScopeKey scope, Expr expression, StaticCycleCheck stratum,
        StaticQueryReader<StaticQueryKey, StaticFact> reader, bool runtimeParameter = false)
    {
        // Only an open's head bypasses opens; its public member steps use the selected structure.
        var steps = new Stack<string>();
        while (expression is Expr.DotCall { Args: null } edge) { steps.Push(edge.Name); expression = edge.Target; }
        StaticFact current;
        if (expression is Expr.AlgorithmExpr(var block)) current = new(StaticFactKind.Structure, BodyIn(Keys.Root, block));
        else if (expression is Expr.Resolve(var name))
        {
            var binding = reader.Read(Project(StaticQueryKind.Binding, scope, StaticQueryProjection.OpenHeadBinding, name, stratum));
            if (binding.HasUnknownSelection) return StaticFact.Unknown;
            if (runtimeParameter && binding.Kind == StaticFactKind.Parameter) return new(StaticFactKind.Runtime);
            if (binding.Kind != StaticFactKind.Declaration) return StaticFact.Missing;
            current = new(StaticFactKind.Structure, BodyIn(binding.Scope!, binding.Property!.Value));
        }
        else return StaticFact.Missing;
        while (steps.TryPop(out var memberName))
        {
            _cancellationToken.ThrowIfCancellationRequested();
            var structure = reader.Read(Project(StaticQueryKind.TargetWalk, current.Scope!, StaticQueryProjection.OpenStructure, stratum: stratum));
            if (structure.IsUnknown) return structure;
            var receiver = structure.Kind == StaticFactKind.Refused ? current.Scope : structure.Scope;
            if (receiver is null) return StaticFact.Missing;
            var members = reader.Read(StaticQueryKey.Members(receiver));
            if (members.IsUnknown) return members;
            var index = (StaticMembers)members.Data!;
            // Written open steps select public members; a transparent reference's own
            // target path selects declared members (Lean openNavigateWith, OD-C).
            if ((runtimeParameter ? index.Declared(memberName) : index.Public(memberName)) is not { } member)
                return StaticFact.Missing;
            current = new(StaticFactKind.Structure, BodyIn(receiver, member.Value));
        }
        return current;
    }

    private StaticFact RowTarget(BodyContext context, StaticCycleCheck stratum,
        StaticQueryReader<StaticQueryKey, StaticFact> reader, bool open = false)
    {
        if (context.Body is Algorithm.Alias { ResolvedTargetCell.IsPending: true } or Algorithm.Alias { ResolvedStructureCell.IsPending: true }) return StaticFact.Unknown;
        if (WrittenReferenceRow(context) is null) return open ? StaticFact.No : StaticFact.Missing;
        var inputs = NoInputs(context, reader);
        if (inputs.IsUnknown) return inputs;
        if (inputs.Kind == StaticFactKind.No) return open ? StaticFact.No : StaticFact.Missing;
        return WrittenRowTarget(context, stratum, reader, open);
    }

    private StaticFact WrittenRowTarget(BodyContext context, StaticCycleCheck stratum,
        StaticQueryReader<StaticQueryKey, StaticFact> reader, bool open = false)
    {
        if (WrittenReferenceRow(context) is not { } expression) return open ? StaticFact.No : StaticFact.Missing;
        if (HasPendingReceiverReturn(context, stratum, reader))
            return IsAlgorithmLink(expression) ? new(StaticFactKind.Runtime, context.Key) : open ? StaticFact.No : StaticFact.Missing;
        if (expression is Expr.Param) return new(StaticFactKind.Runtime, context.Key);
        if (open) return DirectPath(context.Key, expression, stratum, reader, runtimeParameter: true);
        if (expression is Expr.Resolve(var name))
        {
            var binding = reader.Read(StaticQueryKey.Binding(context.Key, name, stratum));
            if (binding.HasUnknownSelection) return StaticFact.Unknown;
            if (binding.Kind == StaticFactKind.Parameter) return new(StaticFactKind.Runtime, context.Key);
            return binding.Kind == StaticFactKind.Declaration
                ? new(StaticFactKind.Structure, BodyIn(binding.Scope!, binding.Property!.Value)) : StaticFact.Missing;
        }
        if (expression is not Expr.DotCall edge) return StaticFact.Missing;
        var selected = reader.Read(Project(StaticQueryKind.TargetWalk, context.Key, StaticQueryProjection.MemberSelection,
            stratum: stratum, node: edge));
        if (selected.IsUnknown || selected.Kind == StaticFactKind.Structure) return selected;
        if (edge.UsesDotAlgorithmIntrinsic()) return new(StaticFactKind.Runtime, context.Key);
        if (selected.Kind != StaticFactKind.Runtime) return StaticFact.Missing;
        // OD-B exempts a written parameter-rooted path only. A property whose VALUE
        // reads a parameter does not turn every path through that property into an alias.
        Expr head = edge.Target;
        while (head is Expr.DotCall { Args: null } parent) head = parent.Target;
        if (head is Expr.Param) return new(StaticFactKind.Runtime, context.Key);
        var root = head is Expr.Resolve resolve
            ? reader.Read(StaticQueryKey.Binding(context.Key, resolve.Name, stratum)) : StaticFact.Missing;
        return root.HasUnknownSelection ? StaticFact.Unknown
            : root.Kind == StaticFactKind.Parameter ? new(StaticFactKind.Runtime, context.Key) : StaticFact.Missing;
    }

    private static Expr? WrittenReferenceRow(BodyContext context)
        => context.Body is Algorithm.Alias alias ? alias.Target
            : context.AllowsReferenceFormation && context.Body is Algorithm.User { HasExplicitParameterList: false, ParameterPatterns.Count: 0 } body
                && AstHelpers.WrittenRows(body) is { Count: 1 } rows && rows[0] is Expr.Resolve or Expr.Param or Expr.DotCall { Args: null }
                    ? rows[0] : null;

    private StaticFact MemberSelection(StaticScopeKey scope, Expr.DotCall edge, StaticCycleCheck stratum,
        StaticQueryReader<StaticQueryKey, StaticFact> reader)
    {
        var receiver = reader.Read(Project(StaticQueryKind.TargetWalk, scope, StaticQueryProjection.Receiver, stratum: stratum, node: edge.Target));
        if (receiver.IsUnknown) return receiver;
        if (receiver.Kind != StaticFactKind.Structure)
            return new(receiver.Kind == StaticFactKind.Runtime ? StaticFactKind.Runtime : StaticFactKind.Missing);
        var members = reader.Read(StaticQueryKey.Members(receiver.Scope!));
        if (members.IsUnknown) return members;
        return ((StaticMembers)members.Data!).Declared(edge.Name) is { } member
            ? new(StaticFactKind.Structure, BodyIn(receiver.Scope!, member.Value)) : StaticFact.Missing;
    }

    private StaticQueryStep<StaticFact> Cycle(BodyContext context, StaticCycleCheck stratum,
        StaticQueryReader<StaticQueryKey, StaticFact> reader)
    {
        if (HasPendingReceiverReturn(context, stratum, reader)) return StaticQueryStep.Complete(StaticFact.No);
        var target = reader.Read(Project(StaticQueryKind.TargetWalk, context.Key, StaticQueryProjection.RowTarget, stratum: stratum));
        if (target.IsUnknown)
        {
            // Inferred inputs can prevent alias formation, but cannot create a target cycle. If the written
            // target is already acyclic, both eligibility refinements agree on No. This is an ordinary read:
            // an Unknown guard must never commit a Follow edge (IR-04).
            var possibleTarget = WrittenRowTarget(context, stratum, reader);
            if (possibleTarget.Kind is StaticFactKind.Missing or StaticFactKind.Runtime
                || possibleTarget.Kind == StaticFactKind.Structure
                    && reader.Read(Project(StaticQueryKind.TargetWalk, possibleTarget.Scope!,
                        StaticQueryProjection.TargetCycle, stratum: stratum)).Kind == StaticFactKind.No)
                return StaticQueryStep.Complete(StaticFact.No);
            return StaticQueryStep.Complete(target);
        }
        return target.Kind == StaticFactKind.Structure
            ? reader.Follow(Project(StaticQueryKind.TargetWalk, target.Scope!, StaticQueryProjection.TargetCycle, stratum: stratum))
            : StaticQueryStep.Complete(StaticFact.No);
    }

    /// <summary>
    /// The cycle of first transparent expansions. Each declared edge is the entire successor for this Boolean
    /// question. A pending member and a completed reference step remain distinct in the recipe: only the former
    /// proves a miss after a return. Bare prefixes still transport that calculation's identity.
    /// </summary>
    private StaticQueryStep<StaticFact> ReceiverExpansionCycle(BodyContext context, StaticCycleCheck stratum,
        StaticQueryReader<StaticQueryKey, StaticFact> reader)
    {
        var step = reader.Read(Project(StaticQueryKind.TargetWalk, context.Key, StaticQueryProjection.ReceiverExpansionStep, stratum: stratum));
        if (step.IsUnknown) return StaticQueryStep.Complete(step);
        return step.Kind is StaticFactKind.ExpansionPending or StaticFactKind.ExpansionFinal
            ? reader.Follow(Project(StaticQueryKind.TargetWalk, step.Scope!, StaticQueryProjection.ReceiverExpansionCycle, stratum: stratum))
            : StaticQueryStep.Complete(StaticFact.No);
    }

    private static bool IsExpandable(BodyContext context)
        => context.Body is Algorithm.Alias { IsReference: true } || context.AllowsReferenceFormation && !context.Body.IsModuleRoot && context.Body is Algorithm.User
            { IsWrittenBlock: false, HasExplicitParameterList: false, ParameterPatterns.Count: 0, Output.Count: 1, Properties.Count: 0, Opens.Count: 0 } body
            && body.Output[0] is Expr.Resolve or Expr.Param or Expr.DotCall { Args: null };

    private static bool IsAlgorithmLink(Expr expression)
        => expression is Expr.DotCall { Args: null } edge && edge.UsesDotAlgorithmIntrinsic();

    private bool HasPendingReceiverReturn(BodyContext context, StaticCycleCheck stratum,
        StaticQueryReader<StaticQueryKey, StaticFact> reader)
    {
        var cycle = reader.Read(Project(StaticQueryKind.TargetWalk, context.Key, StaticQueryProjection.ReceiverExpansionCycle, stratum: stratum));
        return cycle.Kind == StaticFactKind.Refused && reader.Read(Project(StaticQueryKind.TargetWalk, context.Key,
            StaticQueryProjection.ReceiverExpansionStep, stratum: stratum)).Kind == StaticFactKind.ExpansionPending;
    }

    private StaticFact ReceiverExpansionStep(BodyContext context, StaticCycleCheck stratum,
        StaticQueryReader<StaticQueryKey, StaticFact> reader)
    {
        if (!IsExpandable(context)) return StaticFact.No;
        var noInputs = NoInputs(context, reader);
        if (noInputs.IsUnknown) return noInputs;
        if (noInputs.Kind == StaticFactKind.No) return StaticFact.No;
        var head = WrittenReferenceRow(context)!;
        var members = new Stack<string>();
        while (head is Expr.DotCall { Args: null } edge) { members.Push(edge.Name); head = edge.Target; }
        StaticScopeKey? target = null;
        var writtenIdentity = false;
        if (head is Expr.AlgorithmExpr(var block)) { target = BodyIn(context.Key, block); writtenIdentity = true; }
        else if (head is Expr.Resolve(var name))
        {
            var binding = reader.Read(StaticQueryKey.Binding(context.Key, name, stratum));
            if (binding.HasUnknownSelection) return StaticFact.Unknown;
            if (binding.Kind == StaticFactKind.Declaration) target = BodyIn(binding.Scope!, binding.Property!.Value);
        }
        while (target is not null)
        {
            _cancellationToken.ThrowIfCancellationRequested();
            if (!writtenIdentity && IsExpandable(ContextOf(target)))
                return new(members.Count != 0 ? StaticFactKind.ExpansionPending : StaticFactKind.ExpansionFinal, target);
            if (!members.TryPop(out var memberName)) return StaticFact.No;
            var fact = reader.Read(StaticQueryKey.Members(target));
            if (fact.IsUnknown) return fact;
            if (((StaticMembers)fact.Data!).Declared(memberName) is not { } member) return StaticFact.No;
            target = BodyIn(target, member.Value);
            writtenIdentity = false;
        }
        return StaticFact.No;
    }

    private StaticQueryStep<StaticFact> Structure(BodyContext context, StaticCycleCheck stratum,
        StaticQueryReader<StaticQueryKey, StaticFact> reader, bool open = false)
    {
        // Written braces/declarations/opens are structural boundaries irrespective of the transported callable.
        if (context.Body is Algorithm.Alias { ResolvedTargetCell.IsPending: true } or Algorithm.Alias { ResolvedStructureCell.IsPending: true })
            return StaticQueryStep.Complete(StaticFact.Unknown);
        if (!IsExpandable(context))
            return StaticQueryStep.Complete(new StaticFact(StaticFactKind.Structure, context.Key));
        if (HasPendingReceiverReturn(context, stratum, reader))
            return StaticQueryStep.Complete(!open && IsAlgorithmLink(WrittenReferenceRow(context)!)
                ? new StaticFact(StaticFactKind.Runtime, context.Key) : new StaticFact(StaticFactKind.Structure, context.Key));
        if (stratum != StaticCycleCheck.None)
        {
            var lower = reader.Read(Project(StaticQueryKind.TargetWalk, context.Key, StaticQueryProjection.TargetCycle, stratum: StaticCycleCheck.None));
            var final = stratum == StaticCycleCheck.Formation
                ? reader.Read(Project(StaticQueryKind.TargetWalk, context.Key, StaticQueryProjection.TargetCycle, stratum: StaticCycleCheck.Lower)) : StaticFact.No;
            if (lower.Kind == StaticFactKind.Refused || final.Kind == StaticFactKind.Refused)
                return StaticQueryStep.Complete(new StaticFact(StaticFactKind.Structure, context.Key));
            if (lower.IsUnknown || final.IsUnknown) return StaticQueryStep.Complete(StaticFact.Unknown);
        }
        var target = reader.Read(Project(StaticQueryKind.TargetWalk, context.Key,
            open ? StaticQueryProjection.OpenRowTarget : StaticQueryProjection.RowTarget, stratum: stratum));
        if (target.IsUnknown) return StaticQueryStep.Complete(target);
        if (target.Kind == StaticFactKind.Structure)
            return reader.Follow(open ? Project(StaticQueryKind.TargetWalk, target.Scope!, StaticQueryProjection.OpenStructure, stratum: stratum)
                : StaticQueryKey.TargetWalk(target.Scope!, stratum));
        return StaticQueryStep.Complete(open && target.Kind == StaticFactKind.Missing ? StaticFact.Missing
            : !open && target.Kind == StaticFactKind.Runtime ? target : new StaticFact(StaticFactKind.Structure, context.Key));
    }

    private StaticFact Receiver(StaticScopeKey scope, Expr expression, StaticCycleCheck stratum,
        StaticQueryReader<StaticQueryKey, StaticFact> reader)
    {
        expression = expression.UnwrapGraceOperand();
        if (expression is Expr.AlgorithmExpr(var block)) return new(StaticFactKind.Structure, BodyIn(scope, block));
        if (expression is Expr.Param) return new(StaticFactKind.Runtime);
        if (expression is Expr.Resolve(var name))
        {
            var binding = reader.Read(StaticQueryKey.Binding(scope, name, stratum));
            if (binding.HasUnknownSelection) return StaticFact.Unknown;
            if (binding.Kind is StaticFactKind.Parameter or StaticFactKind.Missing) return new(StaticFactKind.Runtime);
            if (binding.Kind != StaticFactKind.Declaration) return new(StaticFactKind.Failure);
            var body = BodyIn(binding.Scope!, binding.Property!.Value);
            var structure = reader.Read(StaticQueryKey.TargetWalk(body, stratum));
            return structure.Kind == StaticFactKind.Refused ? new(StaticFactKind.Structure, body) : structure;
        }
        if (expression is not Expr.DotCall { Args: null } edge) return new(StaticFactKind.Absent);
        var receiver = reader.Read(Project(StaticQueryKind.TargetWalk, scope, StaticQueryProjection.Receiver, stratum: stratum, node: edge.Target));
        if (receiver.IsUnknown) return receiver;
        if (receiver.Kind == StaticFactKind.Failure) return receiver;
        if (receiver.Kind != StaticFactKind.Structure) return new(receiver.Kind == StaticFactKind.Runtime ? StaticFactKind.Runtime : StaticFactKind.Absent);
        var members = reader.Read(StaticQueryKey.Members(receiver.Scope!));
        if (members.IsUnknown) return members;
        var index = (StaticMembers)members.Data!;
        if (index.Declared(edge.Name) is not { } member)
            return new(index.IsBranchOnly(edge.Name) ? StaticFactKind.Failure : StaticFactKind.Absent);
        var target = BodyIn(receiver.Scope!, member.Value);
        var reached = reader.Read(StaticQueryKey.TargetWalk(target, stratum));
        return reached.Kind == StaticFactKind.Refused ? new(StaticFactKind.Structure, target) : reached;
    }

    private StaticFact MissSelection(StaticScopeKey scope, Expr.DotCall edge,
        StaticQueryReader<StaticQueryKey, StaticFact> reader)
    {
        var receiver = reader.Read(Project(StaticQueryKind.TargetWalk, scope, StaticQueryProjection.Receiver, node: edge.Target));
        if (receiver.IsUnknown) return receiver;
        if (receiver.Kind == StaticFactKind.Structure)
        {
            var members = reader.Read(StaticQueryKey.Members(receiver.Scope!));
            if (members.IsUnknown) return members;
            var index = (StaticMembers)members.Data!;
            return new(index.Declared(edge.Name) is not null || index.IsBranchOnly(edge.Name) ? StaticFactKind.Never : StaticFactKind.Always);
        }
        return new(receiver.Kind switch
        {
            StaticFactKind.Failure => StaticFactKind.Never,
            StaticFactKind.Runtime => StaticFactKind.May,
            _ => StaticFactKind.Always,
        });
    }
}
