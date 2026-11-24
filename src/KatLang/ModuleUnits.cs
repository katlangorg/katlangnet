using System.Diagnostics.CodeAnalysis;

namespace KatLang;

/// <summary>The front-end passes that elaborate a loaded module unit, in pipeline order.</summary>
internal enum ModuleUnitPass
{
    /// <summary>Name resolution (<see cref="ParameterDetector"/>): the import view to its detected declaration.</summary>
    Detection,

    /// <summary>Automatic parameter forwarding (<see cref="ImplicitArgumentResolver"/>): detected to resolved.</summary>
    Resolution,

    /// <summary>Exposure classification (<see cref="PropertyExposureResolver"/>): resolved to classified.</summary>
    Exposure,
}

/// <summary>
/// Q-32 I-U (decided 2026-10-06, with Q-31 H-P): ONE module declaration per canonical URL per compiled
/// program. Load elaboration splices one locationless import view per canonical URL (the loader's
/// per-document cache), and a loaded module is a hygienic unit rooted at the prelude, so its elaboration
/// is the same wherever it is reached: each front-end pass elaborates the view ONCE and every reach
/// receives that one declaration — one member binding, one callable identity, one open provider. A
/// program is elaborated in more than one OPERATION — the parse, then each deferred region's
/// materialization when evaluation selects it — so the units an error-free operation elaborated are
/// PUBLISHED here, and a later operation that splices the same view receives the same declaration
/// instead of re-elaborating it (a re-elaboration would mint new member properties, and with them new
/// bindings). An operation that reported an error publishes nothing: its result is never evaluated, and
/// a later operation elaborates — and reports — the module afresh. Never static: a registry belongs to
/// one loader, which belongs to one document.
/// </summary>
internal sealed class ModuleUnitRegistry
{
    // Materializations are serialized by the loader. Publish only after the entire unit succeeds, alongside its
    // module declarations, so another deferred occurrence sees newly completed modules with their exact identities.
    internal StaticStructureOperation.Continuation? StructuralContinuation { get; private set; }
    private readonly Dictionary<Algorithm, Algorithm>[] _published =
    [
        new(ReferenceEqualityComparer.Instance),
        new(ReferenceEqualityComparer.Instance),
        new(ReferenceEqualityComparer.Instance),
    ];

    /// <summary>
    /// The summaries of completed content the program's deferred materializations computed and published with their
    /// units (<see cref="CompletedProviderSummaries"/>): read and written inside the loader's materialization gate only.
    /// </summary>
    internal CompletedProviderSummaries CompletedProviders { get; } = new();

    /// <summary>
    /// The admission facts of the module views the program's deferred materializations completed and published with
    /// their units (<see cref="CompletedModuleViews"/>): read and written inside the loader's materialization gate only.
    /// </summary>
    internal CompletedModuleViews CompletedViews { get; } = new();

    /// <summary>A new operation's units, reading what earlier error-free operations published.</summary>
    internal ModuleUnits BeginOperation() => new(this);

    internal bool TryGet(ModuleUnitPass pass, Algorithm module, [NotNullWhen(true)] out Algorithm? elaborated)
        => _published[(int)pass].TryGetValue(module, out elaborated);

    /// <summary>
    /// Whether <paramref name="resolved"/> is the RESOLVED declaration of a module an earlier error-free operation
    /// carried through its whole pipeline: that operation's exposure received exactly this view, so every rule that
    /// runs between resolution and exposure (the collision, open-provider and output rules) judged the module there,
    /// and found nothing, or the operation would have published nothing. A later operation holds the same view at the
    /// same point of its own pipeline (it receives the unit pass by pass), which is where a rule that validates a
    /// module ONCE per program asks this.
    /// </summary>
    internal bool HasCompleted(Algorithm resolved) => _published[(int)ModuleUnitPass.Exposure].ContainsKey(resolved);

    /// <summary>
    /// <see cref="HasCompleted"/> asked by a rule that is about to walk <paramref name="resolved"/> and, on a yes, does
    /// not: the collision, open-provider and output rules of a deferred materialization, each of which judged the
    /// module in the operation that completed it. Counts the walks not made (<see cref="ValidationWalksSkipped"/>).
    /// </summary>
    internal bool SkipsValidationOf(Algorithm resolved)
    {
        if (!HasCompleted(resolved))
            return false;
        ValidationWalksSkipped++;
        return true;
    }

    /// <summary>
    /// Walks of a completed module that the rules of later operations did not make (<see cref="SkipsValidationOf"/>);
    /// test-observable, never a decision input. Written inside the loader's materialization gate only.
    /// </summary>
    internal long ValidationWalksSkipped { get; private set; }

    internal void Publish(Dictionary<Algorithm, Algorithm>[] units, StaticStructureOperation.Continuation? continuation)
    {
        for (var pass = 0; pass < units.Length; pass++)
        {
            foreach (var (module, elaborated) in units[pass])
                _published[pass].TryAdd(module, elaborated);
        }
        if (continuation is not null) StructuralContinuation = continuation;
    }
}

/// <summary>
/// The loaded module units of ONE front-end operation (see <see cref="ModuleUnitRegistry"/>): what each
/// pass elaborated, by the module declaration it received. Without a registry (a parse with no module
/// loader, a pass run on its own) the units live for the operation only.
/// </summary>
internal sealed class ModuleUnits(ModuleUnitRegistry? registry = null)
{
    private ModuleUnitRegistry? _registry = registry;
    internal ModuleUnitRegistry? Registry => _registry;
    internal void AttachRegistry(ModuleUnitRegistry shared)
    {
        if (_registry is not null && !ReferenceEquals(_registry, shared))
            throw new ArgumentException("One compilation cannot combine deferred regions from different module loaders.", nameof(shared));
        _registry = shared;
    }
    private readonly Dictionary<Algorithm, Algorithm>[] _units =
    [
        new(ReferenceEqualityComparer.Instance),
        new(ReferenceEqualityComparer.Instance),
        new(ReferenceEqualityComparer.Instance),
    ];

    /// <summary>The declaration <paramref name="pass"/> already elaborated <paramref name="module"/> to, in this operation or an earlier published one.</summary>
    internal bool TryGet(ModuleUnitPass pass, Algorithm module, [NotNullWhen(true)] out Algorithm? elaborated)
        => _units[(int)pass].TryGetValue(module, out elaborated)
            || (_registry is not null && _registry.TryGet(pass, module, out elaborated));

    internal void Add(ModuleUnitPass pass, Algorithm module, Algorithm elaborated)
        => _units[(int)pass].Add(module, elaborated);

    private CompletedProviderSummaries.Attempt? _completedProviders;

    /// <summary>
    /// This operation's view of the registry's completed provider summaries, created when a deferred materialization's
    /// exposure first asks for it (the one operation that reads or stages any); null without a registry. What it
    /// staged is published by <see cref="Publish"/> and otherwise dropped with the operation.
    /// </summary>
    internal CompletedProviderSummaries.Attempt? CompletedProviderAttempt
        => _completedProviders ??= _registry?.CompletedProviders.BeginAttempt();

    private CompletedModuleViews.Attempt? _completedViews;

    /// <summary>
    /// This operation's view of the registry's completed module views (<see cref="CompletedModuleViews"/>): created by a
    /// deferred materialization before its load (<see cref="BeginCompletedViews"/>), the one operation that reads or
    /// stages any; null otherwise. What it staged is published by <see cref="Publish"/> and otherwise dropped with the
    /// operation.
    /// </summary>
    internal CompletedModuleViews.Attempt? CompletedViews => _completedViews;

    /// <summary>Starts this operation's view of the completed module views (a deferred materialization; null without a registry).</summary>
    internal CompletedModuleViews.Attempt? BeginCompletedViews(FrontEndTraversalObservations? observations)
        => _completedViews ??= _registry?.CompletedViews.BeginAttempt(_registry, observations);

    /// <summary>
    /// Whether the resolution pass of this operation receives <paramref name="module"/> (a detected module declaration)
    /// RESOLVED BY AN EARLIER OPERATION of the program: the registry holds its resolved unit, so this operation's rewrite
    /// takes that declaration (<c>ImplicitArgumentResolver.ProcessModuleRoot</c>) and its members' signatures are final
    /// here, read from the earlier operation's published resolved views. Only an earlier operation counts: a module this
    /// operation resolves itself is analyzed and selected with its own bodies. The reference mode of the completed-view
    /// test seam (<see cref="CompletedModuleViews.Mode.Unshared"/>) answers no.
    /// </summary>
    internal bool ReceivesEarlierResolution(Algorithm module)
        => _registry is { } registry && registry.TryGet(ModuleUnitPass.Resolution, module, out _)
            && _completedViews?.Mode != CompletedModuleViews.Mode.Unshared;

    /// <summary>
    /// Publishes this operation's units, the completed provider summaries it staged and the facts of the module views
    /// it completed, to the program's registry: call only when the operation reported no error.
    /// </summary>
    internal void Publish(StaticStructureOperation.Continuation? continuation = null)
    {
        _registry?.Publish(_units, continuation);
        _completedProviders?.Publish();
        // After the units: a view's facts are kept only for a view the registry now holds as a completed unit.
        _completedViews?.Publish();
    }
}
