using System.Globalization;
using System.Text;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;

namespace KatLang.Tests;

/// <summary>
/// The zero-argument property cache entries ONE completed run PUBLISHED (KL-06), per binding name
/// (ordinal order) and in total — on success and on failure alike: a failed run keeps what its
/// successful owners published before the failure. A completed run that published nothing is an
/// EMPTY observation (<c>Total == 0</c>). Having NO observation is a different state, which this type
/// cannot hold: it is the absence of a value (<see cref="CachePublicationState.NotObserved"/>).
/// </summary>
public sealed record CachePublications(IReadOnlyDictionary<string, int> ByName, int Total)
{
    public int Published(string name) => ByName.TryGetValue(name, out var count) ? count : 0;

    public CachePublicationState State
        => Total == 0 ? CachePublicationState.CompletedEmpty : CachePublicationState.CompletedNonEmpty;
}

/// <summary>
/// The three publication states a differential corpus keeps apart for each of its programs. They
/// are never written alike: a program without an observation has NO cache guard (Lean's own
/// observation of a run without a comparable publication set is <c>none</c>, which no guard
/// expects), a completed run with an empty cache is guarded at <c>some 0</c>, and a completed run
/// with entries at <c>some n</c> plus one guard per name.
/// </summary>
public enum CachePublicationState
{
    /// <summary>No cache observation: the program is not observed, or it was never evaluated.</summary>
    NotObserved,

    /// <summary>A completed run that published no entry.</summary>
    CompletedEmpty,

    /// <summary>A completed run that published at least one entry.</summary>
    CompletedNonEmpty,
}

/// <summary>
/// The REVIEWED, hand-written cache expectation of one pilot case (KL-06 pilots on the source
/// corpora): the guarded binding names with their published counts. A name with count zero is
/// watched and must stay unpublished; the total is the sum. An expectation with no entry, or with
/// zero counts only, is a COMPLETED run that published nothing — never "no observation", which is
/// the absence of an expectation (<c>null</c>, no guard).
/// </summary>
public sealed class CachePublicationExpectation
{
    private CachePublicationExpectation(IReadOnlyList<(string Name, int Count)> entries) => Entries = entries;

    /// <summary>The guarded names with their published counts, in ordinal name order.</summary>
    public IReadOnlyList<(string Name, int Count)> Entries { get; }

    public int Total => Entries.Sum(entry => entry.Count);

    public CachePublicationState State
        => Total == 0 ? CachePublicationState.CompletedEmpty : CachePublicationState.CompletedNonEmpty;

    /// <summary>
    /// The state an optional expectation stands for: its absence is NO observation, never an empty cache.
    /// </summary>
    public static CachePublicationState StateOf(CachePublicationExpectation? expectation)
        => expectation?.State ?? CachePublicationState.NotObserved;

    /// <summary>A completed run that published nothing and watches no name.</summary>
    public static CachePublicationExpectation Nothing { get; } = Of();

    public static CachePublicationExpectation Of(params (string Name, int Count)[] entries)
    {
        foreach (var (name, count) in entries)
        {
            if (string.IsNullOrWhiteSpace(name) || name.Contains(' ') || name.Contains('='))
                throw new ArgumentException($"'{name}' is not a guarded property name.", nameof(entries));
            ArgumentOutOfRangeException.ThrowIfNegative(count);
        }

        if (entries.Select(entry => entry.Name).Distinct(StringComparer.Ordinal).Count() != entries.Length)
            throw new ArgumentException("A guarded property name is listed twice.", nameof(entries));
        return new(Array.AsReadOnly(entries.OrderBy(entry => entry.Name, StringComparer.Ordinal).ToArray()));
    }

    /// <summary>Parses <c>"A=1 B=0"</c> (space-separated <c>name=count</c>); the empty text is <see cref="Nothing"/>.</summary>
    public static CachePublicationExpectation Parse(string text)
        => Of(text.Split(' ', StringSplitOptions.RemoveEmptyEntries).Select(entry =>
        {
            var separator = entry.LastIndexOf('=');
            if (separator <= 0)
                throw new FormatException($"'{entry}' is not a name=count entry.");
            return (entry[..separator], int.Parse(entry[(separator + 1)..], NumberStyles.None, CultureInfo.InvariantCulture));
        }).ToArray());

    /// <summary>
    /// Whether <paramref name="observed"/> is EXACTLY this expectation: the same total, every listed
    /// name at its count, and no entry under a name the expectation does not list.
    /// </summary>
    public bool Matches(CachePublications observed)
        => observed.Total == Total
            && Entries.All(entry => observed.Published(entry.Name) == entry.Count)
            && observed.ByName.All(entry => Entries.Any(listed => listed.Name == entry.Key));

    public override string ToString()
        => Entries.Count == 0
            ? "nothing published"
            : string.Join(" ", Entries.Select(entry => $"{entry.Name}={entry.Count.ToString(CultureInfo.InvariantCulture)}"));

    internal static string Describe(CachePublications observed)
        => observed.ByName.Count == 0
            ? "nothing published"
            : string.Join(" ", observed.ByName.OrderBy(entry => entry.Key, StringComparer.Ordinal)
                .Select(entry => $"{entry.Key}={entry.Value.ToString(CultureInfo.InvariantCulture)}"));
}

/// <summary>
/// One case of a source corpus's KL-06 cache-publication pilot: its corpus id, the Lean definition
/// its guards name, the neutral observation the corpus already guards (unchanged by the pilot) and
/// the reviewed cache expectation.
/// </summary>
internal sealed record CachePilotCase(string CaseId, string LeanName, string Neutral, CachePublicationExpectation Expectation)
{
    /// <summary>A success with entries.</summary>
    internal const string SuccessWithEntries = "success-with-entries";

    /// <summary>A success that completed with an empty cache.</summary>
    internal const string SuccessWithEmptyCache = "success-with-empty-cache";

    /// <summary>A failure after a publication: the failed run keeps the published entries.</summary>
    internal const string FailureAfterPublication = "failure-after-publication";

    /// <summary>The pre-publication control: a failure that completed with an empty cache.</summary>
    internal const string FailureBeforePublication = "failure-before-publication";

    /// <summary>The four classes every pilot covers, in a fixed order.</summary>
    internal static readonly IReadOnlyList<string> Classes =
        [SuccessWithEntries, SuccessWithEmptyCache, FailureAfterPublication, FailureBeforePublication];

    internal bool IsSuccess => Neutral.StartsWith("ok ", StringComparison.Ordinal);

    internal string Class => (IsSuccess, Expectation.State) switch
    {
        (true, CachePublicationState.CompletedNonEmpty) => SuccessWithEntries,
        (true, _) => SuccessWithEmptyCache,
        (false, CachePublicationState.CompletedNonEmpty) => FailureAfterPublication,
        (false, _) => FailureBeforePublication,
    };

    /// <summary>
    /// The pilot line of a generated artifact's partition comment: the three publication states over
    /// its <paramref name="guardedPrograms"/> programs (entries, empty cache, no observation).
    /// <paramref name="memberTotalGuards"/> counts the pilot cases' transformation members, which are
    /// separate programs guarded on their published total only (SEM-2C; zero elsewhere).
    /// </summary>
    internal static string PartitionLine(IReadOnlyCollection<CachePilotCase> pilot, int guardedPrograms, int memberTotalGuards = 0)
    {
        static string Text(int count) => count.ToString(CultureInfo.InvariantCulture);
        var withEntries = pilot.Count(c => c.Expectation.State == CachePublicationState.CompletedNonEmpty);
        var members = memberTotalGuards == 0
            ? ""
            : $"\n  {Text(memberTotalGuards)} transformation members of those cases guard their published total;";
        return $"cache-publication pilot (KL-06): {Text(pilot.Count)} cases guard their published zero-argument cache entries\n" +
            $"  ({Text(withEntries)} with entries, {Text(pilot.Count - withEntries)} with an empty cache; " +
            $"{Text(pilot.Count(c => !c.IsSuccess))} of them fail);{members}\n" +
            $"  the other {Text(guardedPrograms - pilot.Count - memberTotalGuards)} programs have no cache observation, which is not an empty cache";
    }
}

/// <summary>
/// The cache-recording C# routes of one program graph: the observed counted run with the generic
/// strategies and with the optimizers enabled, each over a <see cref="PublicationRecorder"/>, and
/// the genuinely suspending async twin. The three must agree on what they published before a
/// harness may report it: the sync routes per binding name, the async route in total (and it must
/// never use the synchronous cache member), with every publication owner released.
/// Shared by the four generated differential corpora (KL-06 and its pilots): the host-parent
/// harness compares these results with the plain and counted routes, the source corpora with their
/// existing neutral observation. The planned-loop tables (<c>PlannedLoopPublicationTests</c>,
/// <c>PlannedLoopTempFamilyTests</c>) use it the same way.
/// <para>A PUBLICATION is counted when a zero-argument property first establishes a reusable
/// value in its owning invocation (KL-06 F01, owner decision Option A, November 21 2026). The
/// generic strategy stores it in the cache. A planned loop round stores the value of a planned
/// step property in its frame slot and reports that store to the recorder
/// (<see cref="IPlannedLoopPublicationObserver"/>), which counts it under the same binding name.
/// The async route pins the generic strategies, so only the optimized route has such stores; the
/// generic route must report none.</para>
/// </summary>
internal static class ZeroArgPublicationObserver
{
    internal sealed record Routes(
        EvalResult<Evaluator.CountedResult> Generic,
        EvalResult<Evaluator.CountedResult> Optimized,
        EvalResult<Evaluator.CountedResult> Asynchronous,
        CachePublications Publications)
    {
        /// <summary>
        /// The part of the OPTIMIZED route's publications that planned loop rounds established in
        /// their frame slots (KL-06 F01); the rest of that route's publications are cache stores.
        /// Empty for a program whose optimized run planned no step property.
        /// </summary>
        public required CachePublications OptimizedFrameSlots { get; init; }

        /// <summary>The binding name of every publication of the generic route, in publication order.</summary>
        public required IReadOnlyList<string> GenericOrder { get; init; }

        /// <summary>The binding name of every publication of the optimized route, in publication order.</summary>
        public required IReadOnlyList<string> OptimizedOrder { get; init; }

        /// <summary>The run budgets of the generic and the optimized route (their operational counters).</summary>
        public required (EvaluationBudget Generic, EvaluationBudget Optimized) Budgets { get; init; }

        /// <summary>The run budget of the suspending async route (its operational counters, the <c>tick()</c> count included).</summary>
        public required EvaluationBudget AsynchronousBudget { get; init; }
    }

    /// <summary>
    /// Runs the three cache-recording routes. <paramref name="corpus"/> names the corpus in the
    /// disagreement message (<c>"{corpus} route disagreement for '{caseId}': …"</c>).
    /// <paramref name="optimizedLoopDiagnostics"/> is attached to the OPTIMIZED route's run, so a
    /// test can read which loops that very run planned. <paramref name="recorders"/> makes the
    /// recorder of each synchronous route; only a NEGATIVE CONTROL passes one (a perturbed
    /// <see cref="PublicationRecorder"/>, to show that these requirements reject it). The async
    /// route always keeps the reference cache.
    /// </summary>
    internal static Routes Observe(
        string corpus,
        string caseId,
        Expr program,
        LoopOptimizationDiagnostics? optimizedLoopDiagnostics = null,
        Func<PublicationRecorder>? recorders = null)
    {
        var genericCache = recorders?.Invoke() ?? new PublicationRecorder();
        var (generic, genericBudget) = Evaluator.RunCountedObserved(program, enableOptimizations: false, zeroArgPropertyResultCache: genericCache);
        var optimizedCache = recorders?.Invoke() ?? new PublicationRecorder();
        var (optimized, optimizedBudget) = Evaluator.RunCountedObserved(
            program, enableOptimizations: true, zeroArgPropertyResultCache: optimizedCache, loopDiagnostics: optimizedLoopDiagnostics);
        var asyncCache = new SuspendingCache();
        var (asynchronous, asynchronousBudget) = Task.Run(async () =>
            await Evaluator.RunCountedObservedAsync(program, zeroArgPropertyResultCache: asyncCache)).GetAwaiter().GetResult();

        Require(corpus, caseId, genericCache.ActiveOwners == 0 && optimizedCache.ActiveOwners == 0 && asyncCache.ActiveOwners == 0,
            "a publication owner was left active");
        Require(corpus, caseId, asyncCache.SyncAccesses == 0, "the async route used the synchronous cache member");
        Require(corpus, caseId, genericCache.FrameSlotTotal == 0, "the generic route established a planned loop slot");
        Require(corpus, caseId, genericCache.ByName.Count == optimizedCache.ByName.Count
            && genericCache.ByName.All(entry => optimizedCache.ByName.TryGetValue(entry.Key, out var count) && count == entry.Value),
            "generic and optimized routes published different cache entries");
        Require(corpus, caseId, asyncCache.PublishedCount == genericCache.Total, "async and sync routes published a different number of entries");

        return new(generic, optimized, asynchronous, new CachePublications(genericCache.ByName, genericCache.Total))
        {
            OptimizedFrameSlots = new CachePublications(optimizedCache.FrameSlotsByName, optimizedCache.FrameSlotTotal),
            GenericOrder = genericCache.Order,
            OptimizedOrder = optimizedCache.Order,
            Budgets = (genericBudget, optimizedBudget),
            AsynchronousBudget = asynchronousBudget,
        };
    }

    /// <summary>
    /// The publications of a SOURCE-corpus program whose neutral observation the corpus already
    /// holds: the three cache-recording routes must each observe exactly <paramref name="expectedNeutral"/>
    /// (<c>ok raw=… n=…</c> or <c>err CATEGORY</c>), so the reported entries belong to the outcome
    /// the corpus guards. The existing result oracle is not replaced: it is required to hold on
    /// these routes too.
    /// </summary>
    internal static CachePublications ObserveSourceProgram(string corpus, string caseId, Algorithm root, string expectedNeutral)
        => ObserveSourceRoutes(corpus, caseId, root, expectedNeutral).Publications;

    /// <summary>
    /// <see cref="ObserveSourceProgram"/> with the three routes' results and the optimized route's
    /// frame-slot publications; <paramref name="optimizedLoopDiagnostics"/> and
    /// <paramref name="recorders"/> as for <see cref="Observe"/>.
    /// </summary>
    internal static Routes ObserveSourceRoutes(
        string corpus,
        string caseId,
        Algorithm root,
        string expectedNeutral,
        LoopOptimizationDiagnostics? optimizedLoopDiagnostics = null,
        Func<PublicationRecorder>? recorders = null)
    {
        var routes = Observe(corpus, caseId, new Expr.AlgorithmExpr(root), optimizedLoopDiagnostics, recorders);
        foreach (var (name, result) in new[] { ("generic", routes.Generic), ("optimized", routes.Optimized), ("async", routes.Asynchronous) })
        {
            var neutral = result.IsError
                ? $"err {DifferentialErrors.Observe(result.Error).Category}"
                : $"ok raw={SemanticExplorerHarness.Neutral(result.Value.Value)} n={result.Value.EmittedCount}";
            Require(corpus, caseId, neutral == expectedNeutral,
                $"the cache-recording {name} route observed '{neutral}', not the corpus observation '{expectedNeutral}'");
        }

        return routes;
    }

    /// <summary>
    /// The watched names of a case: the names its author asked to compare plus every name the run
    /// published, in ordinal order — so an entry under an unexpected name is guarded too.
    /// </summary>
    internal static List<string> GuardedNames(IEnumerable<string> watched, CachePublications publications)
        => watched.Concat(publications.ByName.Keys).Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToList();

    /// <summary>
    /// The KL-06 cache guards of one comparable case: one <c>cacheEntries</c> guard per guarded name
    /// (a name with no entry is guarded at zero) and ONE <c>cacheTotal</c> guard.
    /// </summary>
    internal static void AppendCacheGuards(StringBuilder builder, string leanName, IEnumerable<string> watched, CachePublications publications)
    {
        foreach (var name in GuardedNames(watched, publications))
        {
            builder.Append($"#guard cacheEntries {leanName} {LeanAstEncoder.QuoteString(name)} == " +
                $"some {publications.Published(name).ToString(CultureInfo.InvariantCulture)}\n");
        }

        builder.Append($"#guard cacheTotal {leanName} == some {publications.Total.ToString(CultureInfo.InvariantCulture)}\n");
    }

    /// <summary>
    /// A pilot case of a SOURCE corpus: observes the program on the three cache-recording routes
    /// (each must give <paramref name="expectedNeutral"/>), requires the published entries to be
    /// exactly the reviewed <paramref name="expectation"/>, and returns them. A disagreement
    /// throws, naming the corpus and the case: a pilot guard is never emitted from an expectation
    /// C# does not meet, and never from an observation nobody reviewed.
    /// </summary>
    internal static CachePublications ObservePilotCase(
        string corpus, string caseId, Algorithm root, string expectedNeutral, CachePublicationExpectation expectation)
    {
        var observed = ObserveSourceProgram(corpus, caseId, root, expectedNeutral);
        Require(corpus, caseId, expectation.Matches(observed),
            $"C# published [{CachePublicationExpectation.Describe(observed)}], not the reviewed cache expectation [{expectation}]");
        return observed;
    }

    /// <summary>
    /// The cache guards of a pilot case, written from its reviewed expectation (which
    /// <see cref="ObservePilotCase"/> has checked against C#): one guard per listed name, zero
    /// counts included, and ONE total guard.
    /// </summary>
    internal static void AppendCacheGuards(StringBuilder builder, string leanName, CachePublicationExpectation expectation)
    {
        foreach (var (name, count) in expectation.Entries)
        {
            builder.Append($"#guard cacheEntries {leanName} {LeanAstEncoder.QuoteString(name)} == " +
                $"some {count.ToString(CultureInfo.InvariantCulture)}\n");
        }

        builder.Append($"#guard cacheTotal {leanName} == some {expectation.Total.ToString(CultureInfo.InvariantCulture)}\n");
    }

    private static void Require(string corpus, string caseId, bool condition, string what)
    {
        if (!condition)
            throw new InvalidOperationException($"{corpus} route disagreement for '{caseId}': {what}.");
    }

    /// <summary>
    /// The run-scoped publication law itself (<see cref="ZeroArgPropertyPublications"/>, exactly as
    /// <see cref="RunScopedZeroArgPropertyResultCache"/> applies it), recording the binding name of
    /// every entry a request PUBLISHED. Observation only: it changes no request's outcome.
    /// <para>It is also the run's planned-loop publication observer (KL-06 F01): a planned round's
    /// first store of a step property's frame slot is that round's publication of the property. It
    /// is counted under the binding name exactly like a cache store and, separately, as a
    /// frame-slot publication, so a test can tell which storage established an entry.</para>
    /// <para>The three protected hooks exist for NEGATIVE CONTROLS only (a perturbed key, a reuse
    /// counted as a publication, a mis-reported frame slot; <c>PlannedLoopTempFamilyTests</c>):
    /// this class itself overrides none of them, so every corpus observes the law unchanged.</para>
    /// </summary>
    internal class PublicationRecorder : IZeroArgPropertyResultCache, IPlannedLoopPublicationObserver
    {
        private readonly ZeroArgPropertyPublications _publications = new();
        private readonly List<string> _order = [];
        internal SortedDictionary<string, int> ByName { get; } = new(StringComparer.Ordinal);
        internal int Total { get; private set; }
        internal SortedDictionary<string, int> FrameSlotsByName { get; } = new(StringComparer.Ordinal);
        internal int FrameSlotTotal { get; private set; }
        internal IReadOnlyList<string> Order => _order;
        internal int ActiveOwners => _publications.ActiveOwnerCount;

        /// <summary>The key a request is decided under: the run-scoped law's own key.</summary>
        protected virtual ZeroArgPropertyCacheKey KeyOf(ZeroArgPropertyExecution execution) => ZeroArgPropertyCacheKey.FromExecution(execution);

        /// <summary>Whether a read served from a published entry counts as another publication: never, under the law.</summary>
        protected virtual bool CountsReuse => false;

        // DECON-CACHE-2: this is the publication law itself, so its read provenance is the law's.
        public bool ReadObtainsPublishedValue(ZeroArgPropertyCacheKey key) => _publications.ReadObtainsPublishedValue(key);

        public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(ZeroArgPropertyExecution execution, Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        {
            var key = KeyOf(execution);
            if (_publications.TryGetPublished(key, out var cached))
            {
                Record(key, CountsReuse);
                return EvalResult<ZeroArgPropertyResult>.Ok(cached);
            }

            var result = _publications.EvaluateMiss(key, evaluate, out var published);
            Record(key, published);
            return result;
        }

        public EvalResult<ZeroArgPropertyResult> Invoke(ZeroArgPropertyExecution execution, Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        {
            var key = KeyOf(execution);
            var result = _publications.Invoke(key, evaluate, out var published);
            Record(key, published);
            return result;
        }

        private void Record(ZeroArgPropertyCacheKey key, bool published)
        {
            if (!published)
                return;
            var name = key.BindingIdentity is Property property
                ? property.Name
                : throw new InvalidOperationException("A published zero-argument entry must be keyed by its Property binding.");
            Count(name);
        }

        public virtual void PlannedLoopSlotPublished(Property binding) => RecordFrameSlot(binding.Name);

        /// <summary>Counts one planned frame-slot publication under <paramref name="name"/>.</summary>
        protected void RecordFrameSlot(string name)
        {
            FrameSlotsByName[name] = FrameSlotsByName.GetValueOrDefault(name) + 1;
            FrameSlotTotal++;
            Count(name);
        }

        private void Count(string name)
        {
            ByName[name] = ByName.GetValueOrDefault(name) + 1;
            Total++;
            _order.Add(name);
        }
    }

    /// <summary>The async reference cache, genuinely suspending before every access so the run takes the async twins.</summary>
    private sealed class SuspendingCache : IAsyncZeroArgPropertyResultCache
    {
        private readonly RunScopedAsyncZeroArgPropertyResultCache _inner = new();

        // DECON-CACHE-2: the inner cache publishes every read, so its publication provenance is this cache's.
        public bool ReadObtainsPublishedValue(ZeroArgPropertyCacheKey key) => _inner.ReadObtainsPublishedValue(key);

        internal int SyncAccesses { get; private set; }
        internal int PublishedCount => _inner.PublishedCount;
        internal int ActiveOwners => _inner.ActiveOwnerCount;

        public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(ZeroArgPropertyExecution execution, Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        {
            SyncAccesses++;
            return _inner.GetOrEvaluate(execution, evaluate);
        }

        public EvalResult<ZeroArgPropertyResult> Invoke(ZeroArgPropertyExecution execution, Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        {
            SyncAccesses++;
            return _inner.Invoke(execution, evaluate);
        }

        public async ValueTask<EvalResult<ZeroArgPropertyResult>> GetOrEvaluateAsync(ZeroArgPropertyExecution execution, Func<ValueTask<EvalResult<ZeroArgPropertyResult>>> evaluateAsync)
        {
            await Task.Yield();
            return await _inner.GetOrEvaluateAsync(execution, evaluateAsync);
        }

        public async ValueTask<EvalResult<ZeroArgPropertyResult>> InvokeAsync(ZeroArgPropertyExecution execution, Func<ValueTask<EvalResult<ZeroArgPropertyResult>>> evaluateAsync)
        {
            await Task.Yield();
            return await _inner.InvokeAsync(execution, evaluateAsync);
        }
    }
}
