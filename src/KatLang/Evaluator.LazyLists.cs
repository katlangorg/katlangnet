using System.Numerics;
using System.Runtime.CompilerServices;
using KatLang.Evaluation;

namespace KatLang;

/// <summary>
/// LISTS EVALUATED ON DEMAND (lazy collections, issue #204, November 2026). Part of the
/// <see cref="Evaluator"/> partial class. Lean: § "Lazy collections" of <c>KatLang.lean</c>
/// (<c>Result.deferred</c>, <c>Result.pendingList</c>, <c>LazyList</c>, <c>forcePosition</c>,
/// <c>forceLevel</c>, <c>materializeVia</c>).
/// </summary>
public static partial class Evaluator
{
    /// <summary>
    /// The frame of one <c>map</c> transform: the frame the eager loop put around every item's
    /// callback call. Lean: <c>evalMapCounted</c>.
    /// </summary>
    private const string MapTransformContext =
        "while evaluating map transform (map passes each iterated collection item as collected; a collecting parameter collects supplied values as one exact list and nested sequence and list values stay intact)";

    /// <summary>
    /// THE POSITIONS OF ONE LIST INSTANCE EVALUATED ON DEMAND: what a
    /// <see cref="Result.ListValue"/> holds instead of concrete items (<see cref="Result.ListValue.Lazy"/>).
    /// A position is found before it is read, and reading it is one VALUE demand of its slot:
    ///
    /// <list type="bullet">
    ///   <item><b>Known cardinality</b> — a list literal, a <c>map</c> or a <c>take</c> over known
    ///   positions: every position exists from the start (<see cref="IsExhausted"/>), so
    ///   <c>count</c>, bounds checks and pattern cardinality read no element.</item>
    ///   <item><b>Position discovery</b> — a <c>filter</c> and every stage over one: positions are
    ///   found in source order by <see cref="Discover"/>, which stops at the position requested,
    ///   resumes after the candidates already inspected and never inspects one twice.</item>
    ///   <item><b>Indexed value demand</b> — <see cref="Slot"/> is the position's value, or the
    ///   cell whose VALUE it is (<see cref="ForcePosition"/>): memoized, shared by every reader of
    ///   this instance, an ordinary failure kept like any need cell's.</item>
    /// </list>
    ///
    /// <para>Sharing is per position per INSTANCE: two reads of one list share its cells, two
    /// lists built by two evaluations share nothing. The concrete forms a consumer builds — one
    /// level (<see cref="ForceLevel"/>) and the whole value (<see cref="MaterializeValue"/>) — are
    /// remembered here, so each is built at most once.</para>
    ///
    /// <para>Lean: a <c>listValue</c> whose items are <c>deferred</c> cells (known cardinality), or
    /// a <c>pendingList</c> of candidates with verdict cells (discovery).</para>
    /// </summary>
    internal abstract class LazyList(bool reserved = false)
    {
        /// <summary>"Every position" as a <see cref="Discover"/> request.</summary>
        internal const int Everything = int.MaxValue;

        private Result.ListValue? _level;
        private Result.ListValue? _materialized;
        private bool _reserved = reserved;
        private StageSite? _site;

        /// <summary>
        /// How many whole-value reads this list's creation was nested in
        /// (<see cref="EvaluationBudget.TryEnterNestedRead"/>): 0 for a list built by evaluating.
        /// </summary>
        internal int Generation { get; set; }

        /// <summary>
        /// Whether this list is a callback STAGE whose steps report under the call that built it
        /// (<see cref="StageSite"/>): a <c>map</c> or a <c>filter</c>.
        /// </summary>
        internal virtual bool IsStage => false;

        /// <summary>The written call that built this stage, once its dispatch has returned it.</summary>
        internal StageSite? Site => Volatile.Read(ref _site);

        /// <summary>
        /// Records the frame of the written call that built this stage: the FIRST call dispatch
        /// that returns the fresh list is the one that built it.
        /// </summary>
        internal void NoteSiteFrame(CallDiagnosticName? function, Expr.DotCall? dot, EvalCtx ctx)
        {
            if (Volatile.Read(ref _site) is null)
                Interlocked.CompareExchange(ref _site, new StageSite(function, dot, ctx), null);
        }

        /// <summary>
        /// A step's failure as its stage reports it: positioned at the stage's written call when
        /// it has no position of its own, under that call's frame — exactly the report the call
        /// gave when it evaluated its callback itself. A failure that ends the run is positioned
        /// but gains no frame, as through every call frame.
        /// </summary>
        internal EvalError AtSite(EvalError error)
            => Site is { } site ? site.Frame(error) : error;

        /// <summary>
        /// THE LIST WHOSE DISCOVERY FINDS THIS LIST'S POSITIONS: the list itself, or — for a
        /// <c>map</c> or <c>take</c> stage, whose positions are its source's — the nearest list
        /// below it that finds its own. A stage holds it directly, so asking a pipeline of any
        /// height how many positions it has is one call, never one call per stacked stage (a
        /// loop that maps its list every round stacks one stage per round).
        /// </summary>
        internal virtual LazyList Root => this;

        /// <summary>How many of <see cref="Root"/>'s positions this list has at most: the tightest <c>take</c> on the way down.</summary>
        internal virtual int Limit => int.MaxValue;

        /// <summary>The number of positions found so far. Never decreases.</summary>
        internal abstract int Discovered { get; }

        /// <summary>
        /// Whether every position has been found: <see cref="Discovered"/> is then the list's
        /// cardinality. Read it BEFORE <see cref="Discovered"/> when both are needed.
        /// </summary>
        internal abstract bool IsExhausted { get; }

        /// <summary>
        /// Finds positions, in order, until <paramref name="wanted"/> are known or the list is
        /// exhausted. Returns the failure that stopped discovery: the candidate that raised it
        /// keeps it, so every later discovery reaching that candidate reports it again, while the
        /// positions found before it stay readable.
        /// </summary>
        internal abstract ValueTask<EvalError?> Discover(int wanted, bool asynchronous);

        /// <summary>
        /// The slot of a found position: a <see cref="Result"/> that is the position's value
        /// already, or the <see cref="NeedCell"/> whose VALUE it is.
        /// </summary>
        internal abstract object Slot(int index);

        /// <summary>
        /// Whether the list's positions are found by discovery: a <c>filter</c> and every stage
        /// over one. Lean: a <c>pendingList</c> (it stays one however far it has been discovered).
        /// </summary>
        internal virtual bool IsPending => false;

        /// <summary>
        /// The value position <paramref name="index"/> holds without any demand, or <c>null</c>
        /// when the position is deferred. Reads and allocates nothing: what a diagnostic shows.
        /// </summary>
        internal abstract Result? ValueAt(int index);

        /// <summary>The one-level concrete form, once a consumer has built it.</summary>
        internal Result.ListValue? Level => Volatile.Read(ref _level) ?? Volatile.Read(ref _materialized);

        /// <summary>The whole concrete form, once a consumer has built it.</summary>
        internal Result.ListValue? Materialized => Volatile.Read(ref _materialized);

        internal Result.ListValue PublishLevel(Result.ListValue level)
            => Interlocked.CompareExchange(ref _level, level, null) ?? level;

        internal Result.ListValue PublishMaterialized(Result.ListValue whole)
            => Interlocked.CompareExchange(ref _materialized, whole, null) ?? whole;

        /// <summary>
        /// Reserves this list's positions once. A concurrent reader can reuse the reservation
        /// only after the budget admits it.
        /// </summary>
        internal EvalError? EnsureReservation(EvaluationBudget budget, int count)
        {
            lock (this)
            {
                if (_reserved) return budget.CheckContinuation();
                if (budget.TryReserveCollection(count) is { } refused) return refused;
                _reserved = true;
                return null;
            }
        }

        /// <summary>
        /// Lets go of the context of the call that built this stage, once the stage runs no
        /// further step: no failure of its own remains to be framed, so the site keeps only its
        /// span. A stage released before any dispatch recorded its site gets a detached one, so no
        /// later dispatch installs a site holding that dispatch's context.
        /// </summary>
        private protected void ReleaseSite()
        {
            if (Volatile.Read(ref _site) is { } site)
            {
                site.Release();
                return;
            }

            var detached = new StageSite(null, null, default);
            detached.Release();
            if (Interlocked.CompareExchange(ref _site, detached, null) is { } installed)
                installed.Release();
        }
    }

    /// <summary>
    /// THE WRITTEN CALL THAT BUILT A STAGE (<c>map</c> / <c>filter</c>). The stage's steps run
    /// later, on demand, under whichever consumer reads a position — but a step's failure is the
    /// stage's: it keeps the frame and the position the call gave it when the call evaluated its
    /// callback itself (<c>while evaluating call to filter: while evaluating filter predicate
    /// for item 0: …</c>), followed by the frames of the consumer that demanded it. The frame is
    /// rendered only when a step fails. C#-only diagnostics: the Lean model's errors carry no
    /// written-call frames.
    /// </summary>
    internal sealed class StageSite(CallDiagnosticName? function, Expr.DotCall? dot, EvalCtx ctx)
    {
        private SourceSpan? _span;
        private bool _hasSpan;
        // The building call's context: the call's activation and parameter cells, which hold the
        // lists the stage was built from. Released with the stage's own computation state.
        private EvalCtx _ctx = ctx;
        private bool _released;

        /// <summary>The written call's span, recorded by the dispatch that positions the call (once).</summary>
        internal void NoteSpan(SourceSpan? span)
        {
            if (_hasSpan) return;
            _span = span;
            _hasSpan = true;
        }

        /// <summary>
        /// Drops the building call's context once its stage runs no further step
        /// (<see cref="LazyList.ReleaseSite"/>). Only a failure that ends the run can be framed
        /// afterwards (a completed scan's reservation), and that keeps no frame anyway.
        /// </summary>
        internal void Release()
        {
            _released = true;
            _ctx = default;
            function = null;
            dot = null;
        }

        internal EvalError Frame(EvalError error)
        {
            if (error.IsTerminalForRun)
                return AtSpanIfMissing(error, _span);
            System.Diagnostics.Debug.Assert(!_released, "A released stage ran a step whose failure needs its call frame.");
            if (dot is not null)
                error = new EvalError.WithContext(CtxDotCall(dot.Target, dot.Name, _ctx), error) { Span = error.Span };
            else if (function is { IsDiagnosticallyTransparent: false } name)
                error = new EvalError.WithContext(CtxCall(name, _ctx), error) { Span = error.Span };
            return AtSpanIfMissing(error, _span);
        }
    }

    /// <summary>
    /// The stage a call dispatch has just returned, when it still has no recorded site of the
    /// kind the dispatch records: <c>null</c> for every other result.
    /// </summary>
    private static LazyList? FreshStage<T>(EvalResult<T> result)
    {
        if (!result.IsOk) return null;
        // Both spellings of a dispatch carry the stage: the counted result and its plain value
        // projection. The type tests are resolved per instantiation; nothing is boxed.
        var value = result.Value;
        Result? produced = typeof(T) == typeof(CountedResult)
            ? Unsafe.As<T, CountedResult>(ref value).Value
            : typeof(T) == typeof(Result) ? Unsafe.As<T, Result>(ref value) : null;
        return produced is Result.ListValue { Lazy: { IsStage: true } stage } ? stage : null;
    }

    /// <summary>The positions of a concrete collection view: every item is a value already.</summary>
    private sealed class ConcreteSlots(IReadOnlyList<Result> items) : LazyList
    {
        internal override int Discovered => items.Count;
        internal override bool IsExhausted => true;
        internal override ValueTask<EvalError?> Discover(int wanted, bool asynchronous) => default;
        internal override object Slot(int index) => items[index];
        internal override Result? ValueAt(int index) => items[index];
    }

    /// <summary>
    /// The positions of a LIST LITERAL: one slot per written element, a value for a constant or an
    /// opened spread item and a deferred cell for every other element. Lean:
    /// <c>evalListLiteralCounted</c>.
    /// </summary>
    private sealed class KnownSlots(object[] slots) : LazyList(reserved: true)
    {
        internal override int Discovered => slots.Length;
        internal override bool IsExhausted => true;
        internal override ValueTask<EvalError?> Discover(int wanted, bool asynchronous) => default;
        internal override object Slot(int index) => slots[index];
        internal override Result? ValueAt(int index) => slots[index] as Result;
    }

    /// <summary>
    /// A <c>map</c> STAGE: position <c>i</c> is the mapper applied to the source's position
    /// <c>i</c>. Its positions are exactly the source's, so finding them scans what the source
    /// scans and invokes no mapper. A position's cell is created when it is first asked for and
    /// kept: its one VALUE computation reads the source position, THEN projects the mapper (on the
    /// first position read — the mapper's own cell keeps the projection), then makes the ordinary
    /// callback call. Lean: <c>LazyList.mapItems</c> / <c>mapCandidates</c> and the
    /// <c>mappedBuiltin</c> step.
    ///
    /// <para>OBSOLETE OWNERSHIP IS RELEASED (C#-only): once every position is found and every
    /// position's computation has ended — with a value or with the failure its cell keeps — the
    /// stage runs no further step, so it lets go of what only a step reads: its source, the root
    /// whose discovery found its positions, the mapper and the environment of the call that built
    /// it (<see cref="ReleaseIfResolved"/>). It keeps its cells, so every reader still shares each
    /// position's one outcome. A loop that maps its list every round and reads the new list keeps
    /// only the last round's stage, not every round's.</para>
    /// </summary>
    private sealed class MappedList : LazyList
    {
        private const int PageSize = 32;

        // What a step reads, released once the stage runs no further step. The root is null
        // afterwards: the stage is then its own root, with _count positions. The limit stays,
        // so a reader that still holds the root pairs it with the stage's own limit.
        private LazyList? _source;
        private LazyList? _root;
        private readonly int _limit;
        private IReadOnlyList<SequenceBuiltinSuffixArgDescriptor>? _descriptors;
        private IReadOnlyList<PreparedSequenceBuiltinSuffixArg>? _controls;
        private EvalCtx _ctx;
        private ValEnv? _values;

        private readonly EvaluationBudget _budget;
        private readonly bool _pending;
        private NeedCell?[]? _firstPage;
        private Dictionary<int, NeedCell?[]>? _otherPages;
        // How many positions' computations have ended; the cardinality once the stage is released.
        private int _resolved;
        private int _count;

        internal MappedList(
            LazyList source,
            IReadOnlyList<SequenceBuiltinSuffixArgDescriptor> descriptors,
            IReadOnlyList<PreparedSequenceBuiltinSuffixArg> controls,
            EvalCtx ctx,
            ValEnv values)
        {
            _source = source;
            _root = source.Root;
            _limit = source.Limit;
            _descriptors = descriptors;
            _controls = controls;
            _ctx = ctx;
            _values = values;
            _budget = ctx.Budget;
            _pending = source.IsPending;
        }

        internal override LazyList Root => Volatile.Read(ref _root) ?? this;
        // Constructors can capture Root just before another reader releases this stage. The
        // same limit bounds both the old root and this stage's final positions.
        internal override int Limit => _limit;
        internal override int Discovered => Volatile.Read(ref _root) is { } root ? Math.Min(root.Discovered, _limit) : _count;

        internal override bool IsExhausted => CheckExhausted();

        internal override bool IsPending => _pending;
        internal override bool IsStage => true;
        internal override Result? ValueAt(int index) => null;

        internal override ValueTask<EvalError?> Discover(int wanted, bool asynchronous)
        {
            // A released stage has found every position: what is left of a discovery request is
            // the run's continuation check its root's scan would have made first.
            if (Volatile.Read(ref _root) is not { } root)
                return _pending ? new(_budget.CheckContinuation()) : default;
            var discovery = root.Discover(Math.Min(wanted, _limit), asynchronous);
            if (!discovery.IsCompletedSuccessfully) return AwaitDiscovery(discovery);
            var failure = discovery.Result;
            if (failure is null) CheckExhausted();
            return new(failure);
        }

        private async ValueTask<EvalError?> AwaitDiscovery(ValueTask<EvalError?> discovery)
        {
            var failure = await discovery.ConfigureAwait(false);
            if (failure is null) CheckExhausted();
            return failure;
        }

        /// <summary>
        /// Whether every position has been found — the root is exhausted or the stage's limit is
        /// reached — releasing the stage when every position's step has ended as well
        /// (<see cref="ReleaseIfResolved"/>). Every reader that learns the stage is complete
        /// asks this, as do the end of each step and the end of each discovery.
        /// </summary>
        private bool CheckExhausted()
        {
            if (Volatile.Read(ref _root) is not { } root) return true;
            // Exhaustion is read BEFORE the count: once exhausted, the count is final.
            var rootExhausted = root.IsExhausted;
            var discovered = root.Discovered;
            if (!rootExhausted && discovered < _limit) return false;
            ReleaseIfResolved(Math.Min(discovered, _limit));
            return true;
        }

        /// <summary>
        /// The slot of the source position that position <paramref name="index"/> reads, or
        /// <c>null</c> once the stage is released (every position's computation has ended).
        /// </summary>
        internal object? SourceSlot(int index) => Volatile.Read(ref _source)?.Slot(index);

        internal override object Slot(int index)
        {
            // A reader can jump to the last index of a known list, or advance through a
            // filter one match at a time. Allocate storage only for pages actually read.
            lock (this)
            {
                if (index < PageSize)
                {
                    _firstPage ??= new NeedCell?[FirstPageLength()];
                    return _firstPage[index] ??= NewCell(index);
                }

                var pageIndex = index / PageSize;
                _otherPages ??= [];
                if (!_otherPages.TryGetValue(pageIndex, out var page))
                    _otherPages.Add(pageIndex, page = new NeedCell?[PageSize]);
                return page[index % PageSize] ??= NewCell(index);
            }
        }

        // The first page holds every position of a list known to be shorter than a page. Read
        // from the root, not through IsExhausted: no release is attempted while a cell is made.
        private int FirstPageLength()
        {
            if (Volatile.Read(ref _root) is not { } root) return Math.Min(_count, PageSize);
            var exhausted = root.IsExhausted || root.Discovered >= _limit;
            return exhausted ? Math.Min(Math.Min(root.Discovered, _limit), PageSize) : PageSize;
        }

        // The cell's computation is one object: it names the stage and the position, which is
        // how a read finds the stage below (ReadStagePosition).
        private NeedCell NewCell(int index)
            => new(new MappedPosition(this, index), _budget, _budget.CancellationToken);

        internal async ValueTask<EvalResult<CountedResult>> EvaluateAtSite(int index, bool asynchronous)
        {
            var mapped = await Evaluate(index, asynchronous).ConfigureAwait(false);
            var result = mapped.IsError ? AtSite(mapped.Error) : mapped;
            // This position's step has ended; its cell keeps the outcome.
            Interlocked.Increment(ref _resolved);
            CheckExhausted();
            return result;
        }

        /// <summary>
        /// Releases what only a step reads once the stage runs no further step: all
        /// <paramref name="count"/> positions are found and every position's computation has
        /// ended. Each computation ends at most once and only for a position found already, so
        /// the count of ended computations reaching the cardinality means every one has ended.
        /// Afterwards the stage is its own root, and no step is left to read its source, root,
        /// mapper or environment.
        /// </summary>
        private void ReleaseIfResolved(int count)
        {
            if (Volatile.Read(ref _resolved) < count) return;
            lock (this)
            {
                if (_root is null) return;
                _count = count;
                // The cardinality is published before the root is dropped (see Discovered).
                Volatile.Write(ref _root, null);
                Volatile.Write(ref _source, null);
                _descriptors = null;
                _controls = null;
                _values = null;
                _ctx = default;
            }

            ReleaseSite();
        }

        private async ValueTask<EvalResult<CountedResult>> Evaluate(int index, bool asynchronous)
        {
            // TWIN-ONLY (the synchronous run never hops): see StackHop.
            if (asynchronous && StackHop.HostStackIsLow()) await new StackHop();
            // A step runs before its stage is released, never after (ReleaseIfResolved): the
            // fields it reads are all still held.
            var item = await ReadStagePosition(_source!.Slot(index), asynchronous).ConfigureAwait(false);
            if (item.IsError) return item.Error;
            var mapper = asynchronous
                ? await ExpectPreparedAlgorithmSuffixArgAsync(BuiltinId.@map, _descriptors!, _controls!, 0, _ctx).ConfigureAwait(false)
                : ExpectPreparedAlgorithmSuffixArg(BuiltinId.@map, _descriptors!, _controls!, 0);
            if (mapper.IsError) return mapper.Error;

            var supplied = new CountedResult(item.Value, item.Value.ValueCount());
            var mapped = WithCtx(
                MapTransformContext,
                asynchronous
                    ? await EvalSequenceCallbackCallCountedAsync(mapper.Value, supplied, _ctx, _values!, MapTransformFrameName).ConfigureAwait(false)
                    : EvalSequenceCallbackCallCounted(mapper.Value, supplied, _ctx, _values!, MapTransformFrameName));
            // The transform's ordinary call result is ONE element (HO-03).
            return mapped.IsError
                ? mapped.Error
                : EvalResult<CountedResult>.Ok(new CountedResult(mapped.Value.Value, mapped.Value.Value.ValueCount()));
        }
    }

    /// <summary>
    /// ONE POSITION OF A <c>map</c> STAGE: the position cell's VALUE computation
    /// (<see cref="NeedComputation"/>, <see cref="NeedCell.ValueComputation"/>).
    /// </summary>
    private sealed class MappedPosition(MappedList stage, int index) : NeedComputation
    {
        /// <summary>
        /// The slot of the source position this position reads first; <c>null</c> once its stage
        /// is released (every position's computation, this one's included, has ended).
        /// </summary>
        internal object? SourceSlot() => stage.SourceSlot(index);

        internal override EvalResult<CountedResult> Evaluate()
            => stage.EvaluateAtSite(index, asynchronous: false).GetAwaiter().GetResult();

        internal override ValueTask<EvalResult<CountedResult>> EvaluateAsync()
            => stage.EvaluateAtSite(index, asynchronous: true);
    }

    // How many unread map stages stacked below a position are read by ordinary nesting before
    // the read turns to the deepest-first order of ReadStagePosition.
    private const int NestedStageReads = 16;

    /// <summary>
    /// THE SOURCE POSITION A STAGE'S STEP READS, without one native call chain per stacked stage.
    /// A pipeline built at run time — a loop that maps its own list every round — stacks one
    /// <c>map</c> stage per round, and the top position's step reads the position below it, whose
    /// step reads the one below that. When more than <see cref="NestedStageReads"/> unread
    /// positions are stacked this way, they are read DEEPEST FIRST: each then finds its own
    /// source position computed already. That is the order the nested reads take, so every
    /// effect, every value and every failure is the same — a position that fails keeps its
    /// failure in its cell and the stage above reports it under its own frame, as when it read
    /// the position itself — and only the native stack differs. A failure that ends the run ends
    /// the read at once.
    /// </summary>
    private static async ValueTask<EvalResult<Result>> ReadStagePosition(object slot, bool asynchronous)
    {
        if (slot is Result value) return EvalResult<Result>.Ok(value);
        var cell = (NeedCell)slot;

        var depth = 0;
        for (var probe = cell; depth < NestedStageReads && UnreadStagePositionBelow(probe) is { } below; probe = below)
            depth++;

        if (depth == NestedStageReads)
        {
            var stacked = new List<NeedCell>();
            for (var below = UnreadStagePositionBelow(cell); below is not null; below = UnreadStagePositionBelow(below))
                stacked.Add(below);

            for (var at = stacked.Count - 1; at >= 0; at--)
            {
                var read = await DemandCell(stacked[at], asynchronous).ConfigureAwait(false);
                if (read.IsError && read.Error.IsTerminalForRun) return read.Error;
            }
        }

        return await ForceCell(cell, asynchronous).ConfigureAwait(false);
    }

    // The unread cell of the source position that an unread `map` position reads first.
    private static NeedCell? UnreadStagePositionBelow(NeedCell cell)
        => cell.IsValueUnstarted
            && cell.ValueComputation is MappedPosition position
            && position.SourceSlot() is NeedCell below
            && below.IsValueUnstarted
                ? below
                : null;

    /// <summary>
    /// A <c>filter</c> STAGE: its positions are the source positions the predicate accepts, found
    /// in source order. The scan keeps the accepted positions and its FRONTIER (the next source
    /// position to inspect); a discovery resumes there, so an inspected candidate — accepted or
    /// rejected — is never inspected again. The frontier candidate's verdict is one VALUE-only
    /// cell: it reads the source position, projects the predicate on first use and invokes it; an
    /// ordinary failure stays in that cell, so the frontier does not move and every later
    /// discovery reaching it reports the same failure, while the positions accepted before it
    /// stay readable. A predicate that asks for the scan it is part of meets its own verdict cell
    /// in flight: a demand cycle. Lean: <c>LazyList.filterItems</c> / <c>filterCandidates</c>,
    /// <c>LazyList.discover</c> and the <c>keptBuiltin</c> step.
    ///
    /// <para>Scans stacked at run time are discovered without one native call per scan
    /// (<see cref="DiscoverScans"/>), and once every candidate the source will ever have has been
    /// judged the scan lets go of what only a step reads — its source, the predicate and the
    /// environment of the call that built it (<see cref="Release"/>; C#-only).</para>
    /// </summary>
    private sealed class FilteredList : LazyList
    {
        // The shared verdict values: a verdict is read only by its scan.
        private static readonly Result.Bool Kept = new(true);
        private static readonly Result.Bool Rejected = new(false);

        // What a step reads, released once every candidate of the source has been judged. The
        // source is null afterwards: it then has no position at the frontier, and never will.
        private LazyList? _source;
        private IReadOnlyList<SequenceBuiltinSuffixArgDescriptor>? _descriptors;
        private IReadOnlyList<PreparedSequenceBuiltinSuffixArg>? _controls;
        private EvalCtx _ctx;
        private ValEnv? _values;
        private readonly EvaluationBudget _budget;

        // The slots of the accepted source positions, in source order: an accepted position IS
        // its source position (the same value, the same cell), so a scan over a scan of any
        // height hands out a position's slot without asking the scans below it.
        private readonly List<object> _accepted = [];
        private int _frontier;
        private NeedCell? _verdict;
        private bool _exhausted;

        internal FilteredList(
            LazyList source,
            IReadOnlyList<SequenceBuiltinSuffixArgDescriptor> descriptors,
            IReadOnlyList<PreparedSequenceBuiltinSuffixArg> controls,
            EvalCtx ctx,
            ValEnv values)
        {
            _source = source;
            _descriptors = descriptors;
            _controls = controls;
            _ctx = ctx;
            _values = values;
            _budget = ctx.Budget;
        }

        internal override int Discovered
        {
            get { lock (this) return _accepted.Count; }
        }

        internal override bool IsExhausted
        {
            get { lock (this) return _exhausted; }
        }

        internal override bool IsPending => true;
        internal override bool IsStage => true;
        internal override Result? ValueAt(int index) => null;

        internal override object Slot(int index)
        {
            lock (this) return _accepted[index];
        }

        internal override ValueTask<EvalError?> Discover(int wanted, bool asynchronous)
            => DiscoverScans(this, wanted, asynchronous);

        /// <summary>
        /// DISCOVERY OF STACKED SCANS WITHOUT ONE NATIVE CALL PER SCAN. A scan that has judged
        /// every candidate its source has found asks the source for its next position; when that
        /// position is found by another scan (the <c>filter</c> below, through any <c>map</c> and
        /// <c>take</c> stages, which ask it for exactly that many), this frame drives that scan's
        /// discovery itself: the scan above waits on an explicit list, the scan below runs the
        /// iterations its own discovery would run (the same continuation checks, verdicts and
        /// reservations, in the same order), and the scan above resumes when the request is met,
        /// as when the call returned. A failure ends the whole discovery with that failure, as it
        /// ended every call of the chain, and no candidate is inspected that the nested calls would
        /// not inspect. So a scan stacked at run time to any height is discovered on the native
        /// stack of one, on both routes. The order is Lean's: <c>LazyList.discover</c> demands the
        /// candidates' verdicts in candidate order, each reading its source verdict first.
        /// </summary>
        private static async ValueTask<EvalError?> DiscoverScans(FilteredList top, int wanted, bool asynchronous)
        {
            // TWIN-ONLY (the synchronous run never hops): see StackHop. One probe per discovery:
            // the scans below are driven in this frame.
            if (asynchronous && StackHop.HostStackIsLow()) await new StackHop();
            if (!RuntimeHelpers.TryEnsureSufficientExecutionStack())
                return new EvalError.EvaluationStackExhausted();

            var scan = top;
            // The scans waiting for the scan below them, each with the count it asked for: the
            // innermost one inline, the ones above it in a list (innermost last).
            FilteredList? waiting = null;
            var waitingWanted = 0;
            List<(FilteredList Scan, int Wanted)>? above = null;
            while (true)
            {
                if (scan._budget.CheckContinuation() is { } terminal) return terminal;
                int frontier;
                NeedCell? verdict;
                LazyList? source;
                bool met;
                lock (scan)
                {
                    met = scan._exhausted || scan._accepted.Count >= wanted;
                    frontier = scan._frontier;
                    verdict = scan._verdict;
                    source = scan._source;
                }

                if (met)
                {
                    // The request is met: the scan that made it resumes.
                    if (waiting is null) return null;
                    (scan, wanted) = (waiting, waitingWanted);
                    if (above is { Count: > 0 })
                    {
                        (waiting, waitingWanted) = above[^1];
                        above.RemoveAt(above.Count - 1);
                    }
                    else
                    {
                        waiting = null;
                    }

                    continue;
                }

                if (verdict is null)
                {
                    // Is there a source position at the frontier? The source is asked for it, and
                    // for no later one. A released scan's source has no further position.
                    if (source is null)
                    {
                        if (scan.Complete(frontier) is { } refused) return refused;
                        continue;
                    }

                    var sourceExhausted = source.IsExhausted;
                    if (frontier >= source.Discovered)
                    {
                        if (sourceExhausted)
                        {
                            if (scan.Complete(frontier) is { } refused) return refused;
                            continue;
                        }

                        if (source.Root is FilteredList below)
                        {
                            if (waiting is not null) (above ??= []).Add((waiting, waitingWanted));
                            (waiting, waitingWanted) = (scan, wanted);
                            (scan, wanted) = (below, Math.Min(frontier + 1, source.Limit));
                            continue;
                        }

                        if (await source.Discover(frontier + 1, asynchronous).ConfigureAwait(false) is { } sourceFailure)
                            return sourceFailure;
                        continue;
                    }

                    lock (scan)
                    {
                        if (scan._frontier != frontier) continue;
                        verdict = scan._verdict ??= scan.NewVerdict(frontier);
                    }
                }

                var outcome = await DemandCell(verdict, asynchronous).ConfigureAwait(false);
                if (outcome.IsError) return outcome.Error;
                // A verdict exists only while the scan holds its source (Release).
                var accepted = outcome.Value.Value is Result.Bool { Value: true } ? source!.Slot(frontier) : null;
                lock (scan)
                {
                    // Another flow may have judged this candidate meanwhile: it is recorded once.
                    if (scan._frontier != frontier) continue;
                    if (accepted is not null) scan._accepted.Add(accepted);
                    scan._frontier = frontier + 1;
                    scan._verdict = null;
                }

                scan.ReleaseIfJudged(source!, frontier + 1);
            }
        }

        // The scan has no candidate at the frontier, and its source will find none: it is
        // complete. It reserves its positions once (a refusal ends the run and leaves the scan
        // incomplete) and lets go of what only a step reads.
        private EvalError? Complete(int frontier)
        {
            lock (this)
            {
                if (_frontier != frontier || _exhausted) return null;
                if (EnsureReservation(_budget, _accepted.Count) is { } refused) return AtSite(refused);
                _exhausted = true;
            }

            Release();
            return null;
        }

        // Every candidate the source will ever have is judged once the source is exhausted and
        // the frontier has passed its last position: no verdict is left to compute. The scan
        // itself completes when it is next asked for a position it lacks.
        private void ReleaseIfJudged(LazyList source, int judged)
        {
            // Exhaustion is read BEFORE the count: once exhausted, the count is final.
            var exhausted = source.IsExhausted;
            if (exhausted && judged >= source.Discovered)
                Release();
        }

        /// <summary>
        /// Lets go of the source, the predicate and the environment of the call that built the
        /// scan once no verdict is left to compute. The accepted slots stay (each is its source
        /// position's own slot, read already), and so do the frontier and the completion state.
        /// </summary>
        private void Release()
        {
            lock (this)
            {
                if (_source is null || _verdict is not null) return;
                _source = null;
                _descriptors = null;
                _controls = null;
                _values = null;
                _ctx = default;
            }

            ReleaseSite();
        }

        // The verdict cell's computation is one object: it names the scan and the candidate.
        private NeedCell NewVerdict(int position)
            => new(new Verdict(this, position), _budget, _budget.CancellationToken);

        private sealed class Verdict(FilteredList scan, int position) : NeedComputation
        {
            internal override EvalResult<CountedResult> Evaluate()
                => scan.JudgeAtSite(position, asynchronous: false).GetAwaiter().GetResult();

            internal override ValueTask<EvalResult<CountedResult>> EvaluateAsync()
                => scan.JudgeAtSite(position, asynchronous: true);
        }

        private async ValueTask<EvalResult<CountedResult>> JudgeAtSite(int position, bool asynchronous)
        {
            var verdict = await Judge(position, asynchronous).ConfigureAwait(false);
            return verdict.IsError ? AtSite(verdict.Error) : verdict;
        }

        private async ValueTask<EvalResult<CountedResult>> Judge(int position, bool asynchronous)
        {
            // TWIN-ONLY (the synchronous run never hops): see StackHop.
            if (asynchronous && StackHop.HostStackIsLow()) await new StackHop();
            // A verdict is computed while the scan holds its source, never after (Release).
            var item = await ReadStagePosition(_source!.Slot(position), asynchronous).ConfigureAwait(false);
            if (item.IsError) return item.Error;
            var predicate = asynchronous
                ? await ExpectPreparedAlgorithmSuffixArgAsync(BuiltinId.@filter, _descriptors!, _controls!, 0, _ctx).ConfigureAwait(false)
                : ExpectPreparedAlgorithmSuffixArg(BuiltinId.@filter, _descriptors!, _controls!, 0);
            if (predicate.IsError) return predicate.Error;

            var supplied = new CountedResult(item.Value, item.Value.ValueCount());
            var kept = asynchronous
                ? await EvalFilterPredicateTruthAsync(predicate.Value, supplied, position, _ctx, _values!).ConfigureAwait(false)
                : EvalFilterPredicateTruth(predicate.Value, supplied, position, _ctx, _values!);
            return kept.IsError
                ? kept.Error
                : EvalResult<CountedResult>.Ok(new CountedResult(kept.Value ? Kept : Rejected, 1));
        }
    }

    /// <summary>
    /// A <c>take</c> STAGE: the first <c>limit</c> positions of its source, sharing the source's
    /// slots and its discovery state. It asks the source for no position past its limit, so a
    /// full prefix inspects no further candidate. Lean: the prefix of a <c>listValue</c>'s items,
    /// or <c>LazyList.takeCandidates</c> and the <c>takenBuiltin</c> step.
    /// </summary>
    private sealed class PrefixList(LazyList source, int limit) : LazyList
    {
        private readonly LazyList _root = source.Root;
        private readonly int _limit = Math.Min(source.Limit, limit);
        // The list whose slots these are: a prefix of a prefix shares the inner prefix's.
        private readonly LazyList _slots = source is PrefixList prefix ? prefix._slots : source;

        internal override LazyList Root => _root;
        internal override int Limit => _limit;
        internal override int Discovered => Math.Min(_root.Discovered, _limit);

        internal override bool IsExhausted
        {
            get
            {
                var exhausted = _root.IsExhausted;
                return exhausted || _root.Discovered >= _limit;
            }
        }

        internal override ValueTask<EvalError?> Discover(int wanted, bool asynchronous)
            => _root.Discover(Math.Min(wanted, _limit), asynchronous);

        internal override object Slot(int index) => _slots.Slot(index);
        internal override bool IsPending => _root.IsPending;
        internal override Result? ValueAt(int index) => _slots.ValueAt(index);
    }

    /// <summary>The text a diagnostic shows for a position that has not been read. Lean: <c>resultDiagnosticString</c>.</summary>
    internal const string DeferredPositionText = "<deferred>";

    /// <summary>The text a diagnostic shows for a list whose positions are found by discovery.</summary>
    internal const string PendingListText = "[<deferred>...]";

    // The stand-in a diagnostic rendering holds for a deferred position (see DiagnosticItems):
    // recognized by reference, rendered as DeferredPositionText, never part of a value.
    internal static readonly Result.Str DeferredPositionMarker = new(DeferredPositionText);

    /// <summary>
    /// THE ITEMS A DIAGNOSTIC SHOWS for a list evaluated on demand: the values its positions hold
    /// already, and <see cref="DeferredPositionMarker"/> for every deferred position — whether or
    /// not that position has been read since (the diagnostic keeps the failure it reports and
    /// forces nothing). <c>null</c> for a list whose positions are found by discovery, which is
    /// shown as <see cref="PendingListText"/>. Lean: <c>resultDiagnosticString</c> over
    /// <c>deferred</c> items and a <c>pendingList</c>.
    /// </summary>
    internal static IReadOnlyList<Result>? DiagnosticItems(LazyList positions)
        => positions.IsPending ? null : new DiagnosticPositions(positions);

    private sealed class DiagnosticPositions(LazyList positions) : IReadOnlyList<Result>
    {
        public int Count => positions.Discovered;
        public Result this[int index] => positions.ValueAt(index) ?? DeferredPositionMarker;

        public IEnumerator<Result> GetEnumerator()
        {
            for (var index = 0; index < Count; index++) yield return this[index];
        }

        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();
    }

    // The placeholder a list literal's slot accumulator holds for a DEFERRED element, so that the
    // accumulator keeps counting written slots (and stays transient-bounded, SEC-01) while the
    // element's cell is kept beside it. Recognized by reference; never part of a value.
    private static readonly Result DeferredSlot = new Result.Atom(Decimal128.Zero);

    /// <summary>
    /// Whether a list element is evaluated when the literal is built: a scalar literal or the
    /// empty sequence (nothing to defer) — every other ordinary element is one deferred VALUE
    /// computation. Lean: the constant arm of <c>evalListLiteralCounted</c>.
    /// </summary>
    private static bool IsListLiteralConstant(Expr element)
        => element is Expr.Num or Expr.StringLiteral or Expr.BoolLiteral or Expr.EmptySequence;

    /// <summary>
    /// Evaluate a list literal <c>[e1, …, en]</c> as ONE list value whose ordinary elements are
    /// evaluated on demand (issue #204). In written order: an EXPLICIT SPREAD is formed now (its
    /// operand evaluated, the level it opens read, its items supplied as values); a constant is
    /// its value; every other element captures ONE deferred VALUE computation in the literal's
    /// own environment — a parameter's own cell, so the element and the parameter share one
    /// completion — and evaluates nothing. The cardinality is known when the literal is built,
    /// and reserved then. A literal without a deferred element is a concrete list.
    /// Lean: <c>evalListLiteralCounted</c>.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> EvalListLiteral(
        IReadOnlyList<Expr> elements, SourceSpan? span, EvalCtx ctx, ValEnv valEnv)
    {
        var items = NewListSlots(elements);
        List<NeedCell>? deferred = null;
        for (var index = 0; index < elements.Count; index++)
        {
            var element = elements[index];
            if (element is Expr.SequenceSpread || IsListLiteralConstant(element))
            {
                var slotsR = EvalExplicitSequenceValueExprSlots(element, ctx, valEnv);
                if (slotsR.IsError) return slotsR.Error;
                // The written slots' accumulator is transient-bounded BEFORE it grows (SEC-01):
                // `[A*, A*]` never retains more spread items than the list may.
                AddListSlots(items, slotsR.Value, ctx.Budget, element is Expr.SequenceSpread);
                continue;
            }

            if (DeferListElement(element, ctx, valEnv, items, ref deferred) is { } refusal) return refusal;
        }

        return CompleteListLiteral(items, deferred, span, ctx);
    }

    /// <summary>MIRROR OF <see cref="EvalListLiteral"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalListLiteralAsync(
        IReadOnlyList<Expr> elements, SourceSpan? span, EvalCtx ctx, ValEnv valEnv)
    {
        var items = NewListSlots(elements);
        List<NeedCell>? deferred = null;
        for (var index = 0; index < elements.Count; index++)
        {
            var element = elements[index];
            if (element is Expr.SequenceSpread || IsListLiteralConstant(element))
            {
                var slotsR = await EvalExplicitSequenceValueExprSlotsAsync(element, ctx, valEnv).ConfigureAwait(false);
                if (slotsR.IsError) return slotsR.Error;
                AddListSlots(items, slotsR.Value, ctx.Budget, element is Expr.SequenceSpread);
                continue;
            }

            if (DeferListElement(element, ctx, valEnv, items, ref deferred) is { } refusal) return refusal;
        }

        return CompleteListLiteral(items, deferred, span, ctx);
    }

    // One deferred element: its supplied cell (an unavailable parameter's transport is refused
    // here, while the literal is formed) and its placeholder slot.
    private static EvalError? DeferListElement(
        Expr element, EvalCtx ctx, ValEnv valEnv, List<Result> items, ref List<NeedCell>? deferred)
    {
        var cell = SupplyElementCell(element, ctx, valEnv);
        if (cell.Refusal is { } refusal) return refusal;
        var retained = items.Count;
        AddListSlot(items, DeferredSlot, ctx.Budget);
        if (items.Count > retained) (deferred ??= []).Add(cell);
        return null;
    }

    // Cardinality is known once the written slots (spread expansion included) are formed, so the
    // reservation happens before the list is built. An overflowed accumulator (SEC-01) reserves
    // its full counted size: the same refusal.
    private static EvalResult<CountedResult> CompleteListLiteral(
        List<Result> items, List<NeedCell>? deferred, SourceSpan? span, EvalCtx ctx)
    {
        if (ReserveCollection(ctx, ListSlotTotal(items), span) is { } limitError)
            return limitError;
        if (deferred is null)
            return EvalResult<CountedResult>.Ok(new CountedResult(Result.ListValue.TakeOwnership(items.ToArray()), 1));

        var slots = new object[items.Count];
        var next = 0;
        for (var index = 0; index < slots.Length; index++)
            slots[index] = ReferenceEquals(items[index], DeferredSlot) ? deferred[next++] : items[index];
        var positions = new KnownSlots(slots);
        return EvalResult<CountedResult>.Ok(new CountedResult(DeferredList(positions, ctx.Budget), 1));
    }

    /// <summary>
    /// The receiver of a fused <c>filter</c>…<c>count</c> pipeline that is a list evaluated on
    /// demand: the fused executor reads its positions one by one (<see cref="ReadFilterSourcePosition"/>),
    /// exactly as the generic <c>filter</c> stage's scan does. The list interface exists only so
    /// the receiver travels where a concrete receiver's items do; it is never indexed.
    /// </summary>
    internal sealed class LazyIterationItems(LazyList positions) : IReadOnlyList<CountedResult>
    {
        internal LazyList Positions { get; } = positions;

        public int Count => throw new InvalidOperationException("A receiver evaluated on demand is read position by position.");
        public CountedResult this[int index] => throw new InvalidOperationException("A receiver evaluated on demand is read position by position.");
        public IEnumerator<CountedResult> GetEnumerator() => throw new InvalidOperationException("A receiver evaluated on demand is read position by position.");
        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();
    }

    /// <summary>
    /// The fused <c>filter</c>…<c>count</c> executor's read of ONE source position of a receiver
    /// evaluated on demand: the position is found (no further than it), then read; <c>null</c>
    /// when the receiver has no such position. The synchronous route only (the asynchronous
    /// twin pins fusion off).
    /// </summary>
    internal static EvalResult<CountedResult?> ReadFilterSourcePosition(LazyList positions, int index)
    {
        var has = HasPosition(positions, index, asynchronous: false).GetAwaiter().GetResult();
        if (has.IsError) return has.Error;
        if (!has.Value) return EvalResult<CountedResult?>.Ok(null);
        var item = ForcePosition(positions.Slot(index), asynchronous: false).GetAwaiter().GetResult();
        return item.IsError
            ? item.Error
            : EvalResult<CountedResult?>.Ok(new CountedResult(item.Value, item.Value.ValueCount()));
    }

    /// <summary>The list value of one instance evaluated on demand, recorded on its run.</summary>
    private static Result.ListValue DeferredList(LazyList positions, EvaluationBudget budget)
    {
        budget.NoteLazyList();
        positions.Generation = budget.ReadGeneration;
        return Result.ListValue.Deferred(positions);
    }

    /// <summary>
    /// The positional source of a collection value: a lazy list's own positions, and the one-level
    /// collection view of every other value (<see cref="BuiltinCollectionItems"/>: a concrete list
    /// or sequence opens to its items, any other value is a one-element collection).
    /// </summary>
    private static LazyList PositionsOf(Result collection)
        => collection is Result.ListValue { Lazy: { } lazy } ? lazy : new ConcreteSlots(BuiltinCollectionItems(collection));

    /// <summary>
    /// INDEXED VALUE DEMAND: the VALUE one position holds. A deferred position is its cell's one
    /// VALUE demand — memoized, and the element's computation is a subordinate computation of
    /// whichever consumer reads the list, so its own missing output is nested (Q-36). Any other
    /// slot is a value already. Lean: <c>forcePosition</c>.
    /// </summary>
    private static ValueTask<EvalResult<Result>> ForcePosition(object slot, bool asynchronous)
        => slot is Result value ? new(EvalResult<Result>.Ok(value)) : ForceCell((NeedCell)slot, asynchronous);

    private static async ValueTask<EvalResult<Result>> ForceCell(NeedCell cell, bool asynchronous)
    {
        var outcome = await DemandCell(cell, asynchronous).ConfigureAwait(false);
        return outcome.IsError ? NestMissingOutput(outcome.Error) : EvalResult<Result>.Ok(outcome.Value.Value);
    }

    /// <summary>
    /// Whether position <paramref name="index"/> exists, discovering up to it and no further.
    /// </summary>
    private static ValueTask<EvalResult<bool>> HasPosition(LazyList list, int index, bool asynchronous)
    {
        var exhausted = list.IsExhausted;
        if (index < list.Discovered) return new(EvalResult<bool>.Ok(true));
        return exhausted ? new(EvalResult<bool>.Ok(false)) : DiscoverPosition(list, index, asynchronous);
    }

    private static async ValueTask<EvalResult<bool>> DiscoverPosition(LazyList list, int index, bool asynchronous)
    {
        // SelectorIndex saturates a large selector at int.MaxValue. That asks for the
        // complete scan, including any predicate failure encountered along the way.
        var wanted = index == int.MaxValue ? LazyList.Everything : index + 1;
        if (await list.Discover(wanted, asynchronous).ConfigureAwait(false) is { } failure) return failure;
        return EvalResult<bool>.Ok(index < list.Discovered);
    }

    /// <summary>
    /// A STORED PATTERN POSITION: the cell a list pattern, an unpacking receiver or a collecting
    /// binding binds to one position of a list evaluated on demand. A position that is a value
    /// already is a Ready cell; a deferred position is a VALUE-only cell over the position's own
    /// cell — reading the bound name is that position's one VALUE demand, shared with every other
    /// reader of the list, and the name gains no callable identity, plan or slice from the
    /// element's computation (a list element is a value). Lean: the Ready cell holding a
    /// <c>deferred</c> item (<c>NeedDemand.suspendedValue</c>).
    /// </summary>
    private static NeedCell PositionCell(object slot, EvaluationBudget budget)
    {
        if (slot is Result value) return NeedCell.Ready(new CountedResult(value, value.ValueCount()));
        return new NeedCell(new StoredPosition((NeedCell)slot), budget, budget.CancellationToken);
    }

    /// <summary>The computation of a stored pattern position: the VALUE demand of the position's own cell.</summary>
    private sealed class StoredPosition(NeedCell position) : NeedComputation
    {
        internal override EvalResult<CountedResult> Evaluate() => position.Demand();

        internal override ValueTask<EvalResult<CountedResult>> EvaluateAsync() => position.DemandAsync();
    }

    /// <summary>
    /// A result for tests and tools that call an internal evaluator entry point instead of a run:
    /// the outcome with its value materialized, exactly as a run materializes its result
    /// (<see cref="MaterializeRunOutput(EvalResult{CountedResult}, EvalCtx)"/>).
    /// </summary>
    internal static EvalResult<CountedResult> WholeValueForTesting(EvalResult<CountedResult> result, EvalCtx ctx)
        => MaterializeRunOutput(result, ctx);

    /// <summary>The asynchronous twin's <see cref="WholeValueForTesting"/>.</summary>
    internal static ValueTask<EvalResult<CountedResult>> WholeValueForTestingAsync(EvalResult<CountedResult> result, EvalCtx ctx)
        => MaterializeRunOutputAsync(result, ctx);

    /// <summary>
    /// THE WHOLE VALUE of a cell: its VALUE demand, then that value materialized — what a
    /// repeated name's agreement compares. In a run that has created no lazy list it is the VALUE
    /// demand itself. Lean: <c>NeedCapabilities.whole</c>.
    /// </summary>
    private static ValueTask<EvalResult<CountedResult>> DemandWhole(NeedCell cell, EvalCtx ctx, bool asynchronous)
    {
        // The demand comes FIRST: it may be what creates the run's first lazy list.
        var demand = DemandCell(cell, asynchronous);
        if (!demand.IsCompletedSuccessfully) return AwaitWhole(demand, ctx, asynchronous);
        var demanded = demand.Result;
        return demanded.IsError || !ctx.Budget.HasLazyLists || !ContainsLazyList(demanded.Value.Value)
            ? new(demanded)
            : MaterializeWhole(demanded.Value, ctx, asynchronous);
    }

    private static async ValueTask<EvalResult<CountedResult>> AwaitWhole(
        ValueTask<EvalResult<CountedResult>> demand, EvalCtx ctx, bool asynchronous)
    {
        var demanded = await demand.ConfigureAwait(false);
        return demanded.IsError ? demanded : await MaterializeWhole(demanded.Value, ctx, asynchronous).ConfigureAwait(false);
    }

    private static async ValueTask<EvalResult<CountedResult>> MaterializeWhole(CountedResult demanded, EvalCtx ctx, bool asynchronous)
    {
        var whole = await MaterializeValue(demanded.Value, ctx, asynchronous).ConfigureAwait(false);
        return whole.IsError
            ? whole.Error
            : EvalResult<CountedResult>.Ok(new CountedResult(whole.Value, demanded.EmittedCount));
    }

    /// <summary>
    /// ONE LEVEL of a list made concrete: every position found AND read, in order, each before
    /// the next one is looked for. The items keep their own contents (a nested list stays as it
    /// is). An explicit spread opens this level and the strict collection builtins read their
    /// collection through it; every other value is returned as it is. Built at most once per
    /// list instance. Lean: <c>forceLevel</c>.
    /// </summary>
    private static ValueTask<EvalResult<Result>> ForceLevel(Result value, EvalCtx ctx, bool asynchronous)
    {
        if (value is not Result.ListValue { Lazy: { } lazy }) return new(EvalResult<Result>.Ok(value));
        return lazy.Level is { } known ? new(EvalResult<Result>.Ok(known)) : ForceLazyLevel(lazy, ctx, asynchronous);
    }

    private static async ValueTask<EvalResult<Result>> ForceLazyLevel(LazyList lazy, EvalCtx ctx, bool asynchronous)
    {
        var known = lazy.IsExhausted ? lazy.Discovered : -1;
        var read = known > 0 ? new List<Result>(known) : [];
        for (var index = 0; ; index++)
        {
            var has = await HasPosition(lazy, index, asynchronous).ConfigureAwait(false);
            if (has.IsError) return has.Error;
            if (!has.Value) break;
            var item = await ForcePosition(lazy.Slot(index), asynchronous).ConfigureAwait(false);
            if (item.IsError) return item.Error;
            read.Add(item.Value);
        }

        if (lazy.EnsureReservation(ctx.Budget, read.Count) is { } refused) return refused;
        return EvalResult<Result>.Ok(lazy.PublishLevel(Result.ListValue.TakeOwnership(read.ToArray())));
    }

    /// <summary>
    /// Whether <paramref name="value"/> holds a list evaluated on demand at any depth. A value
    /// without one is CONCRETE: materializing it is the identity. Reads nothing and evaluates
    /// nothing; a shared nested structure is inspected once. Lean: <c>Result.isLazy</c>.
    /// </summary>
    internal static bool ContainsLazyList(Result value)
    {
        IReadOnlyList<Result> items;
        switch (value)
        {
            case Result.ListValue list:
                if (list.Lazy is not null) return true;
                items = list.Items;
                break;
            case Result.SequenceValue sequence:
                items = sequence.Items;
                break;
            default:
                return false;
        }

        // A flat value of scalars — the common case — is decided without any traversal state.
        var nested = false;
        for (var index = 0; index < items.Count; index++)
        {
            switch (items[index])
            {
                case Result.ListValue { Lazy: not null }:
                    return true;
                case Result.ListValue or Result.SequenceValue:
                    nested = true;
                    break;
            }
        }

        return nested && ContainsNestedLazyList(items);
    }

    // Indexed continuation frames (see the depth note on Result) and a reference-identity memo of
    // the nested structures already inspected (see its DAG note).
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static bool ContainsNestedLazyList(IReadOnlyList<Result> root)
    {
        var frames = new Stack<(IReadOnlyList<Result> Items, int Next)>();
        var inspected = new HashSet<Result>(ReferenceEqualityComparer.Instance);
        var items = root;
        var next = 0;
        while (true)
        {
            if (next >= items.Count)
            {
                if (frames.Count == 0) return false;
                (items, next) = frames.Pop();
                continue;
            }

            var child = items[next++];
            IReadOnlyList<Result> childItems;
            switch (child)
            {
                case Result.ListValue list:
                    if (list.Lazy is not null) return true;
                    childItems = list.Items;
                    break;
                case Result.SequenceValue sequence:
                    childItems = sequence.Items;
                    break;
                default:
                    continue;
            }

            if (childItems.Count == 0 || !inspected.Add(child)) continue;
            frames.Push((items, next));
            (items, next) = (childItems, 0);
        }
    }

    /// <summary>
    /// THE MATERIALIZED FORM of a value: the value with every position of every list read, at
    /// every depth, left to right and depth first — each position is found and its value fully
    /// materialized before the next position is looked for. The result is CONCRETE, which is what
    /// evaluator equality compares, <c>atoms</c> collects from, a run result is and a host
    /// operation receives. A concrete value is returned unchanged; in a run that has created no
    /// lazy list nothing is even inspected.
    ///
    /// <para>A list can hold itself through a deferred position (<c>L = [L]</c>: building
    /// <c>L</c> reads nothing), so reaching a list this materialization is already inside is a
    /// cycle of the value: <see cref="EvalError.DemandCycle"/>, never an unbounded
    /// materialization. A list's whole concrete form is remembered on the instance and reused by
    /// every later materialization that reaches it.</para>
    ///
    /// <para>Lean: <c>materializeVia</c> (the <c>materializedBuiltin</c> step and
    /// <c>materializePosition</c>).</para>
    /// </summary>
    private static ValueTask<EvalResult<Result>> MaterializeValue(Result value, EvalCtx ctx, bool asynchronous)
        => !ctx.Budget.HasLazyLists || !ContainsLazyList(value)
            ? new(EvalResult<Result>.Ok(value))
            : MaterializeLazyValue(value, ctx, asynchronous);

    /// <summary>The synchronous engine's <see cref="MaterializeValue"/>.</summary>
    private static EvalResult<Result> MaterializeValueSync(Result value, EvalCtx ctx)
        => !ctx.Budget.HasLazyLists || !ContainsLazyList(value)
            ? EvalResult<Result>.Ok(value)
            : MaterializeLazyValue(value, ctx, asynchronous: false).GetAwaiter().GetResult();

    /// <summary>
    /// THE RUN RESULT IS MATERIALIZED (issue #204): the run's assembled output, with every position
    /// of every list it holds read left to right and depth first, WHILE THE RUN IS ACTIVE — so a
    /// host only ever receives concrete values, and an element that fails makes the run fail.
    /// The emitted count is unchanged (a list is one value, read or not). Lean:
    /// <c>evalRunValue</c>.
    /// </summary>
    private static EvalResult<CountedResult> MaterializeRunOutput(EvalResult<CountedResult> result, EvalCtx ctx)
    {
        if (result.IsError || !ctx.Budget.HasLazyLists) return result;
        var whole = MaterializeValueSync(result.Value.Value, ctx);
        return whole.IsError
            ? whole.Error
            : EvalResult<CountedResult>.Ok(new CountedResult(whole.Value, result.Value.EmittedCount));
    }

    /// <inheritdoc cref="MaterializeRunOutput(EvalResult{CountedResult}, EvalCtx)"/>
    private static EvalResult<Result> MaterializeRunOutput(EvalResult<Result> result, EvalCtx ctx)
        => result.IsError || !ctx.Budget.HasLazyLists ? result : MaterializeValueSync(result.Value, ctx);

    /// <summary>The asynchronous twin's <see cref="MaterializeRunOutput(EvalResult{CountedResult}, EvalCtx)"/>.</summary>
    private static ValueTask<EvalResult<CountedResult>> MaterializeRunOutputAsync(EvalResult<CountedResult> result, EvalCtx ctx)
        => result.IsError || !ctx.Budget.HasLazyLists ? new(result) : MaterializeLazyRunOutputAsync(result.Value, ctx);

    private static async ValueTask<EvalResult<CountedResult>> MaterializeLazyRunOutputAsync(CountedResult output, EvalCtx ctx)
    {
        var whole = await MaterializeValue(output.Value, ctx, asynchronous: true).ConfigureAwait(false);
        return whole.IsError
            ? whole.Error
            : EvalResult<CountedResult>.Ok(new CountedResult(whole.Value, output.EmittedCount));
    }

    /// <summary>The asynchronous twin's <see cref="MaterializeRunOutput(EvalResult{Result}, EvalCtx)"/>.</summary>
    private static ValueTask<EvalResult<Result>> MaterializeRunOutputAsync(EvalResult<Result> result, EvalCtx ctx)
        => result.IsError || !ctx.Budget.HasLazyLists ? new(result) : MaterializeValue(result.Value, ctx, asynchronous: true);

    /// <summary>
    /// A value as a PASSIVE OBSERVER may show it (issue #204): the value itself when it is
    /// concrete, and otherwise the value with every list evaluated on demand replaced by a
    /// concrete form the run already built for it — its whole form, or the one-level form a
    /// consumer that read every position built, with the lists inside that form resolved the
    /// same way. A missing cached form or a cycle among those forms returns <c>false</c> and the
    /// observer withholds the value. Taking the snapshot never demands a list position.
    /// </summary>
    internal static bool TrySnapshotValue(Result value, out Result snapshot)
    {
        snapshot = value;
        if (!ContainsLazyList(value)) return true;
        return TrySnapshotLazyValue(value, out snapshot);
    }

    // Post-order rebuild with indexed continuation frames and a reference-identity memo of the
    // concrete structures completed, like the materialization walk — but a lazy list contributes
    // a remembered concrete form (its whole form as it is; its one-level form as a concrete node
    // whose items are walked in turn) or ends the walk.
    private static bool TrySnapshotLazyValue(Result root, out Result snapshot)
    {
        snapshot = root;
        if (root is Result.ListValue { Lazy: { } rootList })
        {
            if (rootList.Materialized is { } whole)
            {
                snapshot = whole;
                return true;
            }

            if (rootList.Level is not { } rootLevel) return false;
            root = rootLevel;
        }

        var frames = new Stack<MaterializeFrame>();
        Dictionary<Result, Result>? completed = null;
        // Track the concrete node each frame walks. For L = [L], L's one-level form leads back
        // to the same node after its lazy child is resolved.
        var active = new HashSet<Result>(ReferenceEqualityComparer.Instance) { root };
        frames.Push(new MaterializeFrame(root));
        while (true)
        {
            var frame = frames.Peek();
            if (frame.Next >= frame.Source!.Count)
            {
                var finished = frame.CompleteConcrete();
                frames.Pop();
                active.Remove(frame.Node);
                if (frames.Count == 0)
                {
                    snapshot = finished;
                    return true;
                }

                (completed ??= new Dictionary<Result, Result>(ReferenceEqualityComparer.Instance))[frame.Node] = finished;
                frames.Peek().Accept(finished);
                continue;
            }

            var child = frame.Source[frame.Next];
            if (child is Result.ListValue { Lazy: { } nested })
            {
                if (nested.Materialized is { } known)
                {
                    frame.Accept(known);
                    continue;
                }

                if (nested.Level is not { } level) return false;
                child = level;
            }

            if (child is Result.ListValue or Result.SequenceValue)
            {
                if (completed is not null && completed.TryGetValue(child, out var concrete))
                    frame.Accept(concrete);
                else if (!active.Add(child))
                    return false;
                else
                    frames.Push(new MaterializeFrame(child));
            }
            else
            {
                frame.Accept(child);
            }
        }
    }

    /// <summary>One open structure of a materialization walk: its node and the next child.</summary>
    private sealed class MaterializeFrame
    {
        internal readonly Result Node;
        // A list evaluated on demand: its positions are found and read one by one.
        internal readonly LazyList? Lazy;
        // A concrete sequence or list: its items are values already.
        internal readonly IReadOnlyList<Result>? Source;
        private readonly bool _isSequence;
        internal int Next;
        // A concrete node's destination, allocated once a child's concrete form differs from the
        // stored child; while it is null the node is its own materialized form.
        private Result[]? _rebuilt;
        // A lazy node's materialized positions, in order.
        private List<Result>? _read;

        internal MaterializeFrame(Result node)
        {
            Node = node;
            switch (node)
            {
                case Result.ListValue { Lazy: { } lazy }:
                    Lazy = lazy;
                    break;
                case Result.ListValue list:
                    Source = list.Items;
                    break;
                case Result.SequenceValue sequence:
                    Source = sequence.Items;
                    _isSequence = true;
                    break;
                default:
                    throw new ArgumentException("Materialization frames require a sequence or list value.", nameof(node));
            }
        }

        internal void Accept(Result materialized)
        {
            if (Lazy is not null)
            {
                (_read ??= []).Add(materialized);
                Next++;
                return;
            }

            if (_rebuilt is null)
            {
                if (ReferenceEquals(materialized, Source![Next]))
                {
                    Next++;
                    return;
                }

                _rebuilt = new Result[Source.Count];
                for (var i = 0; i < Next; i++)
                    _rebuilt[i] = Source[i];
            }

            _rebuilt[Next++] = materialized;
        }

        /// <summary>A lazy node's materialized positions as the exact array of its concrete list.</summary>
        internal Result[] ReadPositions() => _read is null ? [] : _read.ToArray();

        /// <summary>A concrete node's materialized form: itself when no child changed.</summary>
        internal Result CompleteConcrete()
            => _rebuilt is null
                ? Node
                : _isSequence ? Result.SequenceValue.TakeOwnership(_rebuilt) : Result.ListValue.TakeOwnership(_rebuilt);
    }

    private static async ValueTask<EvalResult<Result>> MaterializeLazyValue(Result root, EvalCtx ctx, bool asynchronous)
    {
        var budget = ctx.Budget;
        // Indexed continuation frames (see the depth note on Result): one per open structure.
        var frames = new Stack<MaterializeFrame>();
        // The lists this walk is inside, and the concrete structures it has completed (a shared
        // node is materialized once per walk; a list keeps its own form for every walk).
        HashSet<LazyList>? open = null;
        Dictionary<Result, Result>? completed = null;
        var rootFrame = new MaterializeFrame(root);
        if (rootFrame.Lazy is { } rootList)
        {
            if (rootList.Materialized is { } whole) return EvalResult<Result>.Ok(whole);
            (open = []).Add(rootList);
        }

        frames.Push(rootFrame);
        var unobserved = 0;
        while (true)
        {
            var frame = frames.Peek();
            Result child;
            Result? finished = null;
            if (frame.Lazy is { } lazy)
            {
                // The position is found and read one generation inside its list: a list its
                // computation builds is read in turn, and a result that nests itself forever
                // ends at the recursion limit (EvaluationBudget.TryEnterNestedRead).
                EvalResult<bool> has;
                EvalResult<Result> item = default;
                if (budget.TryEnterNestedRead(lazy.Generation, out var suspendedGeneration) is { } tooDeep)
                    return tooDeep;
                try
                {
                    has = await HasPosition(lazy, frame.Next, asynchronous).ConfigureAwait(false);
                    if (!has.IsError && has.Value)
                        item = await ForcePosition(lazy.Slot(frame.Next), asynchronous).ConfigureAwait(false);
                }
                finally
                {
                    budget.ExitNestedRead(suspendedGeneration);
                }

                if (has.IsError) return has.Error;
                if (has.Value)
                {
                    if (item.IsError) return item.Error;
                    child = item.Value;
                }
                else
                {
                    if (lazy.EnsureReservation(ctx.Budget, frame.Next) is { } refused) return refused;
                    finished = lazy.PublishMaterialized(Result.ListValue.TakeOwnership(frame.ReadPositions()));
                    open!.Remove(lazy);
                    child = finished;
                }
            }
            else if (frame.Next < frame.Source!.Count)
            {
                child = frame.Source[frame.Next];
            }
            else
            {
                finished = frame.CompleteConcrete();
                child = finished;
            }

            if (finished is not null)
            {
                frames.Pop();
                if (frames.Count == 0) return EvalResult<Result>.Ok(finished);
                if (frame.Lazy is null)
                    (completed ??= new Dictionary<Result, Result>(ReferenceEqualityComparer.Instance))[frame.Node] = finished;
                frames.Peek().Accept(finished);
                continue;
            }

            // Slot reads since the last cancellation checkpoint: the walk charges nothing of its
            // own (every position read is its cell's ordinary evaluation), but a wide concrete
            // value must stay cancellable.
            if (++unobserved >= Result.ValueSemanticComparer.UnitsPerCharge)
            {
                unobserved = 0;
                budget.ObserveCancellation();
            }

            switch (child)
            {
                case Result.ListValue { Lazy: { } nested }:
                    if (nested.Materialized is { } known)
                    {
                        frame.Accept(known);
                        break;
                    }

                    // The value holds itself through a position being materialized already.
                    if (!(open ??= []).Add(nested)) return new EvalError.DemandCycle();
                    frames.Push(new MaterializeFrame(child));
                    break;
                case Result.ListValue or Result.SequenceValue:
                    if (completed is not null && completed.TryGetValue(child, out var concrete))
                        frame.Accept(concrete);
                    else
                        frames.Push(new MaterializeFrame(child));
                    break;
                default:
                    frame.Accept(child);
                    break;
            }
        }
    }

    /// <summary>
    /// The operands <c>contains</c> and <c>distinct</c> compare, as WHOLE values: every item of
    /// the bound collection materialized, in order, and then (<c>contains</c>) the searched
    /// value. Concrete operands are returned as they are. Lean: the <c>materializeVia</c> reads of
    /// the two arms of <c>applyBuiltinCountedSequence</c>.
    /// </summary>
    private static async ValueTask<EvalResult<(PreparedSequenceBuiltinInput Input, IReadOnlyList<PreparedSequenceBuiltinSuffixArg> Controls)>> MaterializeComparedOperands(
        BuiltinId builtin,
        PreparedSequenceBuiltinInput input,
        IReadOnlyList<PreparedSequenceBuiltinSuffixArg> controls,
        EvalCtx ctx,
        bool asynchronous)
    {
        var items = input.FlattenedItems;
        Result[]? whole = null;
        for (var index = 0; index < items.Count; index++)
        {
            var itemR = await MaterializeValue(items[index], ctx, asynchronous).ConfigureAwait(false);
            if (itemR.IsError) return itemR.Error;
            if (whole is null && !ReferenceEquals(itemR.Value, items[index]))
            {
                whole = new Result[items.Count];
                for (var copied = 0; copied < index; copied++)
                    whole[copied] = items[copied];
            }

            if (whole is not null) whole[index] = itemR.Value;
        }

        if (whole is not null)
            input = new PreparedSequenceBuiltinInput(new CollectedSequenceBuiltinInput(whole), input.NumericItems);
        if (builtin == BuiltinId.@contains && controls.Count == 1
            && controls[0] is PreparedSequenceBuiltinSuffixArg.ValueArg(var searched))
        {
            var searchedR = await MaterializeValue(searched, ctx, asynchronous).ConfigureAwait(false);
            if (searchedR.IsError) return searchedR.Error;
            if (!ReferenceEquals(searchedR.Value, searched))
                controls = [new PreparedSequenceBuiltinSuffixArg.ValueArg(searchedR.Value)];
        }

        return EvalResult<(PreparedSequenceBuiltinInput, IReadOnlyList<PreparedSequenceBuiltinSuffixArg>)>.Ok((input, controls));
    }

    /// <summary>
    /// THE COLLECTION BUILTINS THAT READ POSITIONS (<c>count</c>, <c>first</c>, <c>last</c>,
    /// <c>take</c>, <c>map</c>, <c>filter</c>) over a positional source: a list evaluated on
    /// demand, or — for the two callback stages — any collection view. One body for both
    /// evaluation routes: the synchronous caller blocks on the completed task, the asynchronous
    /// twin awaits it.
    ///
    /// <list type="bullet">
    ///   <item><c>count</c> needs the cardinality only: every position is found, none is read.</item>
    ///   <item><c>first</c> finds and reads position zero; <c>last</c> finds every position and
    ///   reads the final one. An empty list is their ordinary missing-position failure.</item>
    ///   <item><c>take</c> validates its count before any position is looked for; a non-positive
    ///   count is the empty list and reads nothing; otherwise the result is a prefix sharing the
    ///   source's positions and its discovery state.</item>
    ///   <item><c>map</c> and <c>filter</c> build their stage and evaluate nothing: no element is
    ///   read and the callback is not projected. A source known to be empty is the empty
    ///   list.</item>
    /// </list>
    ///
    /// Lean: the position-reading arms of <c>applyBuiltinCountedSequence</c>.
    /// </summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalPositionalBuiltin(
        BuiltinId builtin,
        SequenceBuiltinMetadata metadata,
        IReadOnlyList<PreparedSequenceBuiltinSuffixArg> controls,
        LazyList source,
        EvalCtx ctx,
        ValEnv values,
        bool asynchronous)
    {
        switch (builtin)
        {
            case BuiltinId.@count:
                {
                    if (await source.Discover(LazyList.Everything, asynchronous).ConfigureAwait(false) is { } failure)
                        return failure;
                    return EvalResult<CountedResult>.Ok(new CountedResult(new Result.Atom(source.Discovered), 1));
                }

            case BuiltinId.@first:
            case BuiltinId.@last:
                {
                    var wanted = builtin == BuiltinId.@first ? 1 : LazyList.Everything;
                    if (await source.Discover(wanted, asynchronous).ConfigureAwait(false) is { } failure)
                        return failure;
                    var found = source.Discovered;
                    if (found == 0)
                    {
                        // The builtin's own empty policy: a missing POSITION of a selection (Q-27).
                        var empty = ApplySequenceBuiltinEmptyPolicy(builtin, metadata, new CollectedSequenceBuiltinInput([]));
                        return empty.IsError ? empty.Error : new EvalError.BadIndex();
                    }

                    var selected = await ForcePosition(source.Slot(builtin == BuiltinId.@first ? 0 : found - 1), asynchronous).ConfigureAwait(false);
                    return selected.IsError ? selected.Error : CountValue(selected.Value);
                }

            case BuiltinId.@take:
                {
                    var countR = ExpectPreparedWholeNumberSuffixArg(builtin, metadata.SuffixArgs, controls, 0);
                    if (countR.IsError) return countR.Error;
                    if (countR.Value <= 0) return MakeCollectionListResult(ctx, []);
                    var limit = countR.Value >= int.MaxValue ? int.MaxValue : (int)countR.Value;
                    return StageResult(new PrefixList(source, limit), ctx);
                }

            case BuiltinId.@map:
                return IsKnownEmpty(source)
                    ? MakeCollectionListResult(ctx, [])
                    : StageResult(new MappedList(source, metadata.SuffixArgs, controls, ctx, values), ctx);

            case BuiltinId.@filter:
                return IsKnownEmpty(source)
                    ? MakeCollectionListResult(ctx, [])
                    : StageResult(new FilteredList(source, metadata.SuffixArgs, controls, ctx, values), ctx);

            default:
                throw new InvalidOperationException($"{BuiltinDisplayName(builtin)} does not read positions.");
        }
    }

    private static bool IsKnownEmpty(LazyList source)
    {
        var exhausted = source.IsExhausted;
        return exhausted && source.Discovered == 0;
    }

    // The list of one stage. A stage of known cardinality reserves its positions now, exactly as
    // the list it replaces was reserved when it was built; a stage whose positions are discovered
    // reserves them when its first concrete form is built.
    private static EvalResult<CountedResult> StageResult(LazyList stage, EvalCtx ctx)
    {
        LazyStageTestSeam.Note(stage);
        var exhausted = stage.IsExhausted;
        if (exhausted && stage.EnsureReservation(ctx.Budget, stage.Discovered) is { } refused)
            return refused;
        return EvalResult<CountedResult>.Ok(new CountedResult(DeferredList(stage, ctx.Budget), 1));
    }

    /// <summary>Whether <paramref name="builtin"/> reads positions. Lean: <c>Builtin.readsPositions</c>.</summary>
    private static bool ReadsPositions(BuiltinId builtin)
        => builtin is BuiltinId.@count or BuiltinId.@first or BuiltinId.@last or BuiltinId.@take or BuiltinId.@map or BuiltinId.@filter;
}
