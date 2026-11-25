using System.Text;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Xunit.Abstractions;

namespace KatLang.Tests.AsyncEvaluation;

/// <summary>
/// The mechanical twin-drift guard for the <c>MIRROR OF</c> rule (AGENTS.md: every async twin is marked
/// <c>// MIRROR OF &lt;sync name&gt;</c> and changes in the SAME change as its counterpart).
///
/// <para><b>What it checks.</b> <see cref="TwinNormalization"/> parses every <c>dotnet/src/KatLang/</c> source once with
/// Roslyn (<c>Microsoft.CodeAnalysis.CSharp</c> 5.12.0, the compiler of the .NET 11.0.100 SDK), resolves every
/// marker to its counterpart, and normalizes both sides of each pair (await,
/// <c>ConfigureAwait(false)</c>, the synchronous counterpart's <c>GetAwaiter().GetResult()</c> adapter, the <c>Async</c> suffix and the marker-derived twin
/// names, the <c>async</c> modifier, <c>asynchronous: true</c>, comments and whitespace). A pair must then be
/// token-for-token identical — or match its <see cref="Allowlist"/> entry EXACTLY: the pair, the classified reason,
/// and the hash of the positioned normalized difference. A one-sided edit changes either the identity or the hash, so it fails
/// here until the other side follows. <see cref="AsyncTwinDifferentialTests"/> and
/// <see cref="AsyncRouteCorpusDifferentialTests"/> compare OUTCOMES over corpora; this guard compares SOURCE, so it
/// also covers paths no corpus reaches.</para>
///
/// <para><b>The ratchet.</b> The allowlist only shrinks. A pair that becomes identical must be removed (and
/// <see cref="AllowlistCeiling"/> lowered with it) and pinned in <see cref="IdenticalPairs"/>; a pair that newly differs
/// cannot be absorbed by a new entry. Every pinned pair, identical or allowlisted, must still resolve: deleting or
/// rewording a marker cannot drop its pair from the guard (<see cref="PairVerdicts"/>). A recorded hash that no longer matches means one side changed: mirror the edit, or — only
/// when BOTH sides changed together and the remaining difference is still exactly the recorded class — re-pin the
/// hash in the same reviewed change (shared edits before a difference also move its pinned token offsets).
/// Growing the list or the ceiling is an owner decision, never a fix.</para>
///
/// <para><b>Difference classes</b> (<see cref="TwinDifference"/>). Each was checked against the helper it names and
/// found equivalent: FrameSplit, OptimizerPinned, AsyncCacheGuard, ResolveAdapter and DistinctWalk are the classes of
/// the November 2026 audit; StackHop is the twin-only hop of 2026-11-14; the remaining classes were found while
/// building this guard and are documented on the enum. 43 of the 72 entries carry at least one of those further
/// classes (30 only further classes, 13 mixed with audit classes). That baseline was accepted by owner direction on
/// 2026-11-14 after an entry-by-entry review of each normalized difference against its helpers; the acceptance covers
/// exactly the pinned entries (pair, classes, hash) and grants no new exception.</para>
///
/// <para><b>Second pattern.</b> About twenty-five methods are ONE body with a <c>bool asynchronous</c> flag (the
/// synchronous family completes them with <c>.GetAwaiter().GetResult()</c>). They have no twin to compare, so
/// <see cref="FlagBranchPoints"/> pins every read of the flag that selects behavior, with a reason; an await-or-call
/// branch (<c>asynchronous ? await XAsync(..) : X(..)</c>) is additionally checked to have arms that normalize
/// identically. Calls passing <c>asynchronous: true</c> must never be completed by blocking.</para>
/// </summary>
public class TwinNormalizationTests(ITestOutputHelper output)
{
    /// <summary>
    /// Why a pinned pair differs after normalization. A pair can combine several classes.
    /// </summary>
    [Flags]
    internal enum TwinDifference
    {
        None = 0,

        /// <summary>One side factors part of the body into a separate (usually <c>NoInlining</c>) helper or leaf frame
        /// to keep its recursion-spine frame small, or bypasses an out-of-line helper on the hot path; the other side
        /// keeps that code inline. Examples: <c>EvalDeclaredAlgorithmMemberCallCounted</c>, <c>LinkedCalleeValue</c>,
        /// <c>EvalPlannedAlgorithmCalleeCallCounted</c>, <c>EvalBoundMemberCallCounted</c>,
        /// <c>EvalParamCountedOf</c>/<c>EvalResolveCountedOf</c>.</summary>
        FrameSplit = 1 << 0,

        /// <summary>The synchronous side attempts the loop or sequence-pipeline optimizer; the twin pins the generic
        /// strategy (<c>ThrowIfAsyncStrategyPinningViolated</c>) and never attempts it.</summary>
        OptimizerPinned = 1 << 1,

        /// <summary>The twin requires the run's cache to implement <c>IAsyncZeroArgPropertyResultCache</c>, or to offer
        /// the twins its view (a synchronous run's long fold continued on the heap, <c>FoldTrampoline</c>), and throws
        /// otherwise.</summary>
        AsyncCacheGuard = 1 << 2,

        /// <summary>META-S3-0b: what the shared synchronous code would resolve or demand synchronously is awaited first
        /// through its asynchronous adapter (<c>ResolveAsync</c>, <c>ProjectCellCallableAsync</c>, an awaited
        /// pre-demand), so the shared code finds it settled.</summary>
        ResolveAdapter = 1 << 3,

        /// <summary>A deliberately different walk: the loader's load-bearing async walk (memo keyed by expression and
        /// depth, load-free children routed back to the synchronous walk) versus the load-free synchronous one.</summary>
        DistinctWalk = 1 << 4,

        /// <summary>Twin-only <c>if (StackHop.HostStackIsLow()) await new StackHop();</c> before a shared probe
        /// (Q-09a; <c>StackHop</c>). The synchronous family never hops. In a flag body the hop is guarded by the
        /// flag (<c>if (asynchronous &amp;&amp; StackHop.HostStackIsLow()) …</c>: the loop entry,
        /// <c>Evaluator.EvalNeedLoop</c>, or the awaiter a <c>reduce</c> step takes before its invocation,
        /// <c>Evaluator.ReduceFold.StepStackHop</c>, shared by the step and its twin), a branch point
        /// of this class. A second flag-guarded hop has another condition: an invocation's
        /// preparation frame is installed only where the execution context flows
        /// (<c>Evaluator.EnterInvocationFrameFlow</c>, called identically by both <c>RunPlanPreparation</c> twins;
        /// <c>EvaluationFlow</c>).</summary>
        StackHop = 1 << 5,

        /// <summary>The twin family mirrors only the COUNTED family (AGENTS.md): where the synchronous side calls the
        /// plain evaluator (<c>Eval</c>, <c>EvalSequenceCallbackCall</c>, …), the twin calls the counted twin and
        /// projects its value.</summary>
        CountedOnly = 1 << 6,

        /// <summary>A C# limit of async methods: no <c>ref</c>/<c>in</c>/<c>out</c> parameter and no <c>ref</c> local
        /// across an await (the twin indexes, or returns the out value inside its result); delegate and result types
        /// are <c>ValueTask</c>-shaped; an expression form whose parts must await (a switch expression over lambdas)
        /// is restated as statements.</summary>
        AsyncLanguage = 1 << 7,

        /// <summary>The twin calls the ONE <c>bool asynchronous</c> body where the synchronous side calls its
        /// synchronous specialization (or the pair itself is the flag body and its specialization). The
        /// marked specializations are compared as pairs, and <see cref="FlagBranchPoints"/> pins the flag
        /// body's branches. Unmarked specializations remain covered only by the outcome corpora.</summary>
        FlagBody = 1 << 8,

        /// <summary>A deferred module region is materialized by awaiting the downloader
        /// (<c>MaterializeRequiredRegion</c>); the synchronous side only reads an already-materialized body
        /// (synchronous entry points reject trees carrying a deferred region).</summary>
        DeferredRegion = 1 << 9,

        /// <summary>An entry point's capability routing: the asynchronous entry accepts what the synchronous one
        /// rejects (asynchronous host operations, the module downloader) and decides the route once.</summary>
        EntryRoute = 1 << 10,

        /// <summary>A concurrent plan preparation is joined by awaiting its waiters, where the synchronous side
        /// blocks on them.</summary>
        AwaitedJoin = 1 << 11,

        /// <summary>The ONE guarded <c>EvalCountedAsync</c> case that awaits an asynchronous host operation.</summary>
        AsyncHostOperation = 1 << 12,

        /// <summary>The same computation spelled through an equivalent one-line helper on one side and inline on the
        /// other (<c>ProjectCountedValue</c>, <c>CountValue</c>, a forwarding wrapper), usually because the
        /// helper takes a result the twin only has after an await.</summary>
        InlinedHelper = 1 << 13,

        /// <summary>The twin delegates a case proven not to suspend to the synchronous member itself.</summary>
        SyncDelegated = 1 << 14,

        /// <summary>Branch points only: <c>asynchronous ? await XAsync(..) : X(..)</c> (or the statement form) whose
        /// arms normalize identically — checked mechanically.</summary>
        AwaitOrCall = 1 << 15,
    }

    /// <summary>The classes the November 2026 audit named (plus the StackHop landing it anticipated).</summary>
    internal const TwinDifference AuditClasses =
        TwinDifference.FrameSplit | TwinDifference.OptimizerPinned | TwinDifference.AsyncCacheGuard
        | TwinDifference.ResolveAdapter | TwinDifference.DistinctWalk | TwinDifference.StackHop;

    internal sealed record AllowedDifference(string Twin, string Counterpart, string Hash, TwinDifference Classes, string Reason)
    {
        public string Id => Twin + " ~ " + Counterpart;
    }

    /// <summary>Why a marker forms no compared pair.</summary>
    internal enum UnpairedMarkerClass
    {
        /// <summary>Documentation that names the convention itself.</summary>
        ProseMention,

        /// <summary>A comment about one arm or step of a member, restating or qualifying its pair.</summary>
        Fragment,

        /// <summary>A marker relating two members of the SAME family (synchronous ↔ synchronous, async ↔ async).</summary>
        Analog,
    }

    internal sealed record UnpairedMarkerEntry(string Key, UnpairedMarkerClass Class, string Reason);

    internal sealed record FlagBranchEntry(string Method, int Ordinal, string Hash, TwinDifference Class, string Reason)
    {
        public string Key => Method + " #" + Ordinal;
    }

    /// <summary>The allowlist size; it may only go DOWN (see the class documentation).</summary>
    internal const int AllowlistCeiling = 66;

    /// <summary>The owner-accepted number of entries with a class beyond <see cref="AuditClasses"/>; it may only go DOWN.</summary>
    internal const int AcceptedBeyondAuditCeiling = 32;

    private const TwinDifference FS = TwinDifference.FrameSplit;
    private const TwinDifference OP = TwinDifference.OptimizerPinned;
    private const TwinDifference ACG = TwinDifference.AsyncCacheGuard;
    private const TwinDifference RA = TwinDifference.ResolveAdapter;
    private const TwinDifference DW = TwinDifference.DistinctWalk;
    private const TwinDifference SH = TwinDifference.StackHop;
    private const TwinDifference CO = TwinDifference.CountedOnly;
    private const TwinDifference AL = TwinDifference.AsyncLanguage;
    private const TwinDifference FB = TwinDifference.FlagBody;
    private const TwinDifference DR = TwinDifference.DeferredRegion;
    private const TwinDifference ER = TwinDifference.EntryRoute;
    private const TwinDifference AJ = TwinDifference.AwaitedJoin;
    private const TwinDifference AH = TwinDifference.AsyncHostOperation;
    private const TwinDifference IH = TwinDifference.InlinedHelper;
    private const TwinDifference SD = TwinDifference.SyncDelegated;
    private const TwinDifference AC = TwinDifference.AwaitOrCall;

    private const string HopReason = "the twin-only stack hop before the shared invocation/argument probe";

    /// <summary>Every pair that differs after normalization, pinned exactly. Ordered by marker file and line.</summary>
    internal static readonly AllowedDifference[] Allowlist =
    [
        new("RunScopedDeconstructionBindingCache.GetOrBindAsync", "RunScopedDeconstructionBindingCache.GetOrBind", "cbd81b217c97a190", AL,
            "the binding delegate returns ValueTask<...>"),
        new("ZeroArgPropertyPublications.InvokeAsync", "ZeroArgPropertyPublications.Invoke", "9cb01c3fcd70c73c", AL,
            "no out parameter on an async member: publication is not reported back, so the early return becomes one conditional"),
        new("ZeroArgPropertyPublications.EvaluateMissAsync", "ZeroArgPropertyPublications.EvaluateMiss", "b3d3b564827915ff", AL,
            "no out parameter on an async member: the published flag assignments are gone; the delegate returns ValueTask<...>"),
        new("Evaluator.EvalDotAlgorithmValueReceiverCountedAsync", "Evaluator.EvalDotAlgorithmValueReceiverCounted", "64cdf3bd98ab9170", CO,
            "the plain Eval of the receiver is the counted twin's .Value"),
        new("Evaluator.ApplyAlgorithmIntrinsicAsync", "Evaluator.ApplyAlgorithmIntrinsic", "61c39aef060f4523", RA,
            "the callee cell's callable is projected through ProjectCellCallableAsync"),
        new("Evaluator.EvalAlgorithmCalleeCallCountedAsync", "Evaluator.EvalAlgorithmCalleeCallCounted", "7c8dc12068e3b9e9", FS | OP | RA,
            "the member arm stays inline (sync: EvalDeclaredAlgorithmMemberCallCounted, which also attempts the sequence pipeline); the member is resolved and the cell projected through the async adapters"),
        new("Evaluator.EvalAlgorithmReceiverAsync", "Evaluator.EvalAlgorithmReceiver", "2b12c3aa2cfca574", AL | CO,
            "the out structural flag comes back inside the navigated result; the plain Eval is the counted twin's .Value"),
        new("Evaluator.TryEvalLinkValueAsync", "Evaluator.TryEvalLinkValue", "ad37915e7491f632", FS | RA,
            "the route decision goes through ResolveAsync; LinkedCalleeValue's body stays inline"),
        new("Evaluator.NormalizeTopLevelBindingAsync", "Evaluator.NormalizeTopLevelBinding", "324d558f23dd71a3", AL,
            "a synchronously completed result is wrapped in new ValueTask<...>(...)"),
        new("Evaluator.EvalAliasMemberCountedAsync", "Evaluator.EvalAliasMemberCounted", "f69d41094bf4d0e4", FS,
            "the out-of-line EvalBoundMemberCallCounted is its body EvalOriginCallCounted(CalleeOrigin.Bound(...), ..., CallDiagnosticName.FromKnown(name))"),
        new("Evaluator.EvalAliasDotStringLexicalReceiverAsync", "Evaluator.EvalAliasDotStringLexicalReceiver", "d6f787076c0b5369", SH, HopReason),
        new("Evaluator.EvalTopLevelZeroArgPropertyCountedAsync", "Evaluator.EvalTopLevelZeroArgPropertyCounted", "d0924c6fd1535640", FS,
            "the sync hot path bypasses ReadValueBindingCounted for a non-alias, non-carrier binding (exactly its EvalZeroArgPropertyAccessCounted arm)"),
        new("Evaluator.EvalParamCountedAsync", "Evaluator.EvalParamCounted", "95ece2c492f52c3b", SD,
            "only the need-cell tier awaits; every other tier is a lookup the synchronous EvalParamCounted reads"),
        new("Evaluator.EvalCountedAsync", "Evaluator.EvalCounted", "4a2c9b0e6541cf2e", FS | AH,
            "the Param/Resolve arms read expr.Span instead of the EvalParamCountedOf/EvalResolveCountedOf leaf frames; the guarded asynchronous host-operation case"),
        new("Evaluator.EvalResolveCountedAsync", "Evaluator.EvalResolveCounted", "1b39417654bf883e", FS | IH,
            "the sync hot path bypasses ReadValueBindingCounted for a non-alias, non-carrier binding; CountValue is the inline new CountedResult(v, v.ValueCount())"),
        new("Evaluator.EvalExpressionSpineCountedAsync", "Evaluator.EvalExpressionSpineCounted", "fb1ae15fdd397f48", AL | CO | FB | FS,
            "no ref local across an await (frames[top] for ref frame/unwound; the null-forgiving ! on frames[top].ListItems, which flow analysis cannot track through an array element); FormSelectionSupplySync/SelectArgumentViewSync/SelectLazyPositionSync are the flag body FormSelectionSupply and the out-of-line selections (an argument view's cell; a position of a list evaluated on demand, read through the flag body ReadLazyPosition) inline; plain Eval leaves are counted .Value; the invariant message names the twin"),
        new("Evaluator.EvalAlgOutputPreparedCoreAsync", "Evaluator.EvalAlgOutputPreparedCore", "2fc68e5da198dd65", DR,
            "a deferred region is materialized by MaterializeRequiredRegionAsync"),
        new("Evaluator.EvalOutputRowsPreparedCoreAsync", "Evaluator.EvalOutputRowsPreparedCore", "d4b66d9b465e1b5e", SH, HopReason),
        new("Evaluator.EvalCaptureValueAsync", "Evaluator.EvalCaptureValue", "6c99463f11b8d9c4", IH,
            "ProjectCountedValue(...) is applied inline to the awaited counted result"),
        new("Evaluator.EvalAlgOutputValueAsync", "Evaluator.EvalAlgOutputCore", "57450608c284d8c9", IH,
            "ProjectCountedValue(EvalAlgOutputCountedCore(...)) is the prepared core's counted value projected inline"),
        new("Evaluator.EvalExplicitSequenceValueRowSlotsAsync", "Evaluator.EvalExplicitSequenceValueRowSlots", "d4b66d9b465e1b5e", SH, HopReason),
        new("Evaluator.EvalZeroArgumentDemandOutputAsync", "Evaluator.EvalZeroArgumentDemandOutput", "d9dc9a5342124686", IH,
            "ProjectCountedValue(EvalBoundZeroArgumentDemandOutputCounted(...)) is the projecting helper ProjectBoundZeroArgumentDemandValueAsync"),
        new("Evaluator.GetOrEvaluateZeroArgPropertyResultAsync", "Evaluator.GetOrEvaluateZeroArgPropertyResult", "bf2d3c3f7cdf2749", SH, HopReason),
        new("Evaluator.GetOrEvaluateZeroArgPropertyResultCoreAsync", "Evaluator.GetOrEvaluateZeroArgPropertyResultCore", "d983542a2392d390", ACG,
            "the shared PropertyAccessCache must be an IAsyncZeroArgPropertyResultCache"),
        new("Evaluator.EvalResolvedAlgOutputForValueDemandAsync", "Evaluator.EvalResolvedAlgOutputForValueDemand", "bc79101f8c8e0ddd", SH, HopReason),
        new("Evaluator.EvalCallCountedExprAsync", "Evaluator.EvalCallCountedExpr", "75f689764a906e0e", OP | FS,
            "no sequence-pipeline attempt (strategy pin asserted instead); the out-of-line EvalWrittenCalleeCallCounted is its body EvalOriginCallCounted(CalleeOrigin.Written(...))"),
        new("Evaluator.EvalResolvedCallCountedAsync", "Evaluator.EvalResolvedCallCounted", "ea3891606b59e41f", FB,
            "ResolveArgAlgsWithSequenceSpread is the flag body ResolveNeedSupply(asynchronous: true)"),
        new("Evaluator.EvalUserCallCountedAsync", "Evaluator.EvalUserCallCounted", "0b0e833d5882c87d", SH, HopReason),
        new("Evaluator.EvalConditionalCallCountedAsync", "Evaluator.EvalConditionalCallCounted", "0b0e833d5882c87d", SH, HopReason),
        new("Evaluator.EvalResolvedArgumentValueAsync", "Evaluator.EvalResolvedArgument", "6c99463f11b8d9c4", IH,
            "ProjectCountedValue(...) is applied inline to the awaited counted result"),
        new("Evaluator.EvalArgumentAlgOutputCountedAsync", "Evaluator.EvalArgumentAlgOutputCounted", "bc79101f8c8e0ddd", SH, HopReason),
        new("Evaluator.BindSequenceBuiltinArgumentsAsync", "Evaluator.BindSequenceBuiltinArguments", "11f07d2a170812e8", IH | RA,
            "BindSequenceBuiltinCollectionValue's body (demand, then SequenceBuiltinValueDemandError ?? BadArity) is inline; the retained collector's slice is read through RetainedCellSliceAsync(cell, ctx), the ResolveAsync adapter of RetainedCellSlice"),
        new("Evaluator.PrepareSequenceBuiltinControlsAsync", "Evaluator.PrepareSequenceBuiltinControls", "01ebd0bb09207b20", RA,
            "a VALUE control that binding demands is demanded asynchronously before the shared synchronous preparer reads it (a deferred control, reduce's initial, is demanded by neither side: the shared preparer retains it)"),
        new("Evaluator.ApplyBuiltinCountedSequenceAsync", "Evaluator.ApplyBuiltinCountedSequence", "18200556ec158c22", RA,
            "algorithm controls are projected through ExpectPreparedAlgorithmSuffixArgAsync(..., ctx)"),
        new("Evaluator.EvalResolvedCallbackCallCountedAsync", "Evaluator.EvalResolvedCallbackCallCounted", "380c1a7f233a624c", SH, HopReason),
        new("Evaluator.EvalFilterPredicateTruthAsync", "Evaluator.EvalFilterPredicateTruth", "2e702caf4ca5d95a", CO,
            "the plain EvalSequenceCallbackCall is the counted twin with its value projected"),
        new("Evaluator.EvalDotCallCountedAsync", "Evaluator.EvalDotCallCounted", "73dcfcbd46966357", OP | AL | FS | CO,
            "no sequence-pipeline attempt; the out receiver flag comes back in the navigated result; EvalBoundMemberCallCounted is inline; the plain Eval of a value receiver is counted .Value"),
        new("Evaluator.EvalDotArgumentsValueReceiverCountedAsync", "Evaluator.EvalDotArgumentsValueReceiverCounted", "aeb13add7645de9f", CO,
            "the plain Eval of the receiver is the counted twin's .Value"),
        new("Evaluator.EvalDotInvokeValueReceiverCountedAsync", "Evaluator.EvalDotInvokeValueReceiverCounted", "3418cdb816113516", CO,
            "the plain Eval of the receiver is the counted twin's .Value"),
        new("Evaluator.CallLexicalWithReceiverCountedAsync", "Evaluator.CallLexicalWithReceiverCounted", "89bafbd222481d7f", RA,
            "the fallback callee lookup goes through ResolveAsync"),
        new("Evaluator.CallLexicalFallbackCalleeWithReceiverCountedAsync", "Evaluator.CallLexicalFallbackCalleeWithReceiverCounted", "07483a53ddc2f0a7", RA,
            "the fallback ResolveAlg goes through ResolveAsync"),
        new("Evaluator.EvalDotStringReceiverAlgOutputAsync", "Evaluator.EvalDotStringReceiverAlgOutput", "b1c84d88a1a5ebd5", FS,
            "the Param arm reads target.Span instead of the EvalParamCountedOf leaf frame"),
        new("Evaluator.EvalDotStringLexicalPropertyReceiverAsync", "Evaluator.EvalDotStringLexicalPropertyReceiver", "2317fceb0f0e1e77", SH | RA,
            "LookupLexicalRaw goes through ResolveAsync; " + HopReason),
        new("Evaluator.EvalDotStringStructuralMemberReceiverAsync", "Evaluator.EvalDotStringStructuralMemberReceiver", "6cc4e6b0a6a90485", SH | AL,
            "the out container comes back as the navigated result's Receiver; " + HopReason),
        new("Evaluator.EvalSequenceConstructCountedAsync", "Evaluator.EvalSequenceConstructCounted", "db75429ce86744ca", CO,
            "the plain Eval of a streamed leaf is the counted twin's .Value"),
        new("Evaluator.EvalSequenceSpreadOperandValueAsync", "Evaluator.EvalSequenceSpreadOperandValue", "942cf72b12a38ad1", CO,
            "the plain Eval of the operand is the counted twin with its value projected"),
        new("Evaluator.PlanRouteOfAsync", "Evaluator.PlanRouteOf", "e534b937c5a3fcf3", RA | AL,
            "the route is computed and published by the synchronous PlanRouteOf inside ResolveAsync; settled routes return ValueTask.FromResult"),
        new("Evaluator.ProjectPlannedAlgorithmCalleeAsync", "Evaluator.ProjectPlannedAlgorithmCallee", "efd281ab500f81d4", RA,
            "the callee cell's callable is projected through ProjectCellCallableAsync"),
        new("Evaluator.EvalPlannedCallCountedAsync", "Evaluator.EvalPlannedCallCounted", "ea933baffe5bd1a7", OP | FS,
            "strategy pin asserted; EvalPlannedAlgorithmCalleeCallCounted's body (projection, failure report, planned dispatch) is inline"),
        new("Evaluator.DispatchPlannedDotAsync", "Evaluator.DispatchPlannedDotCounted", "cd2e50b33c7d4271", RA,
            "the stored fallback identity's callee lookups go through ResolveAsync"),
        new("Evaluator.DispatchPlannedAsync", "Evaluator.DispatchPlannedCounted", "a9529f6698a6a52f", SH, HopReason),
        new("Evaluator.DispatchPlannedUserAsync", "Evaluator.DispatchPlannedUserCounted", "f50c64803cb8a749", SH, HopReason),
        new("Evaluator.PreparePlanSupplyAsync", "Evaluator.PreparePlanSupplyCounted", "6ab7f0d800774d04", AJ,
            "a concurrent preparation is joined by awaiting its waiters (reentrancy is a DemandCycle) instead of JoinPlanPreparationCounted's blocking join"),
        new("Evaluator.SelectedBranchBodyAsync", "Evaluator.SelectedBranchBody", "196591982fbfe597", DR,
            "a deferred region is materialized by MaterializeRequiredRegionAsync"),
        new("Evaluator.BindFlatLiteralHeadAsync", "Evaluator.BindFlatLiteralHead", "5a12adf396077700", AL,
            "no in parameter on an async member"),
        new("Evaluator.BindNeedFamilySupply", "Evaluator.BindNeedFamilySupplyCounted", "9c48563b1f2ad854", AL,
            "the flat-literal head is bound without in ctx, and the binder-or-literal-head conditional is restated as an if/else with one await site per arm"),
        new("Evaluator.EvalPublishedZeroSupplyInvocationAsync", "Evaluator.EvalPublishedZeroSupplyInvocation", "25ad9be885474979", ACG | AL,
            "the shared PropertyAccessCache must be an IAsyncZeroArgPropertyResultCache; the delegate returns ValueTask<...>"),
        new("Evaluator.EvalOriginUserCallCountedAsync", "Evaluator.EvalOriginUserCallCounted", "6dfac2030aaf9993", SH, HopReason),
        new("Evaluator.EvalOriginFamilyCallCountedAsync", "Evaluator.EvalOriginFamilyCallCounted", "bf2d3c3f7cdf2749", SH, HopReason),
        new("FrontEndPipeline.ProcessAsync(string, RunOptions?, PatternComparisonObservations?, FrontEndTraversalObservations?)",
            "FrontEndPipeline.Process(string, RunOptions?, PatternComparisonObservations?, FrontEndTraversalObservations?)", "f7a108499ab61e4d", ER,
            "the synchronous entry rejects a downloader; the asynchronous one elaborates modules with it"),
        new("KatLangEngine.RunAsync", "KatLangEngine.Run", "8ac701d46fdee082", ER,
            "the synchronous entry rejects asynchronous host operations; the asynchronous one decides the tree route once, observing the evaluation token as the synchronous route's guard does, and pairs the cache with it"),
        new("ModuleLoader.ProcessAlgorithmAsync", "ModuleLoader.ProcessAlgorithm", "980aaac8c5d757ee", DW,
            "the ordinary-body part of ProcessAlgorithm on the load-bearing async walk"),
        new("ModuleLoader.ProcessConditionalAlgorithmAsync", "ModuleLoader.ProcessAlgorithm", "e730fe8b8ab2e2ce", DW,
            "the clause-family arm of ProcessAlgorithm on the load-bearing async walk"),
        new("ModuleLoader.RouteComparisonAsync", "ModuleLoader.ProcessComparison", "175724d04148c431", DW,
            "the link loop routes each operand and awaits, keeping the list instance when nothing changed"),
        new("ModuleLoader.RouteSelectionAsync", "ModuleLoader.ProcessSelection", "62693119b807b7ea", DW,
            "children route through RouteExprAsync instead of ProcessExpr"),
        new("ModuleLoader.ProcessExprAsync", "ModuleLoader.ProcessExpr", "51b3902023d354d0", DW,
            "load-bearing vs load-free walk; memo keyed by (expr, depth) vs expr; LINQ projections are explicit loops so rewrites can await"),
    ];

    /// <summary>Every marker that forms no compared pair, by exact key, with its reason.</summary>
    internal static readonly UnpairedMarkerEntry[] UnpairedMarkers =
    [
        new("dotnet/src/KatLang/Evaluator.AlgorithmProjection.cs :: Evaluator.EvalAlgorithmCalleeCallCountedAsync :: MIRROR OF the synchronous member arm (the async strategy pins fusion off).",
            UnpairedMarkerClass.Fragment, "qualifies the member arm of its pinned pair (FrameSplit/OptimizerPinned)"),
        new("dotnet/src/KatLang/Evaluator.Aliases.cs :: Evaluator.AliasChaseMachine.NavigateRoute :: MIRROR OF that navigation, its head", UnpairedMarkerClass.Analog,
            "the synchronous route chase mirrors ResolveDotReceiver's synchronous navigation"),
        new("dotnet/src/KatLang/Evaluator.Async.cs :: type Evaluator :: MIRROR OF ...</c>) and", UnpairedMarkerClass.ProseMention,
            "the twin family's documentation names the marker convention"),
        new("dotnet/src/KatLang/Evaluator.Async.cs :: Evaluator.EvalCountedAsync :: MIRROR OF EvalCounted's compiler-exhaustive switch expression, case for case. A",
            UnpairedMarkerClass.Fragment, "restates the declaration marker of the EvalCountedAsync ~ EvalCounted pair for its switch"),
        new("dotnet/src/KatLang/Evaluator.Async.cs :: Evaluator.EvalDotStringReceiverAlgOutputAsync :: MIRROR OF the synchronous twin: the ordinary value-position parameter read (a",
            UnpairedMarkerClass.Fragment, "explains one arm of its pinned pair (FrameSplit)"),
        new("dotnet/src/KatLang/Evaluator.Async.cs :: Evaluator.EvalSequenceConstructCountedAsync :: MIRROR OF the sync join: stream shared-AST occurrences and bound plain leaves too.",
            UnpairedMarkerClass.Fragment, "explains one step of its pinned pair (CountedOnly)"),
        new("dotnet/src/KatLang/Evaluator.CallPlans.cs :: Evaluator.DispatchPlannedDotCounted :: MIRROR OF the member arm of EvalDotCallCounted: an alias member is called as its",
            UnpairedMarkerClass.Analog, "the synchronous planned dispatch mirrors an arm of the synchronous unplanned dot call"),
        new("dotnet/src/KatLang/Evaluator.CallPlans.cs :: Evaluator.DispatchPlannedDotCounted :: MIRROR OF CallLexicalWithReceiverCounted: the stored fallback identity decides the channel.",
            UnpairedMarkerClass.Analog, "the synchronous planned dispatch mirrors the synchronous lexical receiver call"),
        new("dotnet/src/KatLang/ModuleLoader.cs :: ModuleLoader.RouteExprAsync :: MIRROR OF <see cref=\"RouteAlgorithmAsync\"/> for expression children.",
            UnpairedMarkerClass.Analog, "two async routers of the loader, one per child kind"),
    ];

    /// <summary>Every behavior-selecting read of a <c>bool asynchronous</c> flag, with its reason.</summary>
    internal static readonly FlagBranchEntry[] FlagBranchPoints =
    [
        new("Evaluator.InvocationPlan.PrepareSupply", 0, "15f43bca98b410b5", AC, "the plan route"),
        new("Evaluator.InvocationPlan.PrepareSupply", 1, "fe19b0079f3927da", AC, "the plan supply"),
        new("Evaluator.EnterInvocationFrameFlow", 0, "d04513a7a03f4f62", SH, "the preparation awaits the hop directly when flow is suppressed; the synchronous path skips it"),
        new("Evaluator.EvalMetaLoop", 0, "711e29be2df977ac", AC, "the captured call's sourced initial state"),
        new("Evaluator.FormSpreadSupplySlot", 0, "a3fb71e714ecc550", AC, "the written collector slice"),
        new("Evaluator.FormSpreadSupplySlot", 1, "77f3dfbbf300143d", AC, "the spread operand value"),
        new("Evaluator.FormSpreadSupplySlot", 2, "01da8d2ec5ad13d5", AC, "the argument view's cells"),
        new("Evaluator.DemandCell", 0, "dcef548fb3a0d00b", AL, "the synchronous arm wraps its completed demand in a ValueTask"),
        new("Evaluator.BindAcceptedNeedPatterns", 0, "95ec2ee7f7ec8e90", AC, "the cell's runtime callable"),
        new("Evaluator.BindAcceptedNeedPatterns", 1, "d775df5d15a0b8bc", AC, "a cell's value demand"),
        new("Evaluator.InvokeLoopStepSupply", 0, "91e8f32c0ef5602b", AC, "the family step's dispatch"),
        new("Evaluator.InvokeLoopStepSupply", 1, "0c4a64796b4f56f6", AC, "the builtin step"),
        new("Evaluator.InvokeLoopStepSupply", 2, "08985556eb02434b", AC, "the alias step's target"),
        new("Evaluator.ReadLoopStepRows", 0, "ccc8e5cf06970882", AC, "the while verdict rows"),
        new("Evaluator.ReadLoopStepRows", 1, "c71d04fc631fff1f", AC, "the output rows"),
        new("Evaluator.EvalNeedCallbackSupply", 0, "84910034d2a98b92", AL, "both callback drivers restore the host context: the twin has its own method builder; the plain driver runs inside a synchronous-completion context boundary"),
        new("Evaluator.EvalNeedLoop", 0, "7981bb5f399044bc", SH, "the twin-only stack hop before the shared loop-entry probe (EvaluationBudget.TryAdmitLoopEntry); the synchronous run never hops"),
        new("Evaluator.EvalNeedLoop", 1, "c613b240dc6307dc", RA, "the asynchronous step projection takes ctx for its adapter"),
        new("Evaluator.EvalNeedLoop", 2, "83cadc7942d61e81", AC, "the alias step's target"),
        new("Evaluator.EvalNeedLoop", 3, "70563d5fe6206b30", OP, "only the synchronous run attempts the loop optimizer (and asserts the planner took a user step); its handover continues, synchronously, in the one round kernel"),
        new("Evaluator.EvalNeedLoop", 4, "c3141958221e536e", OP, "the loop diagnostics report the pinned strategy for the asynchronous run"),
        new("Evaluator.EvalReduceCounted", 0, "3e74ef431c3c8c07", AC, "the start of a fold whose initial argument has no cell (a hand-built plan): demanded before the fold"),
        new("Evaluator.ReduceFold.Last", 0, "93cb46627813128f", AC, "the last step: the plain synchronous step (no state machine stays on the host stack while it is suspended) or its twin"),
        new("Evaluator.ReduceFold.StepStackHop", 0, "880b599e7e11d7fb", SH, "the awaiter the twin takes in its step before charging the invocation; the synchronous run never hops"),
        new("Evaluator.ReduceFold.Evaluate", 0, "44913f0c39a63a2a", AC, "the deferred initial accumulator's value demand"),
        new("Evaluator.ReduceFold.Evaluate", 1, "9a301850168d6c9b", AC, "the preceding step, within the accumulator demand's host context boundary"),
        new("Evaluator.MappedList.Evaluate", 0, "7981bb5f399044bc", SH, "the twin-only stack hop before a mapped position's step (it reads the position below it, then invokes the mapper); the synchronous run never hops"),
        new("Evaluator.MappedList.Evaluate", 1, "7eac9c5da48f2140", RA, "the asynchronous mapper projection takes ctx for its adapter"),
        new("Evaluator.MappedList.Evaluate", 2, "bf2ddaef265fd6c3", AC, "the mapper's callback call"),
        new("Evaluator.FilteredList.DiscoverScans", 0, "7981bb5f399044bc", SH, "the twin-only stack hop before a discovery that drives every stacked scan below it from one frame; the synchronous run never hops"),
        new("Evaluator.FilteredList.Judge", 0, "7981bb5f399044bc", SH, "the twin-only stack hop before a candidate's verdict (it reads the source position, then invokes the predicate); the synchronous run never hops"),
        new("Evaluator.FilteredList.Judge", 1, "e8fbcc47ff43b7ab", RA, "the asynchronous predicate projection takes ctx for its adapter"),
        new("Evaluator.FilteredList.Judge", 2, "b419b550f6d45c50", AC, "the predicate's truth"),
    ];

    /// <summary>
    /// Every pair that normalizes IDENTICALLY, pinned by identity (ordered by marker file and line). Without this list a
    /// marker deleted or reworded into prose would silently drop its pair from the guard. A new twin's pair is added here;
    /// a listed pair may leave only when the twin itself is deleted, or move to <see cref="Allowlist"/> never (the
    /// allowlist only shrinks).
    /// </summary>
    internal static readonly string[] IdenticalPairs =
    [
        "Evaluator.EvalInvocationReceiverAsync ~ Evaluator.EvalInvocationReceiver",
        "Evaluator.EvalDotAlgorithmIntrinsicCountedAsync ~ Evaluator.EvalDotAlgorithmIntrinsicCounted",
        "Evaluator.EvalRuntimeAliasValueCountedAsync ~ Evaluator.EvalRuntimeAliasValueCounted",
        "Evaluator.RetainedCellValueAsync ~ Evaluator.RetainedCellValue",
        "Evaluator.JudgedRetainedCellValueAsync ~ Evaluator.JudgedRetainedCellValue",
        "Evaluator.ReadAliasTerminalCountedAsync ~ Evaluator.ReadAliasTerminalCounted",
        "Evaluator.ReadValueBindingCountedAsync ~ Evaluator.ReadValueBindingCounted",
        "Evaluator.EvalInlineAliasValueAsync ~ Evaluator.EvalInlineAliasValue",
        "Evaluator.EvalAliasSpreadOperandValueAsync ~ Evaluator.EvalAliasSpreadOperandValue",
        "Evaluator.EvalAliasCallCountedAsync ~ Evaluator.EvalAliasCallCounted",
        "Evaluator.EvalAliasCallbackCallCountedAsync ~ Evaluator.EvalAliasCallbackCallCounted",
        "Evaluator.EvalAliasZeroArgumentDemandCountedAsync ~ Evaluator.EvalAliasZeroArgumentDemandCounted",
        "Evaluator.EvalStructuralMemberReadAsync ~ Evaluator.EvalStructuralMemberRead",
        "Evaluator.EvalAliasDotStringCountedAsync ~ Evaluator.EvalAliasDotStringCounted",
        "Evaluator.EvalRootProgramCountedAsync ~ Evaluator.EvalRootProgramCounted",
        "Evaluator.EvalWiredRootProgramCountedAsync ~ Evaluator.EvalWiredRootProgramCounted",
        "Evaluator.EvalRootProgramCountedWithTopLevelPropertiesAsync ~ Evaluator.EvalRootProgramCountedWithTopLevelProperties",
        "Evaluator.LookupNativeArgumentAsync ~ Evaluator.LookupNativeArgument",
        "Evaluator.ApplyMathNativeCallAsync ~ Evaluator.ApplyMathNativeCall",
        "Evaluator.CollectHostOperationArgumentsAsync ~ Evaluator.CollectHostOperationArguments",
        "Evaluator.InvokeSynchronousHostOperationAsync ~ Evaluator.InvokeSynchronousHostOperation",
        "Evaluator.EvalNativeCallAsync ~ Evaluator.EvalNativeCall",
        "Evaluator.EvalAlgorithmExprValueAsync ~ Evaluator.EvalAlgorithmExprValue",
        "Evaluator.EvalOutputRowsPreparedAsync ~ Evaluator.EvalOutputRowsPrepared",
        "Evaluator.EvalCapturePreparedCoreAsync ~ Evaluator.EvalCapturePreparedCore",
        "Evaluator.EvalCaptureCountedCoreAsync ~ Evaluator.EvalCaptureCountedCore",
        "Evaluator.EvalAlgOutputCountedCoreAsync ~ Evaluator.EvalAlgOutputCountedCore",
        "Evaluator.EvalAlgOutputSlotsAsync ~ Evaluator.EvalAlgOutputSlots",
        "Evaluator.EvalWhileVerdictSlotsAsync ~ Evaluator.EvalWhileVerdictSlots",
        "Evaluator.EvalExplicitSequenceValueItemsAsync ~ Evaluator.EvalExplicitSequenceValueItems",
        "Evaluator.EvalExplicitSequenceValueExprSlotsAsync ~ Evaluator.EvalExplicitSequenceValueExprSlots",
        "Evaluator.EvalZeroArgumentDemandOutputCountedAsync ~ Evaluator.EvalZeroArgumentDemandOutputCounted",
        "Evaluator.EvalBoundZeroArgumentDemandOutputCountedAsync ~ Evaluator.EvalBoundZeroArgumentDemandOutputCounted",
        "Evaluator.EvaluateZeroArgPropertyResultAsync ~ Evaluator.EvaluateZeroArgPropertyResult",
        "Evaluator.EvaluateDetachedZeroArgPropertyResultAsync ~ Evaluator.EvaluateDetachedZeroArgPropertyResult",
        "Evaluator.EvalPropertyOwnerBodyCountedAsync ~ Evaluator.EvalPropertyOwnerBodyCounted",
        "Evaluator.EvalCollectingPropertyOwnerBodyCountedAsync ~ Evaluator.EvalCollectingPropertyOwnerBodyCounted",
        "Evaluator.EvalZeroArgPropertyAccessCountedAsync(PropertyDeclaringOwner, Property, ZeroArgPropertyAccessKind, Algorithm, EvalCtx, ValEnv) ~ Evaluator.EvalZeroArgPropertyAccessCounted(PropertyDeclaringOwner, Property, ZeroArgPropertyAccessKind, Algorithm, EvalCtx, ValEnv)",
        "Evaluator.EvalZeroArgPropertyAccessCountedAsync(ResolvedLexicalProperty, EvalCtx, ValEnv) ~ Evaluator.EvalZeroArgPropertyAccessCounted(ResolvedLexicalProperty, EvalCtx, ValEnv)",
        "Evaluator.EvalUserCallCountedCoreAsync ~ Evaluator.EvalUserCallCountedCore",
        "Evaluator.TryProjectSharedDeconstructionTargetAsync ~ Evaluator.TryProjectSharedDeconstructionTarget",
        "Evaluator.EvalConditionalCallCountedCoreAsync ~ Evaluator.EvalConditionalCallCountedCore",
        "Evaluator.RejectDotStringIntrinsicArgumentsAsync ~ Evaluator.RejectDotStringIntrinsicArguments",
        "Evaluator.ApplyBuiltinCountedResolvedAsync ~ Evaluator.ApplyBuiltinCountedResolved",
        "Evaluator.EvalBuiltinRangeArgumentsAsync ~ Evaluator.EvalBuiltinRangeArguments",
        "Evaluator.EvalResolvedArgumentCountedAsync ~ Evaluator.EvalResolvedArgumentCounted",
        "Evaluator.DemandSequenceBuiltinCallItemValueAsync ~ Evaluator.DemandSequenceBuiltinCallItemValue",
        "Evaluator.EvalResolvedCallbackCallCountedCoreAsync ~ Evaluator.EvalResolvedCallbackCallCountedCore",
        "Evaluator.EvalSequenceCallbackCallCountedAsync ~ Evaluator.EvalSequenceCallbackCallCounted",
        "Evaluator.EvalReduceInitialAsync ~ Evaluator.EvalReduceInitial",
        "Evaluator.EvalDotReferenceIntrinsicReceiverAsync ~ Evaluator.EvalDotReferenceIntrinsicReceiver",
        "Evaluator.EvalDotArgumentsIntrinsicCountedAsync ~ Evaluator.EvalDotArgumentsIntrinsicCounted",
        "Evaluator.RejectDotInvokeIntrinsicArgumentsAsync ~ Evaluator.RejectDotInvokeIntrinsicArguments",
        "Evaluator.EvalDotInvokeIntrinsicCountedAsync ~ Evaluator.EvalDotInvokeIntrinsicCounted",
        "Evaluator.EvalSequenceSpreadCountedAsync ~ Evaluator.EvalSequenceSpreadCounted",
        "Evaluator.PlanCalleeCellAsync ~ Evaluator.PlanCalleeCell",
        "Evaluator.InvokeCallReferenceValueAsync ~ Evaluator.InvokeCallReferenceValue",
        "Evaluator.PrepareArgumentViewAsync ~ Evaluator.PrepareArgumentView",
        "Evaluator.PrepareLoopInitialStateAsync ~ Evaluator.PrepareLoopInitialState",
        "Evaluator.EvalArgumentViewBuiltinAsync ~ Evaluator.EvalArgumentViewBuiltin",
        "Evaluator.RunPlanPreparationAsync ~ Evaluator.RunPlanPreparationCounted",
        "Evaluator.EvalListLiteralAsync ~ Evaluator.EvalListLiteral",
        "Evaluator.EvalSuspendedValueAsync ~ Evaluator.EvalSuspendedValue",
        "Evaluator.EvalBoundUserBodyCountedAsync ~ Evaluator.EvalBoundUserBodyCounted",
        "Evaluator.EvalNeedUserBody ~ Evaluator.EvalNeedUserBodyCounted",
        "Evaluator.EvalNeedUserSupply ~ Evaluator.EvalNeedUserSupplyCounted",
        "Evaluator.EvalNeedCallbackSupplyAsync ~ Evaluator.EvalNeedCallbackSupplyCounted",
        "Evaluator.EvalNeedFamilyBody ~ Evaluator.EvalNeedFamilyBodyCounted",
        "Evaluator.EvalNeedFamilySupply ~ Evaluator.EvalNeedFamilySupplyCounted",
        "Evaluator.ReduceFold.StepAsync ~ Evaluator.ReduceFold.Step",
        "Evaluator.SelectLiteralRunClauseAsync ~ Evaluator.SelectLiteralRunClause",
        "Evaluator.EvalOriginCallCountedAsync ~ Evaluator.EvalOriginCallCounted",
        "KatLangEngine.EvaluateToAtomsAsync ~ KatLangEngine.EvaluateToAtoms",
    ];

    private static TwinInventory Inventory => TwinNormalization.Current;

    [Fact]
    public void Sources_ParseCleanly_AndTheInventoryIsNotTrivial()
    {
        var inventory = Inventory;
        Assert.True(inventory.ParseErrors.IsEmpty,
            "Roslyn could not parse dotnet/src/KatLang/ (a newer C# feature than the pinned Microsoft.CodeAnalysis.CSharp understands? "
            + "update the package with the SDK): " + string.Join("; ", inventory.ParseErrors.Take(5)));
        Assert.True(inventory.Files.Length >= 100, $"only {inventory.Files.Length} source files found under dotnet/src/KatLang/");
        Assert.True(inventory.Pairs.Length >= 120, $"only {inventory.Pairs.Length} MIRROR OF pairs resolved");
        Assert.True(inventory.Comparisons.Count(static c => c.IsIdentical) >= 50, "fewer than 50 pairs normalize identically");
        Assert.True(inventory.FlagMethods.Length >= 15, $"only {inventory.FlagMethods.Length} `bool asynchronous` methods found");
    }

    /// <summary>
    /// Every marker that names a counterpart resolves to exactly one method, and every marker forms a pair or is
    /// listed (exactly) in <see cref="UnpairedMarkers"/>. A marker naming a missing or ambiguous method is fixed in
    /// the MARKER text (spell the overload's parameter types in its cref), never by listing it.
    /// </summary>
    [Fact]
    public void EveryMarker_ResolvesAndEitherFormsAPairOrIsListed()
    {
        var inventory = Inventory;
        Assert.True(inventory.ResolutionFailures.IsEmpty,
            "MIRROR OF markers that name no single method — correct the marker text (an overload needs its parameter types in the cref): "
            + string.Join("; ", inventory.ResolutionFailures.Select(static f => $"{f.Marker.File}:{f.Marker.Line} {f.Target}: {f.Reason}")));

        var listed = UnpairedMarkers.ToDictionary(static e => e.Key, StringComparer.Ordinal);
        Assert.Equal(UnpairedMarkers.Length, listed.Count);
        Assert.All(UnpairedMarkers, static e => Assert.False(string.IsNullOrWhiteSpace(e.Reason), e.Key));

        // One listed key must stand for exactly one marker, so a second marker with the same words in the same member
        // cannot be absorbed by an existing entry.
        var shared = inventory.UnpairedMarkers.GroupBy(static u => u.Marker.Key, StringComparer.Ordinal).Where(static g => g.Count() > 1).ToList();
        Assert.True(shared.Count == 0,
            "several MIRROR OF markers share one key (same file, member and words); reword one so each is listed on its own: "
            + string.Join("; ", shared.Select(static g => g.Key)));

        var unlisted = inventory.UnpairedMarkers.Where(u => !listed.ContainsKey(u.Marker.Key)).ToList();
        Assert.True(unlisted.Count == 0,
            "MIRROR OF markers that form no compared pair and are not listed in TwinNormalizationTests.UnpairedMarkers. "
            + "A twin's marker belongs on the twin's declaration and must name its synchronous counterpart (`MIRROR OF <see cref=\"X\"/>`); "
            + "list the marker only if it is prose, an arm-level fragment, or relates two members of one family: "
            + string.Join("; ", unlisted.Select(static u => $"{u.Marker.File}:{u.Marker.Line} [{u.Why}] key=\"{u.Marker.Key}\"")));

        var present = inventory.UnpairedMarkers.Select(static u => u.Marker.Key).ToHashSet(StringComparer.Ordinal);
        var stale = UnpairedMarkers.Where(e => !present.Contains(e.Key)).ToList();
        Assert.True(stale.Count == 0,
            "TwinNormalizationTests.UnpairedMarkers lists markers that no longer exist (or now form a pair); remove them: "
            + string.Join("; ", stale.Select(static e => e.Key)));
    }

    /// <summary>
    /// THE GUARD. Every resolved pair normalizes identically, or matches its pinned allowlist entry exactly.
    /// </summary>
    [Fact]
    public void EveryPair_NormalizesToItsCounterpart_OrMatchesItsPinnedDifference()
    {
        var failures = PairVerdicts(Inventory.Comparisons, Allowlist, IdenticalPairs);
        Assert.True(failures.Count == 0, string.Join("\n\n", failures));
    }

    /// <summary>
    /// The guard's verdict over a set of comparisons: every resolved pair is either a pinned identical pair or
    /// matches its allowlist entry exactly, and every pinned pair (identical or allowlisted) is still resolved.
    /// Pure, so <see cref="TheGuardVerdict_RejectsEachKindOfDrift"/> can exercise each failure on synthetic sources.
    /// </summary>
    internal static List<string> PairVerdicts(
        IEnumerable<TwinComparison> comparisons, IReadOnlyCollection<AllowedDifference> allowlist, IReadOnlyCollection<string> identicalPairs)
    {
        var allowed = allowlist.ToDictionary(static e => e.Id, StringComparer.Ordinal);
        var identical = identicalPairs.ToHashSet(StringComparer.Ordinal);
        var resolved = new HashSet<string>(StringComparer.Ordinal);
        var failures = new List<string>();
        if (identical.Count != identicalPairs.Count)
            failures.Add("IdenticalPairs lists a pair twice.");
        foreach (var comparison in comparisons)
        {
            var id = comparison.Pair.Id;
            resolved.Add(id);
            var at = $"{comparison.Pair.Marker.File}:{comparison.Pair.Marker.Line}";
            if (comparison.IsIdentical)
            {
                if (allowed.ContainsKey(id))
                    failures.Add($"{id} ({at}) now normalizes IDENTICALLY: remove its allowlist entry, lower AllowlistCeiling by one, "
                        + "and add the pair to IdenticalPairs (the allowlist only shrinks).");
                else if (!identical.Contains(id))
                    failures.Add($"{id} ({at}) is a new identical pair: add it to TwinNormalizationTests.IdenticalPairs so that losing its "
                        + "marker can never drop it from the guard silently.");
                continue;
            }

            if (identical.Contains(id))
            {
                failures.Add($"TWIN DRIFT: {id} ({at}) is pinned as IDENTICAL but no longer normalizes to its counterpart. Mirror the edit "
                    + "on the other side in this same change (AGENTS.md: a MIRROR OF twin changes together with its counterpart); a pinned "
                    + $"identical pair can never move to the allowlist. Normalized difference (hash {comparison.DifferenceHash}):\n"
                    + Describe(comparison));
                continue;
            }

            if (!allowed.TryGetValue(id, out var entry))
            {
                failures.Add($"TWIN DRIFT: {id} ({at}) no longer normalizes to its counterpart. Mirror the edit on the other side in this same "
                    + "change (AGENTS.md: a MIRROR OF twin changes together with its counterpart). The allowlist only shrinks, so a new "
                    + $"difference cannot be absorbed by adding an entry. Normalized difference (hash {comparison.DifferenceHash}):\n"
                    + Describe(comparison));
                continue;
            }

            if (!string.Equals(entry.Hash, comparison.DifferenceHash, StringComparison.Ordinal))
            {
                failures.Add($"TWIN DRIFT: the pinned difference of {id} ({at}) changed (recorded {entry.Hash}, now {comparison.DifferenceHash}). "
                    + "If one side was edited, mirror the edit on the other side. Only if BOTH sides changed together and the remaining "
                    + $"difference is still exactly the recorded one ({entry.Classes}: {entry.Reason}) re-pin the hash to "
                    + $"{comparison.DifferenceHash} in the same reviewed change; never re-pin to absorb a one-sided edit. Normalized difference now:\n"
                    + Describe(comparison));
            }
        }

        foreach (var id in identicalPairs.Where(id => !resolved.Contains(id)))
            failures.Add($"MISSING PAIR: {id} is pinned in IdenticalPairs but no longer resolves (its marker was deleted, reworded into prose, "
                + "moved into a body, or a side was renamed). Restore or correct the marker; remove the entry only together with the twin itself.");
        foreach (var entry in allowlist.Where(e => !resolved.Contains(e.Id)))
            failures.Add($"MISSING PAIR: the allowlisted {entry.Id} no longer resolves. Restore or correct its marker; remove the entry (and "
                + "lower AllowlistCeiling) only together with the twin itself.");
        return failures;
    }

    /// <summary>The ratchet: the allowlist is exact, well-formed, and can only shrink.</summary>
    [Fact]
    public void Allowlist_IsExact_AndCanOnlyShrink()
    {
        Assert.True(Allowlist.Length <= AllowlistCeiling,
            $"The twin allowlist grew to {Allowlist.Length} entries (ceiling {AllowlistCeiling}). It only shrinks: mirror the edit "
            + "instead of allowlisting a new difference. Raising the ceiling is an owner decision with a documented class.");
        Assert.True(Allowlist.Length == AllowlistCeiling,
            $"The twin allowlist shrank to {Allowlist.Length} entries: lower AllowlistCeiling to {Allowlist.Length} so it cannot grow back.");

        var beyondAudit = Allowlist.Count(static e => (e.Classes & ~AuditClasses) != TwinDifference.None);
        Assert.True(beyondAudit <= AcceptedBeyondAuditCeiling,
            $"{beyondAudit} allowlist entries carry a class beyond the audit's; the accepted baseline is {AcceptedBeyondAuditCeiling}. "
            + "It only shrinks; a new class of difference is an owner decision.");

        Assert.Equal(Allowlist.Length, Allowlist.Select(static e => e.Id).Distinct(StringComparer.Ordinal).Count());
        Assert.All(Allowlist, static e =>
        {
            Assert.False(string.IsNullOrWhiteSpace(e.Reason), e.Id);
            Assert.NotEqual(TwinDifference.None, e.Classes);
            Assert.Equal(TwinDifference.None, e.Classes & TwinDifference.AwaitOrCall);
            Assert.Matches("^[0-9a-f]{16}$", e.Hash);
        });

        var pairs = Inventory.Comparisons.ToDictionary(static c => c.Pair.Id, StringComparer.Ordinal);
        var stale = Allowlist.Where(e => !pairs.ContainsKey(e.Id)).ToList();
        Assert.True(stale.Count == 0,
            "Allowlist entries naming no resolved pair (renamed, removed, or re-marked): remove them and lower AllowlistCeiling — "
            + string.Join("; ", stale.Select(static e => e.Id)));
    }

    /// <summary>
    /// The second pattern: every read of a <c>bool asynchronous</c> flag that selects behavior is pinned with a
    /// reason, and an await-or-call branch has arms that normalize identically.
    /// </summary>
    [Fact]
    public void EveryAsynchronousFlagBranch_IsListedWithAReason()
    {
        var actual = Inventory.FlagBranchPoints.ToDictionary(static b => b.Key, StringComparer.Ordinal);
        var listed = FlagBranchPoints.ToDictionary(static e => e.Key, StringComparer.Ordinal);
        Assert.Equal(FlagBranchPoints.Length, listed.Count);

        var failures = new List<string>();
        foreach (var point in Inventory.FlagBranchPoints)
        {
            if (!listed.TryGetValue(point.Key, out var entry))
            {
                failures.Add($"unlisted `asynchronous` branch point {point.Key} ({point.Method.File}): add it to FlagBranchPoints with a reason "
                    + $"(hash {point.Hash}): {point.Text}");
                continue;
            }

            if (!string.Equals(entry.Hash, point.Hash, StringComparison.Ordinal))
                failures.Add($"the `asynchronous` branch point {point.Key} changed (recorded {entry.Hash}, now {point.Hash}): check that both arms "
                    + $"still do the same work, then re-pin. Now: {point.Text}");
            if (entry.Class == TwinDifference.AwaitOrCall && !point.ArmsMirror)
                failures.Add($"the await-or-call branch {point.Key} no longer has arms that normalize identically: {point.Text}");
            if (entry.Class != TwinDifference.AwaitOrCall && point.ArmsMirror)
                failures.Add($"the branch point {point.Key} is now a plain await-or-call branch: reclassify it as AwaitOrCall.");
            if (string.IsNullOrWhiteSpace(entry.Reason))
                failures.Add($"the branch point {point.Key} has no reason.");
        }

        foreach (var entry in FlagBranchPoints.Where(e => !actual.ContainsKey(e.Key)))
            failures.Add($"FlagBranchPoints lists {entry.Key}, which no longer exists: remove it (ordinals follow source order).");

        Assert.True(failures.Count == 0, string.Join("\n", failures));
    }

    /// <summary>A flag call passing <c>asynchronous: true</c> is awaited, never completed by blocking.</summary>
    [Fact]
    public void NoAsynchronousFlagCall_IsCompletedByBlocking()
        => Assert.True(Inventory.BlockingFlagCalls.IsEmpty,
            "`asynchronous: true` completed with .GetAwaiter().GetResult() (sync-over-async): " + string.Join("; ", Inventory.BlockingFlagCalls));

    /// <summary>
    /// Self-test of the guard on real source: removing ONE statement from the twin of a pair that is byte-identical
    /// after normalization makes the pair differ, and an edit the normalization covers (an extra await) does not.
    /// </summary>
    [Fact]
    public void TheGuard_DetectsAOneSidedEdit_OfAnIdenticalPair()
    {
        var comparison = Inventory.Comparisons.Single(static c => c.Pair.Twin.Key == "Evaluator.EvalWhileVerdictSlotsAsync");
        Assert.True(comparison.IsIdentical, TwinDescribe(comparison));
        var declaration = (MethodDeclarationSyntax)comparison.Pair.Twin.Declaration;

        // Drop the SEC-01 overflow refusal inside the flag-row loop.
        var refusal = declaration.Body!.DescendantNodes().OfType<IfStatementSyntax>()
            .First(static s => s.Condition.ToString() == "discovery.Overflowed");
        var mutated = declaration.RemoveNode(refusal, SyntaxRemoveOptions.KeepNoTrivia)!;
        var drifted = TwinNormalization.CompareReplacingTwin(Inventory, comparison.Pair, mutated);
        Assert.False(drifted.IsIdentical);
        Assert.All(drifted.Hunks, static h => Assert.Empty(h.Added));
        Assert.Contains("RefuseTransientSupply", drifted.Hunks.SelectMany(static h => h.Removed));
        Assert.DoesNotContain(Allowlist, e => e.Id == drifted.Pair.Id);

        // A comment or whitespace change is not drift.
        var recommented = declaration.WithLeadingTrivia(SyntaxFactory.Comment("// reworded"), SyntaxFactory.CarriageReturnLineFeed);
        Assert.True(TwinNormalization.CompareReplacingTwin(Inventory, comparison.Pair, recommented).IsIdentical);
    }

    /// <summary>
    /// An allowlisted difference includes its position, so moving the hop across an ordinary error check
    /// cannot reuse the old pin even when the removed/added tokens are unchanged.
    /// </summary>
    [Fact]
    public void TheGuard_DetectsAOneSidedMove_OfAnAllowlistedDifference()
    {
        var comparison = Inventory.Comparisons.Single(static c =>
            c.Pair.Twin.Key == "Evaluator.EvalAliasDotStringLexicalReceiverAsync");
        var entry = Assert.Single(Allowlist, e => e.Id == comparison.Pair.Id);
        Assert.Equal(entry.Hash, comparison.DifferenceHash);
        var declaration = (MethodDeclarationSyntax)comparison.Pair.Twin.Declaration;
        var statements = declaration.Body!.Statements;
        Assert.Contains("terminal.IsError", statements[1].ToString(), StringComparison.Ordinal);
        Assert.Contains("StackHop.HostStackIsLow()", statements[2].ToString(), StringComparison.Ordinal);
        var reordered = statements.ToArray();
        (reordered[1], reordered[2]) = (reordered[2], reordered[1]);
        var moved = declaration.WithBody(declaration.Body.WithStatements(SyntaxFactory.List(reordered)));
        var drifted = TwinNormalization.CompareReplacingTwin(Inventory, comparison.Pair, moved);

        Assert.Equal(comparison.Hunks.Select(static h => h.ToString()), drifted.Hunks.Select(static h => h.ToString()));
        Assert.NotEqual(entry.Hash, drifted.DifferenceHash);
    }

    /// <summary>The synchronous completion adapter cannot hide a twin that blocks instead of awaiting.</summary>
    [Fact]
    public void TheGuard_DetectsBlockingInPlaceOfATwinAwait()
    {
        var comparison = Inventory.Comparisons.Single(static c => c.Pair.Twin.Key == "Evaluator.EvalAlgOutputCountedCoreAsync");
        Assert.True(comparison.IsIdentical, TwinDescribe(comparison));
        var declaration = (MethodDeclarationSyntax)comparison.Pair.Twin.Declaration;
        var awaited = Assert.Single(declaration.DescendantNodes().OfType<AwaitExpressionSyntax>());
        var blocking = SyntaxFactory.ParseExpression(awaited.Expression + ".GetAwaiter().GetResult()");
        var mutated = declaration.ReplaceNode(awaited, blocking);
        var drifted = TwinNormalization.CompareReplacingTwin(Inventory, comparison.Pair, mutated);
        Assert.False(drifted.IsIdentical);
        Assert.Contains("GetResult", drifted.Hunks.SelectMany(static h => h.Added));
        Assert.Contains(PairVerdicts([drifted], [], [comparison.Pair.Id]),
            static f => f.StartsWith("TWIN DRIFT", StringComparison.Ordinal));
    }

    // ── The guard's failure modes, on synthetic sources (a few lines parsed per case) ──

    private const string SyntheticPairId = "Worker.WorkAsync ~ Worker.Work";
    private const string SyntheticMarker = "/// <summary>MIRROR OF <see cref=\"Work\"/> - keep in lock-step.</summary>";
    private const string SyntheticCheck = "if (y > 10) return -1;";

    /// <summary>
    /// A one-file <c>dotnet/src/KatLang/</c> holding the pair <c>Worker.WorkAsync ~ Worker.Work</c>, identical after
    /// normalization unless the marker, the twin's check or an extra member say otherwise.
    /// </summary>
    private static TwinInventory BuildSynthetic(string marker = SyntheticMarker, string twinCheck = SyntheticCheck, string extra = "")
    {
        var source = """
            using System.Threading.Tasks;

            namespace Demo;

            internal static class Worker
            {
                private static int Step(int x) => x + 1;
                private static ValueTask<int> StepAsync(int x) => new(x + 1);
                private static int Other(int x) => x;
            {EXTRA}
                private static int Work(int x)
                {
                    var y = Step(x);
                    if (y > 10) return -1;
                    return y * 2;
                }

                {MARKER}
                private static async ValueTask<int> WorkAsync(int x)
                {
                    var y = await StepAsync(x).ConfigureAwait(false);
                    {CHECK}
                    return y * 2;
                }
            }
            """
            .Replace("{EXTRA}", extra, StringComparison.Ordinal)
            .Replace("{MARKER}", marker, StringComparison.Ordinal)
            .Replace("{CHECK}", twinCheck, StringComparison.Ordinal);
        var root = Path.Combine(Path.GetTempPath(), "katlang-twin-guard-" + Guid.NewGuid().ToString("N"));
        var directory = Path.Combine(root, "dotnet", "src", "KatLang");
        Directory.CreateDirectory(directory);
        try
        {
            File.WriteAllText(Path.Combine(directory, "Worker.cs"), source);
            return TwinNormalization.Build(root);
        }
        finally
        {
            Directory.Delete(root, recursive: true);
        }
    }

    private static AllowedDifference SyntheticEntry(string hash)
        => new("Worker.WorkAsync", "Worker.Work", hash, TwinDifference.FrameSplit, "synthetic");

    /// <summary>
    /// Each way a pair can leave the pinned baseline fails the verdict: a new identical pair that is not pinned, an
    /// allowlisted pair that became identical, a one-sided edit of a pinned identical pair or of an unpinned pair, a
    /// changed pinned difference, and a pinned pair (identical or allowlisted) whose marker was deleted or reworded.
    /// </summary>
    [Fact]
    public void TheGuardVerdict_RejectsEachKindOfDrift()
    {
        var baseline = BuildSynthetic();
        Assert.Empty(baseline.ResolutionFailures);
        var pair = Assert.Single(baseline.Comparisons);
        Assert.Equal(SyntheticPairId, pair.Pair.Id);
        Assert.True(pair.IsIdentical, TwinDescribe(pair));
        Assert.Empty(PairVerdicts(baseline.Comparisons, [], [SyntheticPairId]));

        Assert.Contains(PairVerdicts(baseline.Comparisons, [], []), static f => f.Contains("is a new identical pair", StringComparison.Ordinal));
        Assert.Contains(PairVerdicts(baseline.Comparisons, [SyntheticEntry("0123456789abcdef")], []),
            static f => f.Contains("now normalizes IDENTICALLY", StringComparison.Ordinal));
        Assert.Contains(PairVerdicts(baseline.Comparisons, [], [SyntheticPairId, SyntheticPairId]),
            static f => f.Contains("lists a pair twice", StringComparison.Ordinal));

        // A one-sided edit: the twin drops its refusal.
        var drifted = BuildSynthetic(twinCheck: "");
        var difference = Assert.Single(drifted.Comparisons);
        Assert.False(difference.IsIdentical);
        Assert.Contains(PairVerdicts(drifted.Comparisons, [], [SyntheticPairId]),
            static f => f.StartsWith("TWIN DRIFT", StringComparison.Ordinal) && f.Contains("pinned as IDENTICAL", StringComparison.Ordinal));
        Assert.Contains(PairVerdicts(drifted.Comparisons, [], []),
            static f => f.StartsWith("TWIN DRIFT", StringComparison.Ordinal) && f.Contains("no longer normalizes", StringComparison.Ordinal));
        Assert.Contains(PairVerdicts(drifted.Comparisons, [SyntheticEntry("0000000000000000")], []),
            static f => f.Contains("pinned difference", StringComparison.Ordinal) && f.Contains("changed", StringComparison.Ordinal));
        Assert.Empty(PairVerdicts(drifted.Comparisons, [SyntheticEntry(difference.DifferenceHash)], []));

        // The same refusal one statement later is a different pinned difference.
        var moved = BuildSynthetic(twinCheck: "y = y + 0; if (y > 10) return -1;");
        Assert.NotEqual(BuildSynthetic(twinCheck: "if (y > 10) return -1; y = y + 0;").Comparisons[0].DifferenceHash,
            moved.Comparisons[0].DifferenceHash);

        // Deleting or rewording the marker drops the pair: a pinned pair then reports it as MISSING.
        foreach (var marker in new[] { "", "/// <summary>MIRROR OF the synchronous worker.</summary>", "// keep in lock-step with Work" })
        {
            var unmarked = BuildSynthetic(marker: marker);
            Assert.Empty(unmarked.Pairs);
            Assert.Contains(PairVerdicts(unmarked.Comparisons, [], [SyntheticPairId]),
                static f => f.StartsWith("MISSING PAIR", StringComparison.Ordinal));
            Assert.Contains(PairVerdicts(unmarked.Comparisons, [SyntheticEntry("0123456789abcdef")], []),
                static f => f.StartsWith("MISSING PAIR", StringComparison.Ordinal));
        }
    }

    /// <summary>
    /// A marker that names no single method fails resolution with a diagnostic naming the remedy; no marker form
    /// silently resolves to the first of several counterparts.
    /// </summary>
    [Theory]
    [InlineData("/// <summary>MIRROR OF <see cref=\"Work\"/> / <see cref=\"Other\"/> - keep in lock-step.</summary>", "", "ambiguous marker")]
    [InlineData("/// <summary>MIRROR OF <see cref=\"Work\"/> / Other - keep in lock-step.</summary>", "", "ambiguous marker")]
    [InlineData("// MIRROR OF Work / Other - keep in lock-step.", "", "ambiguous marker")]
    [InlineData("// MIRROR OF Work(int) / Other(int) - keep in lock-step.", "", "ambiguous marker")]
    [InlineData("/// <summary>MIRROR OF <see cref=\"Missing\"/> - keep in lock-step.</summary>", "", "no method or local function named 'Missing'")]
    [InlineData(SyntheticMarker, "    private static int Work(string s) => s.Length;", "'Work' is ambiguous")]
    [InlineData("/// <summary>MIRROR OF <see cref=\"Work(long)\"/> - keep in lock-step.</summary>", "    private static int Work(string s) => s.Length;", "no overload of 'Work'")]
    public void AnUnresolvableMarker_FailsResolution(string marker, string extra, string reason)
    {
        var inventory = BuildSynthetic(marker: marker, extra: extra);
        var failure = Assert.Single(inventory.ResolutionFailures);
        Assert.Contains(reason, failure.Reason, StringComparison.Ordinal);
        Assert.Empty(inventory.Pairs);
    }

    /// <summary>The single-counterpart forms resolve, overloads included.</summary>
    [Theory]
    [InlineData(SyntheticMarker, "")]
    [InlineData("// MIRROR OF Work - keep in lock-step.", "")]
    [InlineData("/// <summary>MIRROR OF <see cref=\"Work(int)\"/> - keep in lock-step.</summary>", "    private static int Work(string s) => s.Length;")]
    [InlineData("// MIRROR OF Work(int) - keep in lock-step.", "    private static int Work(string s) => s.Length;")]
    [InlineData("/// <summary>MIRROR OF <see cref=\"Worker.Work\"/></summary>", "")]
    [InlineData("/// <summary>MIRROR OF <see cref=\"Demo.Worker.Work(int)\"/></summary>", "")]
    [InlineData("/// <summary>MIRROR OF <see cref=\"global::Demo.Worker.Work(int)\"/></summary>", "")]
    public void ASingleCounterpartMarker_Resolves(string marker, string extra)
    {
        var inventory = BuildSynthetic(marker: marker, extra: extra);
        Assert.Empty(inventory.ResolutionFailures);
        var pair = Assert.Single(inventory.Comparisons);
        Assert.True(pair.IsIdentical, TwinDescribe(pair));
    }

    /// <summary>A qualified cref cannot silently resolve to the twin's own type instead.</summary>
    [Fact]
    public void AQualifiedCounterpart_ResolvesOnlyInItsNamedType()
    {
        const string other = "    private static class OtherType { private static int Work(int x) => x - 1; }";
        var inventory = BuildSynthetic(marker: "/// <summary>MIRROR OF <see cref=\"OtherType.Work\"/></summary>", extra: other);
        Assert.Empty(inventory.ResolutionFailures);
        var pair = Assert.Single(inventory.Comparisons);
        Assert.Equal("Worker.OtherType.Work", pair.Pair.Counterpart.Key);
        Assert.False(pair.IsIdentical);
        Assert.Contains(PairVerdicts(inventory.Comparisons, [], [SyntheticPairId]),
            static f => f.StartsWith("MISSING PAIR", StringComparison.Ordinal));

        var missing = BuildSynthetic(marker: "/// <summary>MIRROR OF <see cref=\"MissingType.Work\"/></summary>");
        Assert.Empty(missing.Pairs);
        Assert.Contains("in containing type 'MissingType'", Assert.Single(missing.ResolutionFailures).Reason, StringComparison.Ordinal);

        // A global qualifier cannot resolve to the similarly named type inside namespace Demo.
        var global = BuildSynthetic(marker: "/// <summary>MIRROR OF <see cref=\"global::Worker.Work\"/></summary>");
        Assert.Empty(global.Pairs);
        Assert.Contains("in containing type 'global::Worker'", Assert.Single(global.ResolutionFailures).Reason, StringComparison.Ordinal);
    }

    /// <summary>The token difference is a correct, deterministic edit script.</summary>
    [Theory]
    [InlineData("", "", "")]
    [InlineData("a b c", "a b c", "")]
    [InlineData("a b c", "a c", "-[b] +[]")]
    [InlineData("a c", "a b c", "-[] +[b]")]
    [InlineData("a b c d", "a x c y", "-[b] +[x]\n-[d] +[y]")]
    [InlineData("x", "y", "-[x] +[y]")]
    public void Diff_RendersMinimalHunks(string left, string right, string expected)
    {
        static System.Collections.Immutable.ImmutableArray<string> Tokens(string s)
            => [.. s.Split(' ', StringSplitOptions.RemoveEmptyEntries)];
        var hunks = TwinNormalization.Diff(Tokens(left), Tokens(right));
        Assert.Equal(expected, string.Join("\n", hunks.Select(static h => h.ToString())));
    }

    /// <summary>
    /// Reporting only: the partition of pairs by similarity and the allowlist by class, written to the test output
    /// and checked for internal consistency.
    /// </summary>
    [Fact]
    public void Inventory_Summary_IsConsistent()
    {
        var comparisons = Inventory.Comparisons;
        var identical = comparisons.Count(static c => c.IsIdentical);
        Assert.Equal(comparisons.Length, identical + Allowlist.Length);
        var outsideAudit = Allowlist.Count(static e => (e.Classes & ~AuditClasses) != TwinDifference.None);
        Assert.InRange(outsideAudit, 0, Allowlist.Length);
        output.WriteLine(Summary());
        output.WriteLine($"  entries with a class outside the audit's: {outsideAudit}");
    }

    internal static string Summary()
    {
        var inventory = Inventory;
        var text = new StringBuilder();
        text.AppendLine($"files={inventory.Files.Length} markers={inventory.Markers.Length} pairs={inventory.Pairs.Length} "
            + $"identical={inventory.Comparisons.Count(static c => c.IsIdentical)} allowlisted={Allowlist.Length} unpaired={inventory.UnpairedMarkers.Length} "
            + $"flagMethods={inventory.FlagMethods.Length} branchPoints={inventory.FlagBranchPoints.Length} build={inventory.BuildTime.TotalMilliseconds:F0}ms");
        foreach (var flag in Enum.GetValues<TwinDifference>().Where(static f => f != TwinDifference.None && f != TwinDifference.AwaitOrCall))
            text.AppendLine($"  {flag}: {Allowlist.Count(e => e.Classes.HasFlag(flag))}");
        return text.ToString();
    }

    private static string Describe(TwinComparison comparison)
    {
        var text = new StringBuilder();
        foreach (var hunk in comparison.Hunks.Take(20))
        {
            var rendered = hunk.ToString();
            text.Append("    ").AppendLine(rendered.Length > 400 ? rendered[..400] + " …" : rendered);
        }

        if (comparison.Hunks.Length > 20)
            text.AppendLine($"    … {comparison.Hunks.Length - 20} more hunks");
        return text.ToString();
    }

    private static string TwinDescribe(TwinComparison comparison) => comparison.Pair.Id + "\n" + Describe(comparison);
}
