using System.Diagnostics.CodeAnalysis;
using System.Runtime.CompilerServices;

namespace KatLang;

/// <summary>
/// The ONE stack-reserve probe of the front end's recursive walks (C#-only host-stack safety,
/// Q-09a; no Lean counterpart). The structural gates (<see cref="AstStructuralPreflight"/>,
/// <c>Parser.MaxNestingDepth</c>, the loader's cumulative traversal budget) bound a tree's SHAPE,
/// calibrated against a walk that starts near the top of a documented 1 MiB thread. A compile does
/// not always start there: a deferred module region compiles its selected branch inside
/// <c>DeferredModuleRegion.CompileLoadedBody</c>, on whatever stack evaluation has already used, and
/// the stack a level costs is not a function of depth alone. So every front-end recursion cycle —
/// the parser's nesting chokepoint, the post-parse validation walk, the elaboration passes and the
/// module loader's walks — probes the runtime's reserve once per level and, when it is short,
/// unwinds with <see cref="FrontEndStackExhaustedException"/>, which exactly four boundaries convert
/// into a structured KatLang failure:
/// <list type="bullet">
/// <item><c>Parser.ParseSyntaxCore</c> — the parser chokepoint reports through
/// <c>ThrowNestingTooDeep</c>, and the post-parse validation walk's catch reports
/// <see cref="DiagnosticCode.NestingTooDeep"/> with the placeholder root (a nested module's parse
/// then classifies as <see cref="DiagnosticCode.ModuleNestingTooDeep"/>);</item>
/// <item><c>FrontEndPipeline.FinalizeElaboration</c> and <c>DeferredModuleRegion.CompileLoadedBody</c>
/// — the elaboration passes, reported as <see cref="DiagnosticCode.ModuleElaborationStackExhausted"/>;</item>
/// <item><c>Evaluator.PreEvaluationValidationError</c> — evaluator entry's validation walk, reported
/// as <see cref="EvalError.EvaluationStackExhausted"/>;</item>
/// </list>
/// and the module loader's own walks convert it at their established catches
/// (<c>ModuleLoader.ElaborateAsync</c> and the deferred materialization). No other route reaches a
/// probed method, so the control exception never escapes a public API.
///
/// <para>A probe changes nothing for a run with enough stack — same values, diagnostics, order,
/// charges, caching and allocations; it can only refuse, earlier than a physical overflow, a run
/// that would have needed the runtime's reserve. Where it fires is host-dependent and never
/// promised; no configured limit influences it (Q-09b). A refusal publishes nothing, is never
/// memoized, is never a clause non-match, and is not a resource limit (Q-71).</para>
///
/// <para><b>A new recursive front-end walk probes at the head of its recursion</b> (an existing
/// method, never a new wrapper frame, keeping any DAG memo check inside the frame), or records
/// why it need not: its depth is bounded by a constant, or on every route that reaches it a
/// probed walk with larger frames has already covered the same tree at the same stack base,
/// reaching every shared node no shallower. Visit order matters: each pass elaborates a spliced
/// module root once, at its FIRST reach, and the exposure pass visits properties before opens
/// while the detector and the resolver visit opens first, so on a module chain the exposure pass
/// alone stacks every module's nesting, and no earlier pass's probe stops it. Within that walk
/// the dependency-summary collection it drives at each scope probes too, so the exposure
/// recursion and the summary recursion each stop at their own probes; neither relies on an
/// earlier pass.</para>
/// </summary>
internal static class FrontEndStack
{
    /// <summary>
    /// Whether the runtime's execution-stack reserve is still available on this thread. The
    /// parser's nesting chokepoint reads this directly, so its refusal reports through the
    /// parser's own budget diagnostic.
    /// </summary>
    internal static bool HasReserve => RuntimeHelpers.TryEnsureSufficientExecutionStack();

    /// <summary>
    /// The per-level probe: returns when the reserve is available and otherwise unwinds the walk
    /// with <see cref="FrontEndStackExhaustedException"/>. The throw lives out of line, so a probe
    /// adds one call and no locals to a calibrated recursive frame.
    /// </summary>
    internal static void Ensure()
    {
        if (!HasReserve)
            ThrowExhausted();
    }

    [DoesNotReturn]
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void ThrowExhausted() => throw new FrontEndStackExhaustedException();
}

/// <summary>
/// The private control signal of <see cref="FrontEndStack.Ensure"/>: a front-end walk ran out of
/// host stack. Never a KatLang error by itself; the boundaries listed on <see cref="FrontEndStack"/>
/// convert it, and it never crosses a public API.
/// </summary>
internal sealed class FrontEndStackExhaustedException : Exception;
