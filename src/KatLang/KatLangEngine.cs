using System.Numerics;
using System.Text;
using KatLang.Evaluation.Caching;
using KatLang.Rendering;

namespace KatLang;

/// <summary>
/// One result's display configuration, carried by its <see cref="RunResult"/> so every rendering
/// surface of that result reads the same values. It keeps the run's two presentation FILTERS
/// apart: <see cref="SourceDecimals"/> is the program root's own <c>DisplayDecimals</c> property
/// exactly as the engine evaluated and validated it (<c>null</c> when the root declares none),
/// and <see cref="HostDecimals"/> is the host filter — <see cref="RunOptions.DefaultDisplayDecimals"/>,
/// or the one <see cref="RunResult.WithHostDisplayDecimals"/> re-applied (<c>null</c> for none);
/// <see cref="MaxDisplayLength"/> is the run's display-length bound. The EFFECTIVE count,
/// <see cref="Decimals"/>, is never stored: every read derives it from the two filters through
/// <see cref="KatLangEngine.CombineDisplayDecimals"/>, so replacing the host filter cannot leave
/// a stale composition behind. The source filter is decided once per run; the host filter is the
/// one part a host may re-apply to a completed result.
/// </summary>
internal readonly record struct DisplayOptions(int? SourceDecimals, int? HostDecimals, int MaxDisplayLength)
{
    public static DisplayOptions Default { get; } = new(null, null, EvaluationLimits.MaxSupportedDisplayLength);

    /// <summary>
    /// The effective display-decimals count: the minimum of the present filters, or <c>null</c>
    /// (canonical full-precision display) when neither is present — the ONE composition law,
    /// <see cref="KatLangEngine.CombineDisplayDecimals"/>, applied on every read.
    /// </summary>
    public int? Decimals => KatLangEngine.CombineDisplayDecimals(SourceDecimals, HostDecimals);
}

/// <summary>
/// Bounded display sink. Rendering appends incrementally and checks BEFORE every append,
/// so the forbidden output is never constructed: the writer stops at the first append that
/// would cross the limit and reports it, rather than building an oversized string and
/// measuring it afterwards.
///
/// <para>Lengths are UTF-16 code units, matching <see cref="string.Length"/>, the source
/// span column model, and actual CLR string storage. EVERY append is charged its actual
/// length, including the platform newline between top-level rows, so the returned string
/// can never exceed the limit — an exact bound on the real output is worth more than a
/// canonical abstraction of it. The consequence is that a many-row rendering can cross the
/// boundary at a different row on a CRLF host (2 units per separator) than on an LF host
/// (1 unit); both return a complete bounded overflow indication rather than partial text.</para>
///
/// <para>The replacement marker is also bounded. The complete limit message is returned
/// when it fits; otherwise a complete one-character marker is returned when possible,
/// and a zero-length limit returns the empty string.</para>
/// </summary>
internal sealed class BoundedDisplayWriter(int limit) : IDisplaySink
{
    private readonly StringBuilder _builder = new();
    private long _charged;

    /// <summary>True once an append was refused; no further output is produced.</summary>
    public bool LimitExceeded { get; private set; }

    public bool Append(string text)
    {
        if (LimitExceeded) return false;
        if (text.Length > limit - _charged)
        {
            LimitExceeded = true;
            return false;
        }

        _charged += text.Length;
        _builder.Append(text);
        return true;
    }

    /// <summary>
    /// Appends a repeated character (formatter indentation), charged one unit
    /// per repetition like every other append — without materializing an
    /// intermediate string.
    /// </summary>
    public bool Append(char c, int count)
    {
        if (LimitExceeded) return false;
        if (count > limit - _charged)
        {
            LimitExceeded = true;
            return false;
        }

        _charged += count;
        _builder.Append(c, count);
        return true;
    }

    /// <summary>Writes the platform newline between top-level rows, charged its actual length.</summary>
    public bool AppendRowSeparator() => Append(Environment.NewLine);

    public override string ToString() => _builder.ToString();
}

/// <summary>
/// Discriminated-union result of a KatLang parse+evaluate run.
/// Pattern-match on <see cref="Success"/>, <see cref="NoProgramOutput"/>,
/// <see cref="ParseFailure"/>, or <see cref="EvalFailure"/>.
/// A C# <c>closed</c> hierarchy: those four nested records are its only
/// variants, no other assembly can derive from it, and a switch EXPRESSION
/// naming all four is compiler-exhaustive with no catch-all arm (a switch
/// statement receives no such guarantee).
/// Instances are produced only by the engine. Their payloads are read-only: hosts cannot
/// manufacture or rewrite a result whose value, numeric projection, output rows, and display
/// configuration describe different runs. The exposed AST is an advanced representation,
/// not a deeply immutable syntax snapshot.
/// </summary>
public closed record RunResult
{
    private RunResult() { }

    internal DisplayOptions DisplayOptions { get; init; } = DisplayOptions.Default;

    /// <summary>True when the run succeeded.</summary>
    public bool IsSuccess => this is Success;

    /// <summary>True when the run completed without program output.</summary>
    public bool IsNoProgramOutput => this is NoProgramOutput;

    /// <summary>True when the run failed with parse or evaluation errors.</summary>
    public bool IsFailure => this is ParseFailure or EvalFailure;

    /// <summary>Parse and evaluation succeeded.</summary>
    public sealed record Success : RunResult
    {
        internal Success(Algorithm.User Root, Result Value, IReadOnlyList<Decimal128> Atoms)
        {
            this.Root = Root;
            this.Value = Value;
            this.Atoms = Atoms;
            EmittedCount = Value.ValueCount();
        }

        /// <summary>The elaborated program.</summary>
        public Algorithm.User Root { get; }

        /// <summary>The complete structured result, including Booleans and strings.</summary>
        public Result Value { get; }

        /// <summary>
        /// Eager, read-only numeric projection through sequences and lists; Booleans and
        /// strings are omitted. Its size is bounded by the run's effective
        /// <see cref="EvaluationLimits.MaxCollectionItems"/>; exceeding that bound produces
        /// an evaluation failure instead of a success. Display uses <see cref="OutputRows"/>.
        /// </summary>
        public IReadOnlyList<Decimal128> Atoms { get; }

        public void Deconstruct(out Algorithm.User Root, out Result Value, out IReadOnlyList<Decimal128> Atoms)
            => (Root, Value, Atoms) = (this.Root, this.Value, this.Atoms);

        internal int EmittedCount { get; init; }

        /// <summary>
        /// The separately produced top-level output rows, exactly as canonical
        /// display derives them. <see cref="Value"/> alone cannot represent the
        /// root-output boundary: a program emitting two rows (<c>A()</c>
        /// newline <c>B()</c>) and a program emitting one sequence value
        /// (<c>(A(), B())</c>) can produce the SAME structural <see cref="Value"/>
        /// — this view keeps them distinguishable. Zero rows means the program
        /// evaluated successfully with empty output (for example a spread
        /// contributing zero items); one row is the whole <see cref="Value"/>
        /// (an explicitly emitted empty string, empty sequence, or empty list
        /// each stay one visible row); several rows are the value's top-level
        /// items in emission order.
        ///
        /// <para>The view is read-only over finished values and is derived on
        /// access without caching: the multi-row case returns the value's
        /// existing backing list, the single-row case allocates one
        /// single-element wrapper, and the zero-row case returns an empty
        /// singleton.</para>
        ///
        /// <para>The evaluator's exact emitted-slot count is used here only as a
        /// zero/one/many discriminator. Each written top-level row contributes
        /// one row to this view — whatever produced its value: a literal, a
        /// property, a call, a selection (<c>A:i</c>, <c>first</c>,
        /// <c>last</c>), or a completed <c>while</c>/<c>repeat</c>, all of
        /// which are value boundaries, so <c>Fibonacci.repeat(10, 0, 1)</c>
        /// is the one row <c>(55, 89)</c> — while a spread row <c>E*</c>
        /// contributes the items it supplies, possibly none.
        /// <see cref="OutputRows"/> is authoritative for presentation.</para>
        /// </summary>
        public IReadOnlyList<Result> OutputRows => EmittedCount switch
        {
            0 => Array.Empty<Result>(),
            1 => Array.AsReadOnly([Value]),
            _ => Value.ToItems(),
        };
    }

    /// <summary>Parse and evaluation completed, but the top-level program did not define output.</summary>
    public sealed record NoProgramOutput : RunResult
    {
        internal NoProgramOutput(Algorithm.User Root, KatLangError Diagnostic)
            => (this.Root, this.Diagnostic) = (Root, Diagnostic);

        public Algorithm.User Root { get; }
        public KatLangError Diagnostic { get; }

        public void Deconstruct(out Algorithm.User Root, out KatLangError Diagnostic)
            => (Root, Diagnostic) = (this.Root, this.Diagnostic);

        internal const string DefaultMessage =
            "No output defined.\n" +
            "This program defines properties, but does not specify what to return.\n" +
            "Add an output expression, or use `()` if the empty sequence value was intended.";

        /// <summary>
        /// The human-readable explanation, <see cref="KatLangError.Message"/> of
        /// <see cref="Diagnostic"/>. Presentation text only: classify through
        /// <see cref="KatLangError.Code"/>, never by comparing this string.
        /// </summary>
        public string Message => Diagnostic.Message;
    }

    /// <summary>Parsing failed — no executable root was produced.</summary>
    public sealed record ParseFailure : RunResult
    {
        internal ParseFailure(IReadOnlyList<KatLangError> Errors) => this.Errors = Errors;

        /// <summary>
        /// The front-end errors in reporting order: at most
        /// <see cref="SourceProcessingLimits.MaxDiagnosticCount"/>, followed — only when the source
        /// reported more — by one unpositioned <see cref="KatLangErrorCode.DiagnosticCountExceeded"/>
        /// error marking the list incomplete.
        /// </summary>
        public IReadOnlyList<KatLangError> Errors { get; }

        public void Deconstruct(out IReadOnlyList<KatLangError> Errors) => Errors = this.Errors;
    }

    /// <summary>Evaluation failed after a successful parse.</summary>
    public sealed record EvalFailure : RunResult
    {
        internal EvalFailure(Algorithm.User Root, IReadOnlyList<KatLangError> Errors)
            => (this.Root, this.Errors) = (Root, Errors);

        public Algorithm.User Root { get; }
        public IReadOnlyList<KatLangError> Errors { get; }

        public void Deconstruct(out Algorithm.User Root, out IReadOnlyList<KatLangError> Errors)
            => (Root, Errors) = (this.Root, this.Errors);
    }

    /// <summary>
    /// Returns a human-readable display string.
    /// On success: multiple top-level outputs are separated for readability;
    /// sequence values keep parentheses.
    /// On failure: newline-joined error messages.
    ///
    /// Rendering is strictly bounded (see <see cref="BoundedDisplayWriter"/>): the returned
    /// string never exceeds the effective <see cref="EvaluationLimits.MaxDisplayLength"/>.
    /// On overflow the partial rendering is discarded. The complete limit message is used
    /// when it fits, otherwise the complete <c>…</c> marker is used when one UTF-16 unit
    /// fits, otherwise the result is empty. Structured values and diagnostics are unchanged;
    /// truncated previews for editor UI belong in a separate, explicitly named API.
    ///
    /// <para>This is the <see cref="DisplayRendering.Text"/> projection of
    /// <see cref="RenderDisplay"/>. Overflow must be detected through that method's
    /// <see cref="DisplayRendering.LimitExceeded"/>, never by inspecting this string: a
    /// program whose legitimate output equals the limit message renders byte-identically.</para>
    /// </summary>
    public string ToDisplayString() => RenderDisplay().Text;

    /// <summary>
    /// Renders this result to bounded display text exactly like <see cref="ToDisplayString"/>
    /// and additionally reports, structurally, whether the rendering exceeded the effective
    /// <see cref="EvaluationLimits.MaxDisplayLength"/>. Overflow is a property of the
    /// RENDERING, not of the run: a <see cref="Success"/> stays a success with its structured
    /// <see cref="Success.Value"/> intact and only the requested text representation is
    /// unavailable, while diagnostics that do not fit the limit report the same condition for
    /// the failure variants. Every rendering surface derives its signal from the same bounded
    /// writer state, so <see cref="Formatting.OutputFormatter.RenderDisplay"/> agrees with this
    /// method for the canonical <c>exact</c> layout.
    /// </summary>
    public DisplayRendering RenderDisplay() => this switch
    {
        Success s => FormatSuccess(s),
        NoProgramOutput n => FormatText(n.Message, n.DisplayOptions.MaxDisplayLength),
        ParseFailure p => FormatErrors(p.Errors, p.DisplayOptions.MaxDisplayLength),
        EvalFailure e => FormatErrors(e.Errors, e.DisplayOptions.MaxDisplayLength),
    };

    /// <summary>
    /// Returns this completed run with <paramref name="hostDisplayDecimals"/> as its HOST display
    /// filter, without evaluating anything again: the one sanctioned re-application of display
    /// configuration to a finished result. A host whose display setting changes after a run — a
    /// playground's "display decimals" control, for example — keeps the result and re-renders the
    /// one this method returns instead of running the program again.
    /// <para><b>Equivalence.</b> For any source and options, the returned result renders
    /// identically — through <see cref="ToDisplayString"/>, <see cref="RenderDisplay"/>, and every
    /// <see cref="Formatting.OutputFormatter"/>, built-in or custom, under any
    /// <see cref="Formatting.OutputFormattingOptions"/>, overflow
    /// (<see cref="DisplayRendering.LimitExceeded"/>) included — to the result of the same run made
    /// with <see cref="RunOptions.DefaultDisplayDecimals"/> set to
    /// <paramref name="hostDisplayDecimals"/> and every other option unchanged, through
    /// <see cref="KatLangEngine.Run(string, RunOptions?)"/> and
    /// <see cref="KatLangEngine.RunAsync(string, RunOptions?)"/> alike. It holds because the host
    /// filter takes no part in evaluation — it is never evaluated, uses no budget, draws no random
    /// value, invokes no host operation, and adds no cancellation checkpoint — so both runs
    /// evaluate identically wherever evaluation is reproducible (an unseeded random draw or a
    /// nondeterministic host operation can differ between any two runs, whatever their display
    /// settings).</para>
    /// <para><b>Per variant.</b> A <see cref="Success"/> returns a NEW <see cref="Success"/> that
    /// shares this one's <see cref="Success.Root"/>, <see cref="Success.Value"/>,
    /// <see cref="Success.Atoms"/>, and output rows (<see cref="Success.OutputRows"/>) and differs
    /// only in its host filter — and so in its effective count. Its source filter — the program
    /// root's own <c>DisplayDecimals</c>, exactly as the run evaluated and validated it — and its
    /// display-length bound are kept. The new host filter REPLACES the previous one rather than
    /// composing with it, so chained calls keep only the last, and re-applying the filter a result
    /// was produced with changes nothing. A <see cref="NoProgramOutput"/>,
    /// <see cref="ParseFailure"/>, or <see cref="EvalFailure"/> renders independently of every
    /// display filter, so it is returned unchanged as this same instance — including the
    /// <see cref="EvalFailure"/> of an invalid root <c>DisplayDecimals</c>, which no host filter
    /// excuses.</para>
    /// <para><b>Purity.</b> Nothing is evaluated, charged, drawn, invoked, or observed for
    /// cancellation, and this result is never modified, so the method is safe to call
    /// concurrently on a shared result.</para>
    /// </summary>
    /// <param name="hostDisplayDecimals">
    /// The host display filter: an upper bound from <c>0</c> through
    /// <see cref="RunOptions.MaxDisplayDecimals"/> on displayed decimal places, or <c>null</c> for no
    /// host filter, which never means zero places. Validated exactly like
    /// <see cref="RunOptions.DefaultDisplayDecimals"/>.
    /// </param>
    /// <returns>
    /// A new <see cref="Success"/> carrying the given host filter, or this same instance for every
    /// other variant.
    /// </returns>
    /// <exception cref="ArgumentOutOfRangeException">
    /// <paramref name="hostDisplayDecimals"/> is negative or greater than
    /// <see cref="RunOptions.MaxDisplayDecimals"/> — rejected, never clamped, for every variant.
    /// </exception>
    public RunResult WithHostDisplayDecimals(int? hostDisplayDecimals)
    {
        if (hostDisplayDecimals is < 0 or > RunOptions.MaxDisplayDecimals)
        {
            throw new ArgumentOutOfRangeException(
                nameof(hostDisplayDecimals),
                hostDisplayDecimals,
                $"Host display decimals must be between 0 and {RunOptions.MaxDisplayDecimals}.");
        }

        // Compiler-exhaustive over the closed hierarchy: a new variant must decide here whether
        // its rendering depends on the host filter. A record copy shares every payload reference
        // (root, value, atoms, emitted count) and replaces only the host filter; the source filter
        // and the display-length bound travel unchanged, and the effective count is derived.
        return this switch
        {
            Success success => success with
            {
                DisplayOptions = success.DisplayOptions with { HostDecimals = hostDisplayDecimals },
            },
            NoProgramOutput or ParseFailure or EvalFailure => this,
        };
    }

    private static DisplayRendering FormatSuccess(Success success)
    {
        var writer = new BoundedDisplayWriter(success.DisplayOptions.MaxDisplayLength);
        AppendSuccessRows(success.OutputRows, success.DisplayOptions, writer);
        return Finish(writer, success.DisplayOptions.MaxDisplayLength);
    }

    /// <summary>
    /// Canonical success rendering shared byte-for-byte by
    /// <see cref="ToDisplayString"/> and the <c>exact</c> output formatter
    /// (the <c>exact</c> output formatter): platform-newline row
    /// separators over <see cref="Success.OutputRows"/>, each row in canonical
    /// inline form.
    /// </summary>
    internal static bool AppendSuccessRows(
        IReadOnlyList<Result> rows,
        DisplayOptions displayOptions,
        BoundedDisplayWriter writer)
    {
        for (var i = 0; i < rows.Count; i++)
        {
            if (i > 0 && !writer.AppendRowSeparator()) return false;
            if (!AppendValue(rows[i], displayOptions, writer)) return false;
        }

        return true;
    }

    /// <summary>
    /// Errors are rendered through the same configured bounded writer.
    /// The structured diagnostics are never dropped or rewritten to fit — only the final
    /// public rendering surface is bounded. Shared with every output formatter,
    /// so failures render identically regardless of the selected formatter.
    /// </summary>
    internal static DisplayRendering FormatErrors(IReadOnlyList<KatLangError> errors, int limit)
    {
        var writer = new BoundedDisplayWriter(limit);

        for (var i = 0; i < errors.Count; i++)
        {
            if (i > 0 && !writer.AppendRowSeparator()) break;
            if (!writer.Append(errors[i].ToString())) break;
        }

        return Finish(writer, limit);
    }

    internal static DisplayRendering FormatText(string text, int limit)
    {
        var writer = new BoundedDisplayWriter(limit);
        writer.Append(text);
        return Finish(writer, limit);
    }

    /// <summary>
    /// Completes one bounded rendering. The writer's refusal state is the ONE place display
    /// overflow becomes known, and it is surfaced here structurally — as the
    /// <see cref="KatLangError"/> projected from <see cref="EvalError.DisplayLengthLimitExceeded"/>
    /// for the limit actually enforced — beside the established bounded text, so no rendering
    /// surface has to rediscover the condition from the text it returns.
    /// </summary>
    internal static DisplayRendering Finish(BoundedDisplayWriter writer, int limit)
    {
        if (!writer.LimitExceeded)
            return new DisplayRendering(writer.ToString(), limitError: null);

        var limitError = KatLangError.FromEvalError(new EvalError.DisplayLengthLimitExceeded(limit));
        var message = limitError.Message;
        if (message.Length <= limit)
            return new DisplayRendering(message, limitError);

        const string marker = "…";
        return new DisplayRendering(marker.Length <= limit ? marker : string.Empty, limitError);
    }

    /// <summary>
    /// Appends one value's canonical display form. The implementation is the
    /// shared formatter-neutral iterative renderer
    /// (<see cref="ValueTextRenderer.AppendValue"/>) with the raw string
    /// strategy. Presentation formatters reuse the renderer by supplying their
    /// own string-leaf policy; canonical display has no dependency on formatter
    /// types or options. See the depth/breadth traversal note on
    /// <see cref="Result"/>.
    /// </summary>
    internal static bool AppendValue(Result value, DisplayOptions displayOptions, BoundedDisplayWriter writer)
        => ValueTextRenderer.AppendValue(value, displayOptions, RawStringTextPolicy.Instance, writer);
}

/// <summary>
/// The primary entry point for embedding KatLang: parse, elaborate, and evaluate source text
/// in one call and receive a structured <see cref="RunResult"/>.
/// <code>
/// var result = KatLangEngine.Run("1 + 2");
/// if (result is RunResult.Success success)
///     Console.WriteLine(success.ToDisplayString()); // 3
/// </code>
/// <para>Everything a run can be configured with — resource limits, cancellation, host
/// operations, module loading, a random seed, and a host display filter — is supplied
/// per run through one <see cref="RunOptions"/> object. <see cref="RunAsync"/> is the
/// asynchronous counterpart and the entry point for module loading and asynchronous host
/// operations; <see cref="EvaluateToAtoms"/> is a numeric-only convenience.</para>
/// <para>Two lower layers are public for advanced hosts: <see cref="Parser"/> runs the same
/// complete front end without evaluating (validation and editor tooling), and
/// <see cref="Evaluator"/> evaluates a host-built <see cref="Expr"/> exactly as supplied —
/// without parsing, module loading, front-end elaboration, or the engine's reading of the
/// program root's <c>DisplayDecimals</c> presentation filter — so it is not a source
/// runner.</para>
/// </summary>
public static class KatLangEngine
{
    private const string DisplayDecimalsPropertyName = "DisplayDecimals";

    /// <summary>
    /// Parse and evaluate KatLang source code, returning a unified <see cref="RunResult"/>.
    /// <see cref="RunOptions.SourceProcessingCancellationToken"/> applies through front-end source
    /// processing only; evaluation is governed separately by
    /// <see cref="RunOptions.EvaluationLimits"/> and cooperatively cancelled by
    /// <see cref="RunOptions.EvaluationCancellationToken"/>.
    /// <para>Source loading is ASYNC-ONLY: a configuration with
    /// <see cref="RunOptions.DownloadCode"/> selects <see cref="RunAsync"/>, where module
    /// downloads are awaited. This synchronous entry point serves downloader-less
    /// configurations — parsing, elaboration, and evaluation are CPU work — and <c>load</c>
    /// syntax without a downloader keeps its established rejection diagnostic.</para>
    /// </summary>
    /// <exception cref="OperationCanceledException">
    /// The configured source-processing token was cancelled during front-end processing,
    /// or the configured evaluation token was cancelled before or during evaluation.
    /// Cancellation is never converted into a <see cref="RunResult"/>.
    /// </exception>
    /// <exception cref="ArgumentNullException"><paramref name="source"/> is null.</exception>
    /// <exception cref="ArgumentException">
    /// <see cref="RunOptions.AllowedHosts"/> contains a null, empty, or whitespace-only entry.
    /// </exception>
    /// <exception cref="InvalidOperationException">
    /// <see cref="RunOptions.HostOperations"/> contains an ASYNCHRONOUS operation, or
    /// <see cref="RunOptions.DownloadCode"/> is configured — either way this synchronous
    /// entry point would have to suspend, which it cannot do; use
    /// <see cref="RunAsync"/>. Thrown before any parsing or evaluation.
    /// </exception>
    /// <remarks>
    /// A KatLang program's own failures — syntax and elaboration errors, failed
    /// <c>load</c>s (a faulting or cancelled downloader included), evaluation errors, and
    /// resource limits — are never thrown: they are structured <see cref="RunResult"/>
    /// variants. Only host misuse (the arguments and configuration above), host
    /// cancellation, and exceptions thrown by <see cref="HostOperation"/> delegates escape
    /// as CLR exceptions. The engine keeps no state between calls, so it may be called
    /// concurrently, also with one shared <see cref="RunOptions"/> instance; host-supplied
    /// delegates (<see cref="RunOptions.DownloadCode"/>, host operations) must then tolerate
    /// concurrent invocation themselves.
    /// </remarks>
    public static RunResult Run(string source, RunOptions? options = null)
    {
        ArgumentNullException.ThrowIfNull(source);
        var hostOperations = options?.HostOperations;
        // Fail fast on a configuration this synchronous entry point can never honor:
        // an asynchronous host operation completes only by suspending evaluation.
        // (A configured DownloadCode is rejected just below by the synchronous
        // front-end pipeline, before parsing, for the same reason.)
        if (hostOperations?.ContainsAsynchronousOperations == true)
        {
            throw new InvalidOperationException(
                "RunOptions.HostOperations contains an asynchronous operation; use KatLangEngine.RunAsync " +
                "(or an async convenience entry point), or configure only synchronous host operations.");
        }

        var limits = options?.EvaluationLimits ?? EvaluationLimits.Default;
        var evaluationCancellationToken = options?.EvaluationCancellationToken ?? default;
        var diagnosticDisplayOptions = new DisplayOptions(null, null, limits.EffectiveMaxDisplayLength);
        var frontEndResult = FrontEndPipeline.Process(source, options);

        if (frontEndResult.HasErrors)
        {
            return FrontEndFailureResult(frontEndResult, diagnosticDisplayOptions);
        }

        var zeroArgPropertyResultCache = new RunScopedZeroArgPropertyResultCache();

        // One budget for the whole run: the program output and the root's own
        // DisplayDecimals property (the source display filter) are evaluated under the
        // same run-scoped budget, so neither can reset or escape the other's accounting —
        // and they share the run's one random stream (RunOptions.RandomSeed), its
        // zero-argument property cache and its cancellation token, the output rows first
        // and DisplayDecimals afterwards, in exactly that evaluation order. The read
        // happens whatever the host filter is: RunOptions.DefaultDisplayDecimals takes no
        // part in evaluation and is consumed afterwards, composed with the source filter
        // by their minimum (ProjectEvaluationOutcome → ResolveDisplayOptions →
        // CombineDisplayDecimals).
        var evalResult = Evaluator.RunCountedWithTopLevelProperty(
            new Expr.AlgorithmExpr(frontEndResult.ElaboratedRoot),
            DisplayDecimalsPropertyName,
            zeroArgPropertyResultCache,
            options?.EvaluationLimits,
            hostOperations,
            options?.RandomSeed,
            evaluationCancellationToken);

        return ProjectEvaluationOutcome(
            frontEndResult,
            evalResult,
            limits,
            options?.DefaultDisplayDecimals,
            diagnosticDisplayOptions,
            evaluationCancellationToken);
    }

    /// <summary>
    /// Asynchronous counterpart of <see cref="Run(string, RunOptions?)"/> with identical
    /// result and error projection semantics — and the canonical entry point for source
    /// that loads modules.
    ///
    /// <para>Parsing and front-end elaboration remain SYNCHRONOUS CPU work; module
    /// acquisition is ASYNC-ONLY. With <see cref="RunOptions.DownloadCode"/> configured,
    /// each module download is awaited where its <c>load</c> is elaborated — an incomplete
    /// download genuinely suspends source processing and resumes it at the same point,
    /// governed as before by <see cref="RunOptions.SourceProcessingCancellationToken"/> and
    /// <see cref="RunOptions.SourceProcessingLimits"/>. Evaluation then goes through the
    /// evaluator's async surface, where an incomplete asynchronous
    /// <see cref="RunOptions.HostOperations"/> awaitable suspends and resumes the run the
    /// same way (see <see cref="HostOperation"/> for the full contract) — one run can
    /// suspend during both source processing and evaluation. When nothing actually
    /// suspends (no downloader, a synchronously-completing downloader, no asynchronous
    /// host operation), the whole run completes synchronously on the calling thread: this
    /// method never schedules work onto another thread and never yields artificially —
    /// thread placement and scheduling remain the host's (and the downloader's
    /// awaitable's) responsibility.</para>
    ///
    /// <para>A configuration with an asynchronous <see cref="RunOptions.HostOperations"/>
    /// operation evaluates through the async twin path — even when the program never calls
    /// that operation. Its larger per-level frames usually reach the host-stack backstop at a
    /// shallower recursion depth than <see cref="Run(string, RunOptions?)"/>, so a deeply
    /// recursive program may fail with the structured
    /// <see cref="KatLangErrorCode.EvaluationStackExhausted"/> error where the synchronous run
    /// reports <see cref="KatLangErrorCode.EvaluationDepthExceeded"/> or completes; a run that
    /// genuinely suspends before descending resumes on a fresh stack and can instead go deeper.
    /// The depth depends on the host and the route, never on which
    /// <see cref="RunOptions.EvaluationLimits"/> are configured (see
    /// <see cref="EvaluationLimits.MaxDepth"/>); both outcomes are ordinary resource-limit
    /// failures, never a process crash.</para>
    /// </summary>
    /// <exception cref="OperationCanceledException">
    /// Same cancellation contract as <see cref="Run(string, RunOptions?)"/>.
    /// </exception>
    /// <exception cref="ArgumentNullException"><paramref name="source"/> is null.</exception>
    /// <exception cref="ArgumentException">
    /// <see cref="RunOptions.AllowedHosts"/> contains a null, empty, or whitespace-only entry.
    /// </exception>
    /// <remarks>
    /// Program failures are structured <see cref="RunResult"/> variants exactly as for
    /// <see cref="Run(string, RunOptions?)"/>. Every exception of this method — argument
    /// and configuration validation, cancellation, and host-operation exceptions alike — is
    /// delivered through the returned task, never thrown by the call itself.
    /// </remarks>
    public static async Task<RunResult> RunAsync(string source, RunOptions? options = null)
    {
        // MIRROR OF Run(string, RunOptions?) — keep in lock-step; only front-end module
        // acquisition and the evaluation calls are awaited, through the async front-end
        // pipeline and the evaluator's async entry points.
        ArgumentNullException.ThrowIfNull(source);
        var hostOperations = options?.HostOperations;
        var limits = options?.EvaluationLimits ?? EvaluationLimits.Default;
        var evaluationCancellationToken = options?.EvaluationCancellationToken ?? default;
        var diagnosticDisplayOptions = new DisplayOptions(null, null, limits.EffectiveMaxDisplayLength);
        var frontEndResult = await FrontEndPipeline.ProcessAsync(source, options).ConfigureAwait(false);

        if (frontEndResult.HasErrors)
        {
            return FrontEndFailureResult(frontEndResult, diagnosticDisplayOptions);
        }

        // Cache-pairing rule (async-capable cache exactly for asynchronous host-operation
        // configurations and for roots carrying deferred module regions):
        // Evaluator.CreateRunScopedZeroArgPropertyResultCache.
        var program = new Expr.AlgorithmExpr(frontEndResult.ElaboratedRoot);
        var zeroArgPropertyResultCache =
            Evaluator.CreateRunScopedZeroArgPropertyResultCache(program, hostOperations);

        // One budget for the whole run, exactly as in Run; the host display filter is
        // likewise consumed only afterwards, by the shared projection.
        var evalResult = await Evaluator.RunCountedWithTopLevelPropertyAsync(
            program,
            DisplayDecimalsPropertyName,
            zeroArgPropertyResultCache,
            options?.EvaluationLimits,
            hostOperations,
            options?.RandomSeed,
            evaluationCancellationToken).ConfigureAwait(false);

        return ProjectEvaluationOutcome(
            frontEndResult,
            evalResult,
            limits,
            options?.DefaultDisplayDecimals,
            diagnosticDisplayOptions,
            evaluationCancellationToken);
    }

    /// <summary>
    /// Shared front-end failure projection for <see cref="Run"/> and
    /// <see cref="RunAsync"/>. Every front-end error blocks evaluation, including
    /// errors in downloaded source: evaluating a recovery tree for more diagnostics
    /// would also execute host operations and consume evaluator resources.
    /// </summary>
    private static RunResult.ParseFailure FrontEndFailureResult(
        FrontEndResult frontEndResult,
        DisplayOptions diagnosticDisplayOptions)
    {
        var parseErrors = frontEndResult.Diagnostics
            .Where(d => d.Severity == DiagnosticSeverity.Error)
            .Select(KatLangError.FromDiagnostic)
            .ToArray();

        // Published results are read-only views, so a consumer cannot change one through a cast.
        return new RunResult.ParseFailure(Array.AsReadOnly(parseErrors))
        {
            DisplayOptions = diagnosticDisplayOptions,
        };
    }

    /// <summary>
    /// Shared post-evaluation projection for <see cref="Run"/> and
    /// <see cref="RunAsync"/>: error classification, display-configuration resolution
    /// (<see cref="ResolveDisplayOptions"/>), bounded host-atom projection, and success
    /// construction — byte-for-byte the former inline body of <see cref="Run"/>.
    /// </summary>
    private static RunResult ProjectEvaluationOutcome(
        FrontEndResult frontEndResult,
        EvalResult<Evaluator.CountedRootProgramResult> evalResult,
        EvaluationLimits limits,
        int? hostDisplayFilter,
        DisplayOptions diagnosticDisplayOptions,
        CancellationToken evaluationCancellationToken)
    {
        if (evalResult.IsError)
        {
            var evalError = KatLangError.FromEvalError(evalResult.Error);
            if (IsTopLevelNoProgramOutput(evalResult.Error))
                return new RunResult.NoProgramOutput(frontEndResult.ElaboratedRoot, evalError)
                {
                    DisplayOptions = diagnosticDisplayOptions,
                };

            var evalErrors = Array.AsReadOnly(new[] { evalError });
            return new RunResult.EvalFailure(frontEndResult.ElaboratedRoot, evalErrors)
            {
                DisplayOptions = diagnosticDisplayOptions,
            };
        }

        // The run's effective display configuration and rendering limit travel with the
        // result, so ToDisplayString and every formatter stay bounded and agree without
        // RunResult having to reach back for the RunOptions.
        var displayOptionsResult = ResolveDisplayOptions(
            evalResult.Value.TopLevelProperty,
            FindTopLevelPropertyDeclarationSpan(frontEndResult.ElaboratedRoot, DisplayDecimalsPropertyName),
            hostDisplayFilter,
            limits.EffectiveMaxDisplayLength);
        if (displayOptionsResult.IsError)
        {
            return new RunResult.EvalFailure(
                frontEndResult.ElaboratedRoot,
                [KatLangError.FromEvalError(displayOptionsResult.Error)])
            {
                DisplayOptions = diagnosticDisplayOptions,
            };
        }

        // Host-atom projection is part of the run's materialization accounting: it opens
        // BOTH sequence and list boundaries recursively, so a modest result value can
        // project into an enormous host list. Bounding it here means a successful
        // evaluation cannot be followed by an unbounded allocation on the way out.
        var hostAtomLimit = limits.EffectiveMaxCollectionItems;
        var projected = evalResult.Value.Output.Value.TryToHostAtoms(hostAtomLimit, out var hostAtoms);
        evaluationCancellationToken.ThrowIfCancellationRequested();
        if (!projected)
        {
            return new RunResult.EvalFailure(
                frontEndResult.ElaboratedRoot,
                [KatLangError.FromEvalError(new EvalError.CollectionSizeLimitExceeded(hostAtomLimit, hostAtomLimit + 1L))])
            {
                DisplayOptions = diagnosticDisplayOptions,
            };
        }

        return new RunResult.Success(
            frontEndResult.ElaboratedRoot,
            evalResult.Value.Output.Value,
            hostAtoms)
        {
            EmittedCount = evalResult.Value.Output.EmittedCount,
            DisplayOptions = displayOptionsResult.Value,
        };
    }

    /// <summary>
    /// Parse and evaluate, returning the flat list of numeric atoms on success: the
    /// <see cref="RunResult.Success.Atoms"/> of <see cref="Run(string, RunOptions?)"/>.
    /// This is a lossy projection for numeric hosts: strings, Booleans, and structure
    /// boundaries are omitted, so it is not a display or serialization of the result. Use
    /// <see cref="Run(string, RunOptions?)"/> to retain the complete value and render it
    /// (<see cref="RunResult.ToDisplayString"/>, <see cref="RunResult.RenderDisplay"/>, or an
    /// <see cref="Formatting.OutputFormatter"/>).
    /// </summary>
    /// <exception cref="KatLangException">
    /// The program did not succeed — a parse or elaboration failure, an evaluation failure,
    /// or a program without output. <see cref="KatLangException.Errors"/> carries the same
    /// structured errors the corresponding <see cref="RunResult"/> variant would.
    /// </exception>
    /// <exception cref="OperationCanceledException">
    /// The configured source-processing token was cancelled during front-end processing,
    /// or the configured evaluation token was cancelled before or during evaluation —
    /// cancellation propagates and is never wrapped in a <see cref="KatLangException"/>.
    /// </exception>
    /// <exception cref="ArgumentNullException"><paramref name="source"/> is null.</exception>
    /// <exception cref="ArgumentException">
    /// <see cref="RunOptions.AllowedHosts"/> contains a null, empty, or whitespace-only entry.
    /// </exception>
    /// <exception cref="InvalidOperationException">
    /// The options require the asynchronous entry point (see <see cref="Run(string, RunOptions?)"/>).
    /// </exception>
    public static IReadOnlyList<Decimal128> EvaluateToAtoms(string source, RunOptions? options = null)
    {
        return Run(source, options) switch
        {
            RunResult.Success s => s.Atoms,
            RunResult.NoProgramOutput n => throw new KatLangException([n.Diagnostic]),
            RunResult.ParseFailure p => throw new KatLangException(p.Errors),
            RunResult.EvalFailure e => throw new KatLangException(e.Errors),
        };
    }

    /// <summary>
    /// Asynchronous counterpart of <see cref="EvaluateToAtoms"/>: a thin projection
    /// over <see cref="RunAsync"/> with identical success and failure semantics.
    /// Like <see cref="RunAsync"/>, it completes synchronously unless an incomplete
    /// <see cref="RunOptions.DownloadCode"/> download or asynchronous
    /// <see cref="RunOptions.HostOperations"/> awaitable genuinely suspends the run.
    /// </summary>
    /// <exception cref="KatLangException">The program did not succeed (see <see cref="EvaluateToAtoms"/>).</exception>
    /// <exception cref="OperationCanceledException">
    /// Same cancellation contract as <see cref="EvaluateToAtoms"/>.
    /// </exception>
    /// <exception cref="ArgumentNullException"><paramref name="source"/> is null.</exception>
    /// <remarks>Like <see cref="RunAsync"/>, every exception — including argument validation —
    /// is delivered through the returned task.</remarks>
    public static async Task<IReadOnlyList<Decimal128>> EvaluateToAtomsAsync(string source, RunOptions? options = null)
    {
        // MIRROR OF EvaluateToAtoms — keep in lock-step.
        return await RunAsync(source, options).ConfigureAwait(false) switch
        {
            RunResult.Success s => s.Atoms,
            RunResult.NoProgramOutput n => throw new KatLangException([n.Diagnostic]),
            RunResult.ParseFailure p => throw new KatLangException(p.Errors),
            RunResult.EvalFailure e => throw new KatLangException(e.Errors),
        };
    }

    private static SourceSpan? FindTopLevelPropertyDeclarationSpan(Algorithm root, string name)
    {
        foreach (var property in root.Properties)
        {
            if (property.Name == name)
                return property.FirstDeclarationSpan;
        }

        return null;
    }

    /// <summary>
    /// The ONE place a completed run's effective display configuration is decided, shared by
    /// <see cref="Run"/> and <see cref="RunAsync"/>; the <see cref="RunResult"/> carries the
    /// outcome, so every rendering surface of that result reads the same value. A run has two
    /// independent presentation FILTERS, each an upper bound on displayed decimal places:
    /// <list type="bullet">
    ///   <item>the SOURCE filter — the program root's own declared <c>DisplayDecimals</c>
    ///   property: <paramref name="sourceSetting"/> is its evaluated value, validated here
    ///   (one numeric value, integral, <c>0</c> through <see cref="RunOptions.MaxDisplayDecimals"/>);
    ///   an invalid value is its own diagnostic whatever the host configured, because the host
    ///   filter never replaces or excuses the source one (a declared property whose EVALUATION
    ///   failed never reaches this point: the run has already failed with that error);</item>
    ///   <item>the HOST filter — <paramref name="hostFilter"/>
    ///   (<see cref="RunOptions.DefaultDisplayDecimals"/>, range-checked when the options were
    ///   initialized).</item>
    /// </list>
    /// Both are composed by <see cref="CombineDisplayDecimals"/>: an absent filter imposes no
    /// limit, both present give their minimum, neither gives canonical rendering.
    /// <para>Absence is structural, never a value: the evaluator's one top-level property
    /// probe returns <c>null</c> exactly when the root declares no such property, so a declared
    /// <c>0</c>, a declared invalid value, and no declaration stay three distinct states, and a
    /// <c>null</c> host filter means no host filter — never zero places. The host filter is pure
    /// configuration consumed after evaluation — it is never evaluated, so nothing about the
    /// run but this display value depends on it.</para>
    /// </summary>
    private static EvalResult<DisplayOptions> ResolveDisplayOptions(
        Evaluator.CountedResult? sourceSetting,
        SourceSpan? span,
        int? hostFilter,
        int maxDisplayLength)
    {
        int? sourceFilter = null;
        if (sourceSetting is { } counted)
        {
            var value = counted.Value.AsNum();
            if (counted.EmittedCount != 1 || value is null)
                return DisplayDecimalsError("DisplayDecimals must be a single numeric value.", span);

            if (value.Value < 0)
                return DisplayDecimalsError("DisplayDecimals must be a non-negative integer.", span);

            if (!Decimal128.IsInteger(value.Value))
                return DisplayDecimalsError("DisplayDecimals must be an integer.", span);

            if (value.Value > RunOptions.MaxDisplayDecimals)
                return DisplayDecimalsError($"DisplayDecimals must be between 0 and {RunOptions.MaxDisplayDecimals}.", span);

            // Validated integral and within [0, MaxDisplayDecimals], so the narrowing is exact.
            sourceFilter = (int)value.Value;
        }

        return EvalResult<DisplayOptions>.Ok(new DisplayOptions(sourceFilter, hostFilter, maxDisplayLength));
    }

    /// <summary>
    /// The ONE composition law of the two display-decimals filters (Q-10, D-F): every present
    /// filter is an upper bound on displayed decimal places, so the effective count is the
    /// minimum of the present ones; an absent filter (<c>null</c>) imposes no limit, and with
    /// neither present the result is <c>null</c> — canonical full-precision rendering. Both
    /// inputs are already validated counts in <c>0</c> through
    /// <see cref="RunOptions.MaxDisplayDecimals"/>.
    /// </summary>
    internal static int? CombineDisplayDecimals(int? sourceFilter, int? hostFilter)
        => (sourceFilter, hostFilter) switch
        {
            ({ } source, { } host) => Math.Min(source, host),
            ({ } source, null) => source,
            (null, { } host) => host,
            (null, null) => null,
        };

    private static EvalError DisplayDecimalsError(string message, SourceSpan? span)
        => new EvalError.IllegalInEval(message) { Span = span };

    private static bool IsTopLevelNoProgramOutput(EvalError error)
        => error is EvalError.WithContext
        {
            ErrorContext: ProgramEvaluationContext,
            Inner: EvalError.MissingOutput,
        };

}
