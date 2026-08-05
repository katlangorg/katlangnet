namespace KatLang.Formatting;

/// <summary>
/// Base class for KatLang plain-text output formatters: presentation-only renderers of an
/// ALREADY EVALUATED <see cref="RunResult"/>. Formatting never re-parses,
/// never re-evaluates, never modifies a <see cref="Result"/>, and never
/// reorders, merges, splits, or reinterprets output values — two formatters
/// may lay the same result out differently, but they always present the same
/// values with the same structure kinds in the same order. The parser and
/// evaluator have no knowledge of formatters or formatting options. This
/// contract produces one bounded plain-text <see cref="string"/>; rich HTML,
/// ANSI-span, semantic-document, and accessibility-tree output belongs in a
/// separate consumer-owned abstraction.
///
/// <para>The built-in formatters are exposed by <see cref="OutputFormatters"/>
/// under the stable ids <c>exact</c>, <c>readable</c>, and <c>concise</c>.
/// External consumers may derive additional formatters: override
/// <see cref="WriteSuccessOutput"/> and render the supplied success rows
/// (from <see cref="RunResult.Success.OutputRows"/>) through the bounded
/// writer. Failure, no-output, display-limit, and overflow handling are shared
/// here and are identical for every formatter.</para>
/// </summary>
public abstract class OutputFormatter
{
    /// <summary>Creates a formatter. Implementations must be stateless and reusable across calls and threads.</summary>
    protected OutputFormatter()
    {
    }

    /// <summary>
    /// Stable identifier for this formatter, suitable for persistence by
    /// external applications. Built-in ids are lowercase and documented on
    /// <see cref="OutputFormatters"/>. Localized display names are consumer
    /// concerns and deliberately not part of this API.
    /// </summary>
    public abstract string Id { get; }

    /// <summary>
    /// Formats an already evaluated run.
    ///
    /// <para>Success output is produced by the formatter-specific
    /// <see cref="WriteSuccessOutput"/>; parse failures, evaluation failures,
    /// and the no-program-output message render identically for every
    /// formatter, exactly like <see cref="RunResult.ToDisplayString"/>.</para>
    ///
    /// <para>The returned string never exceeds the effective display limit:
    /// the evaluated run's own limit, optionally LOWERED (never raised) by
    /// <see cref="OutputFormattingOptions.MaxDisplayLength"/>. On overflow the
    /// partial rendering is discarded and the established bounded overflow
    /// response is returned (the complete limit message when it fits,
    /// otherwise the complete <c>…</c> marker, otherwise the empty string) —
    /// output is never truncated mid-value.</para>
    /// </summary>
    public string Format(RunResult result, OutputFormattingOptions? options = null)
    {
        ArgumentNullException.ThrowIfNull(result);
        var effectiveOptions = options ?? OutputFormattingOptions.Default;
        var limit = effectiveOptions.EffectiveDisplayLimit(result.DisplayOptions.MaxDisplayLength);

        switch (result)
        {
            case RunResult.Success success:
                {
                    var core = new BoundedDisplayWriter(limit);
                    var completed = WriteSuccessOutput(
                        success.OutputRows,
                        effectiveOptions,
                        new BoundedOutputWriter(core, result.DisplayOptions));
                    if (!completed && !core.LimitExceeded)
                    {
                        throw new InvalidOperationException(
                            "The output formatter reported incomplete output without exceeding the display limit.");
                    }

                    return RunResult.Finish(core, limit);
                }

            case RunResult.NoProgramOutput noOutput:
                return RunResult.FormatText(noOutput.Message, limit);

            case RunResult.ParseFailure parseFailure:
                return RunResult.FormatErrors(parseFailure.Errors, limit);

            case RunResult.EvalFailure evalFailure:
                return RunResult.FormatErrors(evalFailure.Errors, limit);

            default:
                throw new InvalidOperationException("Unknown RunResult variant.");
        }
    }

    /// <summary>
    /// Writes the success output through the bounded writer. Implementations
    /// must emit ONLY via the writer (so the display limit is enforced), must
    /// stop and return false as soon as an append is refused, and must not
    /// evaluate anything — <paramref name="outputRows"/> contains finished
    /// values. The narrower row view deliberately withholds the successful
    /// run's parsed AST and host-atom projection: output formatting must depend
    /// only on evaluated output.
    /// Implementations should handle every public <see cref="Result"/> variant
    /// explicitly and fail loudly on an unknown future variant; silently
    /// omitting an unrecognized value would misrepresent program output.
    /// Whole-value traversal must be iterative (see the depth note on
    /// <see cref="Result"/>): host-constructed values nest arbitrarily deep,
    /// and a recursive walk would overflow the host stack.
    /// </summary>
    /// <returns>
    /// True when the output was written completely; false only when the writer
    /// refused an append. The base template validates this contract: returning
    /// false without a refused append throws instead of exposing incomplete
    /// output. Overflow itself is detected from the writer state, so a writer
    /// refusal remains bounded even if an implementation mistakenly returns
    /// true.
    /// </returns>
    protected abstract bool WriteSuccessOutput(
        IReadOnlyList<Result> outputRows,
        OutputFormattingOptions options,
        BoundedOutputWriter writer);
}
