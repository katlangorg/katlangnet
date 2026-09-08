using System.Diagnostics.CodeAnalysis;

namespace KatLang;

/// <summary>
/// The outcome of ONE bounded rendering of a <see cref="RunResult"/> to display text: the
/// text together with a structured indication of whether the rendering exceeded its
/// display limit. Produced by <see cref="RunResult.RenderDisplay"/> and
/// <see cref="Formatting.OutputFormatter.RenderDisplay"/>; the string surfaces
/// <see cref="RunResult.ToDisplayString"/> and <see cref="Formatting.OutputFormatter.Format"/>
/// are its <see cref="Text"/> projection.
///
/// <para>Overflow is a property of the RENDERING, never of the run. Evaluation may have
/// succeeded — a <see cref="RunResult.Success"/> keeps its structured value — while the
/// requested text representation could not be produced within the effective limit, and a
/// lower per-call limit or a more verbose formatter can overflow where canonical display
/// under the run's own limit would not. That is why the signal lives on the rendering
/// rather than on the <see cref="RunResult"/> variants, and why a consumer must never
/// infer overflow from <see cref="Text"/>: a program whose legitimate output equals the
/// limit message renders byte-identically to an overflow but reports
/// <see cref="LimitExceeded"/> false.</para>
/// </summary>
public sealed class DisplayRendering
{
    internal DisplayRendering(string text, KatLangError? limitError)
    {
        Text = text;
        LimitError = limitError;
    }

    /// <summary>
    /// The bounded display text, exactly as the string surfaces return it. Within the
    /// limit it is the complete rendering. On overflow the partial rendering has been
    /// discarded and this is the established bounded overflow response: the complete limit
    /// message when it fits, otherwise the complete <c>…</c> marker when one UTF-16 unit
    /// fits, otherwise the empty string. It never exceeds the effective limit.
    /// </summary>
    public string Text { get; }

    /// <summary>
    /// True when the rendering exceeded its effective display limit, so <see cref="Text"/>
    /// is the bounded overflow response rather than the requested representation. This is
    /// the supported way to detect display overflow; it does not depend on the wording of
    /// <see cref="Text"/>, and it is false for output that merely looks like the notice.
    /// </summary>
    [MemberNotNullWhen(true, nameof(LimitError))]
    public bool LimitExceeded => LimitError is not null;

    /// <summary>
    /// The structured description of the overflow, or <c>null</c> when the rendering
    /// completed within its limit. It is the same facade evaluation failures use, so hosts
    /// classify it the same way: <see cref="KatLangError.Code"/> is
    /// <see cref="KatLangErrorCode.DisplayLengthLimitExceeded"/>,
    /// <see cref="KatLangError.IsResourceLimit"/> is true, and
    /// <see cref="KatLangError.Source"/> is the <see cref="EvalError.DisplayLengthLimitExceeded"/>
    /// naming the limit actually enforced for this rendering. Its
    /// <see cref="KatLangError.Message"/> is the complete human-readable notice whether or
    /// not that notice fit into <see cref="Text"/>. The error is never added to a
    /// <see cref="RunResult"/> failure list.
    /// </summary>
    public KatLangError? LimitError { get; }
}
