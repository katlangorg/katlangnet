using System.Text;

namespace KatLang.Rendering;

/// <summary>
/// The first <see cref="Capacity"/> UTF-16 code units of a text written in fragments, and nothing after
/// them: a fragment that crosses the capacity contributes exactly the units that fit — a RAW cut, never
/// moved off a surrogate pair — and every later append is refused, which is what stops the writer's
/// traversal. No marker is added: the owner of the text's bound cuts it.
///
/// <para><b>Why a raw prefix of the bound plus one.</b> A bound of <c>L</c> units — the diagnostic list's
/// retention bound (<see cref="DiagnosticBag.MaxRetainedMessageLength"/>), a diagnostic name's
/// (<see cref="ExprNameRenderer.MaxRenderedNameLength"/>) — decides a text's bounded form from its first
/// <c>L + 1</c> units alone: whether the text is longer than <c>L</c>, and where its surrogate-safe cut
/// falls (<see cref="ExprNameRenderer.SafePrefixLength"/> reads the units at <c>L - 1</c> and <c>L</c>).
/// So bounding this prefix with a capacity of <c>L + 1</c> gives EXACTLY the bounded form of the whole
/// text, marker included, while a producer whose text grows with the source writes only that prefix
/// (<see cref="DiagnosticBag.RetainedPrefixLength"/>, <see cref="ExprNameRenderer.BoundDisplayName(ParameterPattern)"/>).
/// A surrogate-safe cut here would be wrong: it could keep <c>L</c> units of a longer text, which the bound
/// then stores without its marker.</para>
/// </summary>
internal sealed class TextPrefixBuilder
{
    private readonly StringBuilder _text = new();

    /// <summary>A builder that keeps at most <paramref name="capacity"/> units.</summary>
    internal TextPrefixBuilder(int capacity)
    {
        ArgumentOutOfRangeException.ThrowIfNegative(capacity);
        Capacity = capacity;
    }

    /// <summary>The most units this builder keeps.</summary>
    internal int Capacity { get; }

    /// <summary>True once <see cref="Capacity"/> units are kept: nothing written later can change the prefix.</summary>
    internal bool IsComplete => _text.Length == Capacity;

    /// <summary>Appends what fits of <paramref name="text"/>; false once the prefix is complete (a null string is empty).</summary>
    internal bool Append(string? text) => Append(text.AsSpan());

    /// <summary>Appends what fits of <paramref name="text"/>; false once the prefix is complete.</summary>
    internal bool Append(ReadOnlySpan<char> text)
    {
        var room = Capacity - _text.Length;
        _text.Append(text.Length <= room ? text : text[..room]);
        return !IsComplete;
    }

    /// <summary>Appends <paramref name="c"/> when it fits; false once the prefix is complete.</summary>
    internal bool Append(char c)
    {
        if (!IsComplete)
            _text.Append(c);
        return !IsComplete;
    }

    /// <summary>The kept prefix.</summary>
    public override string ToString() => _text.ToString();
}
