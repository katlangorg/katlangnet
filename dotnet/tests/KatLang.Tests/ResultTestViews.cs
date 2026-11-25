using System.Numerics;

namespace KatLang.Tests;

/// <summary>
/// Test-only views over <see cref="Result"/>.
///
/// <para><see cref="ToAtoms"/> is the numeric SEQUENCE flattening the evaluator tests assert
/// numeric outputs through: the numbers reachable through sequence boundaries only, depth-first
/// and left to right; strings, Boolean values, and exact list values contribute nothing. It is
/// deliberately NOT a language view — KatLang has no numeric truth flattening any more, and
/// <see cref="Result.AsBool"/> is the language's only truth view — so a test that asserts a
/// Boolean result through it fails loudly with an empty list instead of passing on a stale
/// <c>0</c>/<c>1</c> expectation. Boolean results are asserted through the structured value
/// (<see cref="Result.Bool"/>) or the display text.</para>
/// </summary>
internal static class ResultTestViews
{
    public static IReadOnlyList<Decimal128> ToAtoms(this Result value)
    {
        var collected = new List<Decimal128>();
        var pending = new Stack<Result>();
        pending.Push(value);
        while (pending.Count > 0)
        {
            var node = pending.Pop();
            switch (node)
            {
                case Result.Atom(var number):
                    collected.Add(number);
                    break;
                case Result.SequenceValue(var items):
                    for (var i = items.Count - 1; i >= 0; i--)
                        pending.Push(items[i]);
                    break;
                default:
                    break; // strings, Booleans, and opaque list values contribute no atoms
            }
        }

        return collected;
    }
}
