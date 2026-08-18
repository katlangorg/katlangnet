using System.Collections.Concurrent;
using KatLang.Rendering;

namespace KatLang.Tests;

/// <summary>
/// <see cref="Evaluator.FormatResultForDiagnostic"/> — the value fragment a diagnostic quotes
/// its offending operand by — must be bounded DURING construction.
///
/// <para>The adversary is the same one <see cref="NormalizeSharedValueGraphTests"/> and
/// <see cref="SharedValueGraphComplexityTests"/> face: a value is a DAG, so <c>Wrap = [x, x]</c>
/// applied n times reaches n+1 distinct nodes through 2^n root-to-leaf paths. Unlike normalization
/// or equality, diagnostic rendering is path-proportional BY SEMANTICS — it spells out every
/// occurrence, and repeated occurrences must stay repeated occurrences — so the fix cannot be
/// reference-identity memoization, which would change what the message says. The fix is an output
/// budget that also terminates the walk. The unbounded renderer this replaced produced exactly
/// <c>10*2^depth - 4</c> UTF-16 units for that shape (655,356 at depth 16; 2,621,436 at depth 18;
/// roughly 11 TB at depth 40), from a three-line program.</para>
///
/// <para>Work is measured exactly through the passive, call-scoped append count, never by wall
/// clock. Small values are checked against <see cref="NaiveFormat"/>, a test-only replica of the
/// unbounded renderer, so ordinary messages are proven unchanged rather than merely re-asserted.
/// The replica is never run on an adversarial graph.</para>
/// </summary>
public class BoundedDiagnosticValueRenderingTests
{
    private const int Cap = DiagnosticValueRenderer.MaxRenderedValueLength;

    private const string Marker = DiagnosticValueRenderer.TruncationMarker;

    private static Result Atom(decimal value) => new Result.Atom(value);

    private static Result Str(string value) => new Result.Str(value);

    private static Result List(params Result[] items) => Result.ListValue.TakeOwnership(items);

    private static Result Seq(params Result[] items) => Result.SequenceValue.TakeOwnership(items);

    private static string Format(Result value) => Evaluator.FormatResultForDiagnostic(value);

    /// <summary>
    /// Test-only replica of the pre-fix renderer: a plain recursive expansion with no budget of
    /// any kind. It is the semantic oracle for values that fit the cap, and is deliberately never
    /// invoked on a shared or oversized graph.
    /// </summary>
    private static string NaiveFormat(Result value) => value switch
    {
        Result.Atom(var number) => number.ToString(System.Globalization.CultureInfo.InvariantCulture),
        Result.Str(var text) => $"'{text}'",
        Result.SequenceValue(var items) => $"({string.Join(", ", items.Select(NaiveFormat))})",
        Result.ListValue(var items) => $"[{string.Join(", ", items.Select(NaiveFormat))}]",
        _ => "value",
    };

    /// <summary>The doubling DAG: <c>P0 = leaf</c>, <c>Pk = [P(k-1), P(k-1)]</c>.</summary>
    private static Result SharedDag(int depth, Result? leaf = null)
    {
        var node = leaf ?? List(Atom(1), Atom(2));
        for (var i = 0; i < depth; i++)
            node = List(node, node);
        return node;
    }

    /// <summary>The same semantic tree as <see cref="SharedDag"/>, rebuilt without shared structure.</summary>
    private static Result RebuiltTree(int depth)
        => depth == 0
            ? List(Atom(1), Atom(2))
            : List(RebuiltTree(depth - 1), RebuiltTree(depth - 1));

    /// <summary>Asserts the value renders exactly as the unbounded replica would.</summary>
    private static void AssertRendersExactly(Result value)
    {
        var expected = NaiveFormat(value);
        Assert.True(
            expected.Length <= Cap,
            $"oracle case must fit the cap; it was {expected.Length} units");
        Assert.Equal(expected, Format(value));
    }

    // ── Small values render exactly as before ────────────────────────────────────────────────

    [Fact]
    public void Scalars_RenderExactly()
    {
        Assert.Equal("0", Format(Atom(0)));
        Assert.Equal("42", Format(Atom(42)));
        Assert.Equal("-7", Format(Atom(-7)));
        Assert.Equal("1.5", Format(Atom(1.5m)));
        Assert.Equal("-0.25", Format(Atom(-0.25m)));

        // Trailing-zero scale is part of decimal identity and is preserved verbatim, exactly as
        // invariant ToString produced it before; the renderer applies no decimal rounding.
        Assert.Equal("1.50", Format(Atom(1.50m)));
        Assert.Equal("0.0000000000000000000000000001", Format(Atom(0.0000000000000000000000000001m)));
        Assert.Equal(
            decimal.MaxValue.ToString(System.Globalization.CultureInfo.InvariantCulture),
            Format(Atom(decimal.MaxValue)));
        Assert.Equal(
            decimal.MinValue.ToString(System.Globalization.CultureInfo.InvariantCulture),
            Format(Atom(decimal.MinValue)));

        var negativeZero = new decimal(0, 0, 0, isNegative: true, scale: 0);
        Assert.Equal(
            negativeZero.ToString(System.Globalization.CultureInfo.InvariantCulture),
            Format(Atom(negativeZero)));
    }

    [Fact]
    public void Strings_RenderQuotedAndUnescaped()
    {
        // The renderer quotes unconditionally and escapes nothing: quotes, backslashes,
        // newlines, tabs and control characters all pass through verbatim, as before. The
        // control characters are composed from their code points so the expectation cannot
        // drift from the payload it is compared against.
        var tab = ((char)9).ToString();
        var newline = ((char)10).ToString();
        var control = ((char)1).ToString();

        Assert.Equal("''", Format(Str("")));
        Assert.Equal("'abc'", Format(Str("abc")));
        Assert.Equal("'it's'", Format(Str("it's")));
        Assert.Equal(@"'a\b'", Format(Str(@"a\b")));
        Assert.Equal("'a" + tab + "b'", Format(Str("a" + tab + "b")));
        Assert.Equal("'a" + newline + "b'", Format(Str("a" + newline + "b")));
        Assert.Equal("'a" + control + "b'", Format(Str("a" + control + "b")));
        Assert.Equal("'a b'", Format(Str("a b")));
        Assert.Equal("'héllo ☃ 😀'", Format(Str("héllo ☃ 😀")));
    }

    [Fact]
    public void EmptyAndNestedContainers_RenderExactly()
    {
        AssertRendersExactly(Seq());
        AssertRendersExactly(List());
        AssertRendersExactly(Seq(Atom(1)));
        AssertRendersExactly(List(Atom(1)));
        AssertRendersExactly(Seq(List()));
        AssertRendersExactly(List(Seq()));

        // Lists and sequences keep distinct delimiters at every level, and mixed nesting is
        // preserved exactly.
        Assert.Equal("()", Format(Seq()));
        Assert.Equal("[]", Format(List()));
        Assert.Equal("(1)", Format(Seq(Atom(1))));
        Assert.Equal("[1]", Format(List(Atom(1))));
        Assert.Equal("[(1, 2), [3, [4]], 'x']", Format(List(Seq(Atom(1), Atom(2)), List(Atom(3), List(Atom(4))), Str("x"))));
        Assert.Equal("([], (), [()])", Format(Seq(List(), Seq(), List(Seq()))));
    }

    [Fact]
    public void MixedNesting_MatchesTheUnboundedReplica()
    {
        AssertRendersExactly(List(Seq(Atom(1), Str("a")), List(Atom(2.5m), Seq()), Atom(-3)));
        AssertRendersExactly(Seq(List(List(Seq(Atom(0)))), Str("it's"), Atom(1.50m)));
    }

    // ── The cap boundary ─────────────────────────────────────────────────────────────────────

    /// <summary>
    /// A one-element list holding one string leaf, rendering to exactly
    /// <paramref name="length"/> units: <c>[</c> + <c>'</c> + content + <c>'</c> + <c>]</c>.
    /// </summary>
    private static Result RenderingToExactly(int length)
    {
        Assert.True(length >= 4, $"unsupported target length {length}");
        return List(Str(new string('a', length - 4)));
    }

    /// <summary>A flat list of single-digit atoms: <c>[</c> + n digits + (n-1) <c>", "</c> + <c>]</c> = 3n units.</summary>
    private static Result AtomListRenderingToExactly(int length)
    {
        Assert.True(length >= 3 && length % 3 == 0, $"unsupported target length {length}");
        return List([.. Enumerable.Range(0, length / 3).Select(i => Atom(i % 10))]);
    }

    [Theory]
    [InlineData(Cap - 2)]
    [InlineData(Cap - 1)]
    [InlineData(Cap)]
    public void ExactBoundary_AtAndBelowTheCapIsUntouched(int length)
    {
        // A value rendering to exactly Cap units must NOT be truncated: the budget is spent,
        // not overrun, so no marker is added.
        var value = RenderingToExactly(length);
        var full = NaiveFormat(value);
        Assert.Equal(length, full.Length);

        var rendered = Format(value);
        Assert.Equal(full, rendered);
        Assert.DoesNotContain(Marker, rendered);
    }

    [Theory]
    [InlineData(Cap + 1)]
    [InlineData(Cap + 2)]
    [InlineData(Cap + 64)]
    public void ExactBoundary_AboveTheCapTruncatesToTheCappedPrefix(int length)
    {
        var value = RenderingToExactly(length);
        var full = NaiveFormat(value);
        Assert.Equal(length, full.Length);

        var rendered = Format(value);
        Assert.Equal(full[..Cap] + Marker, rendered);
        Assert.Equal(Cap + Marker.Length, rendered.Length);
    }

    [Fact]
    public void ExactBoundary_StructuralShapeTruncatesMidElement()
    {
        // The same boundary reached through structure rather than one long leaf: 510 = 3*170
        // fits whole, 513 = 3*171 overruns and is cut two units into the final element.
        var fits = AtomListRenderingToExactly(510);
        Assert.Equal(NaiveFormat(fits), Format(fits));
        Assert.DoesNotContain(Marker, Format(fits));

        var overruns = AtomListRenderingToExactly(513);
        Assert.Equal(NaiveFormat(overruns)[..Cap] + Marker, Format(overruns));
    }

    [Fact]
    public void ReturnedLengthNeverExceedsTheCapPlusTheMarker()
    {
        // The cap counts rendered content, and the marker is added beyond it — the same
        // contract ExprNameRenderer states for the expression-name fragment.
        foreach (var value in new[] { SharedDag(40), RenderingToExactly(Cap + 2), Str(new string('x', 100_000)) })
        {
            var rendered = Format(value);
            Assert.True(
                rendered.Length <= Cap + Marker.Length,
                $"rendered {rendered.Length} units, cap is {Cap} + marker");
            Assert.EndsWith(Marker, rendered);
        }
    }

    [Fact]
    public void TruncationEmitsExactlyOneMarker()
    {
        // Nested bounded helpers must not each contribute their own marker.
        var nested = List(SharedDag(20), SharedDag(20), SharedDag(20));
        var rendered = Format(nested);
        Assert.Equal(1, rendered.Split(Marker).Length - 1);
        Assert.EndsWith(Marker, rendered);
    }

    // ── The shared doubling DAG: the primary adversary ───────────────────────────────────────

    [Theory]
    [InlineData(16)]
    [InlineData(20)]
    [InlineData(40)]
    public void SharedDag_IsBoundedInOutputAndWork(int depth)
    {
        // depth+1 distinct nodes; 2^depth root-to-leaf paths. The unbounded renderer produced
        // 10*2^depth - 4 units — unreachable at depth 40 — so the full expansion is never built
        // here, not even as an expectation.
        var rendered = DiagnosticValueRenderer.Render(SharedDag(depth), out var appendAttempts);

        Assert.Equal(Cap + Marker.Length, rendered.Length);
        Assert.EndsWith(Marker, rendered);

        // Work is bounded by the OUTPUT budget, not by the graph: every append the renderer
        // makes emits at least one visible unit, and the walk stops at the first refusal.
        Assert.True(
            appendAttempts <= Cap + 1,
            $"depth {depth} made {appendAttempts} append attempts for a {Cap}-unit budget");
    }

    [Fact]
    public void SharedDag_WorkStaysInsideTheBudgetWhilePathsExplode()
    {
        // The decisive property: adding 20 doubling levels multiplies the PATHS by a million
        // and leaves the work inside the same output budget.
        DiagnosticValueRenderer.Render(SharedDag(20), out var shallowWork);
        DiagnosticValueRenderer.Render(SharedDag(40), out var deepWork);

        Assert.True(shallowWork <= Cap + 1, $"{shallowWork} append attempts at depth 20");
        Assert.True(deepWork <= Cap + 1, $"{deepWork} append attempts at depth 40");

        // The two counts are not identical — a deeper graph spends more of the budget on
        // opening brackets before it reaches any atom, so it makes slightly fewer, larger
        // appends. The difference tracks the 20 extra LEVELS, never the 2^20 extra paths.
        Assert.True(Math.Abs(deepWork - shallowWork) <= 40, $"{shallowWork} vs {deepWork}");
    }

    [Fact]
    public void SharedDag_RenderedPrefixStillSpellsOutRepeatedOccurrences()
    {
        // Sharing must stay invisible: the fragment describes the semantic value, never the
        // host graph. A depth-3 DAG fits the cap, so it renders in full — with every repeated
        // occurrence repeated, and no reference/sharing notation of any kind.
        var value = SharedDag(3);
        var rendered = Format(value);

        Assert.Equal("[[[[1, 2], [1, 2]], [[1, 2], [1, 2]]], [[[1, 2], [1, 2]], [[1, 2], [1, 2]]]]", rendered);
        Assert.Equal(NaiveFormat(value), rendered);
        Assert.DoesNotContain("#", rendered);
        Assert.DoesNotContain("ref", rendered);
    }

    [Theory]
    [InlineData(3)]
    [InlineData(8)]
    public void SharingTopologyNeverChangesRenderedText(int depth)
    {
        // Depth 3 fits; depth 8 truncates. In both cases host reference sharing must stay
        // invisible and the traversal must produce the same semantic prefix.
        Assert.Equal(Format(RebuiltTree(depth)), Format(SharedDag(depth)));
    }

    [Fact]
    public void DiamondDag_IsBoundedWhenSharedContentAppearsInManyPositions()
    {
        // Not a chain: one shared node reached through several distinct positions, plus
        // unshared siblings between them. Once the budget is spent, later branches must not be
        // walked — whether or not they are shared.
        var shared = SharedDag(20);
        var mesh = List(
            List(shared, Atom(1), shared),
            Seq(Atom(2), shared),
            List(shared, shared, Seq(shared, Atom(3))));

        var rendered = DiagnosticValueRenderer.Render(mesh, out var appendAttempts);

        Assert.Equal(Cap + Marker.Length, rendered.Length);
        Assert.True(appendAttempts <= Cap + 1, $"{appendAttempts} append attempts for a {Cap}-unit budget");
    }

    [Fact]
    public void RepeatedTinyChild_IsBoundedByOutputNotByDistinctNodes()
    {
        // ONE distinct child repeated 100,000 times. A unique-node bound would call this
        // trivial; the output bound is what actually protects the message. This is precisely
        // where a diagnostic cap differs from the normalization memo.
        var child = List(Atom(1));
        var root = List([.. Enumerable.Repeat(child, 100_000)]);

        var rendered = DiagnosticValueRenderer.Render(root, out var appendAttempts);

        Assert.Equal(Cap + Marker.Length, rendered.Length);
        Assert.StartsWith("[[1], [1], [1]", rendered);
        Assert.True(appendAttempts <= Cap + 1, $"{appendAttempts} append attempts for a {Cap}-unit budget");
    }

    // ── Topology-independent safety: ordinary huge values ────────────────────────────────────

    [Fact]
    public void LargeUnsharedTree_IsBoundedToo()
    {
        // No sharing anywhere: safety must come from the output budget, not from graph shape.
        var root = List([.. Enumerable.Range(0, 50_000).Select(i => List(Atom(i), Seq(Atom(i))))]);

        var rendered = DiagnosticValueRenderer.Render(root, out var appendAttempts);

        Assert.Equal(Cap + Marker.Length, rendered.Length);
        Assert.True(appendAttempts <= Cap + 1, $"{appendAttempts} append attempts for a {Cap}-unit budget");
    }

    [Fact]
    public void WideValue_IsBounded()
    {
        var wide = List([.. Enumerable.Range(0, 100_000).Select(i => Atom(i % 10))]);

        var rendered = DiagnosticValueRenderer.Render(wide, out var appendAttempts);

        Assert.Equal(Cap + Marker.Length, rendered.Length);
        Assert.True(appendAttempts <= Cap + 1, $"{appendAttempts} append attempts for a {Cap}-unit budget");
    }

    [Fact]
    public void DeepValue_RemainsSafeAndBounded()
    {
        // Each level emits one opening bracket, so reaching the budget REQUIRES descending Cap
        // levels: this genuinely exercises deep structural traversal before truncation, and the
        // walk holds its suspended frames on the heap rather than the CLR stack.
        Result deep = Atom(0);
        for (var i = 0; i < 200_000; i++)
            deep = List(deep);

        var rendered = DiagnosticValueRenderer.Render(deep, out var appendAttempts);

        Assert.Equal(new string('[', Cap) + Marker, rendered);
        Assert.True(appendAttempts <= Cap + 1, $"{appendAttempts} append attempts for a {Cap}-unit budget");
    }

    [Fact]
    public void LongString_IsBoundedWithoutBuildingTheWholeToken()
    {
        // A single string leaf may hold up to MaxSupportedStringLength units. The sink appends
        // a prefix of the payload rather than the whole token, so no oversized intermediate is
        // built and then trimmed.
        var rendered = Format(Str(new string('x', 1_000_000)));

        Assert.Equal("'" + new string('x', Cap - 1) + Marker, rendered);
        Assert.Equal(Cap + Marker.Length, rendered.Length);
    }

    [Fact]
    public void LongStringInsideAContainer_IsBounded()
    {
        var rendered = Format(List(Atom(1), Str(new string('y', 100_000)), Atom(2)));

        Assert.Equal("[1, '" + new string('y', Cap - 5) + Marker, rendered);
    }

    [Fact]
    public void HistoricDoubleQuotedStringFragment_IsAlsoBounded()
    {
        Assert.Equal("\"a\\b\"", DiagnosticValueRenderer.RenderDoubleQuotedString(@"a\b"));

        var rendered = DiagnosticValueRenderer.RenderDoubleQuotedString(new string('z', 1_000_000));
        Assert.Equal("\"" + new string('z', Cap - 1) + Marker, rendered);
    }

    [Fact]
    public void TruncationNeverSplitsASurrogatePair()
    {
        // The boundary lands mid-payload; a well-formed pair must not be cut in half, so the
        // rendered content may stop one unit short of the cap.
        var payload = string.Concat(Enumerable.Repeat("😀", 1_000));
        var rendered = Format(Str(payload));

        Assert.EndsWith(Marker, rendered);
        var content = rendered[..^Marker.Length];
        Assert.True(content.Length <= Cap);
        Assert.False(char.IsHighSurrogate(content[^1]), "truncation left an unpaired high surrogate");
        // "'" plus whole pairs only: an odd number of payload units would mean a split pair.
        Assert.Equal(0, (content.Length - 1) % 2);
    }

    [Fact]
    public void SafePrefixLength_HandlesPairsAndMalformedUtf16AtEveryBoundary()
    {
        const string pairBetweenBmp = "A😀B";
        Assert.Equal(0, ExprNameRenderer.SafePrefixLength(pairBetweenBmp, -1));
        Assert.Equal(1, ExprNameRenderer.SafePrefixLength(pairBetweenBmp, 1));
        Assert.Equal(1, ExprNameRenderer.SafePrefixLength(pairBetweenBmp, 2));
        Assert.Equal(3, ExprNameRenderer.SafePrefixLength(pairBetweenBmp, 3));
        Assert.Equal(4, ExprNameRenderer.SafePrefixLength(pairBetweenBmp, int.MaxValue));

        const string consecutive = "😀😀";
        Assert.Equal(0, ExprNameRenderer.SafePrefixLength(consecutive, 1));
        Assert.Equal(2, ExprNameRenderer.SafePrefixLength(consecutive, 2));
        Assert.Equal(2, ExprNameRenderer.SafePrefixLength(consecutive, 3));
        Assert.Equal(4, ExprNameRenderer.SafePrefixLength(consecutive, 4));

        // Ill-formed input is preserved rather than normalized; the helper only avoids
        // creating a new split from a well-formed pair at the chosen boundary.
        Assert.Equal(2, ExprNameRenderer.SafePrefixLength("A\uD83D", 2));
        Assert.Equal(2, ExprNameRenderer.SafePrefixLength("A\uDE00", 2));
    }

    [Fact]
    public void EmptyStringTokens_DoNotInvalidateTheBoundedWorkOracle()
    {
        var value = List([.. Enumerable.Repeat<Result>(Str(""), 100_000)]);
        var rendered = DiagnosticValueRenderer.Render(value, out var appendAttempts);

        Assert.Equal(Cap + Marker.Length, rendered.Length);
        Assert.True(appendAttempts <= Cap + 1, $"{appendAttempts} append attempts for empty strings");
    }

    // ── Sink contract at the extremes ────────────────────────────────────────────────────────

    [Theory]
    [InlineData(0, "")]
    [InlineData(1, "[")]
    [InlineData(2, "[1")]
    [InlineData(3, "[1,")]
    public void Sink_ZeroAndTinyBudgets(int limit, string expectedContent)
    {
        var sink = new BoundedDiagnosticSink(limit);
        ValueTextRenderer.AppendValue(
            List(Atom(1), Atom(2)),
            new DisplayOptions(null, limit),
            QuotedDiagnosticStringPolicy.Instance,
            sink);

        Assert.True(sink.Truncated);
        Assert.Equal(expectedContent + Marker, sink.Finish());
    }

    [Fact]
    public void Sink_RefusesEveryAppendAfterTheFirstOverflow()
    {
        var sink = new BoundedDiagnosticSink(4);

        Assert.True(sink.Append("ab"));
        Assert.False(sink.Append("cdef"));
        Assert.False(sink.Append("g"));
        Assert.False(sink.Append('h', 1));

        Assert.Equal("abcd" + Marker, sink.Finish());
    }

    // ── Policy ───────────────────────────────────────────────────────────────────────────────

    [Fact]
    public void DiagnosticFragmentsShareOneLengthPolicy()
    {
        // The value fragment and the expression-name fragment appear in the same messages and
        // answer to one policy; this pins the documented relationship so the two cannot drift.
        Assert.Equal(ExprNameRenderer.MaxRenderedNameLength, DiagnosticValueRenderer.MaxRenderedValueLength);
        Assert.Equal(ExprNameRenderer.TruncationMarker, DiagnosticValueRenderer.TruncationMarker);
        Assert.Equal(512, DiagnosticValueRenderer.MaxRenderedValueLength);
        Assert.Equal("…", DiagnosticValueRenderer.TruncationMarker);

        // The diagnostic fragment cap is deliberately far below the public display ceiling: a
        // diagnostic quotes a value to identify it, it does not render program output.
        Assert.True(DiagnosticValueRenderer.MaxRenderedValueLength < EvaluationLimits.MaxSupportedDisplayLength);
    }

    // ── No retained state across calls or threads ────────────────────────────────────────────

    [Fact]
    public void RepeatedRenderingIsIndependent()
    {
        var adversary = SharedDag(40);
        var small = List(Atom(1), Atom(2));

        for (var i = 0; i < 8; i++)
        {
            var big = DiagnosticValueRenderer.Render(adversary, out var bigWork);
            Assert.Equal(Cap + Marker.Length, big.Length);
            Assert.True(bigWork <= Cap + 1);

            // An oversized render must leave nothing behind for the next one.
            Assert.Equal("[1, 2]", Format(small));
        }
    }

    [Fact]
    public void ConcurrentRenderingIsIndependent()
    {
        // All rendering state is local to one call (a fresh sink; no pooling, no static or
        // AsyncLocal storage), so concurrent oversized renders cannot interleave.
        var adversary = SharedDag(30);
        var expectedBig = Format(adversary);
        var results = new ConcurrentBag<string>();

        Parallel.For(0, 64, i =>
        {
            results.Add(Format(i % 2 == 0 ? adversary : List(Atom(i), Str("s"))));
        });

        Assert.Equal(64, results.Count);
        foreach (var text in results)
        {
            Assert.True(
                text == expectedBig || (text.StartsWith('[') && text.EndsWith("'s']")),
                $"unexpected interleaved rendering: {text}");
        }
    }

}
