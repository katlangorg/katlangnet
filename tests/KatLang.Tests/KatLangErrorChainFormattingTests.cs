using Xunit.Abstractions;

namespace KatLang.Tests;

/// <summary>
/// THE MESSAGE OF AN ERROR BELOW CONTEXT FRAMES
/// (docs/design/language-rules/evaluator-and-hosting.md § The evaluation-error taxonomy, C# RECORD
/// OPERATIONS ON CONTEXT FRAMES). <see cref="KatLangError.FromEvalError"/> formatted a chain of
/// <see cref="EvalError.WithContext"/> frames by recursion — a native call and a string join per
/// frame, and every recognizer for every frame — and is now one loop. This class pins that the
/// loop writes the text the recursion wrote:
/// <list type="bullet">
///   <item>PARITY: <see cref="Reference"/> is the former recursion, kept verbatim in its
///   traversal (every recognizer for every frame, then <c>{context}: {inner}</c>). Every error
///   kind below every context kind, every pair and triple of frames over the kinds, and seeded
///   longer chains format alike, with and without a fragment renderer.</item>
///   <item>HOST-BUILT FRAMES: a null inner error or context fails as it did.</item>
///   <item>DEPTH: 200,000 frames (also on a 1 MiB thread in a child process, by
///   <see cref="AstStructuralDepthProcessTests"/>), which the recursion could not format and
///   whose chain searches made it quadratic.</item>
/// </list>
/// </summary>
public class KatLangErrorChainFormattingTests(ITestOutputHelper output)
{
    // ── The former formatter (the oracle) ────────────────────────────────────

    // Verbatim in its traversal: every recognizer for the error as it stands — the three that
    // search the whole remaining chain included, at every level — then one native call and one
    // join per frame. The per-shape recognizers and messages are the library's own (pinned by
    // KatLangErrorLegacyContextTests and the message tests): what changed, and what this holds
    // the loop to, is the walk over the frames.
    private static string Reference(EvalError error, Func<string, string>? renderFragment)
    {
        if (KatLangError.TryFormatRecognizedShape(error, renderFragment, searchChain: true, out var recognized))
            return recognized;
        return error is EvalError.WithContext frame
            ? $"{Render(frame.Context, renderFragment)}: {Reference(frame.Inner, renderFragment)}"
            : KatLangError.FormatUnframedEvalError(error, renderFragment);
    }

    private static string Render(string text, Func<string, string>? renderFragment)
        => renderFragment is null ? text : renderFragment(text);

    /// <summary>A renderer that shows where each fragment starts and ends.</summary>
    private static string Marked(string fragment) => "‹" + fragment + "›";

    // A message, or the kind of failure: the corpus holds no shape that fails, but a difference
    // must be reported as one and not as an unrelated crash of this test.
    private static string Outcome(Func<string> format)
    {
        try
        {
            return "text: " + format();
        }
        catch (Exception exception) when (exception is not Xunit.Sdk.XunitException)
        {
            return "throws " + exception.GetType().FullName;
        }
    }

    private static void AssertSameAsTheRecursion(EvalError error, List<string> differences)
    {
        foreach (var renderFragment in (Func<string, string>?[])[null, Marked])
        {
            var expected = Outcome(() => Reference(error, renderFragment));
            var actual = Outcome(() => KatLangError.FormatEvalError(error, renderFragment));
            if (!string.Equals(expected, actual, StringComparison.Ordinal) && differences.Count < 10)
                differences.Add($"{Shape(error)}{(renderFragment is null ? "" : " (rendered)")}\n  recursion: {expected}\n  loop:      {actual}");
        }
    }

    // The kinds of a chain, outermost first: enough to rebuild a failing case, and never a
    // record's own text.
    private static string Shape(EvalError? error)
    {
        var kinds = new List<string>();
        for (; error is EvalError.WithContext frame; error = frame.Inner)
            kinds.Add(frame.ErrorContext?.GetType().Name ?? "null context");
        kinds.Add(error?.GetType().Name ?? "null");
        return string.Join(" > ", kinds);
    }

    // ── Corpus ───────────────────────────────────────────────────────────────

    private static readonly SourceSpan Span = new(3, 4, 3, 9);

    // Every public context kind with every degenerate payload, and the payloads the recognizers
    // read: the legacy host prose of the three recognized frames, a member named like the
    // unknown name below it, the `string` intrinsic's edge.
    private static readonly Lazy<ErrorContext[]> GeneratedContexts = new(() => [.. KatLangErrorTotalityTests.BuildAll<ErrorContext>()]);

    private static readonly Lazy<ErrorContext[]> WrittenContexts = new(() =>
    [
        new TextErrorContext("frame"),
        new TextErrorContext("while evaluating call to F"),
        new TextErrorContext("while evaluating property P"),
        new TextErrorContext("while evaluating dotCall .member of Obj"),
        new TextErrorContext("while evaluating dotCall .string of Obj"),
        new TextErrorContext("while evaluating dotCall .member"),
        new CallContext("F"),
        new CallContext("5.Inc"),
        new PropertyEvaluationContext("P"),
        new ParameterEvaluationContext("p"),
        new ArgumentEvaluationContext("{...}"),
        new DotCallContext("Obj", "member"),
        new DotCallContext("Obj", "string"),
        new DeconstructionBindingContext(["a", "*rest", "z"], true),
        new DeconstructionBindingContext(["a", "b"], false),
        new SequenceValueParameterBindingContext("(b, c)", false),
        new ListValueParameterBindingContext("[b, *c]", true),
        new ReduceInitialAccumulatorContext(["acc", "item"]),
        new LoopStateBindingContext("while", ["x", "y"], 1),
        new VariadicLoopStateBindingContext("repeat", ["x", "*rest"], 1, 0),
        new ImplicitParameterContext(["x", "y"], 1),
        new ProgramEvaluationContext(),
    ]);

    // Every public error kind with every degenerate payload, and the internal provenance the
    // recognizers read: whose missing output it is, a located arity mismatch, the not-callable
    // descriptions with a wording of their own.
    private static readonly Lazy<EvalError[]> GeneratedErrors = new(() => [.. KatLangErrorTotalityTests.BuildAll<EvalError>(typeof(EvalError.WithContext))]);

    private static readonly Lazy<EvalError[]> WrittenErrors = new(() =>
    [
        new EvalError.UnknownName("member"),
        new EvalError.UnknownName("string"),
        new EvalError.MissingOutput { IsNested = true },
        new EvalError.MissingOutput { IsNested = true, KeepsOwnBlame = true },
        new EvalError.MissingOutput { IsSelectedMemberOutput = true },
        new EvalError.MissingOutput { IsSelectedMemberOutput = true, IsNested = true },
        new EvalError.ArityMismatch(2, 1) { Span = Span },
        new EvalError.ArityMismatch(2, 3),
        new EvalError.NotAnAlgorithm(Evaluator.ComputedDotCalleeDescription),
        new EvalError.NotAnAlgorithm(Evaluator.MetaRefusalDescription),
        new EvalError.NotAnAlgorithm("param(f)"),
        new EvalError.LocalOnlyProperty("Obj", "P", PropertyExposure.LocalOnlyCapturedAncestorParameters) { RequiredParameters = ["a", "b"] },
        new EvalError.UnresolvedImplicitParams(["x", "y"]),
    ]);

    private static ErrorContext[] AllContexts() => [.. GeneratedContexts.Value, .. WrittenContexts.Value];

    private static EvalError[] AllErrors() => [.. GeneratedErrors.Value, .. WrittenErrors.Value];

    // One value per kind (the first generated one), then every hand-written payload: the frames
    // and errors of the nested chains.
    private static ErrorContext[] ContextKinds()
        => [.. GeneratedContexts.Value.DistinctBy(static context => context.GetType()), .. WrittenContexts.Value];

    private static EvalError[] ErrorKinds()
        => [.. GeneratedErrors.Value.DistinctBy(static error => error.GetType()), .. WrittenErrors.Value];

    // The errors a recognizer reads below a frame, and three it does not.
    private static EvalError[] RecognizedErrorKinds()
        => [.. ErrorKinds().Where(static error => error is EvalError.MissingOutput or EvalError.ArityMismatch or EvalError.UnknownName
            or EvalError.BadArity or EvalError.UnresolvedImplicitParams or EvalError.NotAnAlgorithm or EvalError.LocalOnlyProperty
            or EvalError.TypeMismatch or EvalError.DivByZero or EvalError.EvaluationStepLimitExceeded)];

    // ── Parity ───────────────────────────────────────────────────────────────

    [Fact]
    public void EveryErrorBelowEveryFrame_FormatsLikeTheRecursion()
    {
        var (contexts, errors) = (AllContexts(), AllErrors());
        var differences = new List<string>();
        var recognized = 0;
        foreach (var error in errors)
        {
            AssertSameAsTheRecursion(error, differences);
            foreach (var context in contexts)
            {
                var framed = new EvalError.WithContext(context, error);
                AssertSameAsTheRecursion(framed, differences);
                if (KatLangError.TryFormatRecognizedShape(framed, null, searchChain: true, out _))
                    recognized++;
            }
        }

        output.WriteLine($"{errors.Length} errors below {contexts.Length} frames; {recognized} framed shapes have a tailored message");
        Assert.True(differences.Count == 0, "the loop and the former recursion differ:\n" + string.Join("\n", differences));
        // Not vacuous: the corpus reaches the tailored shapes as well as the generic rendering.
        Assert.True(recognized > 100 && recognized < errors.Length * contexts.Length / 2, $"{recognized} recognized shapes");
    }

    [Fact]
    public void EveryPairAndTripleOfFrames_FormatsLikeTheRecursion()
    {
        // A tailored shape below one or two ordinary frames, an ordinary frame below a frame the
        // chain searches look for, two recognized frames in either order: every recognizer is
        // asked about an inner part of a chain here, which is where the loop asks fewer of them.
        var contexts = ContextKinds();
        var differences = new List<string>();
        long chains = 0;
        foreach (var error in ErrorKinds())
        {
            foreach (var inner in contexts)
            {
                var one = new EvalError.WithContext(inner, error);
                foreach (var outer in contexts)
                {
                    AssertSameAsTheRecursion(new EvalError.WithContext(outer, one), differences);
                    chains++;
                }
            }
        }

        // Triples over the hand-written frames (every recognized kind, the legacy prose, an ordinary
        // frame) above the errors a recognizer reads.
        var written = WrittenContexts.Value;
        foreach (var error in RecognizedErrorKinds())
        {
            foreach (var inner in written)
            {
                var one = new EvalError.WithContext(inner, error);
                foreach (var middle in written)
                {
                    var two = new EvalError.WithContext(middle, one);
                    foreach (var outer in written)
                    {
                        AssertSameAsTheRecursion(new EvalError.WithContext(outer, two), differences);
                        chains++;
                    }
                }
            }
        }

        output.WriteLine($"{contexts.Length} frame kinds, {written.Length} hand-written frames: {chains} chains of two and three frames");
        Assert.True(differences.Count == 0, "the loop and the former recursion differ:\n" + string.Join("\n", differences));
    }

    [Theory]
    [InlineData(20261111)]
    [InlineData(7)]
    public void SeededLongerChains_FormatLikeTheRecursion(int seed)
    {
        var random = new Random(seed);
        var (contexts, errors) = (ContextKinds(), ErrorKinds());
        var differences = new List<string>();
        var searched = 0;
        for (var sample = 0; sample < 20_000; sample++)
        {
            EvalError chain = errors[random.Next(errors.Length)];
            var frames = random.Next(1, 17);
            for (var level = 0; level < frames; level++)
            {
                chain = new EvalError.WithContext(contexts[random.Next(contexts.Length)], chain);
                // Some frames are located, as the evaluator's are; a span never changes the text.
                if (random.Next(4) == 0)
                    chain = chain with { Span = Span };
            }

            AssertSameAsTheRecursion(chain, differences);
            // A chain-searched shape in an inner part of a chain is the whole message.
            if (chain is EvalError.WithContext { Inner: EvalError.WithContext }
                && KatLangError.TryFormatRecognizedShape(chain, null, searchChain: true, out var whole)
                && !KatLangError.TryFormatRecognizedShape(chain, null, searchChain: false, out _))
            {
                searched++;
                Assert.Equal(whole, KatLangError.FromEvalError(chain).Message);
            }
        }

        output.WriteLine($"seed {seed}: 20000 chains of 1 to 16 frames; {searched} were answered by a chain search below the outermost frame");
        Assert.True(differences.Count == 0, "the loop and the former recursion differ:\n" + string.Join("\n", differences));
        Assert.True(searched > 20, $"{searched} chain-searched samples");
    }

    [Fact]
    public void PublicRoutes_ReportTheFormattedChain()
    {
        // The facade's three renderings of one chain are the formatter's text: the message, its
        // located form, and the terminal-safe form whose fragments are escaped one by one.
        var located = new EvalError.WithContext(new CallContext("Outer"),
            new EvalError.WithContext("host frame \u001b[31m",
                new EvalError.WithContext(new PropertyEvaluationContext("P"), new EvalError.TypeMismatch("a\nb")))) { Span = Span };
        var report = KatLangError.FromEvalError(located);

        Assert.Equal("while evaluating call to Outer: host frame \u001b[31m: while evaluating property P: Type mismatch: a\nb", report.Message);
        Assert.Equal(Reference(located, null), report.Message);
        Assert.Equal("[3:4] " + report.Message, report.ToString());
        Assert.Equal(
            "[3:4] while evaluating call to Outer: host frame \\u001B[31m: while evaluating property P: Type mismatch: a\\u000Ab",
            report.ToTerminalSafeString());
        Assert.Equal("[3:4] " + Reference(located, Marked), report.RenderDiagnostic(Marked));
        Assert.Same(located, report.Source);
        Assert.Equal(KatLangErrorCode.TypeMismatch, report.Code);
    }

    // ── Host-built frames ────────────────────────────────────────────────────

    [Fact]
    public void HostBuiltNullFrames_FailAsTheRecursionDid()
    {
        // No evaluation produces a frame around a null error or with a null context. The former
        // formatter reached its exhaustive switch with null, or read the null context's text;
        // the loop fails with the same exception, at the same frame.
        var unknown = new EvalError.UnknownName("x");
        EvalError[] malformed =
        [
            new EvalError.WithContext("frame", null!),
            new EvalError.WithContext(new CallContext("F"), new EvalError.WithContext("frame", null!)),
            new EvalError.WithContext((ErrorContext)null!, unknown),
            new EvalError.WithContext("frame", new EvalError.WithContext((ErrorContext)null!, unknown)),
            new EvalError.WithContext((ErrorContext)null!, null!),
        ];

        foreach (var error in malformed)
        {
            var expected = Outcome(() => Reference(error, null));
            Assert.StartsWith("throws ", expected, StringComparison.Ordinal);
            Assert.Equal(expected, Outcome(() => KatLangError.FormatEvalError(error, null)));
            Assert.Equal(Outcome(() => Reference(error, Marked)), Outcome(() => KatLangError.FormatEvalError(error, Marked)));
            Assert.Equal(expected, Outcome(() => KatLangError.FromEvalError(error).Message));
        }

        // A renderer's own failure is the caller's, at the fragment it was asked for.
        var chain = new EvalError.WithContext("outer", new EvalError.WithContext("inner", unknown));
        var asked = new List<string>();
        string Failing(string fragment)
        {
            asked.Add(fragment);
            return fragment == "inner" ? throw new NotSupportedException() : fragment;
        }

        Assert.Throws<NotSupportedException>(() => KatLangError.FormatEvalError(chain, Failing));
        Assert.Equal(["outer", "inner"], asked);
    }

    // ── Depth ────────────────────────────────────────────────────────────────

    [Fact]
    public void TwoHundredThousandFrames_FormatWithoutRecursion() => AssertDeepChains();

    /// <summary>
    /// 200,000 host-built frames (a run's own chains are bounded by its depth limit) over an
    /// ordinary error, over a tailored one-frame shape, and over each shape a chain search finds
    /// at the innermost frame. Assertion messages are constants: a failure must not print the
    /// megabytes it is about.
    /// </summary>
    internal static void AssertDeepChains()
    {
        const int depth = 200_000;

        // An ordinary error: every frame is written, in order, once.
        var unknown = Frames(new EvalError.UnknownName("x"), depth);
        var report = KatLangError.FromEvalError(unknown);
        AssertFramed(report.Message, "Unknown name: x", depth);
        Assert.True(report.Code == KatLangErrorCode.UnknownName && !report.IsResourceLimit && report.Span is null, "classification through the frames");
        Assert.True(ReferenceEquals(report.Source, unknown), "the report keeps the host's chain");
        Assert.True(report.ToString() == report.Message, "an unlocated report prints its message");
        // Nothing here needs escaping, so the fragment-by-fragment rendering is the same text.
        Assert.True(report.ToTerminalSafeString() == report.Message, "the terminal-safe rendering of the frames");

        // A tailored shape of the innermost frame and its error ends the same chain.
        var ownMissing = new EvalError.WithContext(new CallContext("F"), new EvalError.MissingOutput());
        var tailored = KatLangError.FromEvalError(ownMissing).Message;
        Assert.True(tailored.StartsWith("Cannot call 'F' because it has no defined output.", StringComparison.Ordinal), "the tailored call message");
        AssertFramed(KatLangError.FromEvalError(Frames(ownMissing, depth)).Message, tailored, depth);

        // The three shapes that are searched for below ordinary frames are the whole message,
        // wherever the frame sits: found by ONE search of the chain, not one per frame.
        (EvalError Shape, string Opening)[] searched =
        [
            (new EvalError.WithContext(new DeconstructionBindingContext(["a", "b"], false), new EvalError.ArityMismatch(2, 3)), "Assignment pattern `a, b` expects"),
            (new EvalError.WithContext(new SequenceValueParameterBindingContext("(b, c)", false), new EvalError.ArityMismatch(2, 3)), "Sequence pattern `(b, c)` expects"),
            (new EvalError.WithContext(new ListValueParameterBindingContext("[b, c]", false), new EvalError.ArityMismatch(2, 3)), "List pattern `[b, c]` expects"),
            (new EvalError.WithContext(new ReduceInitialAccumulatorContext(["acc"]), new EvalError.BadArity()), ""),
        ];
        foreach (var (shape, opening) in searched)
        {
            var shallow = KatLangError.FromEvalError(shape).Message;
            Assert.True(shallow.StartsWith(opening, StringComparison.Ordinal) && !shallow.StartsWith("while ", StringComparison.Ordinal), "a searched shape has its own message");
            Assert.True(KatLangError.FromEvalError(Frames(shape, depth)).Message == shallow, "a searched shape below 200,000 frames is the whole message");
        }

        static EvalError Frames(EvalError inner, int frames)
        {
            for (var level = 0; level < frames; level++)
                inner = new EvalError.WithContext("frame", inner);
            return inner;
        }
    }

    private static void AssertFramed(string message, string innermost, int frames)
    {
        const string frame = "frame: ";
        Assert.True(message.Length == (long)frames * frame.Length + innermost.Length, "message length");
        var text = message.AsSpan();
        for (var level = 0; level < frames; level++)
            Assert.True(text.Slice(level * frame.Length, frame.Length).SequenceEqual(frame), "frame prefix");
        Assert.True(text[(frames * frame.Length)..].SequenceEqual(innermost), "innermost message");
    }
}
