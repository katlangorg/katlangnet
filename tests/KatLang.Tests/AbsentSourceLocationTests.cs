using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.ParserFuzz;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// ABSENCE OF A SOURCE LOCATION IS <c>null</c>, NEVER <c>default(SourceSpan)</c> (F2).
///
/// <para><see cref="SourceSpan"/> is a value type whose <c>default</c> carries the invalid
/// coordinates <c>0:0</c>; its constructors refuse those coordinates, so the default can only
/// arise where construction was bypassed. <c>DeclarationSpans.FirstOrDefault()</c> is exactly
/// such a bypass: <see cref="Property.DeclarationSpans"/> spells "no declared name occurrence"
/// as an EMPTY list, and <c>FirstOrDefault</c> turns that emptiness into the default struct,
/// which the surrounding <c>SourceSpan?</c> then carries as a PRESENT location. A spanless
/// property — a deconstruction's hoisted source, a module's locationless import view, a
/// prelude or host-operation binding, a host-built node — that refused a budgeted invocation
/// therefore reported <c>[0:0]</c> through the public <see cref="KatLangError.Span"/>, and the
/// fabricated span also BLOCKED the attach-if-missing law (<c>Evaluator.AtSpanIfMissing</c>)
/// from later supplying the real enclosing location.</para>
///
/// <para>The one reader is now <c>Property.FirstDeclarationSpan</c>, and every consumer of an
/// optional declaration anchor goes through it: the generic zero-argument property access and
/// its async twin, the top-level property demand and its async twin, the planned loop
/// temporary, the engine's <c>DisplayDecimals</c> anchor, and the import site. These tests pin
/// both halves — a real declaration span still WINS, and a missing one stays absent until a
/// legitimate enclosing span attaches — across the deconstruction, planner, host-built,
/// imported, sync and async paths, on the structured span AND the rendered diagnostic.</para>
/// </summary>
public class AbsentSourceLocationTests
{
    private const string Lib = "https://katlang.org/lib.kat";

    /// <summary>
    /// A module-provided loop step whose local temporary is plannable. The import view is
    /// locationless, so the planned temporary carries no declaration span; the <c>if</c>
    /// control pushes the temporary's read one budget level deeper than the loop's own
    /// entry, which is what makes the temporary's refusal the FIRST one and therefore the
    /// one that stamps the error.
    /// </summary>
    private const string PlannableStepModule = "public Step(a) = {\n  t = a + 1\n  if(t > 0, t, 0)\n}";

    private const string PlannedLoopDocument = "open '" + Lib + "'\nrepeat(Step, 3, 1)";

    /// <summary>The document's own <c>repeat(Step, 3, 1)</c> row — the legitimate enclosing location.</summary>
    private static readonly SourceSpan PlannedLoopCallSpan = new(2, 1, 2, 19);

    private static RunOptions ModuleOptions(
        EvaluationLimits? limits,
        params (string Url, string Source)[] modules)
    {
        var files = modules.ToDictionary(module => module.Url, module => module.Source, StringComparer.Ordinal);
        return new RunOptions
        {
            EvaluationLimits = limits,
            DownloadCode = (url, _) => files.TryGetValue(url, out var source)
                ? ValueTask.FromResult(source)
                : throw new InvalidOperationException($"404: {url}"),
        };
    }

    private static KatLangError SingleError(RunResult result)
        => Assert.Single(Assert.IsType<RunResult.EvalFailure>(result).Errors);

    private static KatLangError ErrorOf(EvalResult<Evaluator.CountedResult> result)
    {
        Assert.True(result.IsError, "expected a resource-limit failure");
        return KatLangError.FromEvalError(result.Error);
    }

    private static KatLangError ErrorOf(EvalResult<Evaluator.CountedRootProgramResult> result)
    {
        Assert.True(result.IsError, "expected a rejected zero-argument demand");
        return KatLangError.FromEvalError(result.Error);
    }

    /// <summary>
    /// The public contract: a present <see cref="KatLangError.Span"/> is a LEGITIMATE location
    /// of <paramref name="source"/>'s own coordinate space — never the default struct, never a
    /// zero coordinate, never text the document does not have. An absent one renders without a
    /// location prefix.
    /// </summary>
    private static void AssertLegitimateOrAbsent(KatLangError error, string source)
    {
        if (error.Span is not { } span)
        {
            Assert.Equal(error.Message, error.ToString());
            return;
        }

        Assert.NotEqual(default, span);
        Assert.True(span.Start.Line >= 1 && span.Start.Column >= 1, $"fabricated start coordinate {span}");
        Assert.True(span.End.Line >= 1 && span.End.Column >= 1, $"fabricated end coordinate {span}");
        Assert.Null(SourceSpanValidator.Validate(span, SourceSpanValidator.LineWidths(source)));
        Assert.Equal($"[{span.Start.Line}:{span.Start.Column}] {error.Message}", error.ToString());
    }

    private static void AssertAbsent(KatLangError error)
    {
        Assert.Null(error.Span);
        Assert.False(error.Span.HasValue);
        Assert.Equal(error.Message, error.ToString());
        Assert.DoesNotContain("[0:0]", error.ToString(), StringComparison.Ordinal);
    }

    // ── 1. Deconstruction: the hoisted source property is spanless by construction ────

    // `x, y = RHS` hoists the right-hand side into the synthetic `$deconstruct$N` property,
    // which declares no source-backed name (Parser.AddDeconstructionProperties). Reading a
    // target evaluates that hoisted property as an ordinary zero-argument property access, so
    // a budget refused there used to be stamped [0:0]; it must now stay absent so the demanding
    // row's own span attaches.

    [Theory]
    [InlineData(1)]
    [InlineData(2)]
    public void DeconstructionHoistedSource_DepthRefusal_IsPositionedAtTheDemandingRow(int maxDepth)
    {
        const string source = "x, y = 1, 2\nx";
        var error = SingleError(KatLangEngine.Run(
            source,
            new RunOptions { EvaluationLimits = new EvaluationLimits { MaxDepth = maxDepth } }));

        Assert.Equal(KatLangErrorCode.EvaluationDepthExceeded, error.Code);
        AssertLegitimateOrAbsent(error, source);
        Assert.Equal(new SourceSpan(2, 1, 2, 2), error.Span);
        Assert.Equal($"[2:1] Evaluation recursion limit of {maxDepth} was exceeded", error.ToString());
    }

    [Theory]
    [InlineData(1)]
    [InlineData(2)]
    public void DeconstructionHoistedSource_StepRefusal_IsPositionedAtTheDemandingRow(int maxSteps)
    {
        const string source = "x, y = 1, 2\nx";
        var error = SingleError(KatLangEngine.Run(
            source,
            new RunOptions { EvaluationLimits = new EvaluationLimits { MaxSteps = maxSteps } }));

        Assert.Equal(KatLangErrorCode.EvaluationStepLimitExceeded, error.Code);
        AssertLegitimateOrAbsent(error, source);
        Assert.Equal(new SourceSpan(2, 1, 2, 2), error.Span);
        Assert.Equal($"[2:1] Evaluation step limit of {maxSteps} was exceeded", error.ToString());
    }

    [Fact]
    public async Task DeconstructionHoistedSource_AsyncTwin_AgreesWithTheSynchronousSpan()
    {
        const string source = "x, y = 1, 2\nx";
        var limits = new EvaluationLimits { MaxDepth = 2 };
        var ast = AsyncEvaluationHarness.Ast(source);

        var sync = ErrorOf(Evaluator.RunCounted(ast, new RunScopedZeroArgPropertyResultCache(), limits));

        // A genuinely suspending cache: the property seam really awaits and resumes, so the
        // error crosses an async seam before it is reported.
        var cache = new SuspendingAsyncZeroArgPropertyResultCache();
        var async = ErrorOf(await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedAsync(ast, cache, limits)));

        Assert.True(cache.AsyncAccesses > 0, "the twin path was not taken");
        Assert.True(cache.ObservedThreadHop, "the run never genuinely suspended");
        AssertLegitimateOrAbsent(sync, source);
        AssertLegitimateOrAbsent(async, source);
        Assert.Equal(sync.Span, async.Span);
        Assert.Equal(sync.ToString(), async.ToString());
        Assert.Equal(new SourceSpan(2, 1, 2, 2), async.Span);
    }

    // ── 2. Planner: an optimized loop temporary with no declaration span ──────────────

    [Fact]
    public void PlannedLoopTemporary_SpanlessDeclaration_IsPositionedAtTheDocumentsLoopCall()
    {
        var parsed = ParsePlannedLoopDocument();
        var diagnostics = new LoopOptimizationDiagnostics();
        var (result, _) = Evaluator.RunCountedObserved(
            new Expr.AlgorithmExpr(parsed.Root),
            new EvaluationLimits { MaxDepth = 1 },
            enableOptimizations: true,
            loopDiagnostics: diagnostics);

        // The PLANNED path must be the one that ran: the loop was optimized, its local
        // property was planned as a temporary, and no expression inside it fell back to
        // generic evaluation. Otherwise this would silently pin the generic path instead.
        var snapshot = diagnostics.GetSnapshot();
        Assert.Equal(1, snapshot.OptimizedLoopHits);
        Assert.Equal(0, snapshot.GenericExpressionEvaluationsInsideOptimizedLoops);
        var plan = Assert.Single(snapshot.LoopPlans);
        Assert.True(plan.Optimized);
        Assert.True(plan.ExecutionCount >= 1);
        var temp = Assert.Single(plan.Temps);
        Assert.Equal("t", temp.Name);
        Assert.True(temp.Planned, $"the loop temporary was not planned: {temp.FallbackReason}");

        var error = ErrorOf(result);
        Assert.Equal(KatLangErrorCode.EvaluationDepthExceeded, error.Code);
        AssertLegitimateOrAbsent(error, PlannedLoopDocument);
        // The IMPORTED temporary contributes no coordinate of its own; the location is the
        // current document's loop call, never a module-relative one and never [0:0].
        Assert.Equal(PlannedLoopCallSpan, error.Span);
        Assert.Equal("[2:1] Evaluation recursion limit of 1 was exceeded", error.ToString());
    }

    [Fact]
    public void PlannedAndGenericLoopStrategies_AgreeOnTheSpanlessTemporarysLocation()
    {
        var ast = new Expr.AlgorithmExpr(ParsePlannedLoopDocument().Root);
        var limits = new EvaluationLimits { MaxDepth = 1 };

        var plannedDiagnostics = new LoopOptimizationDiagnostics();
        var planned = ErrorOf(Evaluator.RunCountedObserved(
            ast, limits, enableOptimizations: true, loopDiagnostics: plannedDiagnostics).Result);

        var genericDiagnostics = new LoopOptimizationDiagnostics();
        var generic = ErrorOf(Evaluator.RunCountedObserved(
            ast, limits, enableOptimizations: false, loopDiagnostics: genericDiagnostics).Result);

        Assert.Equal(1, plannedDiagnostics.GetSnapshot().OptimizedLoopHits);
        Assert.Equal(0, genericDiagnostics.GetSnapshot().OptimizedLoopHits);
        AssertLegitimateOrAbsent(planned, PlannedLoopDocument);
        AssertLegitimateOrAbsent(generic, PlannedLoopDocument);
        Assert.Equal(generic.Span, planned.Span);
        Assert.Equal(generic.ToString(), planned.ToString());
    }

    private static ParseResult ParsePlannedLoopDocument()
    {
        var parsed = Parser.ParseAsync(PlannedLoopDocument, ModuleOptions(limits: null, (Lib, PlannableStepModule)))
            .GetAwaiter()
            .GetResult();
        Assert.False(
            parsed.HasErrors,
            "the planner repro must elaborate cleanly: "
                + string.Join("; ", parsed.Diagnostics.Select(d => d.Message.Split('\n')[0])));
        return parsed;
    }

    // ── 3. Host-built trees: absence must SURVIVE, not become a fake position ─────────

    /// <summary>A host-built root with two spanless properties; reading <c>A</c> reads <c>B</c>.</summary>
    private static Expr HostBuiltChain()
        => new Expr.AlgorithmExpr(new Algorithm.User(
            Parent: null,
            ParameterPatterns: [],
            Opens: [],
            Properties:
            [
                new Property("A", new Algorithm.User(null, [], [], [], [new Expr.Resolve("B")])),
                new Property("B", new Algorithm.User(null, [], [], [], [new Expr.Num(1)])),
            ],
            Output: [new Expr.Resolve("A")]));

    /// <summary>A host-built root whose spanless <c>DisplayDecimals</c> cannot take zero arguments.</summary>
    private static Expr HostBuiltTopLevelProperty()
        => new Expr.AlgorithmExpr(new Algorithm.User(
            Parent: null,
            ParameterPatterns: [],
            Opens: [],
            Properties:
            [
                new Property(
                    "DisplayDecimals",
                    new Algorithm.User(
                        Parent: null,
                        ParameterPatterns: [new CaptureParameterPattern(new ParameterDeclaration("n"))],
                        Opens: [],
                        Properties: [],
                        Output: [new Expr.Param("n")])
                    {
                        HasExplicitParameterList = true,
                    }),
            ],
            Output: [new Expr.Num(1)]));

    [Fact]
    public void HostBuiltSpanlessProperty_RefusedInvocation_StaysSpanless()
    {
        var error = ErrorOf(Evaluator.RunCounted(
            HostBuiltChain(),
            new RunScopedZeroArgPropertyResultCache(),
            new EvaluationLimits { MaxDepth = 1 }));

        Assert.Equal(KatLangErrorCode.EvaluationDepthExceeded, error.Code);
        AssertAbsent(error);
        Assert.Equal("Evaluation recursion limit of 1 was exceeded", error.ToString());
    }

    [Fact]
    public void HostBuiltSpanlessTopLevelProperty_RejectedZeroArgumentDemand_StaysSpanless()
    {
        var error = ErrorOf(Evaluator.RunCountedWithTopLevelProperty(
            HostBuiltTopLevelProperty(),
            "DisplayDecimals",
            new RunScopedZeroArgPropertyResultCache()));

        Assert.Equal(KatLangErrorCode.ArityMismatch, error.Code);
        AssertAbsent(error);
    }

    [Fact]
    public async Task HostBuiltSpanlessTopLevelProperty_AsyncTwin_StaysSpanless()
    {
        var cache = new SuspendingAsyncZeroArgPropertyResultCache();
        var error = ErrorOf(await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedWithTopLevelPropertyAsync(
                HostBuiltTopLevelProperty(), "DisplayDecimals", cache)));

        Assert.Equal(KatLangErrorCode.ArityMismatch, error.Code);
        AssertAbsent(error);
    }

    // ── 4. A REAL declaration span still wins ────────────────────────────────────────

    [Fact]
    public void WrittenPropertyDeclaration_StampsTheRefusedInvocationWithItsOwnSpan()
    {
        // Reading `A` (depth 1) reads `B`, whose entry is refused and stamped with B's own
        // declaration span — the specific location, not the outer row's.
        const string source = "A = B\nB = 1\nA";
        var error = SingleError(KatLangEngine.Run(
            source,
            new RunOptions { EvaluationLimits = new EvaluationLimits { MaxDepth = 1 } }));

        Assert.Equal(KatLangErrorCode.EvaluationDepthExceeded, error.Code);
        AssertLegitimateOrAbsent(error, source);
        Assert.Equal(new SourceSpan(2, 1, 2, 2), error.Span);
    }

    [Fact]
    public void WrittenTopLevelPropertyDeclaration_StampsTheRejectedDemandWithItsOwnSpan()
    {
        const string source = "DisplayDecimals(n) = n\n1 / 3";
        var error = SingleError(KatLangEngine.Run(source));

        Assert.Equal(KatLangErrorCode.ArityMismatch, error.Code);
        AssertLegitimateOrAbsent(error, source);
        Assert.Equal(new SourceSpan(1, 1, 1, 16), error.Span);
    }

    [Fact]
    public async Task WrittenTopLevelPropertyDeclaration_AsyncTwin_KeepsThatSameSpan()
    {
        const string source = "DisplayDecimals(n) = n\n1 / 3";
        var cache = new SuspendingAsyncZeroArgPropertyResultCache();
        var error = ErrorOf(await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedWithTopLevelPropertyAsync(
                AsyncEvaluationHarness.Ast(source), "DisplayDecimals", cache)));

        AssertLegitimateOrAbsent(error, source);
        Assert.Equal(new SourceSpan(1, 1, 1, 16), error.Span);
    }

    // ── 5. The public error contract, swept ──────────────────────────────────────────

    public static TheoryData<string> SpanlessProducerPrograms =>
    [
        // Deconstruction-generated hoisted source, one and several targets.
        "x, y = 1, 2\nx",
        "x, y = 1, 2\ny",
        "x, *rest = 1, 2, 3\nrest",
        // Nested deconstruction inside a brace body.
        "F = {\n  p, q = 1, 2\n  p\n}\nF",
        // Deconstruction feeding a loop step, and a plannable loop temporary beside it.
        "Step(a) = {\n  p, q = a, a\n  p + q\n}\nrepeat(Step, 3, 1)",
        "Step(a) = {\n  t = a + 1\n  if(t > 0, t, 0)\n}\nrepeat(Step, 3, 1)",
        // Prelude and Math bindings declare no source name either.
        "A = Math.Pi\nA",
        "A = Math.Pi\nB = A\nB",
        "A = sum((1, 2, 3))\nA",
        // Ordinary written properties and recursion: the control group.
        "A = B\nB = 1\nA",
        "A = A\nA",
        "F(n) = if(n > 0, F(n - 1), 0)\nF(20)",
    ];

    /// <summary>
    /// Every charge point of a program, swept: each limit makes a DIFFERENT budgeted
    /// invocation the refused one, so the invariant is checked at every place a refusal can
    /// be stamped rather than at a single hand-picked ordinal.
    /// </summary>
    private static IEnumerable<EvaluationLimits> SweepLimits()
    {
        for (var depth = 1; depth <= 6; depth++)
            yield return new EvaluationLimits { MaxDepth = depth };
        for (var steps = 1L; steps <= 24; steps++)
            yield return new EvaluationLimits { MaxSteps = steps };
    }

    [Theory]
    [MemberData(nameof(SpanlessProducerPrograms))]
    public void EveryPublicErrorSpan_IsALegitimateLocationOfItsOwnDocument(string source)
    {
        var observedFailure = false;
        foreach (var limits in SweepLimits())
        {
            if (KatLangEngine.Run(source, new RunOptions { EvaluationLimits = limits }) is not RunResult.EvalFailure failure)
                continue;

            observedFailure = true;
            Assert.NotEmpty(failure.Errors);
            foreach (var error in failure.Errors)
                AssertLegitimateOrAbsent(error, source);
        }

        Assert.True(observedFailure, "no limit in the sweep made this program fail, so nothing was checked");
    }

    [Fact]
    public async Task ImportedContent_KeepsTheLoadingDocumentsCoordinates_UnderAResourceLimit()
    {
        // The import view is locationless at every depth. A refusal inside it must be
        // positioned by the CURRENT document (or stay absent) — never at a module-relative
        // coordinate and never at the fabricated default.
        const string module = "public Deep = Deeper\npublic Deeper = 1";
        const string document = "open '" + Lib + "'\nDeep";
        var options = ModuleOptions(new EvaluationLimits { MaxDepth = 1 }, (Lib, module));

        var error = SingleError(await KatLangEngine.RunAsync(document, options));
        Assert.Equal(KatLangErrorCode.EvaluationDepthExceeded, error.Code);
        AssertLegitimateOrAbsent(error, document);
    }

    // ── 6. The mechanism itself ──────────────────────────────────────────────────────

    [Fact]
    public void NoProductionSite_ReadsAnOptionalSpanThroughFirstOrDefault()
    {
        // The root cause was one expression shape, so it is pinned as one: `FirstOrDefault`
        // over a collection of VALUE-typed spans silently manufactures default(SourceSpan).
        // Property.FirstDeclarationSpan is the sanctioned reader.
        var offenders = Directory
            .EnumerateFiles(Path.Combine(RepoRoot.Find(), "src"), "*.cs", SearchOption.AllDirectories)
            .Where(file => !file.Contains($"{Path.DirectorySeparatorChar}obj{Path.DirectorySeparatorChar}", StringComparison.Ordinal)
                && !file.Contains($"{Path.DirectorySeparatorChar}bin{Path.DirectorySeparatorChar}", StringComparison.Ordinal))
            .SelectMany(file => File.ReadAllLines(file)
                .Select((line, index) => (File: file, Number: index + 1, Text: line))
                // Prose may NAME the defective shape; only code may not use it.
                .Where(entry => !entry.Text.TrimStart().StartsWith("//", StringComparison.Ordinal)
                    && !entry.Text.TrimStart().StartsWith("*", StringComparison.Ordinal))
                .Where(entry => entry.Text.Contains("Spans.FirstOrDefault(", StringComparison.Ordinal)
                    || entry.Text.Contains("Spans.SingleOrDefault(", StringComparison.Ordinal)
                    || entry.Text.Contains("Spans.LastOrDefault(", StringComparison.Ordinal)))
            .Select(entry => $"{Path.GetRelativePath(RepoRoot.Find(), entry.File).Replace('\\', '/')}:{entry.Number}: {entry.Text.Trim()}")
            .ToList();

        Assert.True(
            offenders.Count == 0,
            "A span collection must not be read with *OrDefault (it yields default(SourceSpan), "
                + "a present [0:0] location). Use Property.FirstDeclarationSpan or an explicit "
                + "count check:" + Environment.NewLine + string.Join(Environment.NewLine, offenders));
    }

    [Fact]
    public void FirstDeclarationSpan_IsNullExactlyWhenThereIsNoDeclaredName()
    {
        var spanless = new Property("P", new Algorithm.User(null, [], [], [], []));
        Assert.Empty(spanless.DeclarationSpans);
        Assert.Null(spanless.FirstDeclarationSpan);
        // The shape the defect had: the empty list's FirstOrDefault is a PRESENT [0:0].
        Assert.Equal(default, spanless.DeclarationSpans.FirstOrDefault());
        Assert.True(((SourceSpan?)spanless.DeclarationSpans.FirstOrDefault()).HasValue);

        var declared = spanless with { DeclarationSpans = [new SourceSpan(3, 5, 3, 6), new SourceSpan(9, 1, 9, 2)] };
        Assert.Equal(new SourceSpan(3, 5, 3, 6), declared.FirstDeclarationSpan);
    }
    // ── 7. A written slot that CAN be located IS located ─────────────────────────────

    /// <summary>
    /// The complementary half of the rule above: absence is only legitimate when there is
    /// genuinely nothing to point at. A WRITTEN element of a list literal is precisely
    /// locatable, and a brace-block element used to report its missing output with NO span
    /// at all — <c>[1, { }, 3]</c> produced "Algorithm has no defined output." with no
    /// location, while the very same element inside a parenthesized group was located
    /// exactly at the block.
    ///
    /// <para>The cause was structural, not list-specific: <c>EvalExplicitSequenceValueExprSlots</c>
    /// is the written-slot dispatcher, and only its two UNFOLDING arms — a nested capture
    /// and a zero-argument block — bypass <c>EvalCounted</c>, which positions every arm it
    /// owns. Every other element kind fell through to <c>EvalCounted</c> and was located, so
    /// only block-shaped (and capture-wrapped block) elements lost the position. Both arms
    /// now apply the very span rule <c>EvalCounted</c> applies to the same node
    /// (<c>WithPreferredSpanOf</c> — the written node, else its first positioned row), and
    /// <c>AtSpanIfMissing</c> keeps a span the inner failure already carries, so a nested
    /// slot still reports at its own precise location rather than at the enclosing one.</para>
    /// </summary>
    public static TheoryData<string, string> LocatableWrittenSlotPrograms => new()
    {
        // The repro and its control: the SAME element, in a list and in a group.
        { "[1, {}, 3]", "{}" },
        { "(1, {}, 3)", "{}" },
        // Every position in the list.
        { "[{}, 2, 3]", "{}" },
        { "[1, 2, {}]", "{}" },
        { "[{}]", "{}" },
        // A block with properties is still one written element.
        { "[1, { A = 1 }, 3]", "{ A = 1 }" },
        // Nested: the INNER written slot is blamed, not the enclosing list or group.
        { "[1, [2, {}], 3]", "{}" },
        { "(1, [2, {}])", "{}" },
        { "[1, ({}, 2), 3]", "{}" },
        { "[[{}]]", "{}" },
    };

    [Theory]
    [MemberData(nameof(LocatableWrittenSlotPrograms))]
    public void AnOutputLessWrittenSlot_IsLocatedAtThatSlot(string source, string writtenSlot)
    {
        var error = SingleError(KatLangEngine.Run(source));
        Assert.Equal(KatLangErrorCode.MissingOutput, error.Code);
        AssertLegitimateOrAbsent(error, source);
        Assert.Equal(SpanOfLastOccurrence(source, writtenSlot), error.Span);
    }

    /// <summary>
    /// The list and the parenthesized group agree exactly — same kind, same span, same
    /// rendered message. That equality is the defect's negative: they used to differ only
    /// because the list path skipped positioning.
    /// </summary>
    [Fact]
    public void ListLiteralAndParenthesizedGroup_LocateTheSameElementIdentically()
    {
        var list = SingleError(KatLangEngine.Run("[1, {}, 3]"));
        var group = SingleError(KatLangEngine.Run("(1, {}, 3)"));

        Assert.Equal(group.Code, list.Code);
        Assert.Equal(group.Span, list.Span);
        Assert.Equal(group.Message, list.Message);
        Assert.Equal(new SourceSpan(1, 5, 1, 7), list.Span);
    }

    /// <summary>
    /// Element kinds that were ALREADY located stay located and unchanged: only the two
    /// unfolding arms were unpositioned, so a name, a call, a spread, and ordinary operator
    /// failures inside a list keep their own spans.
    /// </summary>
    [Theory]
    [InlineData("L = {}\n[1, L, 3]", KatLangErrorCode.MissingOutput, 2, 5, 2, 6)]
    [InlineData("[1, {}*, 3]", KatLangErrorCode.SpreadMissingOutput, 1, 5, 1, 7)]
    [InlineData("[1, 1/0, 3]", KatLangErrorCode.DivisionByZero, 1, 5, 1, 8)]
    [InlineData("[1, 'a' + 1, 3]", KatLangErrorCode.TypeMismatch, 1, 5, 1, 12)]
    public void AlreadyLocatedElementKinds_AreUnchanged(
        string source,
        KatLangErrorCode code,
        int startLine,
        int startColumn,
        int endLine,
        int endColumn)
    {
        var error = SingleError(KatLangEngine.Run(source));
        Assert.Equal(code, error.Code);
        AssertLegitimateOrAbsent(error, source);
        Assert.Equal(new SourceSpan(startLine, startColumn, endLine, endColumn), error.Span);
    }

    /// <summary>
    /// Positioning is a diagnostic property only: legitimate empty VALUES in a list stay
    /// ordinary successful elements, and nothing about list construction changed.
    /// </summary>
    [Theory]
    [InlineData("[()]", "[()]")]
    [InlineData("[[]]", "[[]]")]
    [InlineData("[1, (), 3]", "[1, (), 3]")]
    [InlineData("[1, 2, 3]", "[1, 2, 3]")]
    [InlineData("[1, { 2 }, 3]", "[1, 2, 3]")]
    public void ListsOfLegitimateValues_AreUnaffected(string source, string expectedDisplay)
        => Assert.Equal(expectedDisplay, Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString());

    /// <summary>
    /// The async twin assembles written slots through the mirrored helper, and the
    /// optimizers delegate these shapes to the generic strategy, so all four executions
    /// agree on kind, span, and rendered message.
    /// </summary>
    [Theory]
    [InlineData("[1, {}, 3]")]
    [InlineData("[1, [2, {}], 3]")]
    [InlineData("[1, ({}, 2), 3]")]
    [InlineData("(1, [2, {}])")]
    public async Task SyncAsyncAndOptimizedExecution_AgreeOnTheLocation(string source)
    {
        var ast = new Expr.AlgorithmExpr(EvaluatorTestSupport.ParseValidRoot(source));

        var sync = Evaluator.Run(ast);
        var async = await Evaluator.RunAsync(ast, new RunScopedAsyncZeroArgPropertyResultCache());
        var generic = EvaluatorTestSupport.EvalFull(
            source, enableLoopOptimization: false, enableSequencePipelineOptimization: false);
        var optimized = EvaluatorTestSupport.EvalFull(
            source, enableLoopOptimization: true, enableSequencePipelineOptimization: true);

        foreach (var result in new[] { sync, async, generic, optimized })
            Assert.True(result.IsError, "expected every execution strategy to fail");

        var expected = KatLangError.FromEvalError(sync.Error);
        Assert.NotNull(expected.Span);
        foreach (var result in new[] { async, generic, optimized })
        {
            var actual = KatLangError.FromEvalError(result.Error);
            Assert.Equal(expected.Code, actual.Code);
            Assert.Equal(expected.Span, actual.Span);
            Assert.Equal(expected.Message, actual.Message);
        }
    }

    /// <summary>
    /// A HOST-built list literal follows the same rule: the element's span is taken from the
    /// node it was written on, so a host that supplies one gets it back, and a host that
    /// supplies none still gets genuine absence rather than a fabricated location.
    /// </summary>
    [Fact]
    public void HostBuiltListLiteral_UsesTheElementsOwnSpan_OrKeepsAbsence()
    {
        var elementSpan = new SourceSpan(4, 7, 4, 9);
        var positioned = new Expr.ListLiteral([
            new Expr.Num(1),
            new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [], [])) { Span = elementSpan },
            new Expr.Num(3),
        ]);

        var positionedError = KatLangError.FromEvalError(
            Evaluator.Run(new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [], [positioned]))).Error);
        Assert.Equal(KatLangErrorCode.MissingOutput, positionedError.Code);
        Assert.Equal(elementSpan, positionedError.Span);

        var spanless = new Expr.ListLiteral([
            new Expr.Num(1),
            new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [], [])),
            new Expr.Num(3),
        ]);

        var spanlessError = KatLangError.FromEvalError(
            Evaluator.Run(new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [], [spanless]))).Error);
        Assert.Equal(KatLangErrorCode.MissingOutput, spanlessError.Code);
        // Genuinely nothing to point at: absence stays null, never default(SourceSpan).
        Assert.Null(spanlessError.Span);
        Assert.Equal(spanlessError.Message, spanlessError.ToString());
    }

    /// <summary>
    /// The written extent of the LAST occurrence of <paramref name="writtenSlot"/> in
    /// <paramref name="source"/>, as a half-open span. The last occurrence is the innermost
    /// one for the nested cases, which is exactly the slot the blame must name.
    /// </summary>
    private static SourceSpan SpanOfLastOccurrence(string source, string writtenSlot)
    {
        var lines = source.Split('\n');
        for (var index = lines.Length - 1; index >= 0; index--)
        {
            var column = lines[index].LastIndexOf(writtenSlot, StringComparison.Ordinal);
            if (column >= 0)
                return new SourceSpan(index + 1, column + 1, index + 1, column + 1 + writtenSlot.Length);
        }

        Assert.Fail($"`{writtenSlot}` does not occur in:\n{source}");
        throw new InvalidOperationException("unreachable");
    }
}
