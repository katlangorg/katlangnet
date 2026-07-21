using KatLang.Evaluation;
using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

/// <summary>
/// Operational-metamorphic testing: compares related C# executions on the work they
/// perform, which Lean neither models nor should.
///
/// <para>Three observation classes are kept deliberately separate.
/// <b>Language-semantic</b> observations (result kind, value structure, emitted count,
/// semantic error kind) are the ones the Lean differential corpus compares.
/// <b>Host-policy</b> observations (resource-limit errors, optimizer selection, allocation)
/// are C#-only and are never required to match Lean. <b>Operational</b> observations
/// (steps, materialized item slots and string units, peak dynamic depth, cache hits) may be
/// compared BETWEEN C# executions — and only where the two executions are semantically
/// expected to perform equivalent work.</para>
///
/// <para>That last qualifier is the whole design. <c>count(range(1, 10))</c> and
/// <c>range(1, 10).count</c> must charge equally, because the dotted form is DEFINED as the
/// ordinary receiver-first call. A fused pipeline and its generic equivalent must not: the
/// optimizer is allowed to materialize less, so the relation there is "no more expensive",
/// never equality. Nothing here asserts elapsed time.</para>
/// </summary>
public class OperationalMetamorphicTests
{
    // ── Observation model ────────────────────────────────────────────────────

    /// <summary>Language-semantic identity: exactly what the Lean differential compares.</summary>
    private sealed record SemanticObservation(string Outcome, string? Structure, int? Emitted, string? ErrorCategory)
    {
        public bool IsResourceLimit { get; init; }
    }

    /// <summary>Semantic identity plus the C# work the run performed.</summary>
    private sealed record OperationalObservation(
        SemanticObservation Semantic,
        long EvaluationSteps,
        long MaterializedItems,
        long MaterializedStringChars,
        int PeakDynamicDepth);

    private static OperationalObservation Observe(
        string source,
        EvaluationLimits? limits = null,
        bool optimize = true,
        IZeroArgPropertyResultCache? cache = null)
    {
        var parsed = Parser.Parse(source);
        if (parsed.HasErrors)
            return new OperationalObservation(new SemanticObservation("parseError", null, null, null), 0, 0, 0, 0);

        var (result, budget) = Evaluator.RunCountedObserved(
            new Expr.Block(parsed.Root), limits, optimize, cache);

        var semantic = result.IsError
            ? new SemanticObservation("err", null, null, SemanticExplorerHarness.ErrorCategory(result.Error))
            {
                IsResourceLimit = result.Error.IsResourceLimit,
            }
            : new SemanticObservation(
                "ok", SemanticExplorerHarness.Neutral(result.Value.Value), result.Value.EmittedCount, null);

        return new OperationalObservation(
            semantic,
            budget.ConsumedSteps,
            budget.MaterializedItems,
            budget.MaterializedStringChars,
            budget.PeakDepth);
    }

    private static void AssertSemanticallyEqual(string left, string right, EvaluationLimits? limits = null)
    {
        var a = Observe(left, limits);
        var b = Observe(right, limits);
        Assert.Equal(a.Semantic, b.Semantic);
    }

    // ── Relation 1: dotted form == ordinary receiver-first call ──────────────
    //
    // Declared relation: SEMANTIC EQUALITY + EXACT OPERATIONAL EQUALITY. The dotted form is
    // not an optimization of the ordinary form, it is a spelling of it, so any difference in
    // charged work is a defect (this is the relation that caught the duplicate receiver
    // materialization).

    public static TheoryData<string, string> DottedPairs => new()
    {
        { "count(C)", "C.count" },
        { "sum(C)", "C.sum" },
        { "first(C)", "C.first" },
        { "last(C)", "C.last" },
        { "min(C)", "C.min" },
        { "max(C)", "C.max" },
        { "avg(C)", "C.avg" },
        { "order(C)", "C.order" },
        { "orderDesc(C)", "C.orderDesc" },
        { "distinct(C)", "C.distinct" },
        { "atoms(C)", "C.atoms" },
        { "take(C, 3)", "C.take(3)" },
        { "skip(C, 3)", "C.skip(3)" },
        { "contains(C, 3)", "C.contains(3)" },
        { "map(C, Double)", "C.map(Double)" },
        { "filter(C, Big)", "C.filter(Big)" },
        { "reduce(C, Add, 0)", "C.reduce(Add, 0)" },
    };

    private const string Preamble = "Double(x) = x * 2\nBig(x) = x > 5\nAdd(a, b) = a + b\n";

    [Theory]
    [MemberData(nameof(DottedPairs))]
    public void DottedAndOrdinaryForms_ChargeExactlyTheSameWork(string ordinary, string dotted)
    {
        var a = Observe($"{Preamble}C = range(1, 10)\nOutput = {ordinary}");
        var b = Observe($"{Preamble}C = range(1, 10)\nOutput = {dotted}");

        Assert.Equal(a.Semantic, b.Semantic);
        Assert.Equal(a.MaterializedItems, b.MaterializedItems);
        Assert.Equal(a.MaterializedStringChars, b.MaterializedStringChars);
    }

    [Theory]
    [InlineData("7")]
    [InlineData("'text'")]
    [InlineData("()")]
    [InlineData("(1, 2, 3)")]
    [InlineData("[]")]
    [InlineData("[7]")]
    [InlineData("[1, 2, 3]")]
    [InlineData("[(1, 2), [3, 4]]")]
    [InlineData("range(1, 4)")]
    public void DottedAndOrdinaryForms_AgreeForEveryReceiverValueKind(string receiver)
    {
        var a = Observe($"R = {receiver}\nOutput = count(R)");
        var b = Observe($"R = {receiver}\nOutput = R.count");

        Assert.Equal(a.Semantic, b.Semantic);
        Assert.Equal(a.MaterializedItems, b.MaterializedItems);
    }

    [Fact]
    public void DottedChain_ChargesTheSameAsNestedOrdinaryCalls()
    {
        var a = Observe($"{Preamble}Output = count(map(filter(range(1, 20), Big), Double))");
        var b = Observe($"{Preamble}Output = range(1, 20).filter(Big).map(Double).count");

        Assert.Equal(a.Semantic, b.Semantic);
        Assert.Equal(a.MaterializedItems, b.MaterializedItems);
    }

    [Fact]
    public void UserExtensionCall_ChargesTheSameInBothForms()
    {
        var a = Observe("F(c, n) = take(c, n)\nOutput = F(range(1, 10), 3)");
        var b = Observe("F(c, n) = take(c, n)\nOutput = range(1, 10).F(3)");

        Assert.Equal(a.Semantic, b.Semantic);
        Assert.Equal(a.MaterializedItems, b.MaterializedItems);
        Assert.Equal(a.EvaluationSteps, b.EvaluationSteps);
    }

    [Fact]
    public void StructuralPropertyAccess_IsExcludedFromTheRewriteRelation()
    {
        // `Object.Value` is structural member access, NOT an extension-call rewriting, so
        // the dotted/ordinary relation does not apply to it. It is asserted directly.
        Assert.Equal("ok", Observe("Object = (\n    public Value = 7\n)\nOutput = Object.Value").Semantic.Outcome);
    }

    // ── Relation 2: cached <= rebuilt (never equality) ───────────────────────

    [Fact]
    public void CachedReceiver_IsNeverMoreExpensiveThanRebuilding()
    {
        var cached = Observe("V = range(1, 10)\nOutput = V.count + V.count + V.count");
        var rebuilt = Observe("Output = range(1, 10).count + range(1, 10).count + range(1, 10).count");

        Assert.Equal(cached.Semantic, rebuilt.Semantic);
        Assert.True(cached.MaterializedItems <= rebuilt.MaterializedItems,
            $"cached charged {cached.MaterializedItems}, rebuilt charged {rebuilt.MaterializedItems}.");
    }

    // ── Relation 3: optimized <= generic, semantics equal ────────────────────

    [Theory]
    [InlineData("Output = range(1, 20).count")]
    [InlineData("Output = range(1, 20).sum")]
    [InlineData("B(x) = x > 5\nOutput = range(1, 20).filter(B).count")]
    [InlineData("D(x) = x * 2\nOutput = range(1, 20).map(D)")]
    [InlineData("Inc = x + 1\nOutput = Inc.repeat(20, 0)")]
    public void OptimizedAndGenericPaths_AgreeSemanticallyAndNeverCostMore(string source)
    {
        var optimized = Observe(source, optimize: true);
        var generic = Observe(source, optimize: false);

        Assert.Equal(generic.Semantic, optimized.Semantic);
        Assert.True(optimized.MaterializedItems <= generic.MaterializedItems,
            $"optimized charged {optimized.MaterializedItems} > generic {generic.MaterializedItems}.");
    }

    // ── Relation 4: plain / counted / engine agreement ───────────────────────

    [Theory]
    [InlineData("Output = range(1, 10).count")]
    [InlineData("Output = 1, 2, 3")]
    [InlineData("Output = [1, [2, 3]]")]
    [InlineData("Output = ()")]
    [InlineData("Output = 'abc'")]
    public void PlainCountedAndEngine_ProduceTheSameValue(string source)
    {
        var expr = new Expr.Block(Parser.Parse(source).Root);
        var plain = Evaluator.Run(expr);
        var counted = Evaluator.RunCounted(expr, UncachedZeroArgPropertyResultCache.Instance);
        var engine = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));

        Assert.Equal(plain.IsError, counted.IsError);
        Assert.Equal(plain.Value, counted.Value.Value, Result.ValueComparer);
        Assert.Equal(plain.Value, engine.Value, Result.ValueComparer);
        Assert.Equal(counted.Value.EmittedCount, engine.EmittedCount);
    }

    // ── Relation 5: resource-limit laws ──────────────────────────────────────

    public static TheoryData<string> BudgetPrograms => new()
    {
        "Output = range(1, 10).count",
        "f(0) = 0\nf(n) = f(n - 1)\nOutput = f(5)",
        "D(x) = x * 2\nOutput = range(1, 8).map(D)",
        "Output = [1, 2, 3], 'text'",
    };

    [Theory]
    [MemberData(nameof(BudgetPrograms))]
    public void MonotonicSuccess_ALargerLimitNeverTurnsSuccessIntoFailure(string source)
    {
        // For one limit kind at a time: once the program fits, every larger effective limit
        // must produce the SAME semantic result (hard ceilings clamp, so growth stops there).
        AssertMonotonic(source, n => new EvaluationLimits { MaxDepth = n }, 1, EvaluationLimits.MaxSupportedDepth);
        AssertMonotonic(source, n => new EvaluationLimits { MaxSteps = n }, 1, 400);
        AssertMonotonic(source, n => new EvaluationLimits { MaxCollectionItems = n }, 1, 64);
        AssertMonotonic(source, n => new EvaluationLimits { MaxMaterializedItems = n }, 1, 64);
        AssertMonotonic(source, n => new EvaluationLimits { MaxStringLength = n }, 1, 64);
        AssertMonotonic(source, n => new EvaluationLimits { MaxMaterializedStringChars = n }, 1, 64);
    }

    private static void AssertMonotonic(string source, Func<int, EvaluationLimits> make, int from, int to)
    {
        SemanticObservation? firstSuccess = null;
        for (var n = from; n <= to; n = n < 16 ? n + 1 : n * 2)
        {
            var observation = Observe(source, make(n)).Semantic;
            if (firstSuccess is null)
            {
                if (observation.Outcome == "ok") firstSuccess = observation;
                continue;
            }

            Assert.Equal(firstSuccess, observation);
        }

        Assert.NotNull(firstSuccess);
    }

    [Fact]
    public void BoundaryConsistency_EquivalentFormsCrossTheSameCumulativeBoundary()
    {
        for (long budget = 1; budget <= 32; budget++)
        {
            var limits = new EvaluationLimits { MaxMaterializedItems = budget };
            Assert.Equal(
                Observe("Output = count(range(1, 10))", limits).Semantic,
                Observe("Output = range(1, 10).count", limits).Semantic);
        }
    }

    [Theory]
    [MemberData(nameof(BudgetPrograms))]
    public void InBudgetNeutrality_AGenerousExplicitLimitMatchesTheDefaultPolicy(string source)
    {
        var generous = new EvaluationLimits
        {
            MaxDepth = EvaluationLimits.MaxSupportedDepth,
            MaxSteps = 1_000_000,
            MaxCollectionItems = EvaluationLimits.MaxSupportedCollectionItems,
            MaxMaterializedItems = 1_000_000,
            MaxStringLength = EvaluationLimits.MaxSupportedStringLength,
            MaxMaterializedStringChars = 1_000_000,
        };

        Assert.Equal(Observe(source).Semantic, Observe(source, generous).Semantic);
    }

    [Fact]
    public void FailedReservation_DoesNotChangeALaterRunOrASecondaryError()
    {
        var options = new RunOptions { EvaluationLimits = new EvaluationLimits { MaxMaterializedItems = 12 } };
        var before = KatLangEngine.Run("Output = range(1, 10).count", options).ToDisplayString();
        _ = KatLangEngine.Run("Output = range(1, 500).count", options).ToDisplayString();   // rejected
        var after = KatLangEngine.Run("Output = range(1, 10).count", options).ToDisplayString();

        Assert.Equal(before, after);
    }

    // ── Relation 6: rendering laws ───────────────────────────────────────────

    [Theory]
    [InlineData("Output = 1, 2, 3")]
    [InlineData("Output = [1, [2, 3]], (4, 5)")]
    [InlineData("Output = 'abc', 'de'")]
    [InlineData("Output = ()")]
    public void RenderedText_NeverExceedsItsLimit_AndIsDeterministic(string source)
    {
        var natural = KatLangEngine.Run(source).ToDisplayString().Length;

        for (var limit = 0; limit <= natural + 2; limit++)
        {
            var options = new RunOptions { EvaluationLimits = new EvaluationLimits { MaxDisplayLength = limit } };
            var run = KatLangEngine.Run(source, options);
            var text = run.ToDisplayString();

            Assert.Equal(text, run.ToDisplayString());   // repeated rendering is deterministic
            if (text.Contains("Display output limit", StringComparison.Ordinal)) continue;
            Assert.True(text.Length <= limit, $"limit {limit} returned {text.Length} units.");
        }
    }

    [Fact]
    public void Rendering_DoesNotAlterEvaluationCountersOrValues()
    {
        var run = KatLangEngine.Run("Output = range(1, 5)");
        var success = Assert.IsType<RunResult.Success>(run);
        var before = success.Value;

        _ = run.ToDisplayString();
        _ = run.ToDisplayString();

        Assert.Equal(before, success.Value, Result.ValueComparer);
        Assert.Equal(5, success.Atoms.Count);
    }

    // ── Frontend operational invariants (never compared with Lean) ───────────

    [Fact]
    public void ClauseFamilyOpens_StayBranchOwned()
    {
        var body = new Algorithm.User(null, [], [new Expr.Resolve("Lib")], [], [new Expr.Resolve("V")]);
        var family = Assert.IsType<Algorithm.Conditional>(
            Algorithm.ElaborateClauseGroup([new CondBranch(new Pattern.LitInt(0), body)]));

        Assert.Empty(family.Opens);
        Assert.Single(family.Branches[0].Body.Opens);
    }

    [Theory]
    [InlineData(4)]
    [InlineData(10)]
    [InlineData(20)]
    public void MalformedRecoveryFamily_GrowsLinearly(int n)
    {
        var source = string.Concat(Enumerable.Repeat("M(-2, 2) = (open(o\n", n));
        Assert.True(CountNodes(Parser.Parse(source).Root) <= 40 * n + 200);
    }

    [Fact]
    public void WrapperParity_ParseAgreesWithTheFrontEndPipeline()
    {
        foreach (var source in new[] { "Output = 1 + 2", "A = (\n    public B = 1\n)\nOutput = A.B", "M(-2, 2) = (open(o\n" })
        {
            var parsed = Parser.Parse(source);
            var pipeline = FrontEndPipeline.Process(source);
            Assert.Equal(parsed.Diagnostics.Count, pipeline.Diagnostics.Count);
        }
    }

    private static int CountNodes(Algorithm root)
    {
        var n = 0;
        Alg(root);
        return n;

        void Alg(Algorithm a)
        {
            if (++n > 5_000_000) return;
            foreach (var p in a.Properties) { n++; Alg(p.Value); }
            foreach (var e in a.Opens) Ex(e);
            foreach (var e in a.Output) Ex(e);
            foreach (var b in a.Branches) { n++; Alg(b.Body); }
        }

        void Ex(Expr e)
        {
            if (++n > 5_000_000) return;
            switch (e)
            {
                case Expr.Unary(_, var o): Ex(o); break;
                case Expr.Binary(_, var l, var r): Ex(l); Ex(r); break;
                case Expr.Index(var t, var s): Ex(t); Ex(s); break;
                case Expr.SequenceSpread(var o): Ex(o); break;
                case Expr.Grace(var i, _): Ex(i); break;
                case Expr.ListLiteral(var items): foreach (var it in items) Ex(it); break;
                case Expr.Block(var alg): Alg(alg); break;
                case Expr.Call(var fn, var args): Ex(fn); Alg(args); break;
                case Expr.DotCall dc: Ex(dc.Target); if (dc.Args is { } a2) Alg(a2); break;
            }
        }
    }

    // ── Resource-error context suppression is uniform across all limit kinds ─

    [Theory]
    [InlineData("f(0) = 0\nf(n) = f(n - 1)\nOutput = f(50)", 8, 0, 0, 0)]
    [InlineData("Step = x, 1\nOutput = Step.while(0)", 0, 500, 0, 0)]
    [InlineData("Output = range(1, 50).count", 0, 0, 5, 0)]
    [InlineData("Output = 12345.string", 0, 0, 0, 1)]
    public void EveryResourceLimitError_IsReportedWithoutAccumulatedCallContext(
        string source, int depth, int steps, int items, int stringLength)
    {
        // A limit belongs to the RUN, not to any one call on the chain. Depth, step and
        // collection errors already suppressed context; the string and display kinds were
        // MISSING from that predicate, so their messages accumulated one identical frame
        // per active invocation. This theory covers every kind uniformly.
        var limits = new EvaluationLimits
        {
            MaxDepth = depth > 0 ? depth : null,
            MaxSteps = steps > 0 ? steps : null,
            MaxCollectionItems = items > 0 ? items : null,
            MaxStringLength = stringLength > 0 ? stringLength : null,
        };

        var result = Evaluator.RunCounted(
            new Expr.Block(Parser.Parse(source).Root), UncachedZeroArgPropertyResultCache.Instance, limits);

        Assert.True(result.IsError);
        Assert.True(result.Error.IsResourceLimit);
        Assert.IsNotType<EvalError.WithContext>(result.Error);
    }

    // ── A/B/A state isolation ────────────────────────────────────────────────

    [Fact]
    public void EvaluatingAnUnrelatedProgram_DoesNotChangeALaterObservation()
    {
        var a1 = Observe("Output = range(1, 10).count");
        _ = Observe("V = range(1, 500)\nOutput = V.sum");
        var a2 = Observe("Output = range(1, 10).count");

        Assert.Equal(a1, a2);
    }
}
