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
        var a = Observe($"{Preamble}C = range(1, 10)\n{ordinary}");
        var b = Observe($"{Preamble}C = range(1, 10)\n{dotted}");

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
        var a = Observe($"R = {receiver}\ncount(R)");
        var b = Observe($"R = {receiver}\nR.count");

        Assert.Equal(a.Semantic, b.Semantic);
        Assert.Equal(a.MaterializedItems, b.MaterializedItems);
    }

    public static TheoryData<string, string> PreparedBuiltinCallbackPairs => new()
    {
        {
            "Rows = [[1, 2]]\nRows.map(count)",
            "C(x) = x.count\nRows = [[1, 2]]\nRows.map(C)"
        },
        {
            "Rows = ['abc']\nRows.map(count)",
            "C(x) = x.count\nRows = ['abc']\nRows.map(C)"
        },
        {
            "Rows = [[1, [2, 3]]]\nRows.map(atoms)",
            "C(x) = x.atoms\nRows = [[1, [2, 3]]]\nRows.map(C)"
        },
        {
            "Rows = [(1, (2, 3))]\nRows.map(atoms)",
            "C(x) = x.atoms\nRows = [(1, (2, 3))]\nRows.map(C)"
        },
        {
            "Rows = []\nRows.map(count)",
            "C(x) = x.count\nRows = []\nRows.map(C)"
        },
        {
            "Rows = [[]]\nRows.map(first)",
            "C(x) = x.first\nRows = [[]]\nRows.map(C)"
        },
        {
            "Rows = ['abc']\nRows.map(sum)",
            "C(x) = x.sum\nRows = ['abc']\nRows.map(C)"
        },
        {
            "Rows = [[1, 2], []]\nRows.filter(count)",
            "C(x) = x.count\nRows = [[1, 2], []]\nRows.filter(C)"
        },
        {
            "Rows = [2]\nRows.reduce(contains, [1, 2])",
            "C(xs, x) = xs.contains(x)\nRows = [2]\nRows.reduce(C, [1, 2])"
        },
    };

    [Theory]
    [MemberData(nameof(PreparedBuiltinCallbackPairs))]
    public void BuiltinCallbacks_ReusePreparedValuesLikeEquivalentUserWrappers(string builtinSource, string wrapperSource)
    {
        var builtin = Observe(builtinSource);
        var wrapper = Observe(wrapperSource);

        Assert.Equal(wrapper.Semantic, builtin.Semantic);
        Assert.Equal(wrapper.MaterializedItems, builtin.MaterializedItems);
        Assert.Equal(wrapper.MaterializedStringChars, builtin.MaterializedStringChars);
    }

    [Fact]
    public void BuiltinCallback_CumulativeBoundariesMatchEquivalentUserWrapper()
    {
        const string builtinSource = "Rows = [[1, 2]]\nRows.map(count)";
        const string wrapperSource = "C(x) = x.count\nRows = [[1, 2]]\nRows.map(C)";

        for (var limit = 1L; limit <= 8; limit++)
        {
            var limits = new EvaluationLimits { MaxMaterializedItems = limit };
            Assert.Equal(Observe(wrapperSource, limits).Semantic, Observe(builtinSource, limits).Semantic);
        }

        const string builtinStringSource = "Rows = ['abc']\nRows.map(count)";
        const string wrapperStringSource = "C(x) = x.count\nRows = ['abc']\nRows.map(C)";
        for (var limit = 0L; limit <= 5; limit++)
        {
            var limits = new EvaluationLimits { MaxMaterializedStringChars = limit };
            Assert.Equal(Observe(wrapperStringSource, limits).Semantic, Observe(builtinStringSource, limits).Semantic);
        }
    }

    [Fact]
    public void DottedChain_ChargesTheSameAsNestedOrdinaryCalls()
    {
        var a = Observe($"{Preamble}count(map(filter(range(1, 20), Big), Double))");
        var b = Observe($"{Preamble}range(1, 20).filter(Big).map(Double).count");

        Assert.Equal(a.Semantic, b.Semantic);
        Assert.Equal(a.MaterializedItems, b.MaterializedItems);
    }

    [Fact]
    public void UserExtensionCall_ChargesTheSameInBothForms()
    {
        var a = Observe("F(c, n) = take(c, n)\nF(range(1, 10), 3)");
        var b = Observe("F(c, n) = take(c, n)\nrange(1, 10).F(3)");

        Assert.Equal(a.Semantic, b.Semantic);
        Assert.Equal(a.MaterializedItems, b.MaterializedItems);
        Assert.Equal(a.EvaluationSteps, b.EvaluationSteps);
    }

    [Fact]
    public void StructuralPropertyAccess_IsExcludedFromTheRewriteRelation()
    {
        // `Object.Value` is structural member access, NOT an extension-call rewriting, so
        // the dotted/ordinary relation does not apply to it. It is asserted directly.
        Assert.Equal("ok", Observe("Object = (\n    public Value = 7\n)\nObject.Value").Semantic.Outcome);
    }

    // ── Relation 2: cached <= rebuilt (never equality) ───────────────────────

    [Fact]
    public void CachedReceiver_IsNeverMoreExpensiveThanRebuilding()
    {
        var cached = Observe("V = range(1, 10)\nV.count + V.count + V.count");
        var rebuilt = Observe("range(1, 10).count + range(1, 10).count + range(1, 10).count");

        Assert.Equal(cached.Semantic, rebuilt.Semantic);
        Assert.True(cached.MaterializedItems <= rebuilt.MaterializedItems,
            $"cached charged {cached.MaterializedItems}, rebuilt charged {rebuilt.MaterializedItems}.");
    }

    // ── Relation 3: optimized <= generic, semantics equal ────────────────────

    [Theory]
    [InlineData("range(1, 20).count")]
    [InlineData("range(1, 20).sum")]
    [InlineData("B(x) = x > 5\nrange(1, 20).filter(B).count")]
    [InlineData("D(x) = x * 2\nrange(1, 20).map(D)")]
    [InlineData("Inc = x + 1\nInc.repeat(20, 0)")]
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
    [InlineData("range(1, 10).count")]
    [InlineData("1, 2, 3")]
    [InlineData("[1, [2, 3]]")]
    [InlineData("()")]
    [InlineData("'abc'")]
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
        "range(1, 10).count",
        "f(0) = 0\nf(n) = f(n - 1)\nf(5)",
        "D(x) = x * 2\nrange(1, 8).map(D)",
        "[1, 2, 3], 'text'",
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
                Observe("count(range(1, 10))", limits).Semantic,
                Observe("range(1, 10).count", limits).Semantic);
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
        var before = KatLangEngine.Run("range(1, 10).count", options).ToDisplayString();
        _ = KatLangEngine.Run("range(1, 500).count", options).ToDisplayString();   // rejected
        var after = KatLangEngine.Run("range(1, 10).count", options).ToDisplayString();

        Assert.Equal(before, after);
    }

    // ── Relation 6: rendering laws ───────────────────────────────────────────

    [Theory]
    [InlineData("1, 2, 3")]
    [InlineData("[1, [2, 3]], (4, 5)")]
    [InlineData("'abc', 'de'")]
    [InlineData("()")]
    public void RenderedText_NeverExceedsItsLimit_AndIsDeterministic(string source)
    {
        var natural = KatLangEngine.Run(source).ToDisplayString().Length;

        for (var limit = 0; limit <= natural + 2; limit++)
        {
            var options = new RunOptions { EvaluationLimits = new EvaluationLimits { MaxDisplayLength = limit } };
            var run = KatLangEngine.Run(source, options);
            var text = run.ToDisplayString();

            Assert.Equal(text, run.ToDisplayString());   // repeated rendering is deterministic
            Assert.True(text.Length <= limit, $"limit {limit} returned {text.Length} units.");
        }
    }

    [Fact]
    public void Rendering_DoesNotAlterEvaluationCountersOrValues()
    {
        var run = KatLangEngine.Run("range(1, 5)");
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
        foreach (var source in new[] { "1 + 2", "A = (\n    public B = 1\n)\nA.B", "M(-2, 2) = (open(o\n" })
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

    [Fact]
    public void EveryResourceLimitVariant_IsClassifiedAndFormattedUniformly()
    {
        var span = new SourceSpan(2, 3, 2, 7);
        EvalError[] allResourceVariants =
        {
            new EvalError.EvaluationDepthExceeded(8) { Span = span },
            new EvalError.EvaluationStepLimitExceeded(20) { Span = span },
            new EvalError.EvaluationStackExhausted() { Span = span },
            new EvalError.CollectionSizeLimitExceeded(5, 6) { Span = span },
            new EvalError.MaterializationLimitExceeded(5) { Span = span },
            new EvalError.StringSizeLimitExceeded(5, 6) { Span = span },
            new EvalError.StringMaterializationLimitExceeded(5) { Span = span },
            new EvalError.DisplayLengthLimitExceeded(5),
        };

        Assert.Equal(8, allResourceVariants.Select(static error => error.GetType()).Distinct().Count());
        Assert.All(allResourceVariants, error =>
        {
            Assert.True(error.IsResourceLimit, error.GetType().Name);
            var publicError = KatLangError.FromEvalError(error);
            Assert.DoesNotContain("while evaluating", publicError.Message, StringComparison.OrdinalIgnoreCase);
            Assert.InRange(publicError.Message.Length, 1, 240);

            if (error is not EvalError.DisplayLengthLimitExceeded)
            {
                Assert.IsNotType<EvalError.WithContext>(error);
                Assert.NotNull(error.Span);
                Assert.NotNull(publicError.StartLine);
            }
        });

        // Convention guard: every current resource record is named *Exceeded, except the
        // explicit host-stack backstop. A new similarly named variant must be added above.
        var discoverableResourceTypes = typeof(EvalError)
            .GetNestedTypes(System.Reflection.BindingFlags.Public)
            .Where(static type => type.Name.EndsWith("Exceeded", StringComparison.Ordinal)
                || type == typeof(EvalError.EvaluationStackExhausted))
            .ToHashSet();
        Assert.True(discoverableResourceTypes.SetEquals(
            allResourceVariants.Select(static error => error.GetType())));
    }

    [Fact]
    public void EvaluatorResourceLimits_PreserveUsefulSpansWithoutContextChains()
    {
        static EvalError RunError(string source, EvaluationLimits limits)
        {
            var result = Evaluator.RunCounted(
                new Expr.Block(Parser.Parse(source).Root),
                UncachedZeroArgPropertyResultCache.Instance,
                limits);
            Assert.True(result.IsError);
            return result.Error;
        }

        var errors = new EvalError[]
        {
            RunError("f(0) = 0\nf(n) = f(n - 1)\nf(50)", new EvaluationLimits { MaxDepth = 8 }),
            RunError("Step = x, 1\nStep.while(0)", new EvaluationLimits { MaxSteps = 25 }),
            RunError("range(1, 6)", new EvaluationLimits { MaxCollectionItems = 5 }),
            RunError("[1, 2]", new EvaluationLimits { MaxMaterializedItems = 1 }),
            RunError("'abcdef'", new EvaluationLimits { MaxStringLength = 5 }),
            RunError("'abc', 'def'", new EvaluationLimits { MaxMaterializedStringChars = 5 }),
        };

        Assert.All(errors, error =>
        {
            Assert.True(error.IsResourceLimit);
            Assert.IsNotType<EvalError.WithContext>(error);
            Assert.NotNull(error.Span);

            var publicError = KatLangError.FromEvalError(error);
            Assert.NotNull(publicError.StartLine);
            Assert.DoesNotContain("while evaluating", publicError.Message, StringComparison.OrdinalIgnoreCase);
            Assert.InRange(publicError.Message.Length, 1, 240);
        });
    }

    // ── A/B/A state isolation ────────────────────────────────────────────────

    [Fact]
    public void EvaluatingAnUnrelatedProgram_DoesNotChangeALaterObservation()
    {
        var a1 = Observe("range(1, 10).count");
        _ = Observe("V = range(1, 500)\nV.sum");
        var a2 = Observe("range(1, 10).count");

        Assert.Equal(a1, a2);
    }
}
