using System.Numerics;
using System.Reflection;
using KatLang.Evaluation.Caching;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// Model-C inspecting patterns visit the written head from left to right.
/// A repeated contribution is checked immediately and stops later patterns on failure.
/// Ordinary calls, callbacks and loop-state binding share the same rule.
/// </summary>
public class PatternBindingErrorPrecedenceTests
{
    private const string Definitions = "Bad = 1 / 0\nInc(y) = y + 1\n";

    /// <summary>
    /// Ordinary calls: the program, and the reason Lean reports (innermost payload plus the
    /// nested sequence-value groups it is attributed to).
    /// </summary>
    public static TheoryData<string, string> OrdinaryCalls => new()
    {
        // A later nested failure outranks an earlier unequal repeated value.
        { "P((x, x, (a, b))) = a\nP((1, 2, 7))", "BadArity in []" },
        { "P((x, x, (a, b))) = a\nP((1, 2, (7, 8, 9)))", "BadArity in []" },
        { "P(x, x, (a, b)) = a\nP(1, 2, 7)", "BadArity in []" },
        { "P(x, x, (a, b)) = a\nP(1, 2, (7, 8, 9))", "BadArity in []" },
        // ...and so does an argument's retained value error (div0, not arity).
        { "P(x, x, (a, b)) = a\nP(1, 2, Bad)", "BadArity in []" },
        // A conflict INSIDE a nested group is part of binding that group.
        { "P((x, x), (a, b)) = a\nP((1, 2), 7)", "BadArity in []" },
        // Collecting lists: the prefix merges before the suffix binds...
        { "P(x, x, *r, (a, b)) = a\nP(1, 2, 7)", "BadArity in []" },
        { "P(x, x, *r, (a, b)) = a\nP(1, 2, Bad)", "BadArity in []" },
        // ...the suffix binds before the prefix/suffix merge...
        { "P(x, *r, x, (a, b)) = a\nP(1, 2, 7)", "BadArity in []" },
        { "P(x, *r, x, (a, b)) = a\nP(1, 2, (7, 8, 9))", "BadArity in []" },
        // ...and the collector's values are collected before it.
        { "P(x, *r, x) = x\nP(1, Bad, 2)", "BadArity in []" },
        { "P(x, *r, x) = x\nP(1, Inc, 2)", "BadArity in []" },
        // Merges run right to left: the rightmost failing merge decides the kind (A and B
        // are two callables with the equal value 5).
        { Distinct + "P(x, x, f, f) = 0\nP(1, 2, A, B)", "BadArity in []" },
        { Distinct + "P(f, f, x, x) = 0\nP(A, B, 1, 2)", Identity },
        { Distinct + "P(x, x, (a, b), f, f) = 0\nP(1, 2, (3, 4), A, B)", "BadArity in []" },
        // A lone conflict is still the ordinary BadArity.
        { "P(x, x) = x\nP(1, 2)", "BadArity in []" },
        { "P(x, *r, x) = x\nP(1, 9, 2)", "BadArity in []" },
        // The prefix/collector/suffix merge: within ONE merge an unequal value is found before
        // a callable-identity conflict (both x and f repeat across the collector)...
        { Distinct + "P(x, f, *r, f, x) = 0\nP(1, A, B, 2)", Identity },
        // ...and a callable-identity conflict across the collector is the type mismatch.
        { Distinct + "P(f, *r, f) = 0\nP(A, 9, B)", Identity },
        // A repeated name's VALUELESS contribution is a binding failure of its own pattern
        // (Q-05): the slot's own outcome, before any verdict of that range, wherever the
        // unequal name stands, and before a later pattern binds.
        { "P(x, x, f, f) = 0\nP(1, 2, Inc, Inc)", "BadArity in []" },
        { "P(f, f, x, x) = 0\nP(Inc, Inc, 1, 2)", IncValueDemand },
        { "P(x, x, (a, b), f, f) = 0\nP(1, 2, (3, 4), Inc, Inc)", "BadArity in []" },
        { "P(x, x, f, f) = 0\nP(1, 2, Bad, 7)", "BadArity in []" },
        { "P(f, f, (a, b)) = a\nP(7, Bad, 5)", "DivByZero in []" },
        { "P(x, f, *r, f, x) = 0\nP(1, Inc, Inc, 2)", IncValueDemand },
        { "P(f, *r, f) = 0\nP(Inc, 9, Inc)", IncValueDemand },
        { "P(f, *r, f) = 0\nP(7, 9, Bad)", "DivByZero in []" },
        { "P(*r, f, f) = 0\nP(Bad, Inc, Inc)", IncValueDemand },
    };

    /// <summary>Two callables with the equal zero-argument value 5.</summary>
    private const string Distinct = "A = 5\nB = 5 + 0\n";

    /// <summary>
    /// The scalar 7 given to the sequence pattern <c>(a, b)</c>: the pattern's KIND mismatch
    /// (structural patterns open only their own kind; a scalar is never a one-item supply).
    /// </summary>
    private const string PairKindMismatch =
        "TypeMismatch(sequence pattern `(a, b)` expects a sequence value, but received numeric value 7) in []";

    private const string Identity = "TypeMismatch(Repeated bind equality requires the same callable identity) in []";

    /// <summary><c>Inc</c> passed bare: its own value demand, the arity rejection of <c>Inc(y)</c>.</summary>
    private const string IncValueDemand = "ArityMismatch(1, 0) in []";

    [Theory]
    [MemberData(nameof(OrdinaryCalls))]
    public void OrdinaryCalls_ReportTheFailureLeanReports(string program, string expectedReason)
    {
        var result = Run(Definitions + program);
        Assert.True(result.IsError, $"expected a binding failure for {program}");
        Assert.Equal(expectedReason, BindingReason(result.Error));
    }

    /// <summary>Callbacks bind through the counted binder in the same order.</summary>
    public static TheoryData<string, string> Callbacks => new()
    {
        { "P((x, x, (a, b))) = [a]\nmap([(1, 2, (7, 8, 9))], P)", "BadArity in []" },
        { "P((x, x, (a, b))) = [a]\n[(1, 2, 7)].map(P)", "BadArity in []" },
        { "P((x, x, (a, b))) = true\nfilter([(1, 2, 7)], P)", "BadArity in []" },
        { "R((x, x, (a, b)), acc) = acc\nreduce([(1, 2, 7)], R, 0)", "BadArity in []" },
        { "P((x, x), (a, b)) = [a]\nreduce([(1, 2)], P, 7)", "BadArity in []" },
        // The counted collecting list: prefix, then suffix, then the cross merge.
        { "P((x, *m, x, (a, b))) = [a]\nmap([(1, 9, 2, 7)], P)", "BadArity in []" },
        { "P((x, *m, x, (a, b))) = [a]\nmap([(1, 9, 2, (7, 8, 9))], P)", "BadArity in []" },
        { "P((x, x, *m, (a, b))) = [a]\nmap([(1, 2, 9, 7)], P)", "BadArity in []" },
        { "P((x, *m, x)) = [x]\nmap([(1, 9, 2)], P)", "BadArity in []" },
        // The reducer is an ordinary two-argument callback: a flat reducer needing three
        // items is the ordinary arity failure of `R(1, (9, 2, 7))`, while the reducer's
        // explicit accumulator pattern binds the accumulator's items through the same
        // order: the suffix (a, b) fails before the unequal x is merged.
        { "R(x, *m, x, (a, b)) = [a]\nreduce([1], R, (9, 2, 7))", "ArityMismatch(3, 2) in []" },
        { "R(e, (x, *m, x, (a, b))) = [a]\nreduce([1], R, (9, 3, 2, 7))", "BadArity in []" },
    };

    [Theory]
    [MemberData(nameof(Callbacks))]
    public void Callbacks_ReportTheFailureLeanReports(string program, string expectedReason)
    {
        var result = Run(Definitions + program);
        Assert.True(result.IsError, $"expected a binding failure for {program}");
        Assert.Equal(expectedReason, BindingReason(result.Error));
    }

    [Fact]
    public void LoopStateBinding_ReportsTheFailureLeanReports()
    {
        // Loop state binds through the ordinary binder: the nested (a, b) failure of the third
        // state slot outranks the unequal x of the first two.
        var result = Run("Step(x, x, (a, b)) = x, x, (a, b)\nrepeat(Step, 1, 1, 2, 7)");
        Assert.True(result.IsError);
        Assert.Equal("BadArity in []", BindingReason(result.Error));
        var arity = Run("Step(x, x, (a, b)) = x, x, (a, b)\nrepeat(Step, 1, 1, 2, (7, 8, 9))");
        Assert.True(arity.IsError);
        Assert.Equal("BadArity in []", BindingReason(arity.Error));

        // The matching state binds; its three-slot final state is ONE loop result value (Q-26).
        AssertDisplay("Step(x, x, (a, b)) = x, x, (a, b)\nrepeat(Step, 1, 1, 1, (2, 3))", "(1, 1, (2, 3))");
    }

    [Fact]
    public void NestedGroupFailures_KeepTheirPatternWordingAndOuterFrames()
    {
        // The nested failure still renders against the WRITTEN group, and the call/callback
        // frames around it are unchanged.
        var direct = KatLangError.FromEvalError(Run("P((x, x, (a, b))) = a\nP((1, 1, (7, 8, 9)))").Error);
        Assert.Equal("Sequence pattern `(a, b)` expects 2 elements, but received 3 elements.", direct.Message);
        Assert.NotNull(direct.Span);

        var callback = Run("P((x, x, (a, b))) = [a]\nmap([(1, 1, (7, 8, 9))], P)");
        var frames = new List<string>();
        for (var current = callback.Error; current is EvalError.WithContext context; current = context.Inner)
            frames.Add(context.Context);
        Assert.Contains(frames, frame => frame.Contains("while evaluating map transform", StringComparison.Ordinal));
        Assert.Equal(direct.Message, KatLangError.FromEvalError(callback.Error).Message);

        // The retained value error keeps its own location (the division in `Bad`).
        var retained = KatLangError.FromEvalError(Run(Definitions + "P(x, x, (a, b)) = a\nP(1, 1, Bad)").Error);
        var span = Assert.IsType<SourceSpan>(retained.Span);
        Assert.Equal(1, span.Start.Line);
    }

    // ── Retained one- and two-occurrence compatibility cases ────────────

    [Theory]
    [InlineData("P(x, x, (a, b)) = b\nP(1, 1, (2, 3))", "3")]
    [InlineData("P((x, x, (a, b))) = [x, a, b]\nP((1, 1, (2, 3)))", "[1, 2, 3]")]
    [InlineData("P(x, *r, x) = [x, r]\nP(1, 9, 1)", "[1, [9]]")]
    [InlineData("P(x, x, *r, (a, b)) = [x, r, a]\nP(1, 1, 5, 6, (7, 8))", "[1, [5, 6], 7]")]
    [InlineData("A = 5\nP(f, f) = f\nP(A, A)", "5")]
    [InlineData("A = 5\nP(f, f) = f()\nP(A, A)", "5")]
    [InlineData("Same((x, x)) = x\nmap([(1, 1), (2, 2)], Same)", "[1, 2]")]
    [InlineData("F((x, *m, x)) = m\nmap([(1, 9, 1)], F)", "[[9]]")]
    [InlineData("R((x, x), acc) = acc + x\nreduce([(1, 1), (2, 2)], R, 0)", "3")]
    [InlineData("Equal(x, x) = 1\nEqual(x, y) = 0\nEqual(1, 1), Equal(1, 2)", "1\n0")]
    [InlineData("R(e, (x, *m, x, (a, b))) = [a]\nreduce([1], R, (1, 9, 1, (7, 8)))", "[7]")]
    public void RepeatedEqualBinders_StillBind(string source, string expected)
        => AssertDisplay(source, expected);

    [Fact]
    public void RepeatedConflict_DemandsOnlyTheVisitedContributions()
    {
        // Binding every pattern before merging evaluates nothing new: the arguments were
        // evaluated (once each, left to right) before any pattern bound.
        var ticks = new List<Decimal128>();
        var operations = HostOperations.Create(HostOperation.Create("Tick", (args, _) =>
        {
            ticks.Add(Assert.IsType<Result.Atom>(args[0]).Value);
            return args[0];
        }, "value"));
        var parsed = Parser.Parse("P(x, x, (a, b)) = a\nP(Tick(1), Tick(2), Tick(7))", new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors);
        var result = Evaluator.RunCounted(
            new Expr.AlgorithmExpr(parsed.Root), new RunScopedZeroArgPropertyResultCache(), hostOperations: operations);
        Assert.True(result.IsError);
        Assert.Equal("BadArity in []", BindingReason(result.Error));
        Assert.Equal([(Decimal128)1, 2], ticks);
    }

    [Theory]
    [InlineData("P((x, x, (a, b))) = [a]\nmap([(1, 2, (7, 8, 9))], P)")]
    [InlineData("P(x, x, (a, b)) = a\nP(1, 2, Bad)")]
    [InlineData("P(x, *r, x) = x\nP(1, Bad, 2)")]
    [InlineData("P(x, x, f, f) = 0\nP(1, 2, Inc, Inc)")]
    [InlineData("P(x, x) = x\nP(7, Bad)")]
    [InlineData("P(x, x) = x, x(5)\nP(1, Inc)")]
    [InlineData("K((x, x, (a, b))) = true\n[(1, 2, 7), (1, 1, (2, 3))].filter(K).count")]
    [InlineData("R(x, *m, x, (a, b)) = [a]\nreduce([1], R, (9, 2, 7))")]
    [InlineData("Step(x, x, (a, b)) = x, x, (a, b)\nrepeat(Step, 1, 1, 2, 7)")]
    public async Task Precedence_AgreesAcrossGenericOptimizedAndAsyncExecution(string program)
    {
        var ast = AsyncEvaluationHarness.Ast(Definitions + program);
        var (generic, _) = Evaluator.RunCountedObserved(ast, enableOptimizations: false);
        var (planned, _) = Evaluator.RunCountedObserved(ast, enableOptimizations: true);
        var cache = new PassThroughAsyncZeroArgPropertyResultCache();
        var (asynchronous, _) = await AsyncEvaluationHarness
            .Complete(Evaluator.RunCountedObservedAsync(ast, zeroArgPropertyResultCache: cache));

        Assert.True(generic.IsError);
        var reason = BindingReason(generic.Error);
        Assert.Equal(reason, BindingReason(planned.Error));
        Assert.Equal(reason, BindingReason(asynchronous.Error));
        Assert.Equal(0, cache.SyncAccesses);
    }

    // ── Repeated-name binding is order-independent ──────────────────────────

    /// <summary>
    /// Argument multisets for one repeated name, with the outcome every permutation must give
    /// (Lean <c>repeatedNameFailure</c>: every PAIR of contributions compatible; and Q-05: every
    /// contribution supplies its own value). <c>Inc</c> is a callable only, <c>Bad</c> a failed
    /// argument, <c>5</c>/<c>6</c> are values only, <c>A = 5</c>/<c>B = 6</c> carry both.
    /// </summary>
    public static TheoryData<string[], string> RepeatedNameMultisets => new()
    {
        // Inc supplies no value: its own value demand fails, in every order.
        { ["Inc", "5", "A"], IncValueDemand },
        { ["Inc", "A", "A"], IncValueDemand },
        { ["Inc", "5", "5", "A"], IncValueDemand },
        // A valueless contribution is a binding failure: it precedes the unequal-value verdict,
        // in every order.
        { ["A", "B", "Inc"], "BadArity in []" },
        { ["5", "6", "Inc"], "BadArity in []" },
        { ["5", "6", "Bad"], "BadArity in []" },
        // Formerly `ok 5`: the value 5 was paired with Inc's algorithm, and Bad's failure was
        // repaired by the other occurrences' value.
        { ["5", "Inc", "5"], IncValueDemand },
        { ["5", "Bad", "5"], "DivByZero in []" },
        { ["A", "Bad", "A"], "DivByZero in []" },
        // Unequal values, in every order.
        { ["A", "B", "5"], "BadArity in []" },
        // Every pair compatible: binds, in every order (the value is 5 whichever occurrence
        // supplies it).
        { ["A", "A", "5"], "ok 5" },
        { ["5", "5", "A"], "ok 5" },
    };

    [Theory]
    [MemberData(nameof(RepeatedNameMultisets))]
    public void RepeatedNameVerdict_IsTheSameForEveryPermutation(string[] arguments, string expected)
    {
        const string definitions = "A = 5\nB = 6\nBad = 1 / 0\nInc(y) = y + 1\n";
        var captures = string.Join(", ", Enumerable.Repeat("f", arguments.Length));
        Assert.Equal(expected, FirstConstraintOutcome(arguments));
        foreach (var permutation in Permutations(arguments))
        {
            var currentExpected = FirstConstraintOutcome(permutation);
            var call = $"P({string.Join(", ", permutation)})";
            Assert.Equal(currentExpected, Outcome(Run($"{definitions}P({captures}) = f\n{call}")));

            // The same multiset around a collecting parameter: the name spans the prefix and
            // the suffix, and is decided once at the cross merge with all of it in hand.
            var spread = $"P({permutation[0]}, 9, {string.Join(", ", permutation.Skip(1))})";
            var collecting = $"f, *r, {string.Join(", ", Enumerable.Repeat("f", arguments.Length - 1))}";
            Assert.Equal(currentExpected, Outcome(Run($"{definitions}P({collecting}) = f\n{spread}")));
        }
    }

    private static string FirstConstraintOutcome(string[] supplied)
    {
        int? first = null;
        foreach (var item in supplied)
        {
            if (item == "Inc") return IncValueDemand;
            if (item == "Bad") return "DivByZero in []";
            var value = item == "B" || item == "6" ? 6 : 5;
            if (first is { } previous && previous != value) return "BadArity in []";
            first ??= value;
        }
        return "ok 5";
    }

    [Theory]
    [InlineData("P(x, x, *m, x, (a, b)) = a\nP(1, 2, 9, 1, 7)")]
    [InlineData("P(x, x, *m, x, (a, b)) = a\nP(1, 1, 9, 2, 7)")]
    [InlineData("P(x, x, *m, x, (a, b)) = a\nP(2, 1, 9, 1, 7)")]
    [InlineData("P((x, x, *m, x, (a, b))) = [a]\nmap([(1, 2, 9, 1, 7)], P)")]
    [InlineData("P((x, x, *m, x, (a, b))) = [a]\nmap([(1, 1, 9, 2, 7)], P)")]
    public void ThreeOccurrenceName_StopsAtTheFirstConflict(string program)
    {
        // Which occurrence holds the odd value no longer decides whether the later (a, b)
        // failure (the scalar 7 is its kind mismatch) is reported first: the name is decided
        // once, after the suffix has bound.
        var result = Run(program);
        Assert.True(result.IsError);
        Assert.Equal("BadArity in []", BindingReason(result.Error));
    }

    [Theory]
    [InlineData("P(f, f) = f\nP(Inc, A)", IncValueDemand)]
    [InlineData("P(f, f) = f\nP(A, Inc)", IncValueDemand)]
    [InlineData("P(f, f) = f\nP(Inc, Inc)", IncValueDemand)]
    [InlineData("P(f, f) = f\nP(A, A)", "ok 5")]
    [InlineData("P(f, f) = f\nP(A, 5)", "ok 5")]
    [InlineData("P(f, f) = f\nP(5, A)", "ok 5")]
    [InlineData("P(f, f) = f\nP(5, Inc)", IncValueDemand)]
    [InlineData("P(f, f) = f\nP(Inc, 5)", IncValueDemand)]
    // The binding itself fails, before the body runs: formerly (Inc, 5) was combined into
    // the value 5 with Inc's algorithm, so a body ignoring f gave 0 and `f(1)` invoked Inc.
    [InlineData("P(f, f) = 0\nP(Inc, 5)", IncValueDemand)]
    [InlineData("P(f, f) = f(1)\nP(5, Inc)", IncValueDemand)]
    [InlineData("P(f, f) = f()\nP(Inc, 5)", IncValueDemand)]
    public void TwoOccurrenceNames_RequireEachArgumentsOwnValue(string program, string expected)
    {
        // One algorithm channel may ACCOMPANY an equal value its own argument supplied
        // (`P(A, 5)`, `P(5, A)`), but a callable-only argument supplies no value, and the other
        // occurrence's value never completes it (Q-05). Distinct callable identities are the
        // deliberate two-occurrence compatibility rule tested below.
        Assert.Equal(expected, Outcome(Run("A = 5\nInc(y) = y + 1\n" + program)));
    }

    [Theory]
    [InlineData(2)]
    [InlineData(3)]
    [InlineData(4)]
    [InlineData(5)]
    public void EqualValuesWithDifferentCallableIdentities_RejectEveryPermutation(int count)
    {
        // Both zero-argument values are 5. Invoking the first callable used to yield 5 or 6
        // according to argument order, even though the binding verdict was invariant.
        var arguments = new[] { "A", "B" }.Concat(Enumerable.Repeat("5", count - 2)).ToArray();
        var captures = string.Join(", ", Enumerable.Repeat("f", count));
        foreach (var permutation in Permutations(arguments))
        {
            var source = "A(*xs) = 5\nB(*xs) = 5 + xs.count\n"
                + $"P({captures}) = f(1)\nP({string.Join(", ", permutation)})";
            var result = Run(source);
            Assert.True(result.IsError, source);
            Assert.Equal("TypeMismatch(Repeated bind equality requires the same callable identity) in []",
                BindingReason(result.Error));
        }
    }

    [Theory]
    [InlineData(2)]
    [InlineData(3)]
    [InlineData(5)]
    [InlineData(8)]
    public void SuccessfulPermutations_PreserveValueCallableAndCallbackChannels(int count)
    {
        var arguments = new[] { "B", "B" }.Concat(Enumerable.Repeat("5", count - 2)).ToArray();
        // Every possible pair of callable positions, including both fold directions.
        for (var first = 0; first < count; first++)
        for (var second = first + 1; second < count; second++)
        {
            Array.Fill(arguments, "5");
            arguments[first] = arguments[second] = "B";
            var captures = string.Join(", ", Enumerable.Repeat("f", count));
            AssertDisplay("B(*xs) = 5 + xs.count\n"
                + $"P({captures}) = [f, f.count, f(1), map([7], f)]\nP({string.Join(", ", arguments)})",
                "[5, 1, 6, [6]]");
        }
    }

    [Theory]
    [InlineData(2)]
    [InlineData(3)]
    [InlineData(5)]
    [InlineData(8)]
    public void GenuineAliases_PreserveEveryChannelInEveryCallablePosition(int count)
    {
        var captures = string.Join(", ", Enumerable.Repeat("f", count));
        for (var first = 0; first < count; first++)
        for (var second = 0; second < count; second++)
        {
            if (first == second) continue;
            var supplied = Enumerable.Repeat("5", count).ToArray();
            supplied[first] = "A";
            supplied[second] = "Alias";
            var root = EvaluatorTestSupport.ParseValidRoot("A(*xs) = 5 + xs.count\nAlias(*xs) = 5 + xs.count\n"
                + $"P({captures}) = [f, f.count, f(1), map([7], f)]\nP({string.Join(", ", supplied)})");
            var callable = root.Properties.Single(p => p.Name == "A").Value;
            // Host aliases share one declaration. This also tests a rebuilt view
            // of that declaration, rather than accidentally comparing one reference.
            root = root with { Properties = root.Properties.Select(p => p.Name == "Alias"
                ? p with { Value = callable with { } } : p).ToArray() };
            var result = Evaluator.RunCounted(new Expr.AlgorithmExpr(root));
            Assert.Equal("ok raw=L[5, 1, 6, L[6]] n=1", AsyncEvaluationHarness.NeutralOf(result));
        }
    }

    [Theory]
    [InlineData(2)]
    [InlineData(3)]
    [InlineData(5)]
    [InlineData(8)]
    public async Task ForwardedAliases_PreserveCompleteBindingAcrossExecutionStrategies(int count)
    {
        var captures = string.Join(", ", Enumerable.Repeat("f", count));
        var middle = string.Concat(Enumerable.Repeat(", 5", count - 2));
        var ast = AsyncEvaluationHarness.Ast("A(*xs) = 5 + xs.count\n"
            + $"P({captures}) = [f, f.count, f(1), map([7], f)]\n"
            + $"Both(left, right) = [P(left{middle}, right), P(right{middle}, left)]\n"
            + "Share(original) = Both(original, original)\nShare(A)");
        var (generic, _) = Evaluator.RunCountedObserved(ast, enableOptimizations: false);
        var (optimized, _) = Evaluator.RunCountedObserved(ast);
        var asyncResult = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedAsync(
            ast, new PassThroughAsyncZeroArgPropertyResultCache()));
        const string expected = "ok raw=L[L[5, 1, 6, L[6]], L[5, 1, 6, L[6]]] n=1";
        Assert.Equal(expected, AsyncEvaluationHarness.NeutralOf(generic));
        Assert.Equal(expected, AsyncEvaluationHarness.NeutralOf(optimized));
        Assert.Equal(expected, AsyncEvaluationHarness.NeutralOf(asyncResult));
    }

    [Theory]
    [InlineData(2)]
    [InlineData(3)]
    [InlineData(5)]
    public void CountedBinder_RejectsEqualValuesWithDifferentCountsInEveryPosition(int count)
    {
        // Exercise the actual counted pattern binder with noncanonical host-side
        // inputs. Surface callback supply normally re-counts these values first.
        var bind = typeof(Evaluator).GetMethod("EvalResolvedCallbackCallCounted", BindingFlags.Static | BindingFlags.NonPublic)!;
        var patterns = Enumerable.Range(0, count).Select(_ => (ParameterPattern)new CaptureParameterPattern("f")).ToArray();
        for (var changed = 0; changed < count; changed++)
        {
            var inputs = new Evaluator.CountedResult[count];
            for (var index = 0; index < count; index++)
                inputs[index] = new Evaluator.CountedResult(new Result.Atom(5), index == changed ? 2 : 1);
            var callee = new Algorithm.User(null, patterns, [], [], [new Expr.Num(7)]);
            var result = (EvalResult<Evaluator.CountedResult>)bind.Invoke(null, [callee, inputs, Evaluator.EvalCtx.Empty,
                Array.Empty<(string Name, Result Value)>(), "P"])!;
            Assert.True(result.IsError);
            Assert.IsType<EvalError.BadArity>(result.Error);
        }
    }

    [Theory]
    [InlineData("P(f, *r, f) = f(1)\nP(A, 9, B)")]
    [InlineData("P(f, *r, f) = f(1)\nP(B, 9, A)")]
    [InlineData("P(f, f, *r, f) = f(1)\nP(A, B, 9, 5)")]
    [InlineData("P(f, *r, f, f) = f(1)\nP(5, 9, B, A)")]
    public async Task DifferentCallableIdentities_AreCheckedAcrossCollectorsAndAsync(string program)
    {
        var ast = AsyncEvaluationHarness.Ast("A(*xs) = 5\nB(*xs) = 5 + xs.count\n" + program);
        var (generic, _) = Evaluator.RunCountedObserved(ast, enableOptimizations: false);
        var (optimized, _) = Evaluator.RunCountedObserved(ast);
        var asyncResult = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedAsync(
            ast, new PassThroughAsyncZeroArgPropertyResultCache()));
        const string expected = "TypeMismatch(Repeated bind equality requires the same callable identity) in []";
        Assert.Equal(expected, BindingReason(generic.Error));
        Assert.Equal(expected, BindingReason(optimized.Error));
        Assert.Equal(expected, BindingReason(asyncResult.Error));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void CallableIdentity_DistinguishesDeclarationsButPreservesRecordCopies(bool copy)
    {
        Algorithm.User Make() => new(null,
            [new CaptureParameterPattern("xs", Kind: ParameterKind.Collecting)], [], [], [new Expr.Num(5)]);
        var first = Make();
        var second = copy ? first with { } : Make();
        var repeated = new Algorithm.User(null,
            [new CaptureParameterPattern("f"), new CaptureParameterPattern("f")], [], [],
            [new Expr.Call(new Expr.Param("f"), [new Expr.Num(1)])]);
        var result = Evaluator.Run(new Expr.AlgorithmExpr(new Algorithm.User(null, [], [],
            [new Property("A", first), new Property("B", second), new Property("P", repeated)],
            [new Expr.Call(new Expr.Resolve("P"), [new Expr.Resolve("A"), new Expr.Resolve("B")])])));
        if (copy)
            Assert.Equal(new Result.Atom(5), result.Value);
        else
            Assert.Equal("TypeMismatch(Repeated bind equality requires the same callable identity) in []",
                BindingReason(result.Error));
    }

    [Fact]
    public void SameNestedDeclaration_InDifferentActivations_IsNotTheSameCallable()
    {
        const string source = "P(f, f) = f(1)\nOuter(n, previous) = {\n"
            + "  Inner(*xs) = 5 + n * xs.count\n"
            + "  if(n == 1, Outer(2, Inner), P(previous, Inner))\n}\nOuter(1, 0)";
        var result = Run(source);
        Assert.Equal("TypeMismatch(Repeated bind equality requires the same callable identity) in []",
            BindingReason(result.Error));
    }

    [Fact]
    public void RuntimeDotWrappers_AreDistinctButForwardingPreservesOneIdentity()
    {
        AssertDisplay("Obj = { public V = 5 }\nP(f, f) = f\nP(Obj.V, Obj.V)", "5");
        AssertDisplay("Obj = { public V = 5 }\nP(f, f) = f()\nPass(g) = P(g, g)\nPass(Obj.V)", "5");
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void LargeCollector_MaterializationLimitPrecedesOnlyCrossCollectorConflicts(bool prefixConflict)
    {
        var x = new CaptureParameterPattern("x");
        var r = new CaptureParameterPattern("r", Kind: ParameterKind.Collecting);
        var callee = new Algorithm.User(null, prefixConflict ? [x, x, r] : [x, r, x], [], [], [new Expr.Param("x")]);
        var middle = Enumerable.Repeat<Expr>(new Expr.Num(0), EvaluationLimits.MaxSupportedCollectionItems + 1);
        Expr[] arguments = prefixConflict
            ? [new Expr.Num(1), new Expr.Num(2), .. middle]
            : [new Expr.Num(1), .. middle, new Expr.Num(2)];
        var result = Evaluator.Run(new Expr.AlgorithmExpr(new Algorithm.User(null, [], [],
            [new Property("P", callee)], [new Expr.Call(new Expr.Resolve("P"), arguments)])));
        Assert.True(result.IsError);
        var error = result.Error;
        while (error is EvalError.WithContext context)
            error = context.Inner;
        Assert.IsType<EvalError.BadArity>(error);
    }

    private static IEnumerable<string[]> Permutations(string[] items)
    {
        if (items.Length <= 1)
        {
            yield return items;
            yield break;
        }

        for (var index = 0; index < items.Length; index++)
        {
            var rest = items.Where((_, position) => position != index).ToArray();
            foreach (var tail in Permutations(rest))
                yield return [items[index], .. tail];
        }
    }

    private static string Outcome(EvalResult<Result> result)
        => result.IsError
            ? BindingReason(result.Error)
            : Result.ValueComparer.Equals(result.Value, new Result.Atom(5))
                ? "ok 5"
                : $"ok {AsyncEvaluationHarness.NeutralOf(result)}";

    // ── Host-built shapes the parser never produces ─────────────────────────

    [Fact]
    public void SecondCollectingCapture_IsIllegalBeforeEvaluation()
    {
        // Two collecting captures at one pattern level are a rejected signature (X-02,
        // ParameterPattern.FindSignatureViolation; Lean signatureViolation?): the parser rejects
        // the written shape, formula lifting an inferred one, and the pre-evaluation validation
        // this host-built one — before any argument binds, never a binder allocation around two
        // collectors (formerly the second one bound as an ordinary suffix pattern).
        var callee = new Algorithm.User(
            Parent: null,
            ParameterPatterns:
            [
                new SequenceValueParameterPattern([
                    new CaptureParameterPattern("a", Kind: ParameterKind.Collecting),
                    new CaptureParameterPattern("b", Kind: ParameterKind.Collecting)]),
            ],
            Opens: [],
            Properties: [],
            Output: [new Expr.ListLiteral([new Expr.Param("a")])]);

        foreach (var item in new Expr[] { new Expr.EmptySequence(0), new Expr.Capture([new Expr.Num(1), new Expr.Num(2)]), new Expr.Num(7) })
        {
            var illegal = Assert.IsType<EvalError.IllegalInEval>(RunHostMap(callee, item).Error);
            Assert.Equal("Only one collecting binding is allowed per pattern level.", illegal.Reason);
        }
    }

    // ── Helpers ─────────────────────────────────────────────────────────────

    private static EvalResult<Result> Run(string source)
        => Evaluator.Run(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root));

    private static EvalResult<Result> RunHostMap(Algorithm.User callee, Expr item)
        => Evaluator.Run(new Expr.AlgorithmExpr(new Algorithm.User(
            Parent: null,
            ParameterPatterns: [],
            Opens: [],
            Properties: [new Property("P", callee)],
            Output: [new Expr.Call(new Expr.Resolve("map"), [new Expr.ListLiteral([item]), new Expr.Resolve("P")])])));

    private static void AssertDisplay(string source, string expected)
        => Assert.Equal(
            expected,
            Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString().ReplaceLineEndings("\n"));

    /// <summary>
    /// The innermost error with its full structured payload, plus the nested sequence-value
    /// groups the failure is attributed to — everything but the outer call/callback frames.
    /// </summary>
    private static string BindingReason(EvalError error)
    {
        var groups = new List<string>();
        while (error is EvalError.WithContext context)
        {
            if (context.ErrorContext is SequenceValueParameterBindingContext group)
                groups.Add(group.PatternDisplayName);
            error = context.Inner;
        }

        var payload = error switch
        {
            EvalError.ArityMismatch arity => $"ArityMismatch({arity.Expected}, {arity.Actual})",
            EvalError.TypeMismatch mismatch => $"TypeMismatch({mismatch.Message})",
            EvalError.BadArity => "BadArity",
            EvalError.DivByZero => "DivByZero",
            _ => $"{error.GetType().Name}[{error.Code}]",
        };
        return $"{payload} in [{string.Join(", ", groups)}]";
    }
}
