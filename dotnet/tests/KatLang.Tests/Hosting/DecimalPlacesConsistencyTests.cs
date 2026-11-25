using System.Reflection;
using KatLang.Formatting;

namespace KatLang.Tests.Hosting;

/// <summary>
/// CONSISTENCY of the two decimal-places settings (owner decision 2026-11-12): an effective
/// minimum above the effective maximum is an error, and it is never repaired by clamping,
/// swapping, or dropping a value. Where each case is reported:
/// <list type="bullet">
///   <item>the HOST's own pair inconsistent in <see cref="RunOptions"/> — a host argument
///   exception where a run begins, before parsing or evaluation, never a source diagnostic (the
///   init accessors check each value's range only, so no initialization order can throw for a
///   valid final pair);</item>
///   <item>the SOURCE pair inconsistent with itself — the run's <see cref="RunResult.EvalFailure"/>
///   (<see cref="KatLangErrorCode.IllegalInEval"/>), whatever the host settings are;</item>
///   <item>the EFFECTIVE pair inconsistent only across origins — the same failure, its message
///   naming both values and where each came from, positioned at the declaration of the source
///   property that supplies a conflicting value.</item>
/// </list>
/// The CLI's own row (two inconsistent options are a usage error) is pinned in
/// <c>KatLang.CLI.Tests</c>. Also pinned here: the removed <c>DisplayDecimals</c> name has no
/// display meaning left anywhere.
/// </summary>
public sealed class DecimalPlacesConsistencyTests
{
    private static RunOptions Host(int? min, int? max) => new() { MinDecimalPlaces = min, MaxDecimalPlaces = max };

    private static KatLangError SingleEvalError(RunResult result)
        => Assert.Single(Assert.IsType<RunResult.EvalFailure>(result).Errors);

    /// <summary>The conflict's reason, as the evaluator error carries it.</summary>
    private static string Conflict(int min, string minOrigin, int max, string maxOrigin)
        => $"MinDecimalPlaces must not exceed MaxDecimalPlaces: the minimum is {min} (from the {minOrigin}) "
           + $"and the maximum is {max} (from the {maxOrigin}).";

    /// <summary>The same conflict as the public <see cref="KatLangError.Message"/> words it.</summary>
    private static string ConflictMessage(int min, string minOrigin, int max, string maxOrigin)
        => "Illegal in eval: " + Conflict(min, minOrigin, max, maxOrigin);

    /// <summary>
    /// The engine's routes: synchronous, asynchronous, and the async twin, which an asynchronous
    /// host operation in the configuration forces even when the program never calls it.
    /// <paramref name="operation"/> is an optional synchronous operation every route offers.
    /// </summary>
    private static async Task<RunResult[]> OnEveryEngineRouteAsync(
        string source, int? hostMin, int? hostMax, HostOperation? operation = null)
    {
        var unused = HostOperation.CreateAsync("unused", async (_, _) =>
        {
            await Task.Yield();
            return new Result.Atom(0);
        });
        var options = new RunOptions
        {
            MinDecimalPlaces = hostMin,
            MaxDecimalPlaces = hostMax,
            HostOperations = operation is null ? null : HostOperations.Create(operation),
        };
        var twin = new RunOptions
        {
            MinDecimalPlaces = hostMin,
            MaxDecimalPlaces = hostMax,
            HostOperations = operation is null ? HostOperations.Create(unused) : HostOperations.Create(operation, unused),
        };
        return [KatLangEngine.Run(source, options), await KatLangEngine.RunAsync(source, options), await KatLangEngine.RunAsync(source, twin)];
    }

    // ── The host's own pair ─────────────────────────────────────────────────────

    public static TheoryData<int, int> InconsistentPairs => new()
    {
        { 5, 3 },
        { 1, 0 },
        { 99, 98 },
        { 99, 0 },
        { 50, 49 },
    };

    /// <summary>
    /// A host minimum above the host maximum is rejected where a run begins: an
    /// <see cref="ArgumentException"/> before parsing or evaluation — a source that does not even
    /// parse, a host operation, and a downloader are never reached — and never an EvalFailure.
    /// </summary>
    [Theory]
    [MemberData(nameof(InconsistentPairs))]
    public async Task InconsistentHostPair_IsAHostArgumentException_BeforeParsingOrEvaluation(int min, int max)
    {
        var hostCalls = 0;
        var downloads = 0;
        var operations = HostOperations.Create(HostOperation.Create("Touch", (_, _) =>
        {
            hostCalls++;
            return new Result.Atom(1);
        }));

        // Initializing the options never throws for the pair, in either order.
        var options = new RunOptions { MinDecimalPlaces = min, MaxDecimalPlaces = max, HostOperations = operations };
        var reversed = new RunOptions { MaxDecimalPlaces = max, MinDecimalPlaces = min, HostOperations = operations };
        var downloading = new RunOptions
        {
            MinDecimalPlaces = min,
            MaxDecimalPlaces = max,
            DownloadCode = (_, _) =>
            {
                downloads++;
                return ValueTask.FromResult("public X = 1");
            },
        };

        foreach (var source in new[] { "Touch()", "1 +", "MinDecimalPlaces = 0\nMaxDecimalPlaces = 99\nTouch()", "" })
        {
            foreach (var configured in new[] { options, reversed })
            {
                var sync = Assert.Throws<ArgumentException>(() => KatLangEngine.Run(source, configured));
                Assert.Equal("options", sync.ParamName);
                Assert.Contains($"({min})", sync.Message, StringComparison.Ordinal);
                Assert.Contains($"({max})", sync.Message, StringComparison.Ordinal);

                // The asynchronous entry point delivers the same exception through its task.
                var pending = KatLangEngine.RunAsync(source, configured);
                Assert.True(pending.IsFaulted);
                var asynchronous = await Assert.ThrowsAsync<ArgumentException>(() => pending);
                Assert.Equal(sync.Message, asynchronous.Message);

                Assert.Throws<ArgumentException>(() => KatLangEngine.EvaluateToAtoms(source, configured));
                await Assert.ThrowsAsync<ArgumentException>(() => KatLangEngine.EvaluateToAtomsAsync(source, configured));
            }
        }

        await Assert.ThrowsAsync<ArgumentException>(
            () => KatLangEngine.RunAsync("open 'https://katlang.org/consistency.kat'\nX", downloading));

        Assert.Equal(0, hostCalls);
        Assert.Equal(0, downloads);
    }

    /// <summary>
    /// Each value's own range check stays at initialization; the pair is not judged there. So no
    /// initialization order throws for a valid final pair — including a replacement of BOTH
    /// values that passes through an inconsistent intermediate pair, which is what a copy-and-set
    /// of an existing options object performs one init accessor at a time. (<see cref="RunOptions"/>
    /// is a sealed class, so C# offers no <c>with</c> expression for it today; the accessors are
    /// driven here exactly as one would drive them: the minimum first, then the maximum.)
    /// </summary>
    [Fact]
    public void PairValidation_NeverThrowsForAValidFinalState_WhateverTheIntermediateOne()
    {
        // Object initializers, both orders: valid pairs, equal values, and each setting alone.
        foreach (var (min, max) in new (int?, int?)[] { (0, 0), (2, 4), (5, 7), (99, 99), (0, 99), (3, null), (null, 3), (null, null) })
        {
            var forward = new RunOptions { MinDecimalPlaces = min, MaxDecimalPlaces = max };
            var backward = new RunOptions { MaxDecimalPlaces = max, MinDecimalPlaces = min };
            Assert.Equal((min, max), (forward.MinDecimalPlaces, forward.MaxDecimalPlaces));
            Assert.Equal((min, max), (backward.MinDecimalPlaces, backward.MaxDecimalPlaces));
            Assert.IsType<RunResult.Success>(KatLangEngine.Run("1 / 8", forward));
            Assert.IsType<RunResult.Success>(KatLangEngine.Run("1 / 8", backward));
        }

        // An existing pair (1, 3) replaced by (5, 7): setting the minimum first makes the pair
        // (5, 3) until the maximum is set. Neither init accessor throws, and the final object runs.
        var options = new RunOptions { MinDecimalPlaces = 1, MaxDecimalPlaces = 3 };
        var setMin = typeof(RunOptions).GetProperty(nameof(RunOptions.MinDecimalPlaces))!.SetMethod!;
        var setMax = typeof(RunOptions).GetProperty(nameof(RunOptions.MaxDecimalPlaces))!.SetMethod!;

        setMin.Invoke(options, [(int?)5]);
        Assert.Equal(((int?)5, (int?)3), (options.MinDecimalPlaces, options.MaxDecimalPlaces));

        // The intermediate pair itself is what a run refuses — the check exists, at the entry point.
        Assert.Throws<ArgumentException>(() => KatLangEngine.Run("1 / 8", options));

        setMax.Invoke(options, [(int?)7]);
        Assert.Equal(((int?)5, (int?)7), (options.MinDecimalPlaces, options.MaxDecimalPlaces));
        Assert.Equal("0.12500", KatLangEngine.Run("1 / 8", options).ToDisplayString());

        // The range check, by contrast, does fire in the accessor — for either property.
        foreach (var setter in new[] { setMin, setMax })
        {
            var rejected = Assert.Throws<TargetInvocationException>(() => setter.Invoke(options, [(int?)100]));
            Assert.IsType<ArgumentOutOfRangeException>(rejected.InnerException);
        }

        Assert.Equal(((int?)5, (int?)7), (options.MinDecimalPlaces, options.MaxDecimalPlaces));
    }

    [Fact]
    public void HostPair_IsNeverRepaired()
    {
        // Not clamped to the maximum, not swapped, and neither value dropped: the run is refused.
        var options = Host(5, 3);
        Assert.Equal(((int?)5, (int?)3), (options.MinDecimalPlaces, options.MaxDecimalPlaces));
        Assert.Throws<ArgumentException>(() => KatLangEngine.Run("1 / 8", options));

        // The parser takes no part: display configuration is not source processing.
        Assert.False(Parser.Parse("1 / 8", options).HasErrors);
    }

    // ── The program's own pair ──────────────────────────────────────────────────

    public static TheoryData<string, int, int, int, int> InconsistentSourcePairs => new()
    {
        // source, min, max, the line of the MinDecimalPlaces declaration, and of MaxDecimalPlaces
        { "MinDecimalPlaces = 5\nMaxDecimalPlaces = 3\n1 / 7", 5, 3, 1, 2 },
        { "MaxDecimalPlaces = 3\nMinDecimalPlaces = 5\n1 / 7", 5, 3, 2, 1 },
        { "1 / 7\nMaxDecimalPlaces = 0\nMinDecimalPlaces = 1", 1, 0, 3, 2 },
        { "Places = 98\nMinDecimalPlaces = Places + 1\nMaxDecimalPlaces = Places\n1 / 7", 99, 98, 2, 3 },
    };

    /// <summary>
    /// The program's own pair inconsistent: <c>EvalFailure</c> / <c>IllegalInEval</c>, both values
    /// attributed to the program and positioned at its <c>MinDecimalPlaces</c> declaration —
    /// WHATEVER the host settings are. A host setting never excuses an invalid source
    /// configuration, not even one that would make the effective pair consistent.
    /// </summary>
    [Theory]
    [MemberData(nameof(InconsistentSourcePairs))]
    public async Task InconsistentSourcePair_IsAnEvalFailure_WhateverTheHostSettings(
        string source, int min, int max, int minLine, int maxLine)
    {
        SourceProvenance.ParseValid(source);
        _ = maxLine;
        var expectedSpan = new SourceSpan(minLine, 1, minLine, 17);

        foreach (var (hostMin, hostMax) in new (int?, int?)[]
                 {
                     (null, null),
                     // A host minimum of 0 makes the EFFECTIVE pair (0, max) consistent — no excuse.
                     (0, null),
                     (0, 0),
                     (0, 99),
                     (null, 99),
                     (null, 0),
                     (99, 99),
                     (min, null),
                     (null, max),
                 })
        {
            foreach (var run in await OnEveryEngineRouteAsync(source, hostMin, hostMax))
            {
                var error = SingleEvalError(run);
                Assert.Equal(KatLangErrorCode.IllegalInEval, error.Code);
                Assert.Equal(ConflictMessage(min, "program", max, "program"), error.Message);
                Assert.Equal(expectedSpan, error.Span);
                Assert.False(run.DisplayOptions.HasDecimalPlaces);
            }
        }
    }

    // ── The effective pair across origins ───────────────────────────────────────

    /// <summary>
    /// Partial settings across origins: source, host min, host max, then the message's minimum,
    /// its origin, its maximum, its origin, and the property whose declaration positions it. An
    /// empty property name marks a CONTROL row: a nearby configuration that is consistent.
    /// </summary>
    public static TheoryData<string, int?, int?, int, string, int, string, string> CrossOriginConflicts => new()
    {
        // The program declares only a minimum; the host supplies only a maximum below it.
        { "MinDecimalPlaces = 4\n1 / 7", null, 2, 4, "program", 2, "host", "MinDecimalPlaces" },
        { "MinDecimalPlaces = 99\n1 / 7", null, 0, 99, "program", 0, "host", "MinDecimalPlaces" },
        // The mirror image: only a source maximum, only a host minimum above it.
        { "MaxDecimalPlaces = 2\n1 / 7", 4, null, 4, "host", 2, "program", "MaxDecimalPlaces" },
        { "MaxDecimalPlaces = 0\n1 / 7", 1, null, 1, "host", 0, "program", "MaxDecimalPlaces" },
        // A complete source pair against a lone host maximum below its minimum.
        { "MinDecimalPlaces = 3\nMaxDecimalPlaces = 6\n1 / 7", null, 2, 3, "program", 2, "host", "MinDecimalPlaces" },
        // A complete host pair against a lone source maximum below the host minimum; the
        // declaration that positions the error is not on the first line.
        { "X = 1 / 7\nMaxDecimalPlaces = 1\nX", 3, 5, 3, "host", 1, "program", "MaxDecimalPlaces" },
        // Controls. A host minimum ABOVE the source's lowers nothing; a lone source minimum is
        // lowered by a complete host pair to within it; an equal value is no conflict.
        { "MinDecimalPlaces = 3\nMaxDecimalPlaces = 6\n1 / 7", 9, null, 0, "", 0, "", "" },
        { "MinDecimalPlaces = 8\n1 / 7", 2, 5, 0, "", 0, "", "" },
        { "MinDecimalPlaces = 4\n1 / 7", 4, 9, 0, "", 0, "", "" },
        { "MinDecimalPlaces = 4\n1 / 7", null, 4, 0, "", 0, "", "" },
        { "MinDecimalPlaces = 4\nMaxDecimalPlaces = 9\n1 / 7", 4, 4, 0, "", 0, "", "" },
        { "MaxDecimalPlaces = 2\n1 / 7", 2, null, 0, "", 0, "", "" },
    };

    /// <summary>
    /// The effective pair inconsistent only across origins: <c>EvalFailure</c> /
    /// <c>IllegalInEval</c>, naming both effective values and where each came from, positioned at
    /// the declaration of the source property supplying a conflicting value —
    /// <c>MinDecimalPlaces</c> when the effective minimum is the program's, otherwise
    /// <c>MaxDecimalPlaces</c>.
    /// </summary>
    [Theory]
    [MemberData(nameof(CrossOriginConflicts))]
    public async Task ConflictAcrossOrigins_IsAnEvalFailure_NamingBothValuesAndTheirOrigins(
        string source, int? hostMin, int? hostMax, int min, string minOrigin, int max, string maxOrigin, string positionedAt)
    {
        var root = SourceProvenance.ParseValid(source).Root;

        foreach (var run in await OnEveryEngineRouteAsync(source, hostMin, hostMax))
        {
            if (positionedAt.Length == 0)
            {
                Assert.IsType<RunResult.Success>(run);
                continue;
            }

            var error = SingleEvalError(run);
            Assert.Equal(KatLangErrorCode.IllegalInEval, error.Code);
            Assert.Equal(ConflictMessage(min, minOrigin, max, maxOrigin), error.Message);
            Assert.Equal(root.Properties.Single(p => p.Name == positionedAt).FirstDeclarationSpan, error.Span);
            Assert.NotNull(error.Span);

            // A failure displays canonically and carries no pair: nothing was clamped into place.
            Assert.False(run.DisplayOptions.HasDecimalPlaces);
            Assert.Equal(error.ToString(), run.ToDisplayString());
        }
    }

    /// <summary>The conflict is evaluated like any run: the output and BOTH reads happen first.</summary>
    [Fact]
    public void ConflictAcrossOrigins_IsDecidedAfterTheOutputAndBothReads()
    {
        var calls = new List<string>();
        var operations = HostOperations.Create(HostOperation.Create(
            "Note",
            (args, _) =>
            {
                calls.Add(((Result.Atom)args[0]).Value.ToString(System.Globalization.CultureInfo.InvariantCulture));
                return args[0];
            },
            "value"));

        var run = KatLangEngine.Run(
            "MaxDecimalPlaces = Note(9)\nMinDecimalPlaces = Note(4)\nNote(1) / 8",
            new RunOptions { HostOperations = operations, MaxDecimalPlaces = 2 });

        Assert.Equal(ConflictMessage(4, "program", 2, "host"), SingleEvalError(run).Message);
        // The output's call, then the minimum's, then the maximum's.
        Assert.Equal(["1", "4", "9"], calls);
    }

    /// <summary>
    /// The fact the design relies on: when each origin supplies a COMPLETE, self-consistent pair,
    /// the composed pair is always consistent — a minimum of two lower bounds never exceeds the
    /// minimum of the two upper bounds above them. Checked over the whole domain of one pair
    /// against a spread of the other, through the production composition and conflict check.
    /// </summary>
    [Fact]
    public void TwoCompleteConsistentPairs_NeverConflict()
    {
        var root = SourceProvenance.ParseValid("MinDecimalPlaces = 0\nMaxDecimalPlaces = 0\n1").Root;
        int[] spread = [0, 1, 2, 5, 33, 34, 50, 98, 99];

        for (var sourceMin = 0; sourceMin <= RunOptions.DecimalPlacesLimit; sourceMin++)
        {
            for (var sourceMax = sourceMin; sourceMax <= RunOptions.DecimalPlacesLimit; sourceMax++)
            {
                foreach (var hostMin in spread)
                {
                    foreach (var hostMax in spread)
                    {
                        if (hostMin > hostMax)
                            continue;

                        var options = new DisplayOptions(sourceMin, sourceMax, hostMin, hostMax, int.MaxValue);
                        Assert.True(options.MinDecimalPlaces <= options.MaxDecimalPlaces);
                        Assert.Null(KatLangEngine.DecimalPlacesConflict(root, options));
                    }
                }
            }
        }

        // Through the engine, at the corners.
        foreach (var (sourceMin, sourceMax, hostMin, hostMax) in new[] { (0, 0, 99, 99), (99, 99, 0, 0), (2, 4, 1, 3), (1, 3, 2, 4), (0, 99, 50, 50), (50, 50, 0, 99) })
        {
            var run = KatLangEngine.Run(
                $"MinDecimalPlaces = {sourceMin}\nMaxDecimalPlaces = {sourceMax}\n1 / 7", Host(hostMin, hostMax));
            var success = Assert.IsType<RunResult.Success>(run);
            Assert.Equal(Math.Min(sourceMin, hostMin), success.DisplayOptions.MinDecimalPlaces);
            Assert.Equal(Math.Min(sourceMax, hostMax), success.DisplayOptions.MaxDecimalPlaces);
        }
    }

    /// <summary>The conflict check itself: absent settings conflict with nothing, equal ones do not.</summary>
    [Fact]
    public void ConflictCheck_NeedsBothEffectiveSettings_AndAStrictInequality()
    {
        var root = SourceProvenance.ParseValid("MinDecimalPlaces = 0\nMaxDecimalPlaces = 0\n1").Root;
        static DisplayOptions Options(int? sourceMin, int? sourceMax, int? hostMin, int? hostMax)
            => new(sourceMin, sourceMax, hostMin, hostMax, int.MaxValue);

        Assert.Null(KatLangEngine.DecimalPlacesConflict(root, Options(null, null, null, null)));
        Assert.Null(KatLangEngine.DecimalPlacesConflict(root, Options(99, null, null, null)));
        Assert.Null(KatLangEngine.DecimalPlacesConflict(root, Options(null, 0, null, null)));
        Assert.Null(KatLangEngine.DecimalPlacesConflict(root, Options(99, null, 99, null)));
        Assert.Null(KatLangEngine.DecimalPlacesConflict(root, Options(null, 0, null, 0)));
        Assert.Null(KatLangEngine.DecimalPlacesConflict(root, Options(7, 7, null, null)));
        Assert.Null(KatLangEngine.DecimalPlacesConflict(root, Options(7, null, null, 7)));
        // A larger source minimum that the host lowers below the maximum is no conflict.
        Assert.Null(KatLangEngine.DecimalPlacesConflict(root, Options(9, null, 2, 4)));

        Assert.IsType<EvalError.IllegalInEval>(KatLangEngine.DecimalPlacesConflict(root, Options(8, 7, null, null)));
        Assert.IsType<EvalError.IllegalInEval>(KatLangEngine.DecimalPlacesConflict(root, Options(8, null, null, 7)));
        Assert.IsType<EvalError.IllegalInEval>(KatLangEngine.DecimalPlacesConflict(root, Options(null, 7, 8, null)));
    }

    /// <summary>
    /// A value both origins supply equally is attributed to the PROGRAM. No run can observe the
    /// tie — with each origin's own pair consistent, a tied value is never one side of a conflict,
    /// and an inconsistent host pair never reaches the engine — so the rule is pinned on the one
    /// conflict check directly, with pairs the entry point would have refused.
    /// </summary>
    [Fact]
    public void ConflictCheck_AttributesATiedValueToTheProgram()
    {
        var root = SourceProvenance.ParseValid("MinDecimalPlaces = 0\nMaxDecimalPlaces = 0\n1").Root;
        var minDeclaration = new SourceSpan(1, 1, 1, 17);
        var maxDeclaration = new SourceSpan(2, 1, 2, 17);

        // The minimum is tied (program 5, host 5): the program's, so it positions the error.
        var tiedMin = Assert.IsType<EvalError.IllegalInEval>(
            KatLangEngine.DecimalPlacesConflict(root, new DisplayOptions(5, null, 5, 3, int.MaxValue)));
        Assert.Equal(Conflict(5, "program", 3, "host"), tiedMin.Reason);
        Assert.Equal(minDeclaration, tiedMin.Span);

        // The maximum is tied (program 3, host 3) and the minimum is the host's.
        var tiedMax = Assert.IsType<EvalError.IllegalInEval>(
            KatLangEngine.DecimalPlacesConflict(root, new DisplayOptions(null, 3, 5, 3, int.MaxValue)));
        Assert.Equal(Conflict(5, "host", 3, "program"), tiedMax.Reason);
        Assert.Equal(maxDeclaration, tiedMax.Span);

        // Both tied: both the program's, positioned at the minimum.
        var bothTied = Assert.IsType<EvalError.IllegalInEval>(
            KatLangEngine.DecimalPlacesConflict(root, new DisplayOptions(5, 3, 5, 3, int.MaxValue)));
        Assert.Equal(Conflict(5, "program", 3, "program"), bothTied.Reason);
        Assert.Equal(minDeclaration, bothTied.Span);

        // The smaller value decides the origin: a host minimum below the program's is the host's.
        var hostLower = Assert.IsType<EvalError.IllegalInEval>(
            KatLangEngine.DecimalPlacesConflict(root, new DisplayOptions(9, 3, 5, null, int.MaxValue)));
        Assert.Equal(Conflict(5, "host", 3, "program"), hostLower.Reason);
        Assert.Equal(maxDeclaration, hostLower.Span);
    }

    // ── DisplayDecimals has no display meaning left ─────────────────────────────

    /// <summary>
    /// A root <c>DisplayDecimals</c> is an ordinary property like any other: it changes no
    /// display, it is never read by the engine (so its effects never run and its failures never
    /// surface), it is readable by the program, and no diagnostic mentions it.
    /// </summary>
    [Fact]
    public async Task RootDisplayDecimals_IsAnOrdinaryProperty_WithNoDisplayEffect()
    {
        var calls = 0;
        var touch = HostOperation.Create("Touch", (_, _) =>
        {
            Interlocked.Increment(ref calls);
            return new Result.Atom(2);
        });

        const string canonical = "0.3333333333333333333333333333333333\n2.5000";
        var plain = KatLangEngine.Run("1 / 3, 2.5000");
        foreach (var declaration in new[]
                 {
                     "DisplayDecimals = 2",
                     "DisplayDecimals = 0",
                     "DisplayDecimals = -1",
                     "DisplayDecimals = 1.5",
                     "DisplayDecimals = 100",
                     "DisplayDecimals = 'x'",
                     "DisplayDecimals = 1 / 0",
                     "DisplayDecimals = Touch()",
                     "DisplayDecimals(x) = x",
                 })
        {
            var source = declaration + "\n1 / 3, 2.5000";
            SourceProvenance.ParseValid(source);

            foreach (var run in await OnEveryEngineRouteAsync(source, null, null, touch))
            {
                var success = Assert.IsType<RunResult.Success>(run);
                Assert.Equal(canonical, success.ToDisplayString().ReplaceLineEndings("\n"));
                Assert.False(success.DisplayOptions.HasDecimalPlaces);
                foreach (var formatter in new[] { OutputFormatters.Exact, OutputFormatters.Readable, OutputFormatters.Concise })
                    Assert.Equal(formatter.Format(plain), formatter.Format(success));
            }
        }

        Assert.Equal(0, calls);

        // Readable like any other property, and beside the real settings it stays inert.
        Assert.Equal("7", KatLangEngine.Run("DisplayDecimals = 6\nDisplayDecimals + 1").ToDisplayString());
        Assert.Equal(
            "0.33\n6.00",
            KatLangEngine.Run("DisplayDecimals = 6\nMinDecimalPlaces = 2\nMaxDecimalPlaces = 2\n1 / 3, DisplayDecimals")
                .ToDisplayString().ReplaceLineEndings("\n"));
    }

    /// <summary>The removed host members are gone outright: no compatibility shim, no alias.</summary>
    [Fact]
    public void RemovedHostMembers_AreGone_WithoutShims()
    {
        const BindingFlags all = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance | BindingFlags.Static;

        Assert.Null(typeof(RunOptions).GetProperty("DefaultDisplayDecimals", all));
        Assert.Null(typeof(RunOptions).GetField("MaxDisplayDecimals", all));
        Assert.Empty(typeof(RunResult).GetMember("WithHostDisplayDecimals", all));
        Assert.Empty(typeof(KatLangEngine).GetMember("CombineDisplayDecimals", all));

        foreach (var type in typeof(KatLangEngine).Assembly.GetTypes())
        {
            foreach (var member in type.GetMembers(all | BindingFlags.DeclaredOnly))
                Assert.DoesNotContain("DisplayDecimals", member.Name, StringComparison.OrdinalIgnoreCase);
        }

        Assert.Equal(99, RunOptions.DecimalPlacesLimit);
        Assert.NotNull(typeof(RunOptions).GetProperty(nameof(RunOptions.MinDecimalPlaces)));
        Assert.NotNull(typeof(RunOptions).GetProperty(nameof(RunOptions.MaxDecimalPlaces)));
        Assert.NotNull(typeof(RunResult).GetMethod(nameof(RunResult.WithHostDecimalPlaces), [typeof(int?), typeof(int?)]));
    }
}
