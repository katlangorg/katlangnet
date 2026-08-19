using KatLang.Tests.LanguageSpec;

namespace KatLang.Tests.Hosting;

/// <summary>
/// Public host-operation API: construction validation, synchronous behavior through
/// the public engine and evaluator entry points, the property-cache contract
/// (<c>Data</c> vs <c>Data()</c>), shadowing, host exception identity, and the
/// corpus-wide guarantee that an UNUSED host-operation configuration changes no
/// program's outcome.
/// </summary>
public class HostOperationApiTests
{
    private static Result Atom(decimal value) => new Result.Atom(value);

    private static HostOperation SyncConstant(string name, decimal value, Counter? counter = null)
        => HostOperation.Create(name, (_, _) =>
        {
            counter?.Increment();
            return Atom(value);
        });

    /// <summary>Thread-safe invocation counter for host delegates.</summary>
    public sealed class Counter
    {
        private int _count;
        public int Count => Volatile.Read(ref _count);
        public void Increment() => Interlocked.Increment(ref _count);
    }

    // ── Construction validation ─────────────────────────────────────────────

    [Theory]
    [InlineData("")]
    [InlineData("1abc")]
    [InlineData("a-b")]
    [InlineData("a b")]
    [InlineData("host:x")]
    [InlineData("Dot.Name")]
    [InlineData("div")]
    [InlineData("mod")]
    [InlineData("and")]
    [InlineData("or")]
    [InlineData("xor")]
    [InlineData("not")]
    [InlineData("public")]
    [InlineData("open")]
    public void Create_InvalidName_Throws(string name)
        => Assert.Throws<ArgumentException>(() => HostOperation.Create(name, (_, _) => Atom(0)));

    [Theory]
    [InlineData("sum")]
    [InlineData("if")]
    [InlineData("count")]
    [InlineData("map")]
    [InlineData("Math")]
    [InlineData("load")]
    public void Create_ReservedPreludeName_Throws(string name)
        => Assert.Throws<ArgumentException>(() => HostOperation.Create(name, (_, _) => Atom(0)));

    [Fact]
    public void Create_InvalidOrDuplicateParameterNames_Throw()
    {
        Assert.Throws<ArgumentException>(() => HostOperation.Create("F", (_, _) => Atom(0), "1bad"));
        Assert.Throws<ArgumentException>(() => HostOperation.Create("F", (_, _) => Atom(0), "open"));
        Assert.Throws<ArgumentException>(() => HostOperation.Create("F", (_, _) => Atom(0), "a", "a"));
    }

    [Fact]
    public void Create_NullImplementation_Throws()
    {
        Assert.Throws<ArgumentNullException>(
            () => HostOperation.Create("F", null!));
        Assert.Throws<ArgumentNullException>(
            () => HostOperation.CreateAsync("F", null!));
    }

    [Fact]
    public void Factories_NullNamesCollectionsAndElements_Throw()
    {
        Assert.Throws<ArgumentNullException>(
            () => HostOperation.Create(null!, (_, _) => Atom(0)));
        Assert.Throws<ArgumentNullException>(
            () => HostOperation.Create("F", (_, _) => Atom(0), null!));
        Assert.Throws<ArgumentNullException>(
            () => HostOperations.Create((HostOperation[])null!));
        Assert.Throws<ArgumentNullException>(
            () => HostOperations.Create([null!]));
    }

    [Fact]
    public void HostOperationsCreate_DuplicateNames_Throws()
        => Assert.Throws<ArgumentException>(() => HostOperations.Create(
            SyncConstant("Data", 1),
            SyncConstant("Data", 2)));

    [Fact]
    public void FactoryFlavor_IsReflectedInIsAsynchronous()
    {
        Assert.False(SyncConstant("S", 1).IsAsynchronous);
        Assert.True(HostOperation.CreateAsync("A", (_, _) => ValueTask.FromResult(Atom(1))).IsAsynchronous);
        Assert.False(HostOperations.Create(SyncConstant("S", 1)).ContainsAsynchronousOperations);
        Assert.True(HostOperations.Create(
            SyncConstant("S", 1),
            HostOperation.CreateAsync("A", (_, _) => ValueTask.FromResult(Atom(1)))).ContainsAsynchronousOperations);
    }

    [Fact]
    public void PublicConfigurationCollections_AreImmutableSnapshots()
    {
        var parameterNames = new[] { "value" };
        var operation = HostOperation.Create("Echo", (args, _) => args[0], parameterNames);
        parameterNames[0] = "changed";

        Assert.Equal("value", operation.ParameterNames[0]);
        var exposedParameters = Assert.IsAssignableFrom<IList<string>>(operation.ParameterNames);
        Assert.Throws<NotSupportedException>(() => exposedParameters[0] = "changed-again");

        var inputOperations = new[] { operation };
        var operations = HostOperations.Create(inputOperations);
        inputOperations[0] = SyncConstant("Other", 1);

        Assert.Same(operation, operations.Operations[0]);
        var exposedOperations = Assert.IsAssignableFrom<IList<HostOperation>>(operations.Operations);
        Assert.Throws<NotSupportedException>(() => exposedOperations[0] = SyncConstant("Other", 2));
        Assert.False(operations.ContainsAsynchronousOperations);
    }

    // ── Synchronous behavior through the public engine ──────────────────────

    [Fact]
    public void EngineRun_ZeroArgOperation_ProvidesValue()
    {
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(SyncConstant("Data", 21)),
        };

        var result = Assert.IsType<RunResult.Success>(KatLangEngine.Run("Data * 2", options));
        Assert.Equal("42", result.ToDisplayString());
    }

    [Fact]
    public void EngineRun_WithoutConfiguration_SameNameStaysImplicitParameter()
    {
        // The exact same source that succeeds with the operation configured must keep
        // its ordinary meaning without it: an unresolved name is an implicit parameter
        // and the engine reports the unresolved-parameter failure.
        var configured = KatLangEngine.Run("Data * 2", new RunOptions
        {
            HostOperations = HostOperations.Create(SyncConstant("Data", 21)),
        });
        var unconfigured = KatLangEngine.Run("Data * 2");

        Assert.IsType<RunResult.Success>(configured);
        Assert.False(unconfigured.IsSuccess);
    }

    [Fact]
    public void EngineRun_ParameterizedOperation_ReceivesEvaluatedArgumentsInOrder()
    {
        IReadOnlyList<Result>? observed = null;
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.Create(
                    "Combine",
                    (args, _) =>
                    {
                        observed = args;
                        return Atom(((Result.Atom)args[0]).Value - ((Result.Atom)args[1]).Value);
                    },
                    "a", "b")),
        };

        var result = Assert.IsType<RunResult.Success>(KatLangEngine.Run("Combine(10, 3)", options));
        Assert.Equal("7", result.ToDisplayString());
        Assert.NotNull(observed);
        Assert.Equal(2, observed.Count);
        Assert.Equal(10m, ((Result.Atom)observed[0]).Value);
        Assert.Equal(3m, ((Result.Atom)observed[1]).Value);
    }

    [Fact]
    public void SynchronousOperation_ReceivesTheEvaluationToken_ByIdentity()
    {
        using var cts = new CancellationTokenSource();
        var observedToken = default(CancellationToken);
        var options = new RunOptions
        {
            EvaluationCancellationToken = cts.Token,
            HostOperations = HostOperations.Create(
                HostOperation.Create("Data", (_, token) =>
                {
                    observedToken = token;
                    return Atom(42);
                })),
        };

        Assert.IsType<RunResult.Success>(KatLangEngine.Run("Data", options));
        Assert.Equal(cts.Token, observedToken);
    }

    [Fact]
    public void EngineRun_OperationReceivesFullKatLangValues()
    {
        IReadOnlyList<Result>? observed = null;
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.Create(
                    "Pack",
                    (args, _) =>
                    {
                        observed = args;
                        return Atom(args.Count);
                    },
                    "first", "second", "third")),
        };

        var result = Assert.IsType<RunResult.Success>(
            KatLangEngine.Run("Pack([1, 2], (3, 4), 'text')", options));
        Assert.Equal("3", result.ToDisplayString());
        Assert.NotNull(observed);
        Assert.IsType<Result.ListValue>(observed[0]);
        Assert.IsType<Result.SequenceValue>(observed[1]);
        Assert.Equal("text", ((Result.Str)observed[2]).Value);
    }

    [Fact]
    public void EngineRun_OperationResult_ParticipatesInOrdinaryLanguageSemantics()
    {
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.Create("Rows", (_, _) => new Result.ListValue([Atom(1), Atom(2), Atom(3)]))),
        };

        var result = Assert.IsType<RunResult.Success>(
            KatLangEngine.Run("Rows.count\nRows.sum\nsum(Rows)", options));
        Assert.Equal($"3{Environment.NewLine}6{Environment.NewLine}6", result.ToDisplayString());
    }

    [Fact]
    public void EngineRun_ProgramProperty_ShadowsHostOperation()
    {
        var counter = new Counter();
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(SyncConstant("Data", 42, counter)),
        };

        var result = Assert.IsType<RunResult.Success>(KatLangEngine.Run("Data = 5\nData", options));
        Assert.Equal("5", result.ToDisplayString());
        Assert.Equal(0, counter.Count);
    }

    [Fact]
    public void ExplicitParameter_ShadowsHostOperation()
    {
        var counter = new Counter();
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(SyncConstant("Data", 42, counter)),
        };

        var result = Assert.IsType<RunResult.Success>(KatLangEngine.Run("Identity(Data) = Data\nIdentity(5)", options));
        Assert.Equal("5", result.ToDisplayString());
        Assert.Equal(0, counter.Count);
    }

    [Fact]
    public void InlineOpenBody_ResolvesHostOperationsDuringParameterDetection()
    {
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(SyncConstant("Data", 21)),
        };

        var result = Assert.IsType<RunResult.Success>(
            KatLangEngine.Run("open { public Doubled = Data * 2 }\nDoubled", options));
        Assert.Equal("42", result.ToDisplayString());
    }

    [Fact]
    public void EngineRun_MathMemberNamedOperation_DoesNotHijackMathDispatch()
    {
        // "Abs" is not a reserved prelude name (only "Math" is); a host operation
        // named Abs is an ambient top-level name, while Math.Abs keeps its built-in
        // native dispatch — the "host:" native-name prefix keeps them apart.
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.Create("Abs", (_, _) => Atom(1000), "x")),
        };

        var result = Assert.IsType<RunResult.Success>(
            KatLangEngine.Run("Abs(-3)\nMath.Abs(-3)", options));
        Assert.Equal($"1000{Environment.NewLine}3", result.ToDisplayString());
    }

    // ── Property-cache contract: Data vs Data() ─────────────────────────────

    [Fact]
    public void PropertyStyleAccess_InvokesHostOnce_PerRunContext()
    {
        var counter = new Counter();
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(SyncConstant("Data", 42, counter)),
        };

        // Two bare property-style OUTPUT ROWS: the second access is a per-run
        // zero-argument property cache hit, so the host runs once.
        var result = Assert.IsType<RunResult.Success>(KatLangEngine.Run("Data\nData", options));
        Assert.Equal($"42{Environment.NewLine}42", result.ToDisplayString());
        Assert.Equal(1, counter.Count);
    }

    [Fact]
    public void ExplicitCall_BypassesThePropertyCache_InvokingHostEachTime()
    {
        var counter = new Counter();
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(SyncConstant("Data", 42, counter)),
        };

        // The core A-vs-A() distinction applies to host operations unchanged:
        // an explicit call bypasses that property's cache entry.
        var result = Assert.IsType<RunResult.Success>(KatLangEngine.Run("Data()\nData()", options));
        Assert.Equal($"42{Environment.NewLine}42", result.ToDisplayString());
        Assert.Equal(2, counter.Count);
    }

    [Fact]
    public void SequentialRuns_NeverShareHostResults()
    {
        // The property cache is run-scoped; a second run re-invokes the host and
        // observes its current value.
        var next = 0;
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.Create("Data", (_, _) => Atom(Interlocked.Increment(ref next)))),
        };

        Assert.Equal("1", Assert.IsType<RunResult.Success>(KatLangEngine.Run("Data", options)).ToDisplayString());
        Assert.Equal("2", Assert.IsType<RunResult.Success>(KatLangEngine.Run("Data", options)).ToDisplayString());
    }

    [Fact]
    public void BuiltinDirectCallArgument_StillInvokesHostOperation()
    {
        // Builtin direct-call arguments bypass the property cache, but dispatch lives
        // in the wrapper BODY, so the host operation is still invoked on that path.
        var counter = new Counter();
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.Create("Data", (_, _) =>
                {
                    counter.Increment();
                    return new Result.SequenceValue([Atom(1), Atom(2), Atom(3)]);
                })),
        };

        var result = Assert.IsType<RunResult.Success>(KatLangEngine.Run("sum(Data)", options));
        Assert.Equal("6", result.ToDisplayString());
        Assert.Equal(1, counter.Count);
    }

    [Fact]
    public void HostOperationInsideLoopStep_FallsBackToGenericLoopAndRunsPerIteration()
    {
        var counter = new Counter();
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.Create("Tick", (_, _) =>
                {
                    counter.Increment();
                    return Atom(1);
                })),
        };

        var result = Assert.IsType<RunResult.Success>(
            KatLangEngine.Run("Step(n) = n + Tick()\nrepeat(Step, 3, 0)", options));
        Assert.Equal("3", result.ToDisplayString());
        Assert.Equal(3, counter.Count);
    }

    [Fact]
    public void HostOperationInsideFusablePipelineCallback_ComputesTheSameResult()
    {
        // range → filter → count is a fusion-eligible pipeline shape; the predicate
        // body calls a host operation, so whichever strategy runs must route the
        // callback through ordinary evaluation and invoke the host per item.
        var counter = new Counter();
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.Create(
                    "IsEven",
                    (args, _) =>
                    {
                        counter.Increment();
                        var value = ((Result.Atom)args[0]).Value;
                        return Atom(value % 2 == 0 ? 1 : 0);
                    },
                    "x")),
        };

        var result = Assert.IsType<RunResult.Success>(
            KatLangEngine.Run("Pred(x) = IsEven(x)\nrange(1, 6).filter(Pred).count", options));
        Assert.Equal("3", result.ToDisplayString());
        Assert.Equal(6, counter.Count);
    }

    // ── Diagnostics and host exceptions ─────────────────────────────────────

    [Fact]
    public void ArityMismatch_IsAnOrdinaryKatLangDiagnostic()
    {
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.Create("Fetch", (args, _) => args[0], "id")),
        };

        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run("Fetch(1, 2)", options));
        Assert.Contains("argument", failure.Errors[0].Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void HostException_PropagatesToTheHostUnchanged()
    {
        var exception = new InvalidDataException("host database offline");
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.Create("Data", (_, _) => throw exception)),
        };

        var observed = Assert.Throws<InvalidDataException>(() => KatLangEngine.Run("Data + 1", options));
        Assert.Same(exception, observed);
    }

    [Fact]
    public void NullReturningOperation_IsAHostContractViolation()
    {
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.Create("Data", (_, _) => null!)),
        };

        var observed = Assert.Throws<InvalidOperationException>(() => KatLangEngine.Run("Data", options));
        Assert.Contains("returned null", observed.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ForgedHostNativeCall_WithMismatchedSignature_DoesNotInvokeTheHost()
    {
        var counter = new Counter();
        var operations = HostOperations.Create(
            HostOperation.Create("Echo", (_, _) =>
            {
                counter.Increment();
                return Atom(42);
            }, "value"));

        var result = Evaluator.Run(
            new Expr.NativeCall("host:Echo", []),
            operations,
            limits: null,
            CancellationToken.None);

        Assert.True(result.IsError);
        var error = Assert.IsType<EvalError.IllegalInEval>(result.Error);
        Assert.Contains("invalid native-call signature", error.Reason, StringComparison.Ordinal);
        Assert.Equal(0, counter.Count);
    }

    [Fact]
    public async Task LoadedModuleCode_ResolvesHostOperations_Too()
    {
        // Module elaboration splices module trees into the root before parameter
        // detection, so host-operation names resolve inside loaded module code exactly
        // as in the main program.
        var counter = new Counter();
        var options = new RunOptions
        {
            DownloadCode = (_, _) => ValueTask.FromResult("public Doubled = Data * 2"),
            AllowedHosts = ["example.test"],
            HostOperations = HostOperations.Create(SyncConstant("Data", 21, counter)),
        };

        var result = Assert.IsType<RunResult.Success>(
            await KatLangEngine.RunAsync("open 'https://example.test/lib.kat'\nDoubled", options));
        Assert.Equal("42", result.ToDisplayString());
        Assert.Equal(1, counter.Count);
    }

    [Fact]
    public void ReentrantHostOperation_MayRunNestedEngineRuns()
    {
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.Create("Nested", (_, _) =>
                    Atom(KatLangEngine.EvaluateToAtoms("20 + 21")[0]))),
        };

        var result = Assert.IsType<RunResult.Success>(KatLangEngine.Run("Nested + 1", options));
        Assert.Equal("42", result.ToDisplayString());
    }

    // ── Synchronous entry points reject asynchronous configurations ─────────

    [Fact]
    public void SynchronousEntryPoints_RejectAsynchronousOperations_BeforeInvokingAnything()
    {
        var counter = new Counter();
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync("Data", (_, _) =>
                {
                    counter.Increment();
                    return ValueTask.FromResult(Atom(1));
                })),
        };

        Assert.Throws<InvalidOperationException>(() => KatLangEngine.Run("Data", options));
        Assert.Throws<InvalidOperationException>(() => KatLangEngine.EvaluateToAtoms("Data", options));
        Assert.Throws<InvalidOperationException>(() => KatLangEngine.EvaluateToString("Data", options));
        Assert.Equal(0, counter.Count);
    }

    [Fact]
    public void EvaluatorRun_HostOperationOverload_WorksAndValidates()
    {
        var operations = HostOperations.Create(SyncConstant("Data", 21));
        var parsed = Parser.Parse("Data * 2", new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors);

        var result = Evaluator.Run(
            new Expr.AlgorithmExpr(parsed.Root), operations, null, CancellationToken.None);
        Assert.True(result.IsOk);
        Assert.Equal(42m, ((Result.Atom)result.Value).Value);

        Assert.Throws<ArgumentNullException>(() => Evaluator.Run(
            new Expr.AlgorithmExpr(parsed.Root), null!, null, CancellationToken.None));

        var asyncOperations = HostOperations.Create(
            HostOperation.CreateAsync("Data", (_, _) => ValueTask.FromResult(Atom(1))));
        Assert.Throws<InvalidOperationException>(() => Evaluator.Run(
            new Expr.AlgorithmExpr(parsed.Root), asyncOperations, null, CancellationToken.None));
    }

    // ── Corpus differential: an unused configuration changes nothing ────────

    public static TheoryData<string> SpecCaseIds()
    {
        var data = new TheoryData<string>();
        foreach (var specCase in LanguageSpecCorpus.AllCases().OrderBy(static c => c.Id, StringComparer.Ordinal))
            data.Add(specCase.Id);
        return data;
    }

    private static readonly IReadOnlyDictionary<string, SpecCase> SpecById =
        LanguageSpecCorpus.AllCases().ToDictionary(static c => c.Id, StringComparer.Ordinal);

    [Theory]
    [MemberData(nameof(SpecCaseIds))]
    public void UnusedSynchronousConfiguration_ChangesNoProgramOutcome(string caseId)
    {
        var source = SpecById[caseId].Source;
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                SyncConstant("HostProbeUnusedSyncOpZz", 1,
                    new Counter())),
        };

        var baseline = KatLangEngine.Run(source);
        var configured = KatLangEngine.Run(source, options);

        Assert.Equal(baseline.GetType(), configured.GetType());
        Assert.Equal(baseline.ToDisplayString(), configured.ToDisplayString());
    }

    [Theory]
    [MemberData(nameof(SpecCaseIds))]
    public async Task UnusedAsynchronousConfiguration_ChangesNoProgramOutcome(string caseId)
    {
        // An unused ASYNC configuration routes the run through the async twin path;
        // outcomes must still be identical to the default engine run.
        var source = SpecById[caseId].Source;
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync("HostProbeUnusedAsyncOpZz", (_, _) => ValueTask.FromResult(Atom(1)))),
        };

        var baseline = KatLangEngine.Run(source);
        var configured = await KatLangEngine.RunAsync(source, options);

        Assert.Equal(baseline.GetType(), configured.GetType());
        Assert.Equal(baseline.ToDisplayString(), configured.ToDisplayString());
    }
}
