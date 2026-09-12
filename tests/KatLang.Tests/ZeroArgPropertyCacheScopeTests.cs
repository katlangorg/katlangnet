using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;

namespace KatLang.Tests;

/// <summary>
/// The zero-argument property cache's SCOPE law (F3 of the pre-release audit; Lean
/// <c>zeroArgPropertyCacheKey</c>, C# <c>ZeroArgPropertyCacheKey.FromExecution</c>):
///
/// <list type="bullet">
///   <item>An EXPORTED property is self-contained — its value depends on no input that
///   an enclosing owner's call binds — so its first successful property-style result
///   is cached per run per declaring scope. Every activation of a caller, every callback invocation,
///   every loop iteration, every open-provided or structural spelling, and every
///   explicit call of an OUTER property reuses that one value.</item>
///   <item>A LOCAL-ONLY property reads such an input through the dynamically threaded
///   environments, so it is evaluated once per binding context: two activations never
///   share an entry, and within one activation the property reuses its entry.</item>
///   <item>Explicit calls (<c>A()</c>) never consult the cache; builtins are never
///   cached; entries never cross runs; failures are never stored.</item>
/// </list>
///
/// Before this law the key carried the identities of the three environment lists,
/// which every call and callback allocates afresh, so a root constant referenced from
/// two thousand calls was evaluated two thousand times and an opened property never
/// hit at all. Every count here is an EVALUATION count observed through the cache seam
/// (or a host-operation invocation counter), never a timing.
/// </summary>
public class ZeroArgPropertyCacheScopeTests
{
    /// <summary>
    /// Run-scoped cache that records requests and ACTUAL EVALUATIONS per property name,
    /// with the async seam optionally forced to suspend genuinely.
    /// </summary>
    private sealed class CountingCache(bool suspendAsyncAccesses = false) : IAsyncZeroArgPropertyResultCache
    {
        private readonly RunScopedAsyncZeroArgPropertyResultCache _inner = new();

        public Dictionary<string, int> Requests { get; } = new(StringComparer.Ordinal);

        public Dictionary<string, int> Evaluations { get; } = new(StringComparer.Ordinal);

        public int AsyncRequests { get; private set; }

        public int RequestsOf(string name) => Requests.GetValueOrDefault(name);

        public int EvaluationsOf(string name) => Evaluations.GetValueOrDefault(name);

        public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(
            ZeroArgPropertyExecution execution,
            Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        {
            Count(Requests, execution.Binding.Name);
            return _inner.GetOrEvaluate(execution, () =>
            {
                Count(Evaluations, execution.Binding.Name);
                return evaluate();
            });
        }

        public async ValueTask<EvalResult<ZeroArgPropertyResult>> GetOrEvaluateAsync(
            ZeroArgPropertyExecution execution,
            Func<ValueTask<EvalResult<ZeroArgPropertyResult>>> evaluateAsync)
        {
            Count(Requests, execution.Binding.Name);
            AsyncRequests++;
            if (suspendAsyncAccesses)
                await Task.Yield();

            return await _inner.GetOrEvaluateAsync(execution, () =>
            {
                Count(Evaluations, execution.Binding.Name);
                return evaluateAsync();
            }).ConfigureAwait(false);
        }

        private static void Count(Dictionary<string, int> counts, string name)
            => counts[name] = counts.GetValueOrDefault(name) + 1;
    }

    private static Expr Program(string source)
        => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

    private static Property FindProperty(Algorithm root, params string[] path)
    {
        var current = root;
        Property? found = null;
        foreach (var segment in path)
        {
            found = Assert.Single(current.Properties, property => property.Name == segment);
            current = found.Value;
        }

        return found!;
    }

    private static EvalError Innermost(EvalError error)
        => error is EvalError.WithContext context ? Innermost(context.Inner) : error;

    private static IReadOnlyList<Decimal128> Atoms(EvalResult<Result> result)
    {
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        return result.Value.ToAtoms();
    }

    private static (CountingCache Cache, EvalResult<Result> Result) Run(string source, bool optimize = true)
    {
        var cache = new CountingCache();
        var result = Evaluator.Run(Program(source), cache, enableLoopOptimization: optimize);
        return (cache, result);
    }

    // ── 1. Closed/root property under repeated calls ────────────────────────

    [Fact]
    public void ExportedRootProperty_IsEvaluatedOncePerRun_AcrossDirectCalls()
    {
        var (cache, result) = Run("Big = range(1, 100).sum\nF(x) = Big + x\nF(1), F(2), F(3)");

        Assert.Equal([5051m, 5052m, 5053m], Atoms(result));
        Assert.Equal(3, cache.RequestsOf("Big"));
        Assert.Equal(1, cache.EvaluationsOf("Big"));
    }

    [Fact]
    public void ExportedRootProperty_IsEvaluatedOncePerRun_AcrossCallbackInvocations()
    {
        var (cache, result) = Run("Big = range(1, 100).sum\nF(x) = Big + x\nrange(1, 5).map(F).count");

        Assert.Equal([5m], Atoms(result));
        Assert.Equal(5, cache.RequestsOf("Big"));
        Assert.Equal(1, cache.EvaluationsOf("Big"));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ExportedRootProperty_IsEvaluatedOncePerRun_AcrossLoopIterations(bool optimize)
    {
        var (cache, result) = Run("Big = 1 + 2\nStep = n + Big\nStep.repeat(3, 0)", optimize);

        Assert.Equal([9m], Atoms(result));
        Assert.Equal(3, cache.RequestsOf("Big"));
        Assert.Equal(1, cache.EvaluationsOf("Big"));
    }

    /// <summary>
    /// The audit's pathological shape, bounded by an evaluation count rather than a
    /// clock: the expensive root constant is evaluated once for two thousand callback
    /// invocations (it was evaluated once per invocation).
    /// </summary>
    [Fact]
    public void AuditShape_ExpensiveRootConstant_IsEvaluatedOnceForTwoThousandCalls()
    {
        var (cache, result) = Run("Big = range(1, 10000).sum\nF(x) = Big + x\nrange(1, 2000).map(F).count");

        Assert.Equal([2000m], Atoms(result));
        Assert.Equal(2000, cache.RequestsOf("Big"));
        Assert.Equal(1, cache.EvaluationsOf("Big"));
    }

    // ── 2-3. Captured and nested captured properties ────────────────────────

    [Fact]
    public void CapturedLocalProperty_IsEvaluatedOncePerActivation_NeverAcrossActivations()
    {
        const string source = "Outer(x) = {\n    P = x * 10\n    P + P\n}\nOuter(2), Outer(10)";
        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            FindProperty(SourceProvenance.ParseValid(source).Root, "Outer", "P").Exposure);

        var (cache, result) = Run(source);

        Assert.Equal([40m, 200m], Atoms(result));
        Assert.Equal(4, cache.RequestsOf("P"));
        Assert.Equal(2, cache.EvaluationsOf("P"));
    }

    [Fact]
    public void NestedCapture_OfAGrandparentParameter_IsPerActivation_WhileANestedConstantIsPerRun()
    {
        var (captured, capturedResult) = Run(
            "Outer(x) = {\n    Mid = {\n        P = x + 1\n        P + P\n    }\n    Mid\n}\nOuter(1), Outer(2)");
        Assert.Equal([4m, 6m], Atoms(capturedResult));
        Assert.Equal(2, captured.EvaluationsOf("P"));

        // The same nested block with a self-contained constant: every activation of Outer
        // mints a fresh Mid record, but the declaring scope — its declaration lists and
        // their parent chain — is one and the same, so the constant has one value per run.
        var (constant, constantResult) = Run(
            "Outer(x) = {\n    Mid = {\n        K = 1 + 2\n        K + x\n    }\n    Mid\n}\nOuter(1), Outer(2)");
        Assert.Equal([4m, 5m], Atoms(constantResult));
        Assert.Equal(2, constant.RequestsOf("K"));
        Assert.Equal(1, constant.EvaluationsOf("K"));
    }

    // ── 4. Unrelated caller bindings ────────────────────────────────────────

    [Fact]
    public void UnrelatedCallerBindings_NeverSplitAnExportedEntry()
    {
        var (cache, result) = Run(
            "Big = 1 + 2\nF(x) = Big + x\nG(y, z) = Big + y * z\nH = Big\nF(1), G(2, 3), H, F(4)");

        Assert.Equal([4m, 9m, 3m, 7m], Atoms(result));
        Assert.Equal(4, cache.RequestsOf("Big"));
        Assert.Equal(1, cache.EvaluationsOf("Big"));
    }

    [Fact]
    public void ConditionalFamilyBranch_ReadsTheSameExportedEntry()
    {
        var (cache, result) = Run("F(0) = 10\nF(n) = Big + n\nBig = 1 + 2\nF(1), F(2), F(0)");

        Assert.Equal([4m, 5m, 10m], Atoms(result));
        Assert.Equal(1, cache.EvaluationsOf("Big"));
    }

    [Fact]
    public void OpenedProperty_ReusesTheRunEntry()
    {
        // The open resolves its provider afresh on every lookup (a rebuilt owner record),
        // so an owner-reference key never hit here; the declaring scope is the key now.
        var (cache, result) = Run("open Lib\nLib = { public Big = 1 + 2 }\nBig + Big");

        Assert.Equal([6m], Atoms(result));
        Assert.Equal(2, cache.RequestsOf("Big"));
        Assert.Equal(1, cache.EvaluationsOf("Big"));
    }

    [Theory]
    [InlineData("Big, Lib.Big, Big", "100\n100\n100")]
    [InlineData("Lib.Big, Big, Lib.Big", "100\n100\n100")]
    public async Task ExportedProperty_LexicalAndStructuralAccessShareTheFirstResult(string output, string expected)
    {
        var source = "open Lib\nLib = { public Big = Data() }\n" + output;
        foreach (var asynchronous in new[] { false, true })
        {
            var counter = new Counter();
            var options = HostData(counter, asynchronous);
            var result = asynchronous
                ? await KatLangEngine.RunAsync(source, options)
                : KatLangEngine.Run(source, options);
            Assert.Equal(expected.Replace("\n", Environment.NewLine), Assert.IsType<RunResult.Success>(result).ToDisplayString());
            Assert.Equal(1, counter.Count);
        }
    }

    // ── 5. Explicit-call bypass ─────────────────────────────────────────────

    [Fact]
    public void ExplicitCall_NeverConsultsTheCache()
    {
        var (heavy, heavyResult) = Run("Heavy = 1 + 2\nHeavy(), Heavy()");
        Assert.Equal([3m, 3m], Atoms(heavyResult));
        Assert.Empty(heavy.Requests);

        var (nested, nestedResult) = Run("A = Math.RandomInt(0, 10)\nC = A(), A()\nC()");
        Assert.Equal(2, Atoms(nestedResult).Count);
        Assert.Empty(nested.Requests);
    }

    [Fact]
    public void ExplicitOuterCall_KeepsTheNestedExportedEntry_AcrossCalls()
    {
        // `B()` re-evaluates B on every call; the property-style `A` inside it is an
        // exported root property with ONE value per run, so both calls observe the same
        // draw (the fresh environments of each call no longer split the entry).
        var (cache, result) = Run("A = Math.RandomInt(0, 1000000)\nB = A, A\nB(), B()");

        var atoms = Atoms(result);
        Assert.Equal(4, atoms.Count);
        Assert.All(atoms, value => Assert.Equal(atoms[0], value));
        Assert.Equal(4, cache.RequestsOf("A"));
        Assert.Equal(1, cache.EvaluationsOf("A"));
    }

    // ── 6. Nondeterministic and host-backed properties ──────────────────────

    private sealed class Counter
    {
        private int _count;
        public int Count => Volatile.Read(ref _count);
        public void Increment() => Interlocked.Increment(ref _count);
    }

    private static RunOptions HostData(Counter counter, bool asynchronous = false)
    {
        var next = 0;
        HostOperation data = asynchronous
            ? HostOperation.CreateAsync("Data", async (_, _) =>
            {
                await Task.Yield();
                counter.Increment();
                return new Result.Atom(Interlocked.Increment(ref next) * 100);
            })
            : HostOperation.Create("Data", (_, _) =>
            {
                counter.Increment();
                return new Result.Atom(Interlocked.Increment(ref next) * 100);
            });
        return new RunOptions { HostOperations = HostOperations.Create(data) };
    }

    [Fact]
    public void HostOperation_PropertyStyleAccess_InvokesTheHostOncePerRun_AcrossActivations()
    {
        var counter = new Counter();
        var options = HostData(counter);

        var result = Assert.IsType<RunResult.Success>(KatLangEngine.Run("F(x) = Data + x\nF(1), F(2), F(3)", options));
        Assert.Equal($"101{Environment.NewLine}102{Environment.NewLine}103", result.ToDisplayString());
        Assert.Equal(1, counter.Count);

        // Run isolation: a second run re-invokes the host and observes its new value.
        var second = Assert.IsType<RunResult.Success>(KatLangEngine.Run("F(x) = Data + x\nF(1), F(2)", options));
        Assert.Equal($"201{Environment.NewLine}202", second.ToDisplayString());
        Assert.Equal(2, counter.Count);
    }

    [Fact]
    public void HostOperation_ExplicitCall_InvokesTheHostOnEveryCall()
    {
        var counter = new Counter();
        var result = Assert.IsType<RunResult.Success>(KatLangEngine.Run("F(x) = Data() + x\nF(1), F(2), F(3)", HostData(counter)));

        Assert.Equal($"101{Environment.NewLine}202{Environment.NewLine}303", result.ToDisplayString());
        Assert.Equal(3, counter.Count);
    }

    [Fact]
    public async Task AsynchronousHostOperation_PropertyStyleAccess_InvokesTheHostOncePerRun_OnTheSuspendingPath()
    {
        var counter = new Counter();
        var result = Assert.IsType<RunResult.Success>(
            await KatLangEngine.RunAsync("F(x) = Data + x\nF(1), F(2), F(3)", HostData(counter, asynchronous: true)));

        Assert.Equal($"101{Environment.NewLine}102{Environment.NewLine}103", result.ToDisplayString());
        Assert.Equal(1, counter.Count);
    }

    [Fact]
    public void MathRandom_PropertyStyleAccess_SharesOneDrawAcrossActivations()
    {
        // Compare the stored values directly; adding and subtracting x can round
        // Decimal128 and make a cache test depend on the sampled numeric value.
        var (cache, result) = Run("A = Math.Random(0, 1)\nF(x) = A, x\nF(1), F(2)");

        var atoms = Atoms(result);
        Assert.Equal(4, atoms.Count);
        Assert.Equal(atoms[0], atoms[2]);
        Assert.Equal(1, cache.EvaluationsOf("A"));
    }

    [Theory]
    [InlineData("A, A", "100,100", 1)]
    [InlineData("A(), A()", "100,200", 2)]
    [InlineData("A(), A", "100,200", 2)]
    [InlineData("A, A()", "100,200", 2)]
    [InlineData("A, A(), A", "100,200,100", 2)]
    [InlineData("B", "100,100", 1)]
    [InlineData("B()", "100,100", 1)]
    [InlineData("B(), B()", "100,100,100,100", 1)]
    [InlineData("B, B(), B", "100,100,100,100,100,100", 1)]
    [InlineData("if(1, A, 0), A", "100,200", 2)]
    [InlineData("if(1, (A), 0), A", "100,100", 1)]
    public Task ExplicitCallMatrix_ExactHostCountsAcrossExecutionPaths(string output, string expected, int calls)
        => AssertHostCounterPaths("A = Data()\nB = A, A\n" + output, expected, calls);

    [Fact]
    public Task FailedArgumentProbe_PreservesSuccessfulNestedPropertyResults()
        => AssertHostCounterPaths("A = Data()\nBad = A, 1 / 0\nIgnore(f) = 0\nIgnore(Bad), A", "0,100", 1);

    [Fact]
    public Task FailedReentrantParent_PreservesTheSuccessfulStoreOfTheSameProperty()
        => AssertHostCounterPaths(
            "A = if(Data() < 200, A + 1 / 0, 10)\nIgnore(f) = 0\nIgnore(A), A", "0,10", 2);

    [Theory]
    [InlineData(false, "105,105,250,250", 2)]
    [InlineData(true, "310,800", 4)]
    public Task RemovedOpenProvider_FallbackHostValuesRemainActivationSensitive(bool loop, string expected, int calls)
    {
        var body = loop
            ? "Step(n) = {\n open Make\n P = Box.f\n n + P\n}\nStep.repeat(2, 0)"
            : "open Make\nP = Box.f\nP, P";
        return AssertHostCounterPaths($$"""
            open Fallback
            Make(x) = {
                public Box = { f = 42
                    x }
                0
            }
            Fallback = { public Box = 5 }
            Inc(x) = Data() + x
            Times(x) = Data() + x * 10
            Outer(f) = {
                {{body}}
            }
            Outer(Inc), Outer(Times)
            """, expected, calls);
    }

    [Fact]
    public async Task DeferredBranch_RemovedOpenProvider_UpdatesTheEnclosingPropertyCaptureSummary()
    {
        var counter = new Counter();
        var downloads = 0;
        var options = new RunOptions
        {
            HostOperations = HostData(counter, asynchronous: true).HostOperations,
            AllowedHosts = ["cache.test"],
            DownloadCode = async (_, _) =>
            {
                downloads++;
                await Task.Yield();
                return "public Unused = 0";
            },
        };
        const string source = """
            open Fallback
            Make(x) = {
                public Box = { f = 42
                    x }
                0
            }
            Fallback = { public Box = 5 }
            Inc(x) = Data() + x
            Times(x) = Data() + x * 10
            Outer(f) = {
                Read(0) = 0
                Read(n) = {
                    open Make, 'https://cache.test/lib'
                    P = Box.f
                    (P, P)
                }
                Cached = Read(1)
                Read(0), Cached
            }
            Outer(Inc), Outer(Times)
            """;
        var parsed = await SourceProvenance.ParseValidAsync(source, options);
        Assert.Equal(0, downloads);
        var outer = parsed.Root.Properties.Single(p => p.Name == "Outer").Value;
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters,
            outer.Properties.Single(p => p.Name == "Cached").Exposure);
        var cache = new CountingCache();
        var result = await Evaluator.RunAsync(new Expr.AlgorithmExpr(parsed.Root), cache,
            hostOperations: options.HostOperations);
        Assert.Equal([0m, 105m, 105m, 0m, 250m, 250m], Atoms(result));
        Assert.Equal(2, counter.Count);
        Assert.Equal(2, cache.EvaluationsOf("P"));
        Assert.Equal(1, downloads);
    }

    [Fact]
    public async Task ReentrantPropertyRead_KeepsTheFirstCompletedCacheEntry()
    {
        // The inner read completes with 10 while the outer read is still computing
        // 11. Finishing that pending read must not replace the first stored result.
        const string source = "A = if(Data() < 200, A + 1, 10)\nA, A";
        await AssertHostCounterPaths(source, "11,10", 2);

        // The synchronous cache additionally reports only one successful store.
        var counter = new Counter();
        var options = HostData(counter);
        var expr = new Expr.AlgorithmExpr((await SourceProvenance.ParseValidAsync(source, options)).Root);
        var cache = new RunScopedZeroArgPropertyResultCache();
        var observed = Evaluator.RunCountedObserved(expr,
            zeroArgPropertyResultCache: cache, hostOperations: options.HostOperations);
        Assert.False(observed.Result.IsError);
        Assert.Equal([11m, 10m], observed.Result.Value.Value.ToAtoms());
        Assert.Equal(2, counter.Count);
        Assert.Equal(1, cache.GetSnapshot().Stores);
    }

    [Theory]
    [InlineData("Outer(x) = {\n P = Data() + x\n P, P\n}\nOuter(1), Outer(1)", "101,101,201,201", 2)]
    [InlineData("Outer(x) = {\n Mid = {\n  P = Data() + x\n  P, P\n }\n Mid\n}\nOuter(1), Outer(2)", "101,101,202,202", 2)]
    [InlineData("F(0) = 0\nF(x) = {\n P = Data() + x\n P + P\n}\nF(1), F(1)", "202,402", 2)]
    [InlineData("Outer(*items) = {\n P = Data() + items.sum\n P + P\n}\nOuter(1, 2), Outer(1, 2)", "206,406", 2)]
    [InlineData("Outer(s) = {\n F(x) = {\n  P = Data() + s + x\n  P + P\n }\n [1, 1].map(F)*\n}\nOuter(1)", "204,404", 2)]
    [InlineData("F(n) = {\n P = Data() + n\n if(n == 0, P + P, P + P + F(n - 1))\n}\nF(2)", "1206", 3)]
    [InlineData("Step(n) = {\n P = Data() + n\n P + P - n\n}\nStep.repeat(3, 0)", "1200", 3)]
    [InlineData("Outer(x) = {\n P = Data() + x\n Q = P + P\n Q(), Q()\n}\nOuter(1)", "202,402", 2)]
    [InlineData("Outer(x) = {\n P = Data() + x\n Q = P + P\n P, Q, P\n}\nOuter(1)", "101,202,101", 1)]
    [InlineData("Outer(x) = {\n A = {\n P = Data() + x\n P\n }\n if(1, A, 0), if(1, A, 0)\n}\nOuter(1)", "101,101", 1)]
    public Task LocalOnlyHostValues_RespectEveryBindingBoundary(string source, string expected, int calls)
        => AssertHostCounterPaths(source, expected, calls);

    [Fact]
    public Task IdenticalBodies_InDistinctDeclarations_HaveDistinctResults()
        => AssertHostCounterPaths(
            "F(x) = {\n P = Data()\n P + x\n}\nG(x) = {\n P = Data()\n P + x\n}\nF(1), G(1), F(1), G(1)",
            "101,201,101,201", 2);

    private static async Task AssertHostCounterPaths(string source, string expected, int calls)
    {
        var expectedAtoms = expected.Split(',').Select(value => (Decimal128)int.Parse(value)).ToArray();
        // Plain evaluation projects the canonical counted evaluator. Exercise both
        // strategies, then the forced async counted twin with sync and suspending hosts.
        for (var mode = 0; mode < 4; mode++)
        {
            var counter = new Counter();
            var options = HostData(counter, asynchronous: mode == 3);
            var expr = new Expr.AlgorithmExpr((await SourceProvenance.ParseValidAsync(source, options)).Root);
            var cache = new CountingCache(suspendAsyncAccesses: mode == 2);
            var observed = mode < 2
                ? Evaluator.RunCountedObserved(expr, enableOptimizations: mode == 1,
                    zeroArgPropertyResultCache: cache, hostOperations: options.HostOperations)
                : await Evaluator.RunCountedObservedAsync(expr,
                    zeroArgPropertyResultCache: cache, hostOperations: options.HostOperations);
            Assert.False(observed.Result.IsError, $"mode {mode}: {observed.Result}");
            Assert.Equal(expectedAtoms, observed.Result.Value.Value.ToHostAtoms());
            Assert.Equal(calls, counter.Count);
        }
    }

    // ── 7. Builtins ─────────────────────────────────────────────────────────

    [Fact]
    public void Builtins_AreNeverCached_WhilePreludeConstantsAreExported()
    {
        // A bare builtin is an arity error: the access reaches the cache seam like any
        // zero-parameter prelude property, but a failure is never stored, so nothing is
        // ever cached for it.
        var bare = new RunScopedZeroArgPropertyResultCache();
        var bareResult = Evaluator.Run(Program("F(x) = range + x\nF(1)"), bare);
        Assert.True(bareResult.IsError);
        Assert.IsType<EvalError.ArityMismatch>(Innermost(bareResult.Error));
        var bareSnapshot = bare.GetSnapshot();
        Assert.Equal(1, bareSnapshot.Misses);
        Assert.Equal(0, bareSnapshot.Stores);
        Assert.Equal(0, bareSnapshot.MaxCacheSize);

        // A zero-parameter Math member is an exported prelude property: one evaluation
        // serves every activation.
        var (constant, constantResult) = Run("F(x) = Math.Pi + x\nF(1) - 1 == F(2) - 2");
        Assert.Equal([1m], Atoms(constantResult));
        Assert.Equal(1, constant.EvaluationsOf("Pi"));
    }

    // ── 8. Execution parity ─────────────────────────────────────────────────

    public static TheoryData<string> ParityPrograms => new()
    {
        "Big = range(1, 100).sum\nF(x) = Big + x\nF(1), F(2), F(3)",
        "Big = range(1, 100).sum\nF(x) = Big + x\nrange(1, 5).map(F)",
        "Outer(x) = {\n    P = x * 10\n    P + P\n}\nOuter(2), Outer(10)",
        "Outer(x) = {\n    Mid = {\n        K = 1 + 2\n        K + x\n    }\n    Mid\n}\nOuter(1), Outer(2)",
        "open Lib\nLib = { public Big = 1 + 2 }\nBig + Big",
        "A = 41 + 1\nB = A, A\nB(), B()",
        "Big = 1 + 2\nStep = n + Big\nStep.repeat(3, 0)",
        "Apply(f) = {\n    Data = [1, 2, 3]\n    Big = Data.f\n    Big\n}\nSum(v) = v.sum\nCnt(v) = v.count\nApply(Sum), Apply(Cnt)",
    };

    [Theory]
    [MemberData(nameof(ParityPrograms))]
    public async Task PlainCountedAsyncAndSuspendingExecutions_AgreeOnResultsAndEvaluationCounts(string source)
    {
        var expr = Program(source);

        var plainCache = new CountingCache();
        var plain = Evaluator.Run(expr, plainCache, enableLoopOptimization: false);

        var countedCache = new CountingCache();
        var counted = Evaluator.RunCountedObserved(expr, enableOptimizations: false, zeroArgPropertyResultCache: countedCache);

        var asyncCache = new CountingCache();
        var asynchronous = await Evaluator.RunAsync(expr, asyncCache);

        var suspendingCache = new CountingCache(suspendAsyncAccesses: true);
        var suspending = await Evaluator.RunAsync(expr, suspendingCache);

        var optimizedCache = new CountingCache();
        var optimized = Evaluator.Run(expr, optimizedCache, enableLoopOptimization: true);

        var expected = Atoms(plain);
        Assert.False(counted.Result.IsError);
        Assert.Equal(expected, counted.Result.Value.Value.ToAtoms());
        Assert.Equal(expected, Atoms(asynchronous));
        Assert.Equal(expected, Atoms(suspending));
        Assert.Equal(expected, Atoms(optimized));

        Assert.NotEmpty(plainCache.Evaluations);
        foreach (var other in new[] { countedCache, asyncCache, suspendingCache, optimizedCache })
        {
            Assert.Equal(plainCache.Requests, other.Requests);
            Assert.Equal(plainCache.Evaluations, other.Evaluations);
        }

        // The async runs went through the async seam (the twin family), not the inline
        // synchronous pipeline.
        Assert.Equal(asyncCache.Requests.Values.Sum(), asyncCache.AsyncRequests);
        Assert.Equal(suspendingCache.Requests.Values.Sum(), suspendingCache.AsyncRequests);
    }

    [Fact]
    public void OptimizedLoop_ExportedStepLocalTemp_SharesTheRunEntryWithGenericExecution()
    {
        // The step-local string temp is exported: one materialization per run on both
        // strategies (it was one per iteration plus one per temp call — 600 chars for
        // twenty iterations — because each iteration and each call ran in fresh
        // environments). `n` still walks 0, 1, 3, 7, ... (2^20 - 1).
        const string source =
            "Step = {\n    T = 'xxxxxxxxxx'\n    A = x + (T == T)\n    (T == T) + A + A - 2 + (T == T) - 1\n}\nStep.repeat(20, 0)";
        var expr = Program(source);

        var genericCache = new CountingCache();
        var generic = Evaluator.RunCountedObserved(expr, enableOptimizations: false, zeroArgPropertyResultCache: genericCache);
        var optimizedCache = new CountingCache();
        var diagnostics = new LoopOptimizationDiagnostics();
        var optimized = Evaluator.RunCountedObserved(
            expr, enableOptimizations: true, zeroArgPropertyResultCache: optimizedCache, loopDiagnostics: diagnostics);

        Assert.False(generic.Result.IsError);
        Assert.False(optimized.Result.IsError);
        Assert.Equal([1_048_575m], generic.Result.Value.Value.ToAtoms());
        Assert.Equal([1_048_575m], optimized.Result.Value.Value.ToAtoms());
        Assert.Equal(10, generic.Budget.MaterializedStringChars);
        Assert.Equal(10, optimized.Budget.MaterializedStringChars);
        Assert.Equal(generic.Budget.PeakDepth, optimized.Budget.PeakDepth);
        Assert.Equal(1, genericCache.EvaluationsOf("T"));
        Assert.Equal(1, optimizedCache.EvaluationsOf("T"));
        Assert.Equal(genericCache.RequestsOf("T"), optimizedCache.RequestsOf("T"));
        Assert.Equal(1, diagnostics.GetSnapshot().OptimizedLoopHits);
        Assert.Equal(0, diagnostics.GetSnapshot().OptimizedLoopFallbacks);
    }

    // ── Soundness of the exported classification the law relies on ─────────

    [Fact]
    public void ParameterNamingDotFallback_MakesThePropertyLocalOnly_SoActivationsNeverShareIt()
    {
        // `Data` has no member `f`, so the runtime takes the fallback `f(Data)` and Big's
        // value depends on Apply's parameter: local-only, one evaluation per activation.
        // (Exposure once left this property exported; a run-wide entry would then have
        // served Sum's result to the Cnt activation.)
        const string source =
            "Apply(f) = {\n    Data = [1, 2, 3]\n    Big = Data.f\n    Big\n}\nSum(v) = v.sum\nCnt(v) = v.count\nApply(Sum), Apply(Cnt)";
        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            FindProperty(SourceProvenance.ParseValid(source).Root, "Apply", "Big").Exposure);

        var (cache, result) = Run(source);

        Assert.Equal([6m, 3m], Atoms(result));
        Assert.Equal(2, cache.EvaluationsOf("Big"));
    }

    [Fact]
    public void StructuralNavigationIntoAParameterizedOwner_IsRefusedForTheLocalOnlyMember()
    {
        // Through the earlier exported classification this navigation READ the dynamic
        // binding of G's `f` (6, then 3 for a Cnt call): a self-contained value that was
        // not self-contained. The member is local-only now, so the edge is refused.
        const string source =
            "Outer(f) = {\n    Lib = {\n        Data = [1, 2, 3]\n        public Big = Data.f\n    }\n    Lib.Big\n}\nG(f) = Outer.Lib.Big\nSum(v) = v.sum\nG(Sum)";

        var result = Evaluator.Run(Program(source));

        Assert.True(result.IsError);
        var localOnly = Assert.IsType<EvalError.LocalOnlyProperty>(Innermost(result.Error));
        Assert.Equal("Big", localOnly.PropertyName);
    }

    [Fact]
    public void StructuralWinner_HidingAParameterName_StaysExportedAndPerRun()
    {
        // The receiver DECLARES `m`, so the Param fallback is never selected: P is
        // exported and one entry serves both activations, correctly.
        var (cache, result) = Run(
            "M = { public m = 1 + 2 }\nApply(m) = {\n    P = M.m\n    P\n}\nApply(7), Apply(8)");

        Assert.Equal([3m, 3m], Atoms(result));
        Assert.Equal(1, cache.EvaluationsOf("P"));
    }

    // ── Safety ──────────────────────────────────────────────────────────────

    [Fact]
    public void SharedCacheInstance_NeverServesAnExportedEntryAcrossRuns()
    {
        var cache = new CountingCache();
        var expr = Program("Big = 1 + 2\nF(x) = Big + x\nF(1)");

        Assert.Equal([4m], Atoms(Evaluator.Run(expr, cache)));
        Assert.Equal([4m], Atoms(Evaluator.Run(expr, cache)));

        Assert.Equal(2, cache.EvaluationsOf("Big"));
    }

    [Fact]
    public void FailedEvaluation_IsNeverStored()
    {
        var cache = new RunScopedZeroArgPropertyResultCache();
        var result = Evaluator.Run(Program("Big = 1 / 0\nF(x) = Big + x\nF(1)"), cache);

        Assert.True(result.IsError);
        Assert.IsType<EvalError.DivByZero>(Innermost(result.Error));
        var snapshot = cache.GetSnapshot();
        Assert.Equal(1, snapshot.Misses);
        Assert.Equal(0, snapshot.Stores);
        Assert.Equal(0, snapshot.MaxCacheSize);
    }

    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    [InlineData(2)]
    public async Task SuspendedFailure_CanRetryTheSameKey_AndOnlySuccessIsReused(int failure)
    {
        using var cancellation = new CancellationTokenSource();
        cancellation.Cancel();
        var exception = new InvalidOperationException("host failure");
        var owner = SourceProvenance.ParseValid("A = 1\nA").Root;
        var execution = new ZeroArgPropertyExecution(owner, owner.Properties[0],
            ZeroArgPropertyAccessKind.CountedLexical, new object(), new object(), new object(), new object());
        var cache = new RunScopedAsyncZeroArgPropertyResultCache();
        var attempts = 0;
        async ValueTask<EvalResult<ZeroArgPropertyResult>> Fail()
        {
            attempts++;
            await Task.Yield();
            if (failure == 1) throw exception;
            if (failure == 2) throw new OperationCanceledException(cancellation.Token);
            return new EvalError.DivByZero();
        }

        if (failure == 0)
            Assert.IsType<EvalError.DivByZero>((await cache.GetOrEvaluateAsync(execution, Fail)).Error);
        else if (failure == 1)
            Assert.Same(exception, await Assert.ThrowsAsync<InvalidOperationException>(
                async () => await cache.GetOrEvaluateAsync(execution, Fail)));
        else
            Assert.Equal(cancellation.Token, (await Assert.ThrowsAnyAsync<OperationCanceledException>(
                async () => await cache.GetOrEvaluateAsync(execution, Fail))).CancellationToken);

        EvalResult<ZeroArgPropertyResult> Succeed()
        {
            attempts++;
            return EvalResult<ZeroArgPropertyResult>.Ok(new ZeroArgPropertyResult(new Result.Atom(7), 1));
        }
        Assert.False(cache.GetOrEvaluate(execution, Succeed).IsError);
        Assert.False((await cache.GetOrEvaluateAsync(execution, Fail)).IsError);
        Assert.Equal(2, attempts);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task LoadedDeclarations_KeepCacheScope_ThroughEagerAndDeferredElaboration(bool deferred)
    {
        var counter = new Counter();
        var downloads = 0;
        var options = new RunOptions
        {
            HostOperations = HostData(counter, asynchronous: true).HostOperations,
            AllowedHosts = ["cache.test"],
            DownloadCode = async (_, _) =>
            {
                downloads++;
                await Task.Yield();
                return "public Big = Data()\nPrivate = Data()\npublic Read = Private";
            },
        };
        var source = deferred
            ? "F(0) = 0\nF(n) = {\n open 'https://cache.test/lib'\n P = Big + n\n P + P\n}\nF(0), F(1), F(2)"
            : "open Lib\nLib = load('https://cache.test/lib')\nF(x) = Big + x\nBig, Lib.Big, F(1), Lib.Private, Lib.Read";
        var parsed = await SourceProvenance.ParseValidAsync(source, options);
        Assert.Equal(deferred ? 0 : 1, downloads);
        var cache = new CountingCache();
        var result = await Evaluator.RunAsync(new Expr.AlgorithmExpr(parsed.Root), cache,
            hostOperations: options.HostOperations);
        Assert.Equal(deferred ? new Decimal128[] { 0, 202, 204 } : [100, 100, 101, 200, 200], Atoms(result));
        Assert.Equal(1, downloads);
        Assert.Equal(deferred ? 1 : 2, counter.Count);
        Assert.Equal(1, cache.EvaluationsOf("Big"));
        if (deferred) Assert.Equal(2, cache.EvaluationsOf("P"));
    }

    [Fact]
    public void HostBuiltTree_IsCachedByTheExposureItDeclares()
    {
        // The evaluator trusts a host-built tree's exposure exactly as it does for open
        // and structural access: a parameter-reading property left at the default
        // Exported gets one value per run, while the honest classification gets one per
        // activation. Pipeline-elaborated trees always carry the honest classification.
        static Expr Tree(PropertyExposure exposure)
        {
            var outer = new Algorithm.User(
                Parent: null,
                Parameters: [new ParameterDeclaration("x")],
                Opens: [],
                Properties:
                [
                    new Property(
                        "P",
                        new Algorithm.User(null, [], [], [], [new Expr.Param("x")]),
                        Exposure: exposure),
                ],
                Output: [new Expr.Resolve("P")]);
            var root = new Algorithm.User(
                Parent: null,
                Parameters: [],
                Opens: [],
                Properties: [new Property("Outer", outer)],
                Output:
                [
                    new Expr.Call(new Expr.Resolve("Outer"), new OutputBundle([new Expr.Num(2m)])),
                    new Expr.Call(new Expr.Resolve("Outer"), new OutputBundle([new Expr.Num(10m)])),
                ]);
            return new Expr.AlgorithmExpr(root);
        }

        Assert.Equal([2m, 2m], Atoms(Evaluator.Run(Tree(PropertyExposure.Exported), new CountingCache())));
        Assert.Equal([2m, 10m], Atoms(Evaluator.Run(Tree(PropertyExposure.LocalOnlyCapturedAncestorParameters), new CountingCache())));
    }

    [Fact]
    public void CacheKey_ExportedBinding_IgnoresEnvironmentIdentities_ButNotTheDeclaringScopeOrRun()
    {
        var comparer = ZeroArgPropertyCacheKeyComparer.Instance;
        var declaringScope = new Algorithm.User(
            null, [], [], [new Property("Value", new Algorithm.User(null, [], [], [], [new Expr.Num(1m)]))], [new Expr.Num(0m)]);
        var binding = declaringScope.Properties[0];
        var run = new object();

        ZeroArgPropertyExecution Execution(Algorithm owner, object valueEnv, object algEnv, object countedEnv, object? runIdentity = null)
            => new(owner, binding, ZeroArgPropertyAccessKind.CountedLexical, valueEnv, algEnv, countedEnv, runIdentity ?? run);

        var baseline = ZeroArgPropertyCacheKey.FromExecution(Execution(declaringScope, new object(), new object(), new object()));

        // Fresh environments and a rebuilt owner record over the same declaring scope: HIT.
        var otherEnvironments = ZeroArgPropertyCacheKey.FromExecution(
            Execution(declaringScope with { }, new object(), new object(), new object()));
        Assert.True(comparer.Equals(baseline, otherEnvironments));
        Assert.Equal(comparer.GetHashCode(baseline), comparer.GetHashCode(otherEnvironments));

        // A different declaring scope (its own declaration list) is a different key even
        // for the same shared binding object; so is a different run.
        var otherScope = new Algorithm.User(
            null, [], [], [binding, new Property("Extra", new Algorithm.User(null, [], [], [], [new Expr.Num(2m)]))], [new Expr.Num(0m)]);
        Assert.False(comparer.Equals(baseline, ZeroArgPropertyCacheKey.FromExecution(Execution(otherScope, new object(), new object(), new object()))));
        Assert.False(comparer.Equals(baseline, ZeroArgPropertyCacheKey.FromExecution(Execution(declaringScope, new object(), new object(), new object(), new object()))));

        // A local-only binding keeps its declaring scope and every environment identity.
        var localOnly = new Property(
            "Local",
            new Algorithm.User(null, [], [], [], [new Expr.Param("x")]),
            Exposure: PropertyExposure.LocalOnlyCapturedAncestorParameters);
        var localScope = new Algorithm.User(null, [new ParameterDeclaration("x")], [], [localOnly], [new Expr.Resolve("Local")]);
        var valueEnv = new object();
        var algEnv = new object();
        var countedEnv = new object();
        ZeroArgPropertyCacheKey LocalKey(Algorithm owner, object v, object a, object c)
            => ZeroArgPropertyCacheKey.FromExecution(new(owner, localOnly, ZeroArgPropertyAccessKind.CountedLexical, v, a, c, run));

        var localBaseline = LocalKey(localScope, valueEnv, algEnv, countedEnv);
        Assert.True(comparer.Equals(localBaseline, LocalKey(localScope, valueEnv, algEnv, countedEnv)));
        Assert.False(comparer.Equals(localBaseline, LocalKey(localScope, new object(), algEnv, countedEnv)));
        Assert.False(comparer.Equals(localBaseline, LocalKey(localScope, valueEnv, new object(), countedEnv)));
        Assert.False(comparer.Equals(localBaseline, LocalKey(localScope, valueEnv, algEnv, new object())));
        Assert.True(comparer.Equals(localBaseline, LocalKey(localScope with { }, valueEnv, algEnv, countedEnv)));
    }
}
