using System.Numerics;
using System.Text;

namespace KatLang.Tests;

/// <summary>
/// RECURSIVE INFERENCE AND THE OPERATION'S LIFECYCLE (owner direction 2026-11-05). Origins live in capture records that
/// reach the tree only through the operation's own publication, so these tests look at the boundary from outside: real
/// deferred units on the async route, shared contexts, later units, same-tree retries, ledger exhaustion and cancellation
/// inside the rounds and inside the seal. Entry-only async coverage is labelled; a test that needs the async twin uses a
/// genuinely suspending download.
/// </summary>
public sealed class RecursiveInferenceLifecycleTests
{
    private const string Url = "https://modules.example/";

    private static RunOptions Serve(IReadOnlyDictionary<string, string> modules, CancellationToken evaluation = default, SourceProcessingLimits? limits = null)
        => new()
        {
            AllowedHosts = ["modules.example"],
            DownloadCode = async (url, _) =>
            {
                // Suspends this delegate, which promises nothing about its caller: one that looks only after the pool has
                // finished the delegate carries on synchronously. A test that needs the two apart gates the download itself.
                await Task.Yield();
                return modules[url];
            },
            EvaluationCancellationToken = evaluation,
            SourceProcessingLimits = limits,
        };

    private static async Task<string> Value(string source, IReadOnlyDictionary<string, string> modules)
    {
        var result = await KatLangEngine.RunAsync(source, Serve(modules));
        return SixRouteAgreement.Neutral(Assert.IsType<RunResult.Success>(result).Value);
    }

    private const string Deferred = "G(0) = 0\nG(a) = {\n    M = load('" + Url + "u.kat')\n    M.H(a)\n}\nG(10)";

    // ── deferred units ──────────────────────────────────────────────────────────────────────────

    [Fact]
    public async Task ADeferredUnit_CompletesItsOwnCycle()
    {
        Assert.Equal("13", await Value(Deferred, new Dictionary<string, string> { [Url + "u.kat"] = "H = if(tick() > 3, x, H + 1)\n0" }));
    }

    /// <summary>Each member lists its own names first in a deferred unit too: the positional call proves the order.</summary>
    [Fact]
    public async Task ADeferredUnit_KeepsWrittenReferenceOrder()
    {
        var modules = new Dictionary<string, string> { [Url + "u.kat"] = "A = if(tick() > 3, x * 100 + y * 10 + z, B + 0)\nB = A + z - z\n0" };
        var value = await Value("G(0) = 0\nG(a) = {\n    M = load('" + Url + "u.kat')\n    M.B(a, 2, 3)\n}\nG(1)", modules);
        Assert.Equal("231", value);
    }

    /// <summary>A later unit with its own cycle reads an earlier unit's sealed facts as fixed.</summary>
    [Fact]
    public async Task ALaterUnitCycle_ReadsAnEarlierUnitsFinalFacts()
    {
        var modules = new Dictionary<string, string>
        {
            [Url + "a.kat"] = "H(x) = x\n0",
            [Url + "b.kat"] = "M = load('" + Url + "a.kat')\nV = if(tick() > 5, M.H, V + 1)\n0",
        };
        Assert.Equal("S[15, 1]", await Value("M = load('" + Url + "a.kat')\nG(0) = {\n    N = load('" + Url + "b.kat')\n    N.V(10)\n}\nG(n) = n\nG(0), M.H(1)", modules));
    }

    /// <summary>A later unit reads a signature an earlier unit completed.</summary>
    [Fact]
    public async Task ALaterUnit_ReadsACompletedCycle()
    {
        var modules = new Dictionary<string, string>
        {
            [Url + "a.kat"] = "P(p) = p\nH = if(tick() > 3, P, K + 0)\nK = H + 0\n0",
            [Url + "b.kat"] = "M = load('" + Url + "a.kat')\nV = M.K + 1\n0",
        };
        Assert.Equal("8", await Value("M = load('" + Url + "a.kat')\nG(0) = {\n    N = load('" + Url + "b.kat')\n    N.V(7)\n}\nG(n) = n\nG(0)", modules));
    }

    /// <summary>
    /// A later cycle over an earlier cycle origin holds that origin's SOURCES, never the earlier descriptor as one root, and
    /// inherits the earlier origin unchanged through a determined chain. The report is the real consumer of both.
    /// </summary>
    [Fact]
    public async Task ALaterCycle_FlattensAnEarlierOrigin()
    {
        var modules = new Dictionary<string, string>
        {
            [Url + "a.kat"] = "P(p) = p\nQ(p) = p\nH = K + P\nK = H + Q\n0",
            [Url + "b.kat"] = "M = load('" + Url + "a.kat')\npublic V = V + M.K + 0\npublic W = M.K + 0\n0",
        };

        async Task<string> Report(string member)
        {
            var main = "M = load('" + Url + "a.kat')\nG(0) = {\n    N = load('" + Url + "b.kat')\n    N." + member + "(1, 2)\n}\nG(n) = n\nG(0)";
            var failure = Assert.IsType<RunResult.EvalFailure>(await KatLangEngine.RunAsync(main, Serve(modules)));
            return failure.Errors[0].Message;
        }

        Assert.Contains("Parameter 'p' is inferred around the recursive group 'V'; it comes from 'P', 'Q'.", await Report("V"), StringComparison.Ordinal);
        Assert.Contains("Parameter 'p' is inferred around the recursive group 'H', 'K'; it comes from 'P', 'Q'.", await Report("W"), StringComparison.Ordinal);
    }

    // ── same-tree retries and failure ───────────────────────────────────────────────────────────

    private static string Ring(int members)
        => string.Join("\n", Enumerable.Range(0, members).Select(i => $"D{i} = D{(i + 1) % members} + x{i}")) + "\nF = if(tick() > 3, x, F + 1)\n0";

    private static Task<EvalResult<IReadOnlyList<Decimal128>>> RunFlat(Algorithm root, CancellationToken token = default)
        => Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(root), limits: null, token);

    /// <summary>
    /// A module with a long ring, so rounds and sealing both run for a while inside the deferred unit. The producer holds
    /// until its consumer has left, so the two must be apart, and the download is what keeps them apart: a download that is
    /// finished when its caller looks counts as completing synchronously, which by the run contract keeps the materialization
    /// on the consumer's own stack, where the producer would wait for itself. It therefore stays suspended until the consumer
    /// has parked.
    /// </summary>
    private static async Task CancelInDeferredUnitAt(long step)
    {
        var modules = new Dictionary<string, string> { [Url + "u.kat"] = Ring(16) };
        var main = "G(0) = 0\nG(a) = {\n    M = load('" + Url + "u.kat')\n    M.F(a)\n}\nG(10)";
        // The consumer's own thread sets this: run inline there, the unit's compilation would be on the consumer's stack again.
        var consumerParked = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var downloads = 0;
        var options = new RunOptions
        {
            AllowedHosts = ["modules.example"],
            DownloadCode = async (url, _) =>
            {
                downloads++;
                await consumerParked.Task.ConfigureAwait(false);
                return modules[url];
            },
        };
        var parsed = await Parser.ParseAsync(main, options);
        Assert.False(parsed.HasErrors);
        var family = Assert.IsType<Algorithm.Conditional>(Assert.Single(parsed.Root.Properties, static property => property.Name == "G").Value);
        var region = Assert.Single(family.Branches, static branch => branch.Body.DeferredRegion is not null).Body.DeferredRegion!;
        using var cancellation = new CancellationTokenSource();
        using var consumerLeft = new ManualResetEventSlim();
        var reached = 0L;
        region.Loader.TraversalObservations = new FrontEndTraversalObservations
        {
            OnSignatureSelectionStep = count =>
            {
                reached = count;
                if (count != step)
                    return;
                cancellation.Cancel();
                // The producer holds here until its only consumer has left, which cancels the producer's own token: its next
                // charge then observes that, at this exact step.
                Assert.True(consumerLeft.Wait(TimeSpan.FromSeconds(30)), "The consumer did not leave.");
            },
        };

        // The consumer runs apart from the test's own scheduler: its departure must not wait for a free test thread.
        var consumer = Task.Run(async () =>
        {
            try
            {
                // An evaluation returns to its caller only by suspending, and it suspends nowhere before this download, so
                // from here on the consumer is parked on the materialization and the producer cannot be running on it.
                var evaluation = RunFlat(parsed.Root, cancellation.Token);
                Assert.Equal(1, downloads);
                consumerParked.SetResult();
                await evaluation.ConfigureAwait(false);
            }
            finally
            {
                consumerLeft.Set();
            }
        });
        await Assert.ThrowsAnyAsync<OperationCanceledException>(() => consumer);
        Assert.True(reached >= step, $"Cancelled at step {reached}.");

        // A retry starts a second attempt exactly because the first published nothing; a published unit would need none.
        region.Loader.TraversalObservations = null;
        var retry = await RunFlat(parsed.Root);
        Assert.False(retry.IsError, retry.IsError ? retry.Error.ToString() : "");
        Assert.Equal([(Decimal128)13], retry.Value);
        Assert.True(region.IsMaterialized);
        Assert.Equal(2, region.MaterializationAttempts);
    }

    /// <summary>
    /// Cancellation inside a deferred unit's rounds and inside its origin preparation, at exact steps: nothing is published,
    /// the same tree is whole, and an unchanged retry completes it.
    /// </summary>
    [Theory]
    [InlineData(40)]
    [InlineData(1500)]
    public Task CancellationInsideADeferredCompletion_LeavesTheSameTreeUsable(long step) => CancelInDeferredUnitAt(step);

    /// <summary>
    /// Every step of a real selection, rounds, origin preparation and the final recomposition check, is a cancellation
    /// point over one retained input: the run is cancelled there, and the SAME input then resolves in full. Past the last
    /// charge the selection is over, so a token cancelled there belongs to the enclosing operation: the run either stops or
    /// returns the whole answer, origin included, never a part of it.
    /// </summary>
    [Fact]
    public void EveryStepOfASelection_IsACancellationPoint_AndTheSameInputRetries()
    {
        const string Source = "P(p) = p\nQ(p) = p\nA = B + P + 0\nB = A + Q + 0\nC = A + 0\n0";
        var root = ParameterDetector.DetectPrevalidated(SourceProvenance.ParseSyntaxValidRoot(Source)).Root;
        static Algorithm Resolve(Algorithm input, CancellationToken token, FrontEndTraversalObservations? observations)
            => ImplicitArgumentResolver.ResolveNameResolvedPrevalidated(input, observations, cancellationToken: token);
        static ParameterCycleOrigin OriginOf(Algorithm resolved, string name)
            => ParameterPattern.FlattenCaptures(resolved.Properties.Single(property => property.Name == name).Value.ParameterPatterns)
                .Single().InferredProvenance!.CycleOrigin!;

        var count = new FrontEndTraversalObservations();
        _ = Resolve(root, default, count);
        var steps = count.SignatureSelectionSteps;
        Assert.True(steps > 30, $"{steps} steps");

        var finished = new List<long>();
        for (var step = 1L; step <= steps; step++)
        {
            using var cancellation = new CancellationTokenSource();
            var at = step;
            var observer = new FrontEndTraversalObservations { OnSignatureSelectionStep = position => { if (position == at) cancellation.Cancel(); } };
            try
            {
                var whole = Resolve(root, cancellation.Token, observer);
                finished.Add(step);
                Assert.Equal(2, OriginOf(whole, "A").Roots.Count);
                Assert.Same(OriginOf(whole, "A"), OriginOf(whole, "C"));
            }
            catch (OperationCanceledException)
            {
            }

            Assert.Empty(root.Properties.Single(static property => property.Name == "A").Value.Params);
            Assert.Equal(2, OriginOf(Resolve(root, default, null), "A").Roots.Count);
        }

        // Only the last charge of the selection can precede the end of it.
        Assert.True(finished.Count <= 2 && finished.All(step => step > steps - 2), $"Finished at {string.Join(",", finished)} of {steps}.");
    }

    private const string Rotation = "P(p) = p\nQ(p) = p\nA = B + P + 0\nB = A + Q + 0\nC = A + 0\n0";

    /// <summary>
    /// Cancellation at the resolver's final publication boundary, after every origin is prepared: it surfaces as this
    /// token's cancellation, and the same retained input resolves in full. The selection's result never split from it.
    /// </summary>
    [Fact]
    public void CancellationAtTheFinalPublication_IsTheOperations_AndTheSameInputRetries()
    {
        var root = ParameterDetector.DetectPrevalidated(SourceProvenance.ParseSyntaxValidRoot(Rotation)).Root;
        using var cancellation = new CancellationTokenSource();
        var observer = new FrontEndTraversalObservations
        {
            StageObserver = (name, begin) => { if (name == "completed-publication" && begin) cancellation.Cancel(); },
        };
        var error = Assert.ThrowsAny<OperationCanceledException>(
            () => ImplicitArgumentResolver.ResolveNameResolvedPrevalidated(root, observer, cancellationToken: cancellation.Token));
        Assert.Equal(cancellation.Token, error.CancellationToken);
        Assert.Empty(root.Properties.Single(static property => property.Name == "A").Value.Params);

        var retried = ImplicitArgumentResolver.ResolveNameResolvedPrevalidated(root);
        var capture = ParameterPattern.FlattenCaptures(retried.Properties.Single(static property => property.Name == "A").Value.ParameterPatterns).Single();
        Assert.Equal(2, capture.InferredProvenance!.CycleOrigin!.Roots.Count);
    }

    /// <summary>
    /// Cancellation while exposure seals a resolved recursive unit: the publication is failed and unusable, so nothing reads
    /// its origins, and resolving the same retained input again succeeds with them.
    /// </summary>
    [Fact]
    public void CancellationWhileSealing_PublishesNoRecursiveUnit_AndTheSameInputRetries()
    {
        var root = ParameterDetector.DetectPrevalidated(SourceProvenance.ParseSyntaxValidRoot(Rotation)).Root;
        var resolved = ImplicitArgumentResolver.ResolveNameResolvedPrevalidated(root);
        using var cancellation = new CancellationTokenSource();
        var observer = new FrontEndTraversalObservations
        {
            StageObserver = (name, begin) => { if (name == "retarget-and-seal" && begin) cancellation.Cancel(); },
        };
        var error = Assert.Throws<OperationCanceledException>(() => PropertyExposureResolver.Resolve(resolved, observer, cancellationToken: cancellation.Token));
        Assert.Equal(cancellation.Token, error.CancellationToken);
        var publication = Assert.IsType<CompletedStructurePublication>(resolved.CompletedStructure);
        Assert.True(publication.Facts.IsFailed);
        Assert.False(publication.Facts.IsSealed);

        var exposed = PropertyExposureResolver.Resolve(ImplicitArgumentResolver.ResolveNameResolvedPrevalidated(root), observations: null);
        Assert.True(exposed.CompletedStructure!.Facts.IsSealed);
    }

    // ── charges, and the three failure classes ──────────────────────────────────────────────────

    /// <summary>A growing ring: every member gains names for n rounds, so a state is wide and a transient long.</summary>
    private static readonly Func<int, string> GrowingRing = members =>
        string.Join("\n", Enumerable.Range(0, members).Select(i => $"D{i} = D{(i + 1) % members} + x{i}")) + "\n0";

    /// <summary>The ring's storage charge, read from the real selector's ledger, over the model law of plain names.</summary>
    private static long Charged(int members)
    {
        var references = Enumerable.Range(0, members)
            .Select(i => (IReadOnlyList<SignatureEquationReference>)[new SignatureEquationReference((i + 1) % members, null, $"E{(i + 1) % members}", -1, new Expr.Resolve("r"), "r")])
            .ToArray();
        var closed = new SignatureFact([], null, isLifted: false, composition: null, new CallableSignature("", []));
        SignatureFact Compose(int equation, IReadOnlyList<(int Reference, CallableSignature Signature)> lifted)
        {
            var names = new List<string> { $"x{equation}" };
            foreach (var (_, signature) in lifted)
                names.AddRange(signature.ParameterNames.Where(name => !names.Contains(name)));
            IReadOnlyList<ParameterPattern> patterns = [.. names.Select(static name => (ParameterPattern)new CaptureParameterPattern(name))];
            return new SignatureFact(patterns, null, lifted.Count > 0, null, CallableSignature.FromInferredPatterns($"E{equation}", patterns));
        }

        var ledger = new StaticQueryResourceBudget(StaticQueryLimits.Default);
        var selection = new SignatureSelector(references, new bool[members], Compose, static (_, settled, _) => settled, closed, ledger, CancellationToken.None).Solve();
        Assert.True(selection.Succeeded);
        Assert.Equal(members, selection.Facts[0].Patterns.Count);
        return ledger.MetadataUnits;
    }

    /// <summary>
    /// A long transient settles (n rounds of n members of up to n names), and its charges grow with that real work:
    /// doubling the ring multiplies the storage charge at least fourfold. Uncharged rounds would stay linear.
    /// </summary>
    [Fact]
    public void ALongTransient_IsChargedForItsRealWork()
    {
        var (small, large) = (Charged(32), Charged(64));
        Assert.True(large >= 4 * small, $"{small} -> {large}");
    }

    /// <summary>
    /// Exhausting the envelope is the resource refusal, never a recursion refusal: the same ring is refused under a small
    /// envelope and settles under the default one. The envelope belongs to a parse, so the funded retry parses the same text.
    /// </summary>
    [Fact]
    public void AnExhaustedCompletion_IsAResourceRefusal_NeverNonSettling()
    {
        var source = GrowingRing(64);
        var tight = Parser.Parse(source, new RunOptions { SourceProcessingLimits = new() { MaxStaticStructureBytes = 256 * 1024 } });
        var refusal = Assert.Single(tight.Diagnostics, static diagnostic => diagnostic.Severity == DiagnosticSeverity.Error);
        Assert.Equal(DiagnosticCode.StaticStructureLimitExceeded, refusal.Code);
        Assert.False(Parser.Parse(source).HasErrors);
    }

    /// <summary>
    /// Retains one detected tree across a genuine storage refusal and a funded fresh operation: no reparse, cache clearing
    /// or identity replacement. The retry publishes the complete signatures and the shared origin the failed attempt could not.
    /// </summary>
    [Fact]
    public void AnExhaustedCompletion_RetriesTheSameTreeWithAFundedOperation()
    {
        const int Members = 16;
        var source = "P(p) = p\nQ(p) = p\n" + string.Join("\n", Enumerable.Range(0, Members)
            .Select(i => $"D{i} = D{(i + 1) % Members} + x{i} + {(i == 0 ? "P" : "Q")}")) + "\nC = D0 + 0\n0";
        var detected = ParameterDetector.DetectPrevalidated(SourceProvenance.ParseSyntaxValidRoot(source));
        Assert.Empty(detected.Diagnostics);
        var root = detected.Root;
        var prelude = BuiltinRegistry.CreateSemanticPreludeAlgorithm();
        var limits = StaticStructureAdmission.Measure(root, prelude).Limits;
        StaticStructureOperation Operation(StaticQueryLimits bound)
        {
            var operation = new StaticStructureOperation(root, bound, prelude, phase: StaticAstPhase.NameResolved);
            operation.RegisterNameResolvedInput(root);
            return operation;
        }

        // Calibrate the ceiling from this exact input after its closed gate and first simultaneous round. Previous peaks
        // fit, so the restricted attempt reaches recursive completion before exhausting actual subsequent storage charges.
        var funded = Operation(limits);
        var peaks = new List<long>();
        var calibration = new FrontEndTraversalObservations
        {
            OnSignatureSelectionStep = _ => peaks.Add(funded.Queries.Resources.PeakStorageUnits),
        };
        _ = ImplicitArgumentResolver.ResolvePrevalidated(root, calibration, structuralOperation: funded);
        const int Checkpoint = 2 * Members + 4;
        Assert.True(peaks.Count > Checkpoint);
        var ceiling = peaks[Checkpoint - 1];
        Assert.InRange(ceiling, 1, funded.Queries.Resources.PeakStorageUnits - 1);

        var exhausted = Operation(limits with { MaxStorageUnits = ceiling });
        var observations = new FrontEndTraversalObservations();
        Assert.Throws<StaticQueryLimitExceededException>(
            () => ImplicitArgumentResolver.ResolvePrevalidated(root, observations, structuralOperation: exhausted));
        Assert.True(exhausted.Queries.Resources.IsFailed);
        Assert.True(observations.SignatureSelectionSteps >= Checkpoint);
        Assert.Throws<InvalidOperationException>(exhausted.Queries.Resources.EnsureUsable);
        Assert.Null(root.CompletedStructure);
        for (var i = 0; i < Members; i++)
        {
            var input = root.Properties.Single(property => property.Name == $"D{i}").Value;
            Assert.Equal([$"x{i}"], input.Params);
            Assert.Null(input.CompletedStructure);
        }

        var retry = ImplicitArgumentResolver.ResolvePrevalidated(root, structuralOperation: Operation(limits));
        var exposed = PropertyExposureResolver.Resolve(retry, observations: null);
        Assert.True(exposed.CompletedStructure!.Facts.IsSealed);
        var completed = exposed.Properties.Single(static property => property.Name == "D0").Value;
        Assert.Equal(Members + 1, completed.ParameterCount);
        var origin = ParameterPattern.FlattenCaptures(completed.ParameterPatterns).Single(static capture => capture.Name == "p").InferredProvenance!.CycleOrigin!;
        Assert.Equal(Members, origin.Members.Count);
        Assert.Equal(["P", "Q"], origin.Roots.Select(static item => item.Provider));
        var reader = exposed.Properties.Single(static property => property.Name == "C").Value;
        Assert.Same(origin, ParameterPattern.FlattenCaptures(reader.ParameterPatterns).Single(static capture => capture.Name == "p").InferredProvenance!.CycleOrigin);
    }

    /// <summary>Each cancellation point: any token cancelled ahead of the operation is observed, and nothing is published.</summary>
    [Fact]
    public void ACancelledOperation_PublishesNothing()
    {
        using var cancellation = new CancellationTokenSource();
        cancellation.Cancel();
        Assert.ThrowsAny<OperationCanceledException>(() => Parser.Parse(GrowingRing(8), new RunOptions { SourceProcessingCancellationToken = cancellation.Token }));
    }

    /// <summary>
    /// A sweep of the ledger through the rounds: each work bound either refuses as exhaustion, with the ledger failed and no
    /// selection returned, or returns the whole answer. Never a partial one, never non-settling.
    /// </summary>
    [Fact]
    public void EveryWorkBound_RefusesAsExhaustion_OrAnswersWhole()
    {
        var references = new IReadOnlyList<SignatureEquationReference>[]
        {
            [new(1, null, "one", -1, new Expr.Resolve("r"), "r")],
            [new(0, null, "zero", -1, new Expr.Resolve("r"), "r")],
        };
        var closed = new SignatureFact([], null, isLifted: false, composition: null, new CallableSignature("", []));
        SignatureFact Compose(int equation, IReadOnlyList<(int Reference, CallableSignature Signature)> lifted)
        {
            var names = new List<string> { $"x{equation}" };
            foreach (var (_, signature) in lifted)
                names.AddRange(signature.ParameterNames.Where(name => !names.Contains(name)));
            IReadOnlyList<ParameterPattern> patterns = [.. names.Select(static name => (ParameterPattern)new CaptureParameterPattern(name))];
            return new SignatureFact(patterns, null, lifted.Count > 0, null, CallableSignature.FromInferredPatterns($"E{equation}", patterns));
        }

        var completed = 0;
        var refused = 0;
        for (var bound = 1L; bound < 400; bound++)
        {
            var ledger = new StaticQueryResourceBudget(new StaticQueryLimits(bound, 64));
            var seals = 0;
            IReadOnlyDictionary<int, SignatureFact> Seal(IReadOnlyList<int> component, IReadOnlyDictionary<int, SignatureFact> settled, SignatureSelector.LiftedFrom from)
            {
                seals++;
                return settled;
            }

            try
            {
                var selection = new SignatureSelector(references, [false, false], Compose, Seal, closed, ledger, CancellationToken.None).Solve();
                Assert.True(selection.Succeeded);
                Assert.Equal(2, selection.Facts.Count);
                Assert.Equal(1, seals);
                completed++;
            }
            catch (StaticQueryLimitExceededException)
            {
                Assert.True(ledger.IsFailed);
                refused++;
            }
        }

        Assert.True(refused > 10, $"{refused} refusals");
        Assert.True(completed > 10, $"{completed} completions");
    }

    /// <summary>A wide lower fact a member lifts is charged each round, though Q-04 filters every name of it from the member.</summary>
    [Fact]
    public void AWideFilteredLowerFact_IsCharged()
    {
        static long Storage(int width)
        {
            var wide = new CallableSignature("W", [.. Enumerable.Range(0, width).Select(static i => new CallableParameter($"w{i}"))]);
            var references = new IReadOnlyList<SignatureEquationReference>[]
            {
                [new(1, null, "one", -1, new Expr.Resolve("r"), "r"), new(2, null, "wide", -1, new Expr.Resolve("r"), "r")],
                [new(0, null, "zero", -1, new Expr.Resolve("r"), "r"), new(2, null, "wide", -1, new Expr.Resolve("r"), "r")],
                [],
            };
            var closed = new SignatureFact([], null, isLifted: false, composition: null, new CallableSignature("", []));
            SignatureFact Compose(int equation, IReadOnlyList<(int Reference, CallableSignature Signature)> lifted)
            {
                IReadOnlyList<ParameterPattern> patterns = equation == 2
                    ? [.. Enumerable.Range(0, width).Select(static i => (ParameterPattern)new CaptureParameterPattern($"w{i}"))]
                    : [new CaptureParameterPattern("x")];
                return new SignatureFact(patterns, null, lifted.Count > 0, null, CallableSignature.FromInferredPatterns($"E{equation}", patterns));
            }

            var ledger = new StaticQueryResourceBudget(StaticQueryLimits.Default);
            Assert.True(new SignatureSelector(references, [false, false, false], Compose, static (_, settled, _) => settled, closed, ledger, CancellationToken.None).Solve().Succeeded);
            return ledger.MetadataUnits;
        }

        var (small, large) = (Storage(16), Storage(1024));
        Assert.True(large > small + 1000, $"{small} -> {large}");
    }

    // ── shared contexts and readers ─────────────────────────────────────────────────────────────

    /// <summary>
    /// Concurrent readers of ONE published tree: every thread evaluates the same root and reports through the same generated
    /// note, which is immutable, so each sees the complete result.
    /// </summary>
    [Fact]
    public async Task ConcurrentReaders_OfOneTree_SeeOneCompleteResult()
    {
        var parsed = Parser.Parse("P(p) = p\nQ(p) = p\nA = if(tick() > 2, 0, B + P)\nB = A + Q\nA(1, 2)");
        Assert.False(parsed.HasErrors);
        var results = await Task.WhenAll(Enumerable.Range(0, 16).Select(_ => Task.Run(() => Evaluator.RunFlat(new Expr.AlgorithmExpr(parsed.Root)))));
        Assert.All(results, static result => Assert.True(result.IsError));
        var notes = results.Select(static result => Assert.IsType<EvalError.ArityMismatch>(Terminal(result.Error)).InferredImplicitParameters).ToArray();
        Assert.All(notes, note => Assert.Equal(["P", "Q"], Assert.Single(note!).CycleOrigin!.Roots.Select(static root => root.Provider).Order(StringComparer.Ordinal)));
        Assert.Single(notes.Select(static note => note![0]).Distinct());
    }

    private static EvalError Terminal(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;
        return error;
    }

    /// <summary>
    /// A completed recursive group in a shared syntax diamond: every level holds one body twice, so the paths double per
    /// level. Analysis stays linear in the levels and every occurrence reads the one published record.
    /// </summary>
    [Fact]
    public void ARecursiveGroupInASharedDiamond_StaysLinearInItsLevels()
    {
        static long Bodies(int depth)
        {
            static string Level(int remaining, string indent) => remaining == 0
                ? "{\n" + indent + "    public A = B + P\n" + indent + "    public B = A + Q\n" + indent + "    0\n" + indent + "}"
                : "{\n" + indent + "    public L = " + Level(remaining - 1, indent + "    ") + "\n" + indent + "    public R = " + Level(remaining - 1, indent + "    ")
                    + "\n" + indent + "    0\n" + indent + "}";
            static Algorithm.User Share(Algorithm.User body)
            {
                if (body.Properties.FirstOrDefault(static property => property.Name == "L") is not { } left)
                    return body;
                var shared = Share((Algorithm.User)left.Value);
                return body with { Properties = [.. body.Properties.Select(property => property with { Value = shared })] };
            }

            var source = "P(p) = p\nQ(p) = p\nD = " + Level(depth, "") + "\n0";
            var detected = ParameterDetector.DetectPrevalidated(SourceProvenance.ParseSyntaxValidRoot(source));
            Assert.Empty(detected.Diagnostics);
            var root = (Algorithm.User)detected.Root;
            var host = root with { Properties = [.. root.Properties.Select(static property => property.Name == "D" ? property with { Value = Share((Algorithm.User)property.Value) } : property)] };
            var observations = new FrontEndTraversalObservations();
            var diagnostics = new DiagnosticBag();
            var resolved = ImplicitArgumentResolver.ResolveNameResolvedPrevalidated(host, observations, diagnostics);
            Assert.Equal(0, diagnostics.ReportedCount);

            var left = resolved.Properties.Single(static property => property.Name == "D").Value;
            var right = left;
            for (var level = 0; level < depth; level++)
            {
                left = left.Properties.Single(static property => property.Name == "L").Value;
                right = right.Properties.Single(static property => property.Name == "R").Value;
            }

            Assert.Same(left, right);
            var cycle = ParameterPattern.FlattenCaptures(left.Properties.Single(static property => property.Name == "A").Value.ParameterPatterns).Single().InferredProvenance!.CycleOrigin!;
            Assert.Equal(["A", "B"], cycle.Members.Select(static member => member.Path));
            return observations.SignatureAnalysisBodies;
        }

        var (small, large) = (Bodies(3), Bodies(9));
        Assert.True(large <= 4 * small, $"{small} -> {large} analyzed bodies across 2^3 and 2^9 paths.");
    }

    /// <summary>
    /// A later unit inherits a completed group nested in a module both units reach: its report through the inherited member
    /// names the group within its own body and every source, however deep the read.
    /// </summary>
    [Fact]
    public async Task ALaterUnit_InheritsANestedCompletedGroup()
    {
        var modules = new Dictionary<string, string>
        {
            [Url + "a.kat"] = "P(p) = p\nQ(p) = p\npublic Inner = {\n    public H = K + P\n    public K = H + Q\n    0\n}\n0",
            [Url + "b.kat"] = "M = load('" + Url + "a.kat')\npublic W = M.Inner.K + 0\n0",
        };
        var main = "M = load('" + Url + "a.kat')\nX = M.Inner.H + 0\nG(0) = {\n    N = load('" + Url + "b.kat')\n    N.W(1, 2)\n}\nG(n) = n\nG(0)";
        var failure = Assert.IsType<RunResult.EvalFailure>(await KatLangEngine.RunAsync(main, Serve(modules)));
        Assert.Contains("Parameter 'p' is inferred around the recursive group 'H', 'K'; it comes from 'P', 'Q'.", failure.Errors[0].Message, StringComparison.Ordinal);
    }

    /// <summary>
    /// Many readers of a completed wide cycle share one list: a chain of K readers stays FE-3 linear, however many names the
    /// cycle holds. The output's size bounds the growth; a per-path materialization would be quadratic.
    /// </summary>
    [Fact]
    public void ManyReadersOfACompletedCycle_ShareItsList()
    {
        var builder = new StringBuilder();
        for (var i = 0; i < 64; i++)
            builder.Append($"P{i}(p{i}) = p{i}\n");
        builder.Append("A = B + ").Append(string.Join(" + ", Enumerable.Range(0, 64).Select(static i => $"P{i}"))).Append('\n');
        builder.Append("B = A + 0\n");
        for (var i = 0; i < 64; i++)
            builder.Append($"R{i} = A + {i}\n");
        builder.Append("0\n");
        var parsed = Parser.Parse(builder.ToString());
        Assert.False(parsed.HasErrors);
        var first = parsed.Root.Properties.Single(static property => property.Name == "R0").Value.ParameterPatterns;
        Assert.Equal(64, first.Count);
        for (var i = 1; i < 64; i++)
            Assert.Same(first, parsed.Root.Properties.Single(property => property.Name == $"R{i}").Value.ParameterPatterns);
    }
}
