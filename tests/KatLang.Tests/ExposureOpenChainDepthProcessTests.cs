using System.Diagnostics;

namespace KatLang.Tests;

/// <summary>
/// OOS-22: the summary channel's level expansion on long opened chains, process-isolated. Settling an
/// opened link's charge at the owner expands it there, which settles the next link's, and so on
/// (<c>ExpandAtLevel</c> → <c>AddEscaping</c> → <c>TryResolveLocalHeadCandidate</c> → <c>ExpandAtLevel</c>,
/// or through the local-path and resolved-candidate arms); the rewrites of the candidates that chain
/// nests (parameter qualification, requirement stripping, the lexical-absence reduction) reach every
/// level of that nesting too. Both formerly recursed on the host stack once per link, and a program of
/// a few hundred links killed the process: on a 1 MiB Release thread the opened chain
/// (<c>NestedOwnerChain(700, last: "p")</c>) overflowed after about 560 links, the dotted chain after
/// about 1,280, the mixed chain sooner. Both now run on explicit stacks. A stack overflow cannot be
/// caught, so the probe runs in a child process — the source is generated before the constrained
/// thread starts, and only the front-end operation itself runs on a thread of exactly 1 MiB
/// (<see cref="AstStructuralDepthProcessTests.RunOnThreadWithStack(int, Action, TimeSpan?)"/>). Every
/// case asserts the classification a short control of the same shape has
/// (<see cref="ExposureOpenChainComplexityTests"/>), never mere survival. The child runs from whichever
/// Debug/Release assembly is under test; <c>dotnet test -c Release --filter ExposureOpenChainDepthProcessTests</c>
/// is the Release invocation.
/// </summary>
public sealed class ExposureOpenChainDepthProcessTests
{
    private const string ProbeChildEnvironment = "KATLANG_OPEN_CHAIN_DEPTH_PROBE_CHILD";
    private const string ProbeMarkerFileEnvironment = "KATLANG_OPEN_CHAIN_DEPTH_PROBE_MARKER_FILE";
    private const string ProbeSuccessMarker = "katlang-open-chain-depth-probe-ok";
    private const string Module = "https://katlang.org/oos22/m.kat";

    /// <summary>
    /// The child's whole-process budget: test discovery in a fresh <c>dotnet vstest</c> host (12 s idle,
    /// over 60 s under full-suite load) plus the probe's own work — the whole child took 30 s in Release
    /// and 59 s in Debug on an idle machine (October 2026), because the exposure settlement of an opened
    /// chain is quadratic in its length
    /// (<see cref="ExposureOpenChainComplexityTests.NestedOwnerOpenedChain_BuildsEachCandidateOnce_AndSettlesQuadratically"/>).
    /// A real hang still fails, within that bound.
    /// </summary>
    private static readonly TimeSpan ProbeChildBudget = TimeSpan.FromSeconds(300);

    private static readonly TimeSpan ThreadBudget = TimeSpan.FromSeconds(180);

    private static void OnOneMebibyteStack(Action work)
        => AstStructuralDepthProcessTests.RunOnThreadWithStack(1024 * 1024, work, ThreadBudget);

    private static Algorithm ParseValidOnOneMebibyte(string source)
    {
        ParseResult parsed = null!;
        OnOneMebibyteStack(() => parsed = Parser.Parse(source));
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Take(5)));
        return parsed.Root;
    }

    private static Property Member(Algorithm owner, params string[] path) => ExposureOpenChainComplexityTests.Member(owner, path);

    private static void AssertRequires(Property property, params (string Name, int Depth)[] requirements)
        => ExposureOpenChainComplexityTests.AssertRequires(property, requirements);

    [Fact]
    public async Task LongOpenChains_AreClassifiedOnAOneMebibyteStack_InSubprocess()
        => await RunProbeChild(nameof(LongOpenChains_ProbeChild));

    [Fact]
    public void LongOpenChains_ProbeChild()
    {
        if (Environment.GetEnvironmentVariable(ProbeChildEnvironment) != "1")
            return;

        // The historical witness, then 2,000 links: the reader requires the owner's `p` directly and every
        // link one level out (CapturedTerminalChain_RequiresTheOwnersInputThroughout at 16–64 links).
        foreach (var length in new[] { 700, 2_000 })
        {
            var source = ExposureOpenChainComplexityTests.NestedOwnerChain(length, last: "p");
            var owner = Member(ParseValidOnOneMebibyte(source), "O").Value;
            AssertRequires(Member(owner, "R"), ("p", 0));
            foreach (var i in new[] { 1, 2, length / 2, length - 1, length })
            {
                AssertRequires(Member(owner, $"P{i}"));
                AssertRequires(Member(owner, $"P{i}", $"A{i}"), ("p", 1));
            }
        }

        // A long chain through the internal pipeline: the candidate work stays linear — each link
        // settled once at the owner and qualified once (2N rebuilds, as at 400 links in process).
        {
            const int Length = 1_000;
            var source = ExposureOpenChainComplexityTests.NestedOwnerChain(Length, last: "p");
            var observations = new FrontEndTraversalObservations();
            Algorithm.User exposed = null!;
            OnOneMebibyteStack(() => exposed = ExposureOpenChainComplexityTests.Exposed(source, observations));
            AssertRequires(Member(Member(exposed, "O").Value, "R"), ("p", 0));
            Assert.Equal(2L * Length, observations.OpenCandidateSeedRebuilds);
            Assert.Equal((long)Length * (Length + 3), observations.RequiredAncestorSettlementFrames);
        }

        // A constant terminal: the whole chain is exported (NestedOwnerOpenedChain_WithAConstantTerminal).
        {
            const int Length = 1_000;
            var owner = Member(ParseValidOnOneMebibyte(ExposureOpenChainComplexityTests.NestedOwnerChain(Length)), "O").Value;
            AssertRequires(Member(owner, "R"));
            AssertRequires(Member(owner, $"P{Length}", $"A{Length}"));
        }

        // Dotted reads (the local-path arm, no candidates) and the mixed chain with local intermediaries
        // (ControlChains_BuildNoCandidates, MixedChain_WithLocalIntermediaries).
        {
            const int Length = 2_000;
            var dotted = Member(ParseValidOnOneMebibyte(ExposureOpenChainComplexityTests.NestedOwnerChain(Length, "dotted")), "O").Value;
            AssertRequires(Member(dotted, "R"));
            AssertRequires(Member(dotted, "P1", "A1"));
            AssertRequires(Member(dotted, $"P{Length}", $"A{Length}"));

            const int Mixed = 1_000;
            var mixed = Member(ParseValidOnOneMebibyte(ExposureOpenChainComplexityTests.NestedOwnerChain(Mixed, "mixed", last: "p")), "O").Value;
            AssertRequires(Member(mixed, "R"), ("p", 0));
            AssertRequires(Member(mixed, "P1", "A1"), ("p", 1));
            AssertRequires(Member(mixed, "P1", "Local1"), ("p", 1));
            AssertRequires(Member(mixed, $"P{Mixed}", $"A{Mixed}"), ("p", 1));
        }

        // Lexical shadowing in the middle of the chain: link 1,000 declares its own `A1001`, which wins
        // over the opened one, so the links above it are exported and those below still require `p`.
        {
            const int Length = 2_000;
            const int Shadow = Length / 2;
            var source = ExposureOpenChainComplexityTests.NestedOwnerChain(Length, last: "p")
                .Replace($"open P{Shadow + 1}\n", $"open P{Shadow + 1}\n        A{Shadow + 1} = 5\n", StringComparison.Ordinal);
            var owner = Member(ParseValidOnOneMebibyte(source), "O").Value;
            AssertRequires(Member(owner, "R"));
            AssertRequires(Member(owner, "P1", "A1"));
            AssertRequires(Member(owner, $"P{Shadow}", $"A{Shadow}"));
            AssertRequires(Member(owner, $"P{Shadow + 1}", $"A{Shadow + 1}"), ("p", 1));
            AssertRequires(Member(owner, $"P{Length}", $"A{Length}"), ("p", 1));
        }

        // The settled chain read again from the enclosing level (`X = O.R`): the root expands the nested
        // resolved candidates of the navigated member's seed (the resolved-candidate arm).
        {
            const int Length = 1_000;
            var source = "O = {\n" + ExposureOpenChainComplexityTests.Chain("open", Length, "5", "    ")
                + ExposureOpenChainComplexityTests.Reader("open", "    ") + "    R\n}\nX = O.R\nX";
            var root = ParseValidOnOneMebibyte(source);
            AssertRequires(Member(root, "X"));
            AssertRequires(Member(root, "O", "R"));
        }

        AssertDeepCandidateRewrites();
        AssertDeferredBranchElaboratesTheChain();
        WriteProbeMarker();
    }

    // Exercise each rewritten operation directly: an acyclic source chain need not repeat the head
    // whose lexical-absence reduction walks the nesting, even when it qualifies/strips all 2,000 links.
    private static void AssertDeepCandidateRewrites()
    {
        const int Depth = 2_000;
        var owner = Member(SourceProvenance.ParseValid("F(p) = p\n0").Root, "F").Value;
        var observations = new FrontEndTraversalObservations();
        var memo = new PropertyDependencyGraphBuilder.SummaryMemo(observations);
        var identity = OpenProviderIdentity.DeclaredAtRoot(owner);
        var candidate = new ResolvedOpenCandidate(new PropertyDependencyGraphBuilder.SummarySeed(["p"]), 0, identity, memo);
        for (var i = 0; i < Depth; i++)
        {
            var seed = new PropertyDependencyGraphBuilder.SummarySeed(
                pendingReferences: [new PendingReference("a", [], [candidate])]);
            candidate = new ResolvedOpenCandidate(seed, 0, identity, memo);
        }

        var names = new HashSet<string>(["p"], StringComparer.Ordinal);
        OnOneMebibyteStack(() =>
        {
            var before = observations.OpenCandidateSeedRebuilds;
            var qualified = candidate.QualifiedBy(owner, names);
            Assert.Equal(Depth + 1, observations.OpenCandidateSeedRebuilds - before);
            Assert.True(qualified.RequiresAny(names, owner));
            var leaf = qualified;
            for (var i = 0; i < Depth; i++)
                leaf = Assert.IsType<ResolvedOpenCandidate>(Assert.Single(Assert.Single(leaf.Seed.PendingReferences).Candidates));
            Assert.Equal(new OwnerQualifiedParameter("p", owner), Assert.Single(leaf.Seed.OwnerQualifiedParameters));

            before = observations.OpenCandidateSeedRebuilds;
            var stripped = qualified.Seed.Clone();
            stripped.RemoveRequiredAncestorOwnedParameterNames(names, owner, ownerHasParameters: true, observations);
            Assert.Equal(Depth, observations.OpenCandidateSeedRebuilds - before);
            Assert.False(new ResolvedOpenCandidate(stripped, 0, identity, memo).RequiresAny(names, owner));

            before = observations.OpenCandidateSeedRebuilds;
            var reduced = candidate.UnderMissingLexicalHead("a");
            Assert.Equal(Depth, observations.OpenCandidateSeedRebuilds - before);
            Assert.Empty(reduced.Seed.PendingReferences);
            Assert.Equal(["p"], reduced.Seed.RequiredAncestorOwnedParameterNames);
            // The rewrites operate on copies and cannot replace the original nested requirements.
            Assert.Single(candidate.Seed.PendingReferences);
            Assert.True(candidate.RequiresAny(names, owner));
        });
    }

    /// <summary>
    /// The chain inside a branch body that loads a module (formerly the eager parse already overflowed
    /// while summarizing that body): the provisional elaboration completes without fetching, the
    /// branch's materialization when a run selects it elaborates the chain again through the same
    /// machinery (<c>PropertyExposureResolver.ElaborateDeferredBranch</c>), and a run that never selects
    /// it never fetches the module.
    /// </summary>
    private static void AssertDeferredBranchElaboratesTheChain()
    {
        const int Length = 1_000;
        var fetches = 0;
        var options = new RunOptions
        {
            DownloadCode = (url, _) =>
            {
                Assert.Equal(Module, url);
                fetches++;
                return ValueTask.FromResult("public M = 7");
            },
        };
        var owner = ExposureOpenChainComplexityTests.NestedOwnerChain(Length, last: "p", call: "")
            .ReplaceLineEndings("\n").Replace("\n", "\n    ", StringComparison.Ordinal);
        string Program(int argument) => $"F(0) = 0\nF(n) = {{\n    open '{Module}'\n    {owner}M\n}}\nF({argument})";

        var selectedSource = Program(1);
        var unselectedSource = Program(0);
        ParseResult provisional = null!;
        OnOneMebibyteStack(() =>
        {
            var parse = Parser.ParseAsync(selectedSource, options);
            Assert.True(parse.IsCompleted, "Parsing with a deferred-only module completes synchronously.");
            provisional = parse.GetAwaiter().GetResult();
        });
        Assert.False(provisional.HasErrors, string.Join(Environment.NewLine, provisional.Diagnostics.Take(5)));
        // The provisional body is present but not yet classified (its exposure is published when the
        // branch materializes); summarizing the branch body already walks the whole chain.
        var parsed = Member(provisional.Root, "F").Value;
        var body = Assert.IsType<Algorithm.Conditional>(parsed).Branches[^1].Body;
        Assert.Equal(Length, Member(body, "O").Value.Properties.Count(p => p.Name.StartsWith('P')));
        Assert.Equal(0, fetches);

        foreach (var (source, expected, expectedFetches) in new[] { (unselectedSource, "0", 0), (selectedSource, "7", 1) })
        {
            fetches = 0;
            RunResult result = null!;
            OnOneMebibyteStack(() =>
            {
                var run = KatLangEngine.RunAsync(source, options);
                Assert.True(run.IsCompleted, "A run whose downloader completes synchronously completes synchronously.");
                result = run.GetAwaiter().GetResult();
            });
            Assert.Equal(expected, Assert.IsType<RunResult.Success>(result).ToDisplayString());
            Assert.Equal(expectedFetches, fetches);
        }
    }

    /// <summary>
    /// Runs one env-gated probe child in a fresh <c>dotnet vstest</c> process: normal exit, no
    /// stack-overflow text, the success marker the child writes last (a non-matching filter exits 0),
    /// and completion within <see cref="ProbeChildBudget"/>, killing the process tree otherwise.
    /// </summary>
    private static async Task RunProbeChild(string childTestName)
    {
        var assemblyPath = typeof(ExposureOpenChainDepthProcessTests).Assembly.Location;
        var testName = typeof(ExposureOpenChainDepthProcessTests).FullName + "." + childTestName;
        var markerFile = Path.Combine(Path.GetTempPath(), $"katlang-open-chain-depth-probe-{Guid.NewGuid():N}.txt");
        var startInfo = new ProcessStartInfo("dotnet")
        {
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            UseShellExecute = false,
            CreateNoWindow = true,
        };
        startInfo.ArgumentList.Add("vstest");
        startInfo.ArgumentList.Add(assemblyPath);
        startInfo.ArgumentList.Add("--Tests:" + testName);
        startInfo.Environment[ProbeChildEnvironment] = "1";
        startInfo.Environment[ProbeMarkerFileEnvironment] = markerFile;
        startInfo.Environment["DOTNET_NOLOGO"] = "1";

        try
        {
            using var process = new Process { StartInfo = startInfo };
            process.Start();
            var stdoutTask = process.StandardOutput.ReadToEndAsync();
            var stderrTask = process.StandardError.ReadToEndAsync();

            var exited = true;
            using var timeout = new CancellationTokenSource(ProbeChildBudget);
            try
            {
                await process.WaitForExitAsync(timeout.Token);
            }
            catch (OperationCanceledException)
            {
                exited = false;
                try { process.Kill(entireProcessTree: true); }
                catch { /* process already exited */ }
                await process.WaitForExitAsync();
            }

            var combined = await stdoutTask + Environment.NewLine + await stderrTask;
            Assert.True(exited, $"Probe subprocess '{childTestName}' did not exit within {ProbeChildBudget.TotalSeconds} seconds."
                + Environment.NewLine + combined);
            Assert.DoesNotContain("Stack overflow", combined, StringComparison.OrdinalIgnoreCase);
            Assert.DoesNotContain("StackOverflowException", combined, StringComparison.OrdinalIgnoreCase);
            Assert.True(process.ExitCode == 0,
                $"Probe subprocess '{childTestName}' exited with {process.ExitCode}.{Environment.NewLine}{combined}");
            Assert.True(File.Exists(markerFile),
                $"Probe child '{childTestName}' did not write its success marker.{Environment.NewLine}{combined}");
            Assert.Equal(ProbeSuccessMarker, (await File.ReadAllTextAsync(markerFile)).Trim());
        }
        finally
        {
            try { File.Delete(markerFile); }
            catch { /* best-effort cleanup */ }
        }
    }

    private static void WriteProbeMarker()
    {
        var markerFile = Environment.GetEnvironmentVariable(ProbeMarkerFileEnvironment);
        Assert.False(string.IsNullOrWhiteSpace(markerFile));
        File.WriteAllText(markerFile!, ProbeSuccessMarker);
    }
}
