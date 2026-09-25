namespace KatLang.Tests;

public sealed class ModuleSecurityHostileReviewTests
{
    private const string Host = "trusted.example";
    private const string Url = "https://trusted.example/m.kat";

    [Theory]
    [InlineData("https://alice:NEVER-ECHO-SECRET@trusted.example:99999/x")]
    [InlineData("https://alice:NEVER-ECHO-SECRET@tru sted.example/x")]
    [InlineData("https://alice:NEVER-ECHO-SECRET@[bad-ip]/x")]
    [InlineData("https://alice:NEVER-ECHO-SECRET@trusted.example\\x")]
    public async Task MalformedCredentialTarget_NeverLeaksCredentials(string target)
    {
        var calls = 0;
        var parsed = await Parser.ParseAsync($"M = load('{target}')\nM.V", new RunOptions
        {
            AllowedHosts = [Host],
            DownloadCode = (_, _) => { calls++; return ValueTask.FromResult("public V = 1"); },
        });
        Assert.True(parsed.HasErrors);
        Assert.Equal(0, calls);
        Assert.All(parsed.Diagnostics, d => Assert.DoesNotContain("NEVER-ECHO-SECRET", d.Message));
        Assert.Contains(parsed.Diagnostics, d => d.Code == DiagnosticCode.InvalidLoadUrl);
    }

    [Fact]
    public void EmptyUserInfo_IsRefusedLikeOtherUserInfo()
    {
        Assert.False(ModuleLoadTarget.TryAdmit("https://@trusted.example/x",
            ModuleLoadTarget.AllowedHosts.From([Host]), out _, out var rejection));
        Assert.Equal(DiagnosticCode.InvalidLoadUrl, rejection.Code);
    }

    [Theory]
    [InlineData(499)]
    [InlineData(500)]
    [InlineData(501)]
    [InlineData(100_000)]
    public void HostMessageEcho_EnforcesTheExactCodeUnitBound(int length)
    {
        var text = new string('x', length);
        Assert.Equal(new string('x', Math.Min(length, 500)) + (length > 500 ? "..." : ""),
            ModuleLoadTarget.EchoHostMessage(text));
        var crossingPair = new string('x', 499) + "\U0001F600SECRET";
        Assert.Equal(new string('x', 499) + "\\uD83D...", ModuleLoadTarget.EchoHostMessage(crossingPair));
    }

    [Theory]
    [InlineData("\U000E0001", "\\uDB40\\uDC01")]
    [InlineData("\U0001BCA0", "\\uD82F\\uDCA0")]
    public void SupplementaryFormatControls_AreEscaped(string control, string escaped)
        => Assert.Equal(escaped, ModuleLoadTarget.EchoHostMessage(control));

    [Theory]
    [InlineData("HTTPS://TRUSTED.EXAMPLE:443/a/../b#frag", "https://trusted.example/b")]
    [InlineData("https://trusted.example/a/%2e%2e/b", "https://trusted.example/b")]
    [InlineData("https://trusted.example/a/%2E%2E/b", "https://trusted.example/b")]
    [InlineData("https://trusted.example/a/./b", "https://trusted.example/a/b")]
    [InlineData("https://trusted.example:1/x?q=1#two", "https://trusted.example:1/x?q=1")]
    [InlineData("https://trusted.example:65535//X%2Fy?q=2", "https://trusted.example:65535//X%2Fy?q=2")]
    [InlineData("https://127.1:443/m#", "https://127.0.0.1/m")]
    [InlineData("https://[2001:DB8:0:0:0:0:0:1]:8443/x", "https://[2001:db8::1]:8443/x")]
    [InlineData("https://bücher.example/x", "https://xn--bcher-kva.example/x")]
    public void AdmissionRoundTrip_PreservesTheExactTransportAndIdentity(string input, string expected)
    {
        var hosts = ModuleLoadTarget.AllowedHosts.From([Host, "127.0.0.1", "2001:db8::1", "bücher.example"]);
        Assert.True(ModuleLoadTarget.TryAdmit(input, hosts, out var canonical, out var rejection), rejection.Message);
        Assert.Equal(expected, canonical);
        Assert.True(ModuleLoadTarget.TryAdmit(canonical, hosts, out var again, out rejection), rejection.Message);
        Assert.Equal(canonical, again);
    }

    [Theory]
    [InlineData("trusted.example", "https://trusted.example/m.kat", "HTTPS://TRUSTED.EXAMPLE:443/a/../m.kat#alias")]
    [InlineData("bücher.example", "https://xn--bcher-kva.example/m.kat", "https://bücher.example/m.kat#alias")]
    [InlineData("127.0.0.1", "https://127.0.0.1/m.kat", "https://0x7f.1:443/m.kat")]
    [InlineData("::1", "https://[::1]/m.kat", "https://[0:0:0:0:0:0:0:1]:443/m.kat#alias")]
    public async Task AliasedCycleAndCache_UseTheSameCanonicalIdentity(string host, string canonical, string alias)
    {
        var requests = new List<string>();
        var cyclic = await Parser.ParseAsync($"M = load('{canonical}')", new RunOptions
        {
            AllowedHosts = [host],
            DownloadCode = (url, _) =>
            {
                requests.Add(url);
                return ValueTask.FromResult($"N = load('{alias}')");
            },
        });
        Assert.Equal([canonical], requests);
        Assert.Equal(DiagnosticCode.LoadCycle, Assert.Single(cyclic.Diagnostics).Code);
        requests.Clear();
        var reused = await Parser.ParseAsync($"M = load('{canonical}')\nN = load('{alias}')\nM.V + N.V", new RunOptions
        {
            AllowedHosts = [host],
            SourceProcessingLimits = new SourceProcessingLimits { MaxModuleCount = 1 },
            DownloadCode = (url, _) => { requests.Add(url); return ValueTask.FromResult("public V = 1"); },
        });
        Assert.False(reused.HasErrors, string.Join("\n", reused.Diagnostics));
        Assert.Equal([canonical], requests);
    }

    [Fact]
    public async Task CancelledDeferredDownloads_ConsumeAttemptsAcrossEvaluationsOfOneParsedTree()
    {
        var calls = 0;
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource<string>(TaskCreationOptions.RunContinuationsAsynchronously);
        var parsed = await Parser.ParseAsync($"F(0) = 0\nF(n) = {{ M = load('{Url}')\nM.V }}\nF(1)", new RunOptions
        {
            AllowedHosts = [Host],
            SourceProcessingLimits = new SourceProcessingLimits { MaxModuleCount = 1 },
            DownloadCode = async (_, token) =>
            {
                Interlocked.Increment(ref calls);
                entered.TrySetResult();
                return await release.Task.WaitAsync(token);
            },
        });
        Assert.False(parsed.HasErrors, string.Join("\n", parsed.Diagnostics));
        Assert.Equal(0, calls);
        using var cancellation = new CancellationTokenSource();
        var run = Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root), limits: null, cancellation.Token);
        await entered.Task.WaitAsync(TimeSpan.FromSeconds(10));
        Assert.False(run.IsCompleted);
        cancellation.Cancel();
        var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => run);
        Assert.Equal(cancellation.Token, error.CancellationToken);
        // Completing the old gate makes any illicit retry observable without a timing wait.
        release.TrySetResult("public V = 7");
        var retry = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root));
        Assert.True(retry.IsError);
        Assert.Equal(KatLangErrorCode.ModuleCountExceeded, retry.Error.Code);
        Assert.Equal(1, calls);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task DownloaderOwnedCancellation_IsBoundedEvenWithoutHostCancellation(bool faultedTask)
    {
        var calls = 0;
        var parsed = await Parser.ParseAsync(string.Join("\n", Enumerable.Range(0, 8).Select(i => $"M{i} = load('{Url}')")), new RunOptions
        {
            AllowedHosts = [Host],
            SourceProcessingLimits = new SourceProcessingLimits { MaxModuleCount = 2 },
            DownloadCode = (_, _) =>
            {
                calls++;
                if (faultedTask) return ValueTask.FromException<string>(new OperationCanceledException("timeout"));
                throw new OperationCanceledException("timeout");
            },
        });
        Assert.Equal(2, calls);
        Assert.Equal(2, parsed.Diagnostics.Count(d => d.Code == DiagnosticCode.LoadFetchFailed));
        Assert.Equal(6, parsed.Diagnostics.Count(d => d.Code == DiagnosticCode.ModuleCountExceeded));
    }
}
