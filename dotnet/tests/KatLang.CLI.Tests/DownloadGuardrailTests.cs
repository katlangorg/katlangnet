using System.Net;
using System.Net.Sockets;

namespace KatLang.CLI.Tests;

/// <summary>
/// The guardrails of the CLI's one downloader (<see cref="HttpSourceDownloader"/>), for a
/// program URL and a module alike: HTTPS only, no user information, and public addresses only,
/// judged on the address a host RESOLVES to and enforced where the connection is opened. The
/// address rule itself (<see cref="PublicAddress"/>) is tested on its own; the transport is
/// tested over its real socket handler with a substituted resolver, so no test resolves a real
/// name or leaves the machine, and a loopback server stands in for a public host only through
/// the explicit test seam.
/// </summary>
public sealed class DownloadGuardrailTests
{
    private static readonly TimeSpan Watchdog = TimeSpan.FromSeconds(60);

    private static readonly TimeSpan Deadline = TimeSpan.FromSeconds(20);

    // ── The address rule ────────────────────────────────────────────────────

    [Theory]
    // Loopback.
    [InlineData("127.0.0.1")]
    [InlineData("127.255.255.254")]
    // Private (RFC 1918), to both edges of each range.
    [InlineData("10.0.0.0")]
    [InlineData("10.0.0.1")]
    [InlineData("10.255.255.255")]
    [InlineData("172.16.0.0")]
    [InlineData("172.16.0.1")]
    [InlineData("172.31.255.255")]
    [InlineData("192.168.0.0")]
    [InlineData("192.168.1.1")]
    [InlineData("192.168.255.255")]
    // Carrier-grade NAT.
    [InlineData("100.64.0.0")]
    [InlineData("100.64.0.1")]
    [InlineData("100.127.255.255")]
    // Link-local, the cloud metadata address among them.
    [InlineData("169.254.0.0")]
    [InlineData("169.254.169.254")]
    [InlineData("169.254.255.255")]
    // Unspecified and "this network".
    [InlineData("0.0.0.0")]
    [InlineData("0.1.2.3")]
    // Multicast, reserved, broadcast.
    [InlineData("224.0.0.1")]
    [InlineData("239.255.255.255")]
    [InlineData("240.0.0.1")]
    [InlineData("255.255.255.255")]
    // Protocol assignments, 6to4 relays, benchmarking, documentation.
    [InlineData("192.0.0.1")]
    [InlineData("192.88.99.1")]
    [InlineData("198.18.0.1")]
    [InlineData("198.19.255.255")]
    [InlineData("192.0.2.1")]
    [InlineData("198.51.100.1")]
    [InlineData("203.0.113.1")]
    // IPv6: unspecified, loopback, unique-local, link-local, site-local, multicast, discard.
    [InlineData("::")]
    [InlineData("::1")]
    [InlineData("fc00::1")]
    [InlineData("fd12:3456:789a::1")]
    [InlineData("fdff:ffff:ffff:ffff:ffff:ffff:ffff:ffff")]
    [InlineData("fe80::1")]
    [InlineData("febf::1")]
    [InlineData("fec0::1")]
    [InlineData("ff02::1")]
    [InlineData("ff0e::1")]
    [InlineData("100::1")]
    // Everything outside global unicast space.
    [InlineData("::2")]
    [InlineData("1::1")]
    [InlineData("4000::1")]
    [InlineData("8000::1")]
    [InlineData("e000::1")]
    // Protocol assignments (Teredo among them) and documentation, inside global unicast space.
    [InlineData("2001::1")]
    [InlineData("2001:0:4136:e378:8000:63bf:3fff:fdd2")]
    [InlineData("2001:1ff:ffff::1")]
    [InlineData("2001:db8::1")]
    [InlineData("2001:db8:ffff:ffff:ffff:ffff:ffff:ffff")]
    [InlineData("3fff::1")]
    [InlineData("3fff:fff:ffff::1")]
    // An address that carries a non-public IPv4 address: IPv4-mapped, NAT64, 6to4.
    [InlineData("::ffff:127.0.0.1")]
    [InlineData("::ffff:10.0.0.1")]
    [InlineData("::ffff:192.168.1.1")]
    [InlineData("::ffff:169.254.169.254")]
    [InlineData("::ffff:0.0.0.0")]
    [InlineData("::ffff:100.64.0.1")]
    [InlineData("64:ff9b::127.0.0.1")]
    [InlineData("64:ff9b::10.0.0.1")]
    [InlineData("64:ff9b::169.254.169.254")]
    [InlineData("2002:7f00:1::1")]
    [InlineData("2002:a00:1::1")]
    [InlineData("2002:c0a8:101::1")]
    // IPv4-compatible (deprecated) and the local-use NAT64 prefix.
    [InlineData("::127.0.0.1")]
    [InlineData("::8.8.8.8")]
    [InlineData("64:ff9b:1::8.8.8.8")]
    public void ANonPublicAddress_IsRefused(string address)
        => Assert.False(PublicAddress.IsPublic(IPAddress.Parse(address)), address);

    [Theory]
    [InlineData("1.1.1.1")]
    [InlineData("8.8.8.8")]
    [InlineData("9.255.255.255")]
    [InlineData("11.0.0.0")]
    [InlineData("100.63.255.255")]
    [InlineData("100.128.0.0")]
    [InlineData("126.255.255.255")]
    [InlineData("128.0.0.1")]
    [InlineData("169.253.255.255")]
    [InlineData("169.255.0.0")]
    [InlineData("172.15.255.255")]
    [InlineData("172.32.0.0")]
    [InlineData("185.199.108.133")]
    [InlineData("192.0.1.1")]
    [InlineData("192.0.3.1")]
    [InlineData("192.167.255.255")]
    [InlineData("192.169.0.0")]
    [InlineData("198.17.255.255")]
    [InlineData("198.20.0.0")]
    [InlineData("198.51.99.1")]
    [InlineData("203.0.112.1")]
    [InlineData("203.0.114.1")]
    [InlineData("223.255.255.255")]
    [InlineData("2001:200::1")]
    [InlineData("2001:4860:4860::8888")]
    [InlineData("2001:db7:ffff::1")]
    [InlineData("2001:db9::1")]
    [InlineData("2606:4700:4700::1111")]
    [InlineData("2a00:1450:4001::1")]
    [InlineData("3ffe::1")]
    [InlineData("3fff:1000::1")]
    // An address that carries a public IPv4 address is as public as that address.
    [InlineData("::ffff:8.8.8.8")]
    [InlineData("64:ff9b::8.8.8.8")]
    [InlineData("2002:808:808::1")]
    public void APublicAddress_IsAllowed(string address)
        => Assert.True(PublicAddress.IsPublic(IPAddress.Parse(address)), address);

    [Fact]
    public void TheRule_JudgesTheAddress_NotItsSpelling()
    {
        // One address, three spellings: mapped, mapped in hexadecimal, and plain.
        Assert.False(PublicAddress.IsPublic(IPAddress.Parse("::ffff:7f00:1")));
        Assert.False(PublicAddress.IsPublic(IPAddress.Parse("::ffff:127.0.0.1")));
        Assert.False(PublicAddress.IsPublic(IPAddress.Parse("127.0.0.1").MapToIPv6()));
        Assert.True(PublicAddress.IsPublic(IPAddress.Parse("8.8.8.8").MapToIPv6()));
        // A scope id changes nothing: a link-local address stays refused.
        Assert.False(PublicAddress.IsPublic(new IPAddress(IPAddress.Parse("fe80::1").GetAddressBytes(), 3)));
        Assert.Throws<ArgumentNullException>(() => PublicAddress.IsPublic(null!));
    }

    // ── The shipped guardrails ──────────────────────────────────────────────

    [Fact]
    public void TheShippedDownloader_RelaxesNothing()
    {
        var production = DownloadSeam.Production;

        Assert.False(production.AllowPlainHttp);
        Assert.False(production.IsAllowedAddress(IPAddress.Loopback));
        Assert.False(production.IsAllowedAddress(IPAddress.IPv6Loopback));
        Assert.False(production.IsAllowedAddress(IPAddress.Parse("10.0.0.1")));
        Assert.True(production.IsAllowedAddress(IPAddress.Parse("1.1.1.1")));

        // The seam that lets a loopback server stand in admits loopback and nothing else new.
        var seam = DownloadSeam.LoopbackStandsInForPublic;
        Assert.True(seam.AllowPlainHttp);
        Assert.True(seam.IsAllowedAddress(IPAddress.Loopback));
        Assert.True(seam.IsAllowedAddress(IPAddress.IPv6Loopback));
        Assert.False(seam.IsAllowedAddress(IPAddress.Parse("10.0.0.1")));
        Assert.False(seam.IsAllowedAddress(IPAddress.Parse("169.254.169.254")));
        Assert.False(seam.IsAllowedAddress(IPAddress.Parse("192.168.1.1")));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task TheShippedInstance_RefusesALoopbackServer_BeforeAnyConnection(bool program)
    {
        // A live server on this machine, reachable by anything that tries. The shipped
        // downloader refuses its plain-HTTP address, its HTTPS address, and the name that
        // resolves to it: the server sees no connection at all.
        await using var server = new LoopbackHttpServer(() => LoopbackHttpServer.Ok("public V = 1"));
        var port = new Uri(server.Url("127.0.0.1")).Port;

        async Task<DownloadException> RefusedAsync(string url)
            => await Assert.ThrowsAsync<DownloadException>(() => Guarded(Download(HttpSourceDownloader.Shared, url, program)));

        Assert.Equal(DownloadFailure.NotHttps, (await RefusedAsync($"http://127.0.0.1:{port}/module.kat")).Failure);
        Assert.Equal(DownloadFailure.NotHttps, (await RefusedAsync($"http://localhost:{port}/module.kat")).Failure);

        var literal = await RefusedAsync($"https://127.0.0.1:{port}/module.kat");
        Assert.Equal(DownloadFailure.NonPublicAddress, literal.Failure);
        Assert.Equal("its host is not at a public address (127.0.0.1).", literal.Message);

        var v6 = await RefusedAsync($"https://[::1]:{port}/module.kat");
        Assert.Equal(DownloadFailure.NonPublicAddress, v6.Failure);
        Assert.Equal("its host is not at a public address (::1).", v6.Message);

        // "localhost" is a name: the platform resolves it, and every address it has is refused.
        var name = await RefusedAsync($"https://localhost:{port}/module.kat");
        Assert.Equal(DownloadFailure.NonPublicAddress, name.Failure);

        Assert.Equal(0, server.RequestCount);
    }

    public static TheoryData<string> AddressesANameMayResolveTo => new()
    {
        "127.0.0.1",
        "10.0.0.1",
        "192.168.1.1",
        "169.254.169.254",
        "::1",
        "fe80::1",
        "::ffff:127.0.0.1",
        "100.64.0.1",
        "fd00::1",
        "0.0.0.0",
    };

    [Theory]
    [MemberData(nameof(AddressesANameMayResolveTo))]
    public async Task AName_ThatResolvesToANonPublicAddress_IsRefusedBeforeAnyConnection(string resolved)
    {
        // The name looks like any public host. Only its ADDRESS shows what it is, and the
        // address is judged where the connection would be opened.
        var address = IPAddress.Parse(resolved);
        var resolver = new RecordingResolver(_ => [address]);
        using var transport = new HttpSourceDownloader(
            HttpSourceDownloader.MaxResponseBodyBytes,
            Deadline,
            handler: null,
            new DownloadSeam(AllowPlainHttp: false, PublicAddress.IsPublic, resolver.ResolveAsync));

        foreach (var program in new[] { false, true })
        {
            var error = await Assert.ThrowsAsync<DownloadException>(
                () => Guarded(Download(transport, "https://files.public-looking.example/program.kat", program)));

            Assert.Equal(DownloadFailure.NonPublicAddress, error.Failure);
            Assert.Equal($"its host is not at a public address ({address}).", error.Message);
        }

        Assert.Equal(["files.public-looking.example", "files.public-looking.example"], resolver.Names);
    }

    [Fact]
    public async Task AName_ThatResolvesToALoopbackServer_NeverReachesIt()
    {
        // The same refusal with something listening: nothing arrives.
        await using var server = new LoopbackHttpServer(() => LoopbackHttpServer.Ok("public V = 1"));
        var port = new Uri(server.Url("127.0.0.1")).Port;
        using var transport = new HttpSourceDownloader(
            HttpSourceDownloader.MaxResponseBodyBytes,
            Deadline,
            handler: null,
            new DownloadSeam(AllowPlainHttp: true, PublicAddress.IsPublic, (_, _) => Task.FromResult(new[] { IPAddress.Loopback })));

        var error = await Assert.ThrowsAsync<DownloadException>(
            () => Guarded(transport.DownloadAsync($"http://rebinding.example:{port}/module.kat", CancellationToken.None).AsTask()));

        Assert.Equal(DownloadFailure.NonPublicAddress, error.Failure);
        Assert.Equal(0, server.RequestCount);
    }

    // ── The seam: a loopback server stands in for a public host ─────────────

    [Fact]
    public async Task TheConnectionGoesToTheAddressThatWasJudged_AndTheNameIsResolvedOnce()
    {
        await using var server = new LoopbackHttpServer(() => LoopbackHttpServer.Ok("public Value = 42"));
        var port = new Uri(server.Url("127.0.0.1")).Port;
        var resolver = new RecordingResolver(_ => [IPAddress.Loopback]);
        using var transport = new HttpSourceDownloader(
            HttpSourceDownloader.MaxResponseBodyBytes,
            Deadline,
            handler: null,
            DownloadSeam.LoopbackStandsInForPublic with { ResolveAsync = resolver.ResolveAsync });

        var text = await Guarded(transport.DownloadProgramAsync($"http://stand-in.example:{port}/module.kat", CancellationToken.None).AsTask());

        // The name exists only in the substituted resolver, so the request can only have
        // arrived over a connection opened to the address that resolver returned.
        Assert.Equal("public Value = 42", text);
        Assert.Equal(1, server.RequestCount);
        Assert.Equal(["stand-in.example"], resolver.Names);
        Assert.Contains($"\r\nHost: stand-in.example:{port}\r\n", Assert.IsType<string>(server.RequestHead), StringComparison.Ordinal);
    }

    [Fact]
    public async Task ARefusedAddressInTheAnswer_IsSkipped_AndAPermittedOneIsUsed()
    {
        // Two addresses for one name: a private one first, then the stand-in. The private one
        // is never tried (it would not answer within the deadline); the permitted one is used.
        await using var server = new LoopbackHttpServer(() => LoopbackHttpServer.Ok("public Value = 42"));
        var port = new Uri(server.Url("127.0.0.1")).Port;
        using var transport = new HttpSourceDownloader(
            HttpSourceDownloader.MaxResponseBodyBytes,
            TimeSpan.FromSeconds(10),
            handler: null,
            DownloadSeam.LoopbackStandsInForPublic with
            {
                ResolveAsync = (_, _) => Task.FromResult(new[] { IPAddress.Parse("10.255.255.1"), IPAddress.Parse("169.254.169.254"), IPAddress.Loopback }),
            });

        var text = await Guarded(transport.DownloadAsync($"http://mixed.example:{port}/module.kat", CancellationToken.None).AsTask());

        Assert.Equal("public Value = 42", text);
        Assert.Equal(1, server.RequestCount);
    }

    [Theory]
    [InlineData(1)]
    [InlineData(3)]
    [InlineData(7)]
    public async Task StalledAddresses_ShareABoundedPartOfTheDeadline_SoAReachableLastAddressStillAnswers(int stalled)
    {
        // A host with several addresses of which only the last answers. However many stall
        // before it, together they may use no more than a third of the deadline, so the address
        // that answers still has time for the connection and the response. (At five seconds
        // each, three stalled addresses once used up the whole deadline.)
        await using var server = new LoopbackHttpServer(() => LoopbackHttpServer.Ok("public Value = 42"));
        var port = new Uri(server.Url("127.0.0.1")).Port;
        var answer = Enumerable.Range(1, stalled).Select(index => IPAddress.Parse($"203.0.113.{index}")).Append(IPAddress.Loopback).ToArray();
        var dialed = new List<string>();
        var deadline = TimeSpan.FromSeconds(12);
        using var transport = new HttpSourceDownloader(
            HttpSourceDownloader.MaxResponseBodyBytes,
            deadline,
            handler: null,
            new DownloadSeam(
                AllowPlainHttp: true,
                // The documentation range stands in for addresses that never answer: nothing
                // is ever sent to one, because the substituted opener below stalls instead.
                static address => IPAddress.IsLoopback(address) || address.ToString().StartsWith("203.0.113.", StringComparison.Ordinal),
                (_, _) => Task.FromResult(answer))
            {
                OpenAsync = async (target, cancellationToken) =>
                {
                    lock (dialed)
                        dialed.Add("dial " + target.Address);

                    if (IPAddress.IsLoopback(target.Address))
                        return await DownloadSeam.OpenSocketAsync(target, cancellationToken);

                    try
                    {
                        await Task.Delay(Timeout.InfiniteTimeSpan, cancellationToken);
                    }
                    catch (OperationCanceledException)
                    {
                        lock (dialed)
                            dialed.Add("gave up " + target.Address);
                        throw;
                    }

                    throw new InvalidOperationException("unreachable");
                },
            });
        var clock = System.Diagnostics.Stopwatch.StartNew();

        var text = await Guarded(transport.DownloadAsync($"http://many-addresses.example:{port}/module.kat", CancellationToken.None).AsTask());

        Assert.Equal("public Value = 42", text);
        Assert.Equal(1, server.RequestCount);
        // One address at a time, in the answer's order, each given up before the next is dialed.
        var expected = answer[..^1].SelectMany(address => new[] { "dial " + address, "gave up " + address }).Append("dial 127.0.0.1");
        Assert.Equal(expected, dialed);
        // The stalled attempts took their budget, a third of the deadline, and no more than
        // that by any margin a slow machine could explain.
        Assert.Equal(deadline / 3, transport.ConnectFallbackBudget);
        Assert.InRange(clock.Elapsed, transport.ConnectFallbackBudget - TimeSpan.FromSeconds(1), deadline - TimeSpan.FromSeconds(3));
    }

    [Fact]
    public async Task AnAddressThatRefuses_GivesItsTimeBack_AndTheNextIsDialedAtOnce()
    {
        // A refusal is not a stall: the next address is tried immediately, with no waiting.
        await using var server = new LoopbackHttpServer(() => LoopbackHttpServer.Ok("public Value = 42"));
        var port = new Uri(server.Url("127.0.0.1")).Port;
        var dialed = new List<IPAddress>();
        using var transport = new HttpSourceDownloader(
            HttpSourceDownloader.MaxResponseBodyBytes,
            TimeSpan.FromSeconds(30),
            handler: null,
            new DownloadSeam(
                AllowPlainHttp: true,
                static address => IPAddress.IsLoopback(address) || address.ToString().StartsWith("203.0.113.", StringComparison.Ordinal),
                (_, _) => Task.FromResult(new[] { IPAddress.Parse("203.0.113.1"), IPAddress.Parse("203.0.113.2"), IPAddress.Loopback }))
            {
                OpenAsync = (target, cancellationToken) =>
                {
                    lock (dialed)
                        dialed.Add(target.Address);
                    return IPAddress.IsLoopback(target.Address)
                        ? DownloadSeam.OpenSocketAsync(target, cancellationToken)
                        : ValueTask.FromException<Stream>(new SocketException((int)SocketError.ConnectionRefused));
                },
            });
        var clock = System.Diagnostics.Stopwatch.StartNew();

        var text = await Guarded(transport.DownloadAsync($"http://refusing.example:{port}/module.kat", CancellationToken.None).AsTask());

        Assert.Equal("public Value = 42", text);
        Assert.Equal([IPAddress.Parse("203.0.113.1"), IPAddress.Parse("203.0.113.2"), IPAddress.Loopback], dialed);
        // Far less than one stalled attempt's share (five seconds here).
        Assert.True(clock.Elapsed < TimeSpan.FromSeconds(4), $"took {clock.Elapsed}");
    }

    [Fact]
    public async Task WhenEveryAddressStalls_TheDownloadEndsByItsDeadline()
    {
        // The last address is not bounded by the fallback budget; the download's deadline ends it.
        using var transport = new HttpSourceDownloader(
            HttpSourceDownloader.MaxResponseBodyBytes,
            TimeSpan.FromSeconds(3),
            handler: null,
            new DownloadSeam(
                AllowPlainHttp: true,
                static _ => true,
                (_, _) => Task.FromResult(new[] { IPAddress.Parse("203.0.113.1"), IPAddress.Parse("203.0.113.2") }))
            {
                OpenAsync = async (_, cancellationToken) =>
                {
                    await Task.Delay(Timeout.InfiniteTimeSpan, cancellationToken);
                    throw new InvalidOperationException("unreachable");
                },
            });

        var error = await Assert.ThrowsAsync<DownloadException>(
            () => Guarded(transport.DownloadAsync("http://nothing-answers.example/module.kat", CancellationToken.None).AsTask()));

        Assert.Equal(DownloadFailure.DeadlineExceeded, error.Failure);
        Assert.Equal("the download did not complete within 3 seconds.", error.Message);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task AnIpv4MappedAddress_IsDialedAsTheIpv4AddressItCarries(bool literal)
    {
        // ::ffff:a.b.c.d is judged as a.b.c.d, and it must be dialed as a.b.c.d too: an IPv6
        // socket is IPv6-only, so it cannot reach an IPv4 host through the mapped form. Here the
        // mapped loopback address comes once from the resolver and once as a literal in the link.
        await using var server = new LoopbackHttpServer(() => LoopbackHttpServer.Ok("public Value = 42"));
        var port = new Uri(server.Url("127.0.0.1")).Port;
        var mapped = IPAddress.Loopback.MapToIPv6();
        Assert.True(mapped.IsIPv4MappedToIPv6);
        var dialed = new List<IPEndPoint>();
        using var transport = new HttpSourceDownloader(
            HttpSourceDownloader.MaxResponseBodyBytes,
            Deadline,
            handler: null,
            DownloadSeam.LoopbackStandsInForPublic with
            {
                ResolveAsync = (_, _) => Task.FromResult(new[] { mapped }),
                OpenAsync = (target, cancellationToken) =>
                {
                    lock (dialed)
                        dialed.Add(target);
                    return DownloadSeam.OpenSocketAsync(target, cancellationToken);
                },
            });
        var url = literal ? $"http://[{mapped}]:{port}/module.kat" : $"http://mapped.example:{port}/module.kat";

        var text = await Guarded(transport.DownloadAsync(url, CancellationToken.None).AsTask());

        Assert.Equal("public Value = 42", text);
        Assert.Equal(1, server.RequestCount);
        var target = Assert.Single(dialed);
        Assert.Equal(AddressFamily.InterNetwork, target.AddressFamily);
        Assert.Equal(new IPEndPoint(IPAddress.Loopback, port), target);
    }

    [Fact]
    public async Task ANonPublicIpv4MappedAddress_IsStillRefused_AndNeverDialed()
    {
        var dialed = 0;
        using var transport = new HttpSourceDownloader(
            HttpSourceDownloader.MaxResponseBodyBytes,
            Deadline,
            handler: null,
            DownloadSeam.Production with
            {
                ResolveAsync = (_, _) => Task.FromResult(new[] { IPAddress.Parse("10.0.0.1").MapToIPv6(), IPAddress.Loopback.MapToIPv6() }),
                OpenAsync = (target, cancellationToken) =>
                {
                    Interlocked.Increment(ref dialed);
                    return DownloadSeam.OpenSocketAsync(target, cancellationToken);
                },
            });

        var error = await Assert.ThrowsAsync<DownloadException>(
            () => Guarded(transport.DownloadAsync("https://mapped-private.example/module.kat", CancellationToken.None).AsTask()));

        Assert.Equal(DownloadFailure.NonPublicAddress, error.Failure);
        Assert.Equal($"its host is not at a public address ({IPAddress.Parse("10.0.0.1").MapToIPv6()}).", error.Message);
        Assert.Equal(0, dialed);
    }

    [Fact]
    public async Task ThroughTheCli_ALoopbackServerStandsInForAPublicHost_ForAModule()
    {
        // The whole path through real sockets: KatLang admits the module's host (any host),
        // the downloader resolves it, judges the address, connects, and KatLang runs the text.
        await using var server = new LoopbackHttpServer(() => LoopbackHttpServer.Ok("public Value = 41"));
        var port = new Uri(server.Url("127.0.0.1")).Port;
        using var transport = new HttpSourceDownloader(
            HttpSourceDownloader.MaxResponseBodyBytes,
            Deadline,
            handler: new SchemeDowngradingHandler(DownloadSeam.LoopbackStandsInForPublic with
            {
                ResolveAsync = (_, _) => Task.FromResult(new[] { IPAddress.Loopback }),
            }));

        var result = await Guarded(Cli.InvokeWithTransportAsync(
            transport, "eval", $"open 'https://modules.stand-in.example:{port}/module.kat'\nValue + 1\n", "--allow-loading"));

        Assert.Equal((0, "42", ""), (result.ExitCode, result.TrimmedOutput, result.Error));
        Assert.Equal(1, server.RequestCount);
    }

    // ── Names and connections that fail ─────────────────────────────────────

    [Fact]
    public async Task ANameThatDoesNotResolve_IsAFailedDownload()
    {
        using var unknown = new HttpSourceDownloader(
            HttpSourceDownloader.MaxResponseBodyBytes,
            Deadline,
            handler: null,
            DownloadSeam.Production with { ResolveAsync = (_, _) => Task.FromException<IPAddress[]>(new SocketException((int)SocketError.HostNotFound)) });
        using var empty = new HttpSourceDownloader(
            HttpSourceDownloader.MaxResponseBodyBytes,
            Deadline,
            handler: null,
            DownloadSeam.Production with { ResolveAsync = (_, _) => Task.FromResult(Array.Empty<IPAddress>()) });

        foreach (var transport in new[] { unknown, empty })
        {
            var error = await Assert.ThrowsAsync<DownloadException>(
                () => Guarded(transport.DownloadProgramAsync("https://no-such-host.example/program.kat", CancellationToken.None).AsTask()));

            Assert.Equal(DownloadFailure.NameResolution, error.Failure);
            Assert.Equal("its host name could not be resolved.", error.Message);
        }

        var line = CliApplication.DownloadFailureLine("https://no-such-host.example/program.kat", DownloadException.NameResolution());
        Assert.Equal("katlang: cannot download 'https://no-such-host.example/program.kat': its host name could not be resolved.", line);
    }

    [Fact]
    public async Task AnAddressThatRefusesTheConnection_IsAFailedDownload()
    {
        // A port nothing listens on: taken, then released.
        var listener = new TcpListener(IPAddress.Loopback, 0);
        listener.Start();
        var port = ((IPEndPoint)listener.LocalEndpoint).Port;
        listener.Stop();
        using var transport = new HttpSourceDownloader(
            HttpSourceDownloader.MaxResponseBodyBytes, Deadline, handler: null, DownloadSeam.LoopbackStandsInForPublic);

        var error = await Assert.ThrowsAsync<DownloadException>(
            () => Guarded(transport.DownloadAsync($"http://127.0.0.1:{port}/module.kat", CancellationToken.None).AsTask()));

        Assert.Equal(DownloadFailure.ConnectionFailed, error.Failure);
        Assert.Equal("the connection failed.", error.Message);
    }

    [Fact]
    public async Task TheDeadline_CoversNameResolution()
    {
        using var transport = new HttpSourceDownloader(
            HttpSourceDownloader.MaxResponseBodyBytes,
            TimeSpan.FromMilliseconds(400),
            handler: null,
            DownloadSeam.Production with
            {
                ResolveAsync = async (_, cancellationToken) =>
                {
                    await Task.Delay(Timeout.InfiniteTimeSpan, cancellationToken);
                    return [];
                },
            });

        var error = await Assert.ThrowsAsync<DownloadException>(
            () => Guarded(transport.DownloadAsync("https://slow-dns.example/module.kat", CancellationToken.None).AsTask()));

        Assert.Equal(DownloadFailure.DeadlineExceeded, error.Failure);
        Assert.Equal("the download did not complete within 0.4 seconds.", error.Message);
    }

    [Fact]
    public async Task CallerCancellation_DuringNameResolution_CarriesTheCallersToken()
    {
        var resolving = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        using var transport = new HttpSourceDownloader(
            HttpSourceDownloader.MaxResponseBodyBytes,
            Deadline,
            handler: null,
            DownloadSeam.Production with
            {
                ResolveAsync = async (_, cancellationToken) =>
                {
                    resolving.TrySetResult();
                    await Task.Delay(Timeout.InfiniteTimeSpan, cancellationToken);
                    return [];
                },
            });
        using var caller = new CancellationTokenSource();

        var download = transport.DownloadAsync("https://slow-dns.example/module.kat", caller.Token).AsTask();
        await Guarded(resolving.Task);
        await caller.CancelAsync();

        var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => Guarded(download));
        Assert.Equal(caller.Token, error.CancellationToken);
    }

    // ── The address checks that need no network ─────────────────────────────

    [Theory]
    [InlineData("http://example.com/module.kat", "NotHttps", "only HTTPS addresses are downloaded.")]
    [InlineData("ftp://example.com/module.kat", "NotHttps", "only HTTPS addresses are downloaded.")]
    [InlineData("file:///C:/module.kat", "NotHttps", "only HTTPS addresses are downloaded.")]
    [InlineData("data:text/plain,public V = 1", "NotHttps", "only HTTPS addresses are downloaded.")]
    [InlineData("https://alice:s3cret@example.com/module.kat", "UserInformation", "it contains user information ('user@' or 'user:password@').")]
    [InlineData("https://alice@example.com/module.kat", "UserInformation", "it contains user information ('user@' or 'user:password@').")]
    [InlineData("https://@example.com/module.kat", "UserInformation", "it contains user information ('user@' or 'user:password@').")]
    [InlineData("example.com/module.kat", "InvalidAddress", "it is not a valid address.")]
    [InlineData("", "InvalidAddress", "it is not a valid address.")]
    [InlineData("https://exa mple.com/module.kat", "InvalidAddress", "it is not a valid address.")]
    public async Task AnAddressTheDownloaderRefuses_NeverBecomesARequest(string url, string failure, string message)
    {
        var handler = new StubHttpHandler(() => StubHttpHandler.Text("public V = 1"));
        using var transport = handler.Transport();

        foreach (var program in new[] { false, true })
        {
            var error = await Assert.ThrowsAsync<DownloadException>(() => Guarded(Download(transport, url, program)));

            Assert.Equal(Enum.Parse<DownloadFailure>(failure), error.Failure);
            Assert.Equal(message, error.Message);
            Assert.DoesNotContain("s3cret", error.Message);
        }

        Assert.Empty(handler.RequestedUrls);
    }

    [Fact]
    public async Task AFragment_IsNeverSent()
    {
        var handler = new StubHttpHandler(() => StubHttpHandler.Text("public V = 1"));
        using var transport = handler.Transport();

        await Guarded(transport.DownloadAsync("https://example.com/module.kat?x=1#fragment", CancellationToken.None).AsTask());

        Assert.Equal("https://example.com/module.kat?x=1#fragment", Assert.Single(handler.RequestedUrls));
        // The handler sees the request address; what goes on the wire is its path and query.
        await using var server = new LoopbackHttpServer(() => LoopbackHttpServer.Ok("public V = 1"));
        using var real = new HttpSourceDownloader(
            HttpSourceDownloader.MaxResponseBodyBytes, Deadline, handler: null, DownloadSeam.LoopbackStandsInForPublic);
        await Guarded(real.DownloadAsync(server.Url("127.0.0.1") + "?x=1#fragment", CancellationToken.None).AsTask());
        Assert.StartsWith("GET /module.kat?x=1 HTTP/1.1\r\n", Assert.IsType<string>(server.RequestHead), StringComparison.Ordinal);
    }

    // ── A program's content type, over the real transport ───────────────────

    [Fact]
    public async Task AProgram_MustBeServedAsSourceText_AndAModuleNeedNot_OverRealTransport()
    {
        const string html = "HTTP/1.1 200 OK\r\nContent-Type: text/html; charset=utf-8\r\nContent-Length: 16\r\nConnection: close\r\n\r\npublic Value = 1";
        using var transport = new HttpSourceDownloader(
            HttpSourceDownloader.MaxResponseBodyBytes, Deadline, handler: null, DownloadSeam.LoopbackStandsInForPublic);

        await using (var server = new LoopbackHttpServer(() => html))
        {
            var error = await Assert.ThrowsAsync<DownloadException>(
                () => Guarded(transport.DownloadProgramAsync(server.Url("127.0.0.1"), CancellationToken.None).AsTask()));

            Assert.Equal(DownloadFailure.NotKatLangSource, error.Failure);
            Assert.Equal("text/html", error.Returned);
            Assert.Equal(
                $"katlang: not KatLang source: '{server.Url("127.0.0.1")}' returned text/html.",
                CliApplication.DownloadFailureLine(server.Url("127.0.0.1"), error));
        }

        await using (var server = new LoopbackHttpServer(() => html))
        {
            Assert.Equal(
                "public Value = 1",
                await Guarded(transport.DownloadAsync(server.Url("127.0.0.1"), CancellationToken.None).AsTask()));
        }

        await using (var server = new LoopbackHttpServer(() => LoopbackHttpServer.Ok("public Value = 1")))
        {
            Assert.Equal(
                "public Value = 1",
                await Guarded(transport.DownloadProgramAsync(server.Url("127.0.0.1"), CancellationToken.None).AsTask()));
        }

        await using (var server = new LoopbackHttpServer(
            () => "HTTP/1.1 200 OK\r\nContent-Length: 16\r\nConnection: close\r\n\r\npublic Value = 1"))
        {
            var error = await Assert.ThrowsAsync<DownloadException>(
                () => Guarded(transport.DownloadProgramAsync(server.Url("127.0.0.1"), CancellationToken.None).AsTask()));

            Assert.Equal("no Content-Type", error.Returned);
        }
    }

    // ── Support ─────────────────────────────────────────────────────────────

    private static Task<string> Download(HttpSourceDownloader transport, string url, bool program)
        => (program
            ? transport.DownloadProgramAsync(url, CancellationToken.None)
            : transport.DownloadAsync(url, CancellationToken.None)).AsTask();

    private static async Task<T> Guarded<T>(Task<T> operation)
    {
        var finished = await Task.WhenAny(operation, Task.Delay(Watchdog));
        Assert.True(finished == operation, $"The operation did not finish within the {Watchdog.TotalSeconds}s test watchdog.");
        return await operation;
    }

    private static async Task Guarded(Task operation)
    {
        var finished = await Task.WhenAny(operation, Task.Delay(Watchdog));
        Assert.True(finished == operation, $"The operation did not finish within the {Watchdog.TotalSeconds}s test watchdog.");
        await operation;
    }

    /// <summary>A resolver that answers from a function and records every name it was asked.</summary>
    private sealed class RecordingResolver(Func<string, IPAddress[]> answer)
    {
        private readonly List<string> _names = [];

        public IReadOnlyList<string> Names
        {
            get
            {
                lock (_names)
                    return [.. _names];
            }
        }

        public Task<IPAddress[]> ResolveAsync(string host, CancellationToken cancellationToken)
        {
            lock (_names)
                _names.Add(host);
            return Task.FromResult(answer(host));
        }
    }

    /// <summary>
    /// Lets the CLI's HTTPS-only module path reach a plain-HTTP loopback fixture: KatLang
    /// admits only <c>https</c> load targets, so the request arrives as HTTPS, and this handler
    /// sends it as plain HTTP through an inner downloader's own socket handler — the real
    /// connect path, resolver and address rule included.
    /// </summary>
    private sealed class SchemeDowngradingHandler(DownloadSeam seam) : HttpMessageHandler
    {
        private readonly HttpSourceDownloader _inner = new(
            HttpSourceDownloader.MaxResponseBodyBytes, TimeSpan.FromSeconds(20), handler: null, seam);

        protected override async Task<HttpResponseMessage> SendAsync(HttpRequestMessage request, CancellationToken cancellationToken)
        {
            var plain = new UriBuilder(request.RequestUri!) { Scheme = Uri.UriSchemeHttp }.Uri;
            var text = await _inner.DownloadAsync(plain.AbsoluteUri, cancellationToken);
            return StubHttpHandler.Text(text);
        }

        protected override void Dispose(bool disposing)
        {
            if (disposing)
                _inner.Dispose();
            base.Dispose(disposing);
        }
    }
}
