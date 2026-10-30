namespace KatLang.Tests;

/// <summary>Independent regressions over the complete ALIAS-UNIFY-1 worktree, including the round-14 witnesses.</summary>
public sealed class AliasUnifyIndependentReviewTests
{
    [Theory]
    [InlineData("public H = fam(Lib.M2.G) + 0\npublic M1 = load('{0}')\npublic M2 = load('{0}')\n")]
    [InlineData("public H = fam(Lib.M1.G) + 0\npublic M1 = load('{0}')\npublic M2 = load('{0}')\n")]
    [InlineData("public H = Lib.M2.G + 0\npublic M1 = load('{0}')\npublic M2 = load('{0}')\n")]
    [InlineData("public M1 = load('{0}')\npublic H = fam(Lib.M2.G) + 0\npublic M2 = load('{0}')\n")]
    [InlineData("public M1 = load('{0}')\npublic M2 = load('{0}')\npublic H = fam(Lib.M2.G) + 0\n")]
    [InlineData("public H = fam(Lib.M2.G) + 0\npublic M2 = load('{0}')\n")]
    public async Task APathIntoASharedModule_ReadsItsProcessedMember_InEveryHolderOrder(string members)
    {
        // The unapplied round-13 coverage witness, independently re-run here: H must see G(x), including
        // through the second holder before its own turn. An async downloader also pins one module unit.
        const string url = "https://katlang.org/lazy/g.kat";
        var downloads = 0;
        var options = new RunOptions
        {
            DownloadCode = async (requested, cancellationToken) =>
            {
                Assert.Equal(url, requested);
                Interlocked.Increment(ref downloads);
                await Task.Yield();
                cancellationToken.ThrowIfCancellationRequested();
                return "F(x) = x\npublic G = F + 0\n0";
            },
        };
        var source = "open M\nM = {\npublic fam(0) = 0\npublic fam(n) = n\n}\nLib = {\n"
            + string.Format(System.Globalization.CultureInfo.InvariantCulture, members, url) + "0\n}\nLib.H(3)";
        var success = Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(source, options));
        Assert.Equal("3", success.ToDisplayString().ReplaceLineEndings("\n"));
        Assert.Equal(1, downloads);
    }

    [Theory]
    [InlineData("{ public K = Lib }.K.f", false)]
    [InlineData("{ public K = Lib }.K.f", true)]
    [InlineData("{ public K = Alias }.K.f", false)]
    [InlineData("{ public K = Alias }.K.f", true)]
    [InlineData("{ public K = { public S = Lib\n0 } }.K.S.f", false)]
    [InlineData("{ public K = { public S = Lib\n0 } }.K.S.f", true)]
    public async Task ABlockHeadedMemberCallee_ReadsItsProcessedReferences(string callee, bool readerFirst)
    {
        // The callee is the family f on all spellings, so G fills a VALUE slot and contributes y to H.
        // Reading the written block's K instead of its processed transparent reference loses f and the lift.
        const string declarations = "Lib = {\npublic f(0) = 0\npublic f(n) = n\n0\n}\nAlias = Lib\n";
        var formula = "H = " + callee + "(G) + 0\n";
        var source = "G(y) = y\n" + (readerFirst ? formula + declarations : declarations + formula) + "H(5)";
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("ok", outcome.Kind);
        Assert.Equal("5", outcome.Value);
    }
}
