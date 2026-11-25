using System.Text;

namespace KatLang.Tests;

/// <summary>
/// B3-5★ resource policy for formula lifting: lifting STORAGE is charged to the operation's static ledger where it is
/// physically allocated — a flat signature template built on an intern miss, an owner head a composition copies
/// (<see cref="ImplicitSignatureTemplateInterner.SignatureStorageUnits"/> per pattern), a synthesized argument bundle the
/// resolver builds (<see cref="ImplicitArgumentResolver.BundleStorageUnits"/> per argument) — and never per logical read.
///
/// <para>The shape that needs it is a chain of distinct-name lifts, <c>F(i) = F(i-1) + x(i)</c>: each link extends its
/// callee's COMPOSED signature, which copies the callee's local head, so link i holds an i-pattern head and an i-argument
/// bundle and the chain is Θ(N²) physical. Before the charge only the cyclic completion path was metered, so a 67 KB chain
/// elaborated to gigabytes and longer ones exhausted the host; now it is refused deterministically with
/// <see cref="DiagnosticCode.StaticStructureLimitExceeded"/>. FE-3's K owners over one L-wide tail stay O(K + L) and are
/// charged that much.</para>
/// </summary>
public class LiftingChainAdmissionTests
{
    private const long SixtyFourMiB = 64L * 1024 * 1024;
    private const string ModuleHost = "modules.example";

    /// <summary>The chain's property lines: <c>F0 = x0 + 0</c>, then <c>F(i) = F(i-1) + x(i)</c> up to <paramref name="links"/>.</summary>
    private static string ChainLines(int links, string indent = "")
    {
        var builder = new StringBuilder(indent).Append("F0 = x0 + 0\n");
        for (var i = 1; i <= links; i++)
            builder.Append(indent).Append('F').Append(i).Append(" = F").Append(i - 1).Append(" + x").Append(i).Append('\n');
        return builder.ToString();
    }

    /// <summary>The audit's program: the chain, then the root row <c>0</c>.</summary>
    private static string Chain(int links) => ChainLines(links) + "0";

    private static RunOptions Envelope(long bytes) => new() { SourceProcessingLimits = new() { MaxStaticStructureBytes = bytes } };

    /// <summary>Detects and resolves <paramref name="source"/> with observations, returning them and the ledger units resolution added.</summary>
    private static (FrontEndTraversalObservations Observed, long LedgerUnits) Resolve(string source)
    {
        var detected = ParameterDetector.DetectPrevalidated(SourceProvenance.ParseSyntaxValidRoot(source));
        Assert.Empty(detected.Diagnostics);
        var ledger = detected.Operation!.Queries.Resources;
        var before = ledger.MetadataUnits;
        var observed = new FrontEndTraversalObservations();
        var diagnostics = new DiagnosticBag();
        _ = ImplicitArgumentResolver.ResolvePrevalidated(detected, observed, diagnostics);
        Assert.Empty(diagnostics);
        return (observed, ledger.MetadataUnits - before);
    }

    private static long ChargedFor(FrontEndTraversalObservations observed)
        => ImplicitSignatureTemplateInterner.SignatureStorageUnits * (observed.SignatureTemplateSlotsBuilt + observed.OwnerSignatureHeadSlots)
            + ImplicitArgumentResolver.BundleStorageUnits * observed.ImplicitArgumentSlotsBuilt;

    // ── (a) an in-budget chain is unchanged ────────────────────────────────────────────────────────

    /// <summary>
    /// A short chain parses cleanly, and its last link's lifted parameters keep PAR-05's order — its own name, then its
    /// callee's, newest first — and evaluate as before.
    /// </summary>
    [Fact]
    public void AShortChain_ParsesCleanly_WithItsLiftedParametersInOrder()
    {
        const int Links = 64;
        var root = SourceProvenance.ParseValid(Chain(Links)).Root;
        var last = Assert.IsType<Algorithm.User>(Assert.Single(root.Properties, property => property.Name == $"F{Links}").Value);
        Assert.Equal([.. Enumerable.Range(0, Links + 1).Reverse().Select(i => $"x{i}")], last.Params);

        var call = ChainLines(Links) + $"F{Links}({string.Join(", ", Enumerable.Range(0, Links + 1).Reverse())})";
        _ = SourceProvenance.ParseValid(call);
        Assert.Equal("2080", KatLangEngine.Run(call).ToDisplayString());
    }

    // ── (b) a long chain is refused under its envelope ─────────────────────────────────────────────

    /// <summary>
    /// Under a 64-MiB envelope, 256 links are admitted and 1,024 are refused with exactly one unpositioned
    /// <see cref="DiagnosticCode.StaticStructureLimitExceeded"/>: the result is an unevaluable placeholder, nothing is
    /// published, and the engine refuses to run it. The same 1,024 links elaborate under the default envelope.
    /// </summary>
    [Fact]
    public void UnderA64MiBEnvelope_256LinksAreAdmitted_And1024AreRefused()
    {
        var options = Envelope(SixtyFourMiB);
        var admitted = Parser.Parse(Chain(256), options);
        Assert.Empty(admitted.Diagnostics);

        var refused = Parser.Parse(Chain(1024), options);
        var refusal = Assert.Single(refused.Diagnostics);
        Assert.Equal(DiagnosticCode.StaticStructureLimitExceeded, refusal.Code);
        Assert.Equal(DiagnosticSeverity.Error, refusal.Severity);
        Assert.Null(refusal.Span);
        Assert.True(refused.HasErrors);
        Assert.Empty(refused.Root.Properties);
        Assert.Null(refused.Root.CompletedStructure);
        var failure = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(Chain(1024), options));
        Assert.Equal(KatLangErrorCode.StaticStructureLimitExceeded, Assert.Single(failure.Errors).Code);

        Assert.False(Parser.Parse(Chain(1024)).HasErrors);
    }

    // ── (c) a refused chain stops allocating ───────────────────────────────────────────────────────

    /// <summary>
    /// The refused 1,024-link parse allocates a bounded multiple of its 64-MiB envelope: the refusal fires while the
    /// quadratic storage is being built, instead of after the whole elaboration (about 0.5 GB unmetered, 4.4 GB at 3,200
    /// links) has been allocated.
    /// </summary>
    [Fact]
    public void TheRefusedChain_AllocatesABoundedMultipleOfItsEnvelope()
    {
        var options = Envelope(SixtyFourMiB);
        var source = Chain(1024);
        Assert.False(Parser.Parse(Chain(8), options).HasErrors);

        var before = GC.GetAllocatedBytesForCurrentThread();
        var refused = Parser.Parse(source, options);
        var allocated = GC.GetAllocatedBytesForCurrentThread() - before;

        Assert.Equal(DiagnosticCode.StaticStructureLimitExceeded, Assert.Single(refused.Diagnostics).Code);
        Assert.InRange(allocated, 0, 8 * SixtyFourMiB);
    }

    // ── (d) every allocation site is charged ───────────────────────────────────────────────────────

    /// <summary>
    /// The lifting units charged equal the weights times the slots the three allocation hooks observe — flat templates
    /// built, owner heads copied, argument bundles built — so no observed allocation escapes the ledger; and the ledger
    /// really received them (what resolution charges besides lifting stays linear). The chain's physical shape is pinned:
    /// link i copies an i-pattern head and builds an i-argument bundle (plus the first link's and the shared tail's).
    /// </summary>
    [Theory]
    [InlineData(128)]
    [InlineData(256)]
    [InlineData(512)]
    public void EveryLiftingAllocation_IsChargedToTheLedger(int links)
    {
        var (observed, ledgerUnits) = Resolve(Chain(links));

        Assert.Equal(ChargedFor(observed), observed.LiftingStorageUnitsCharged);
        Assert.Equal(1, observed.SignatureTemplateSlotsBuilt);
        Assert.Equal(links, observed.OwnerSignatureInstances);
        Assert.Equal((long)links * (links + 1) / 2, observed.OwnerSignatureHeadSlots);
        Assert.Equal(0, observed.OwnerSignaturesMaterialized);
        Assert.Equal(2 + (long)(links - 1) * links / 2, observed.ImplicitArgumentSlotsBuilt);
        Assert.InRange(ledgerUnits - observed.LiftingStorageUnitsCharged, 0, 128L * links);
    }

    /// <summary>
    /// The interner charges an intern miss and a composition before it allocates — exactly the array it builds, a composed
    /// tail's local head included — and charges nothing for an intern hit or an empty head (the tail itself). A ledger
    /// without room refuses the copy and is failed, without building it.
    /// </summary>
    [Fact]
    public void TheInterner_ChargesExactlyTheArraysItBuilds()
    {
        var ledger = new StaticQueryResourceBudget(StaticQueryLimits.Default);
        var observed = new FrontEndTraversalObservations();
        var interner = new ImplicitSignatureTemplateInterner(observed, ledger, CancellationToken.None);
        ParameterPattern[] tail = [new CaptureParameterPattern("a"), new CaptureParameterPattern("b"), new CaptureParameterPattern("c")];
        var units = ImplicitSignatureTemplateInterner.SignatureStorageUnits;

        var flat = interner.InternFlat(tail);
        Assert.Equal(3 * units, ledger.MetadataUnits);
        Assert.Same(flat, interner.InternFlat([.. tail]));
        Assert.Equal(3 * units, ledger.MetadataUnits);

        var first = interner.Compose([new CaptureParameterPattern("d")], flat);
        Assert.Equal(4 * units, ledger.MetadataUnits);
        var second = interner.Compose([new CaptureParameterPattern("e"), new CaptureParameterPattern("f")], first);
        Assert.Equal(3, second.Head.Count);
        Assert.Same(flat, second.Tail);
        Assert.Equal(7 * units, ledger.MetadataUnits);
        Assert.Same(second, interner.Compose([], second));
        Assert.Equal(7 * units, ledger.MetadataUnits);
        Assert.Equal(ledger.MetadataUnits, observed.LiftingStorageUnitsCharged);
        // Work: a miss's patterns, then one unit per composition — a cyclic completion already charges its compositions'
        // work node by node (SignatureSelector.ChargeComposition), so a copy's patterns are never counted as work twice.
        Assert.Equal(3 + 1 + 1, ledger.AdapterWork);

        var tight = new StaticQueryResourceBudget(new StaticQueryLimits(long.MaxValue, 64, MaxStorageUnits: 2 * units));
        var refusing = new ImplicitSignatureTemplateInterner(null, tight, CancellationToken.None);
        Assert.Throws<StaticQueryLimitExceededException>(() => refusing.Compose([new CaptureParameterPattern("g")], second));
        Assert.True(tight.IsFailed);
        Assert.Equal(0, tight.MetadataUnits);
    }

    // ── (e) FE-3 stays linear ──────────────────────────────────────────────────────────────────────

    private static string Names(string prefix, int count) => string.Join(", ", Enumerable.Range(0, count).Select(i => $"{prefix}{i}"));

    /// <summary>
    /// FE-3's K = L = 512 sibling owners over one L-wide callee (<c>ImplicitSignatureTemplateTests</c>' shapes, with and
    /// without an own parameter per owner): one template, one bundle and per-owner heads exactly as before, a lifting
    /// charge of O(K + L), and no refusal under the default envelope or even a 64-MiB one.
    /// G's names are output rows, as in that class: a 512-term `+` chain would exceed the structural depth gate.
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void Fe3SiblingOwners_AreChargedLinearly_AndAdmitted(bool ownParameter)
    {
        const int Owners = 512;
        const int Width = 512;
        var source = $"G = {Names("v", Width)}\n"
            + string.Concat(Enumerable.Range(0, Owners).Select(i => ownParameter ? $"A{i} = abs(G) + w{i}\n" : $"A{i} = abs(G)\n"))
            + "1";
        _ = SourceProvenance.ParseValid(source);
        Assert.Empty(Parser.Parse(source, Envelope(SixtyFourMiB)).Diagnostics);

        var (observed, _) = Resolve(source);
        Assert.Equal(1, observed.SignatureTemplatesBuilt);
        Assert.Equal(Width, observed.SignatureTemplateSlotsBuilt);
        Assert.Equal(Owners, observed.OwnerSignatureInstances);
        Assert.Equal(ownParameter ? Owners : 0, observed.OwnerSignatureHeadSlots);
        Assert.Equal(0, observed.OwnerSignaturesMaterialized);
        Assert.Equal(1, observed.ImplicitArgumentBundlesBuilt);
        Assert.Equal(Width, observed.ImplicitArgumentSlotsBuilt);
        Assert.Equal(ChargedFor(observed), observed.LiftingStorageUnitsCharged);
        Assert.Equal(
            ImplicitSignatureTemplateInterner.SignatureStorageUnits * (Width + (ownParameter ? Owners : 0)) + ImplicitArgumentResolver.BundleStorageUnits * Width,
            observed.LiftingStorageUnitsCharged);
    }

    // ── a deferred unit: what its module decides is charged to its materialization, the rest to the parse ──

    private static RunOptions ModuleOptions(SourceProcessingLimits? limits = null, string module = "Z = 10\n0")
        => new()
        {
            AllowedHosts = [ModuleHost],
            DownloadCode = (_, _) => ValueTask.FromResult(module),
            SourceProcessingLimits = limits,
        };

    /// <summary>The chain inside a branch body that loads a module: a deferred unit, compiled when <c>G(1)</c> selects it.</summary>
    private static string DeferredChain(int links)
        => "G(0) = 0\nG(a) = {\n    M = load('https://" + ModuleHost + "/m.kat')\n" + ChainLines(links, "    ") + "    M.Z + a\n}\nG(1)";

    /// <summary>
    /// A chain ONLY THE LOADED MODULE DECIDES: each link reads one name <c>S(i)</c>, which a block the root opens provides
    /// as a constant and the branch's module provides as a member that needs a parameter (<c>S(i) = x(i) + 0</c>). With
    /// the module treated as empty the names are the constants and nothing lifts; once it is loaded they are its members
    /// (the branch's own open is consulted first) and the chain is the Θ(N²) one of <see cref="ChainLines"/>.
    /// </summary>
    private static string ModuleDecidedChain(int links)
    {
        var builder = new StringBuilder("open L\nL = {\n");
        for (var i = 0; i <= links; i++)
            builder.Append("    public S").Append(i).Append(" = 0\n");
        builder.Append("}\nG(0) = 0\nG(a) = {\n    open 'https://" + ModuleHost + "/m.kat'\n    F0 = S0 + 0\n");
        for (var i = 1; i <= links; i++)
            builder.Append("    F").Append(i).Append(" = F").Append(i - 1).Append(" + S").Append(i).Append('\n');
        return builder.Append("    Z + a\n}\nG(1)").ToString();
    }

    /// <summary>The module of <see cref="ModuleDecidedChain"/>: <c>Z</c>, and one member per link that needs one parameter.</summary>
    private static string ChainModule(int links)
    {
        var builder = new StringBuilder("public Z = 10\n");
        for (var i = 0; i <= links; i++)
            builder.Append("public S").Append(i).Append(" = x").Append(i).Append(" + 0\n");
        return builder.ToString();
    }

    /// <summary>
    /// The deferred materialization's resolver charges its own operation. The chain here is one only the loaded module
    /// decides, so the provisional body lifts nothing and the eager parse admits the program whatever its length; a short
    /// chain in the selected branch runs, and a long one is refused at run time with the structural resource error.
    /// </summary>
    [Fact]
    public async Task AChainInADeferredUnit_IsChargedToItsMaterialization()
    {
        var limits = new SourceProcessingLimits { MaxStaticStructureBytes = SixtyFourMiB };
        Assert.Empty((await Parser.ParseAsync(ModuleDecidedChain(1024), ModuleOptions(limits, ChainModule(1024)))).Diagnostics);

        var success = Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(ModuleDecidedChain(64), ModuleOptions(limits, ChainModule(64))));
        Assert.Equal("11", success.ToDisplayString());

        var refused = Assert.IsType<RunResult.EvalFailure>(await KatLangEngine.RunAsync(ModuleDecidedChain(1024), ModuleOptions(limits, ChainModule(1024))));
        Assert.Contains(refused.Errors, error => error.Code == KatLangErrorCode.StaticStructureLimitExceeded);
    }

    /// <summary>
    /// A chain the branch writes itself does not depend on its module, so it is resolved in the branch's PROVISIONAL body,
    /// eagerly, like a chain in any other branch (the enclosing declarations are classified from that body, owner decision
    /// 2026-11-16), and its storage is charged to the parse: a short chain is admitted and runs, and a long one is refused
    /// by the parse with the structural resource error, whether or not a run would select the branch. Before, the eager
    /// front end lifted nothing in a load-bearing branch, and this refusal waited for the branch's selection. A chain
    /// over names the module would supply is no different: with the module treated as empty they are inferred parameters.
    /// </summary>
    [Fact]
    public async Task AChainALoadBearingBranchWritesItself_IsChargedToTheParse_LikeAnyOtherBranch()
    {
        var limits = new SourceProcessingLimits { MaxStaticStructureBytes = SixtyFourMiB };
        Assert.Empty((await Parser.ParseAsync(DeferredChain(64), ModuleOptions(limits))).Diagnostics);
        var success = Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(DeferredChain(64), ModuleOptions(limits)));
        Assert.Equal("11", success.ToDisplayString());

        var refused = await Parser.ParseAsync(DeferredChain(1024), ModuleOptions(limits));
        var refusal = Assert.Single(refused.Diagnostics);
        Assert.Equal(DiagnosticCode.StaticStructureLimitExceeded, refusal.Code);
        Assert.Null(refusal.Span);
        var failure = Assert.IsType<RunResult.ParseFailure>(await KatLangEngine.RunAsync(DeferredChain(1024), ModuleOptions(limits)));
        Assert.Equal(KatLangErrorCode.StaticStructureLimitExceeded, Assert.Single(failure.Errors).Code);

        // The same 1,024 links elaborate under the default envelope, in the parse and in the materialization.
        Assert.False((await Parser.ParseAsync(DeferredChain(1024), ModuleOptions())).HasErrors);
    }
}
