namespace KatLang.Tests;

/// <summary>
/// PROBE (2026-11-18, follow-up of <c>eb67160c</c>): ONE open-target block object that a host-built tree shares
/// between a load-free branch the module loader keeps by reference in a deferred unit and that unit's NESTED
/// placeholder (a load-bearing branch of a family the unit declares, deferred again). A block written as an open
/// target is keyed at the prelude wherever it is written, so one shared object can have ONE static key in the
/// outer unit and in the inner one, and the materialization gate (<c>StaticStructureOperation.CompleteLookups</c>)
/// never rebuilds an inherited entry that has a body: the inner unit might answer with the OUTER unit's completed
/// entry. The probe asks whether anything of that is observable: a valid program must have the value, and an
/// unresolvable target the refusal, of the same tree without the sharing. It did not get that far: the shared tree's
/// EAGER elaboration throws (the skipped probe below records the finding and its reproducer).
///
/// <para>Construction needs the RAW tree: no public entry elaborates a host-built raw tree with loads
/// (<see cref="Parser.ParseAsync"/> takes source text, and a region materializes from the raw body it recorded).
/// The test gives the shared tree to the loader, completes the production front-end passes with
/// that loader's module units, and evaluates the prepared host AST through the public
/// <see cref="Evaluator.RunFlatAsync(Expr, EvaluationLimits?, CancellationToken)"/>. The oracles are the same raw
/// tree staged without the sharing (two block objects) and the source parsed and run normally.</para>
/// </summary>
public class DeferredSharedOpenTargetBlockTests
{
    private const string Host = "modules.example";
    private const string UnusedUrl = "https://" + Host + "/unused.kat";
    private const string Block = "{ public S = { public Y = 3 } }";
    private const string Load = "load('" + UnusedUrl + "')";

    /// <summary>Where the inner unit writes its open of the shared block.</summary>
    public enum InnerPosition
    {
        /// <summary>In the open list of the nested placeholder itself.</summary>
        PlaceholderOpens,

        /// <summary>In a load-free branch of a family nested in the placeholder, which the inner unit keeps by reference.</summary>
        KeptBranchInPlaceholder,
    }

    /// <summary>
    /// The program: <c>F</c>'s second branch is the outer unit; its family <c>K</c> has a load-free branch that opens
    /// the block (kept by reference), and its family <c>G</c> has a load-bearing branch, the inner unit, that opens the
    /// block's <paramref name="innerStep"/> at <paramref name="position"/>. Valid, it is <c>K(5) + G(1) = 8 + 4</c>.
    /// Without <paramref name="loads"/> the two holders are constants: the same tree with nothing deferred.
    /// </summary>
    private static string Source(InnerPosition position, string innerStep, bool loads = true)
    {
        var holder = loads ? Load : "0";
        return "F(0) = 0\n" +
               "F(n) = { H = " + holder + "\n" +
               "  K(0) = 0\n" +
               "  K(j) = { open " + Block + ".S\n" +
               "    j + Y }\n" +
               "  G(0) = 0\n" +
               (position == InnerPosition.PlaceholderOpens
                   ? "  G(m) = { open " + Block + "." + innerStep + "\n" +
                     "    H2 = " + holder + "\n" +
                     "    m + Y }\n"
                   : "  G(m) = { H2 = " + holder + "\n" +
                     "    Q(0) = 0\n" +
                     "    Q(k) = { open " + Block + "." + innerStep + "\n" +
                     "      k + Y }\n" +
                     "    Q(m) }\n") +
               "  K(5) + G(1) }\n" +
               "F(1)\n";
    }

    private sealed class ModuleHost
    {
        public int Fetches { get; private set; }

        public ValueTask<string> Download(string url, CancellationToken cancellationToken)
        {
            Assert.Equal(UnusedUrl, url);
            Fetches++;
            return ValueTask.FromResult("public ZzUnused = 0\n");
        }

        public RunOptions Options => new() { AllowedHosts = [Host], DownloadCode = Download };
    }

    private static Algorithm.Conditional Family(Algorithm owner, string name)
        => Assert.IsType<Algorithm.Conditional>(owner.Properties.Single(property => property.Name == name).Value);

    /// <summary><paramref name="owner"/> with its property <paramref name="name"/> holding <paramref name="value"/>.</summary>
    private static Algorithm.User WithProperty(Algorithm.User owner, string name, Algorithm value)
        => owner with { Properties = [.. owner.Properties.Select(property => property.Name == name ? property.WithValue(value) : property)] };

    /// <summary><paramref name="owner"/> with the second branch of its family <paramref name="name"/> rewritten.</summary>
    private static Algorithm.User WithSecondBranch(Algorithm.User owner, string name, Func<Algorithm.User, Algorithm.User> rewrite)
    {
        var family = Family(owner, name);
        var second = family.Branches[1];
        return WithProperty(owner, name, family with
        {
            Branches = [family.Branches[0], second with { Body = rewrite(Assert.IsType<Algorithm.User>(second.Body)) }],
        });
    }

    /// <summary>The block heading the first open target of <paramref name="owner"/>.</summary>
    private static Expr.AlgorithmExpr OpenHead(Algorithm owner)
        => Assert.IsType<Expr.AlgorithmExpr>(Assert.IsType<Expr.DotCall>(owner.Opens[0]).Target);

    /// <summary>The raw tree, with the inner unit's open target headed by the kept branch's block object when <paramref name="share"/>.</summary>
    private static Algorithm.User RawTree(Algorithm.User raw, InnerPosition position, bool share)
    {
        if (!share)
            return raw;

        var unit = Assert.IsType<Algorithm.User>(Family(raw, "F").Branches[1].Body);
        var kept = OpenHead(Family(unit, "K").Branches[1].Body);
        Algorithm.User ShareHead(Algorithm.User body)
        {
            var dot = Assert.IsType<Expr.DotCall>(body.Opens[0]);
            Assert.NotSame(kept, dot.Target);
            return body with { Opens = [dot with { Target = kept }] };
        }

        return WithSecondBranch(raw, "F", outer => WithSecondBranch(outer, "G", inner =>
            position == InnerPosition.PlaceholderOpens ? ShareHead(inner) : WithSecondBranch(inner, "Q", ShareHead)));
    }

    /// <summary>
    /// Each case should pass eager elaboration. The public evaluator returns either its numeric result
    /// or the nested unit's materialization diagnostics. An unexpected exception retains its stack.
    /// </summary>
    private static async Task<string> StageAndRun(string source, InnerPosition position, bool share, ModuleHost host)
    {
        var diagnostics = new DiagnosticBag();
        var input = FrontEndPipeline.ElaborationInput.Parse(source, diagnostics);
        Assert.Empty(diagnostics);
        var raw = RawTree(Assert.IsType<Algorithm.User>(input.Take()), position, share);
        var loader = new ModuleLoader(diagnostics, host.Download, [Host]);
        input.Put(await loader.ElaborateAsync(raw));
        Assert.Empty(diagnostics);
        Assert.Null(AstStructuralPreflight.Check(input.Current, EvaluationLimits.MaxSupportedAstDepth, AstConsumerProfile.FullyRecursive));
        var modules = loader.ModuleUnits.BeginOperation();
        var rejected = FrontEndPipeline.CompleteBeforeExposure(input, diagnostics, null, modules,
            loader.DeferredRegionCount > 0, null, out var deferredOperation, CancellationToken.None);
        Assert.Null(rejected);
        Assert.Empty(diagnostics);
        var exposed = PropertyExposureResolver.ResolveCompilation(input.Take(), null, null, modules, CancellationToken.None);
        modules.Publish(deferredOperation?.Freeze());

        var result = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(exposed), null, CancellationToken.None);
        if (!result.IsError)
            return "value " + string.Join(", ", result.Value);
        var error = result.Error;
        while (error is EvalError.WithContext context)
            error = context.Inner;
        return error is EvalError.ModuleRegionMaterializationFailed failed
            ? "refused " + string.Join(" | ", failed.Diagnostics.Select(diagnostic => $"{diagnostic.Code}: {diagnostic.Message}"))
            : "error " + result.Error;
    }

    /// <summary>The block's unresolvable step: the inner unit's rows then read <c>Y</c>, which nothing declares.</summary>
    private const string Refused =
        "refused UndeclaredIdentifier: Identifier 'Y' is used in conditional branch '{0}', but it is not declared in the branch pattern.";

    public static TheoryData<InnerPosition, string, string> DeferredCases() => new()
    {
        { InnerPosition.PlaceholderOpens, "S", "value 12" },
        { InnerPosition.KeptBranchInPlaceholder, "S", "value 12" },
        { InnerPosition.PlaceholderOpens, "Nope", string.Format(System.Globalization.CultureInfo.InvariantCulture, Refused, "G") },
        { InnerPosition.KeptBranchInPlaceholder, "Nope", string.Format(System.Globalization.CultureInfo.InvariantCulture, Refused, "Q") },
    };

    /// <summary>
    /// The oracle the probe compares with is sound: the raw tree staged WITHOUT the sharing runs exactly as the source
    /// parsed and run normally — the value, or the same refusal — and downloads the unused module once.
    /// </summary>
    [Theory]
    [MemberData(nameof(DeferredCases))]
    public async Task StagedUnsharedTree_RunsLikeTheSource(InnerPosition position, string innerStep, string expected)
    {
        var source = Source(position, innerStep);
        var normal = await KatLangEngine.RunAsync(source, new ModuleHost().Options);
        var host = new ModuleHost();
        var staged = await StageAndRun(source, position, share: false, host);
        Assert.Equal(1, host.Fetches);
        if (expected.StartsWith("value ", StringComparison.Ordinal))
        {
            Assert.Equal(expected, staged);
            Assert.Equal(expected["value ".Length..], Assert.IsType<RunResult.Success>(normal).ToDisplayString());
            return;
        }

        // One diagnostic, with the message's hint after the expected sentence; the normal run reports it as its one error.
        Assert.StartsWith(expected, staged, StringComparison.Ordinal);
        Assert.DoesNotContain(" | ", staged, StringComparison.Ordinal);
        var error = Assert.Single(Assert.IsType<RunResult.EvalFailure>(normal).Errors);
        Assert.Equal(KatLangErrorCode.UndeclaredIdentifier, error.Code);
        Assert.EndsWith(staged["refused UndeclaredIdentifier: ".Length..], error.Message, StringComparison.Ordinal);
    }

    /// <summary>
    /// THE PROBE. FINDING (2026-11-18, on <c>5fee88d9</c>): the shared tree never reaches a materialization. Its EAGER
    /// elaboration throws <see cref="InvalidOperationException"/> "A static context can publish each pass's body only
    /// once." from <c>StaticStructureOperation.Publish</c>, reached from <c>ParameterDetector.ProcessUserAlgorithm</c>
    /// through <c>ProcessSharedOpenAlgorithm</c> while the detector processes the outer placeholder's branches: the one
    /// block, keyed at the prelude, is published a second time. Every case below, valid or refused, throws so, where
    /// the unshared tree gives 12 or the refusal (<see cref="StagedUnsharedTree_RunsLikeTheSource"/>) and the same
    /// sharing with nothing deferred gives 12
    /// (<see cref="SharedOpenTargetBlock_WithNothingDeferred_RunsLikeTheUnsharedTree"/>). So the question of the
    /// materialization gate stays open behind it. Skipped, not fixed: the deferred-region code is being changed elsewhere.
    /// </summary>
    [Theory(Skip = "FINDING 2026-11-18: the eager elaboration of a host-built tree that shares one open-target block between a deferred unit's kept branch and its nested placeholder throws InvalidOperationException (\"A static context can publish each pass's body only once.\") from ParameterDetector; see the summary.")]
    [MemberData(nameof(DeferredCases))]
    public async Task SharedOpenTargetBlock_BetweenAKeptBranchAndANestedPlaceholder_RunsLikeTheUnsharedTree(
        InnerPosition position, string innerStep, string expected)
    {
        var source = Source(position, innerStep);
        var host = new ModuleHost();
        var shared = await StageAndRun(source, position, share: true, host);
        Assert.Equal(await StageAndRun(source, position, share: false, new ModuleHost()), shared);
        Assert.StartsWith(expected, shared, StringComparison.Ordinal);
        Assert.Equal(1, host.Fetches);
    }

    /// <summary>
    /// The control that places the finding: the SAME sharing in the same tree with nothing deferred (the two holders
    /// constants instead of loads) elaborates and runs like the unshared tree and the source.
    /// </summary>
    [Theory]
    [InlineData(InnerPosition.PlaceholderOpens)]
    [InlineData(InnerPosition.KeptBranchInPlaceholder)]
    public async Task SharedOpenTargetBlock_WithNothingDeferred_RunsLikeTheUnsharedTree(InnerPosition position)
    {
        var source = Source(position, "S", loads: false);
        Assert.Equal("12", Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(source)).ToDisplayString());
        var host = new ModuleHost();
        Assert.Equal("value 12", await StageAndRun(source, position, share: false, host));
        Assert.Equal("value 12", await StageAndRun(source, position, share: true, host));
        Assert.Equal(0, host.Fetches);
    }
}
