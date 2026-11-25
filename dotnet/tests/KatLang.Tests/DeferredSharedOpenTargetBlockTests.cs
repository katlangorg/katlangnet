using System.Numerics;

namespace KatLang.Tests;

/// <summary>
/// ONE open-target block object that a host-built tree shares between places of a deferred unit: a load-free branch the
/// module loader keeps by reference, a NESTED placeholder (a load-bearing branch of a family the unit declares, deferred
/// again) or a load-free branch inside one. A block written as an open target is keyed at the prelude wherever it is
/// written, so the shared object is ONE static context per operation, and the inner unit that materializes a nested
/// placeholder can inherit the OUTER unit's entry for it WITH its body, which the materialization gate
/// (<c>StaticStructureOperation.CompleteLookups</c>) never rebuilds. A valid program must have the value, and an
/// unresolvable target the refusal, of the same tree without the sharing.
///
/// <para>The eager detector used to publish the block twice because it memoized provisional targets per open list.
/// A placeholder and a kept branch also need distinct source views during the outer materialization so the kept
/// branch reports diagnostics and its publication survives the placeholder's retraction in either declaration order.
/// The inner materialization inherits the outer entry if it keeps the raw block by reference again. If it rebuilds
/// its own open list, its block has a fresh entry. The success cases check the actual views and facts.</para>
///
/// <para>Construction needs the RAW tree: no public entry elaborates a host-built raw tree with loads
/// (<see cref="Parser.ParseAsync"/> takes source text, and a region materializes from the raw body it recorded).
/// The test gives the shared tree to the loader, completes the production front-end passes with
/// that loader's module units, and evaluates the prepared host AST through the public evaluator: the asynchronous
/// <see cref="Evaluator.RunFlatAsync(Expr, EvaluationLimits?, CancellationToken)"/>, and the synchronous
/// <see cref="Evaluator.RunFlat(Expr)"/>, which agrees on a tree with nothing deferred and refuses one with a deferred
/// region before evaluating it (the documented async-only contract). The oracles are the same raw tree staged without
/// the sharing (two block objects) and the source run through <see cref="KatLangEngine.RunAsync(string, RunOptions?)"/>
/// and <see cref="KatLangEngine.Run(string, RunOptions?)"/>.</para>
/// </summary>
public class DeferredSharedOpenTargetBlockTests
{
    private const string Host = "modules.example";
    private const string UnusedUrl = "https://" + Host + "/unused.kat";
    private const string Block = "{ public S = { public Y = 3 } }";
    private const string Load = "load('" + UnusedUrl + "')";

    /// <summary>A block whose own open list holds a nested inline target: the shared block is itself a level with opens.</summary>
    private const string BlockWithOpen = "{ open { public Z = 2 }\n    public S = { public Y = Z + 1 } }";

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
    /// The raw tree with EVERY open target headed by a block (in the walk's order: properties as written, branches in
    /// order) headed by the first such block object instead, so the tree holds one block object where the source wrote
    /// <paramref name="expectedShared"/> + 1 equal blocks. The block's own body is not walked, so an open nested in the
    /// block stays its own.
    /// </summary>
    private sealed class HeadSharer(int expectedShared)
    {
        private Expr.AlgorithmExpr? _first;
        private int _shared;

        public Algorithm.User Share(Algorithm.User raw)
        {
            var shared = Assert.IsType<Algorithm.User>(Visit(raw));
            Assert.Equal(expectedShared, _shared);
            return shared;
        }

        private Algorithm Visit(Algorithm algorithm) => algorithm switch
        {
            Algorithm.User user => user with
            {
                Opens = [.. user.Opens.Select(ShareHead)],
                Properties = [.. user.Properties.Select(property => property.WithValue(Visit(property.Value)))],
            },
            Algorithm.Conditional family => family with
            {
                Branches = [.. family.Branches.Select(branch => branch with { Body = Visit(branch.Body) })],
            },
            _ => algorithm,
        };

        private Expr ShareHead(Expr open)
        {
            if (open is not Expr.DotCall { Target: Expr.AlgorithmExpr head } dot)
                return open;
            if (_first is null)
            {
                _first = head;
                return open;
            }

            Assert.NotSame(_first, head);
            _shared++;
            return dot with { Target = _first };
        }
    }

    private static Func<Algorithm.User, Algorithm.User> SharedHeads(bool share, int expectedShared)
        => raw => share ? new HeadSharer(expectedShared).Share(raw) : raw;

    private static Task<StagedOutcome> StageAndRun(string source, InnerPosition position, bool share, ModuleHost host)
        => StageAndRun(source, raw => RawTree(raw, position, share), host,
            share ? (root, succeeded) => CheckMaterializedBlocks(root, position, succeeded) : null);

    private static void CheckMaterializedBlocks(Algorithm root, InnerPosition position, bool succeeded)
    {
        var region = Family(root, "F").Branches[1].Body.DeferredRegion;
        if (region is null) return; // The load-free control.
        Assert.True(region.TryGetMaterialized(out var outer));
        var kept = OpenHead(Family(outer, "K").Branches[1].Body).Algorithm;
        var nested = Family(outer, "G").Branches[1].Body.DeferredRegion!;
        if (!succeeded)
        {
            Assert.False(nested.TryGetMaterialized(out _));
            return;
        }
        Assert.True(nested.TryGetMaterialized(out var inner));

        var inside = OpenHead(position == InnerPosition.PlaceholderOpens
            ? inner : Family(inner, "Q").Branches[1].Body).Algorithm;
        var facts = inner.CompletedStructure!.Facts;
        var key = facts.Child(facts.PreludeKey, inside)!;
        Assert.Same(inside, facts.Facts(key)!.Body);
        if (position == InnerPosition.KeptBranchInPlaceholder)
        {
            Assert.Same(kept, inside);
            var earlier = outer.CompletedStructure!.Facts;
            Assert.Same(earlier.Facts(key), facts.Facts(key));
        }
        else
            Assert.NotSame(kept, inside);
    }

    /// <summary>
    /// Each case passes eager elaboration. The public evaluator returns either its numeric result
    /// or the nested unit's materialization diagnostics; an unexpected exception keeps its stack.
    /// </summary>
    private static async Task<StagedOutcome> StageAndRun(string source, Func<Algorithm.User, Algorithm.User> shape, ModuleHost host, Action<Algorithm, bool>? inspect = null)
    {
        var diagnostics = new DiagnosticBag();
        var input = FrontEndPipeline.ElaborationInput.Parse(source, diagnostics);
        Assert.Empty(diagnostics);
        var raw = shape(Assert.IsType<Algorithm.User>(input.Take()));
        var loader = new ModuleLoader(diagnostics, host.Download, [Host]);
        input.Put(await loader.ElaborateAsync(raw));
        Assert.Empty(diagnostics);
        Assert.Null(AstStructuralPreflight.Check(input.Current, EvaluationLimits.MaxSupportedAstDepth, AstConsumerProfile.FullyRecursive));
        var modules = loader.ModuleUnits.BeginOperation();
        var deferred = loader.DeferredRegionCount > 0;
        var rejected = FrontEndPipeline.CompleteBeforeExposure(input, diagnostics, null, modules,
            deferred, null, out var deferredOperation, CancellationToken.None);
        Assert.Null(rejected);
        Assert.Empty(diagnostics);
        var exposed = PropertyExposureResolver.ResolveCompilation(input.Take(), null, null, modules, CancellationToken.None);
        modules.Publish(deferredOperation?.Freeze());
        var program = new Expr.AlgorithmExpr(exposed);

        // The synchronous entry: the same outcome with nothing deferred; with a deferred region, the documented refusal of
        // the route before anything is evaluated (no module is fetched).
        StagedOutcome? synchronous = null;
        if (deferred)
        {
            var fetches = host.Fetches;
            var refused = Assert.Throws<InvalidOperationException>(() => Evaluator.RunFlat(program));
            Assert.StartsWith("The program contains conditional branches whose module dependencies load on demand", refused.Message, StringComparison.Ordinal);
            Assert.Equal(fetches, host.Fetches);
        }
        else
        {
            synchronous = Outcome(Evaluator.RunFlat(program));
        }

        var outcome = Outcome(await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(exposed), null, CancellationToken.None));
        if (synchronous is not null)
            Assert.Equal(synchronous, outcome);
        inspect?.Invoke(exposed, outcome.Span is null);
        return outcome;
    }

    private sealed record StagedOutcome(string Text, SourceSpan? Span = null);

    private static StagedOutcome Outcome(EvalResult<IReadOnlyList<Decimal128>> result)
    {
        if (!result.IsError)
            return new("value " + string.Join(", ", result.Value));
        var error = result.Error;
        while (error is EvalError.WithContext context)
            error = context.Inner;
        var failed = Assert.IsType<EvalError.ModuleRegionMaterializationFailed>(error);
        var diagnostic = Assert.Single(failed.Diagnostics);
        Assert.NotNull(diagnostic.Span);
        return new($"refused {diagnostic.Code}: {diagnostic.Message}", diagnostic.Span);
    }

    /// <summary>
    /// The source parsed and run normally, through the asynchronous engine entry and the synchronous one: without a load
    /// both give the same; with one, the synchronous entry (no downloader) refuses each load as the documented parse
    /// error, never an exception about the program.
    /// </summary>
    private static async Task<RunResult> RunSource(string source, bool loads = true)
    {
        var normal = await KatLangEngine.RunAsync(source, new ModuleHost().Options);
        var synchronous = KatLangEngine.Run(source);
        if (loads)
        {
            var unavailable = Assert.IsType<RunResult.ParseFailure>(synchronous);
            Assert.NotEmpty(unavailable.Errors);
            Assert.All(unavailable.Errors, error => Assert.Equal(KatLangErrorCode.LoadElaborationUnavailable, error.Code));
        }
        else
        {
            Assert.Equal(
                Assert.IsType<RunResult.Success>(normal).ToDisplayString(),
                Assert.IsType<RunResult.Success>(synchronous).ToDisplayString());
        }

        return normal;
    }

    /// <summary>
    /// The staged outcome agrees with the source's: the same value, or the same single refusal, which the engine reports
    /// as its one error with the call context in front of the message.
    /// </summary>
    private static void AssertAgreesWithTheSource(StagedOutcome result, RunResult normal)
    {
        var staged = result.Text;
        if (staged.StartsWith("value ", StringComparison.Ordinal))
        {
            Assert.Equal(staged["value ".Length..], Assert.IsType<RunResult.Success>(normal).ToDisplayString());
            return;
        }

        Assert.StartsWith("refused ", staged, StringComparison.Ordinal);
        Assert.DoesNotContain(" | ", staged, StringComparison.Ordinal);
        var error = Assert.Single(Assert.IsType<RunResult.EvalFailure>(normal).Errors);
        Assert.Equal(error.Span, result.Span);
        var separator = staged.IndexOf(": ", StringComparison.Ordinal);
        Assert.Equal(staged["refused ".Length..separator], error.Code.ToString());
        Assert.EndsWith(staged[(separator + 2)..], error.Message, StringComparison.Ordinal);
    }

    /// <summary>The block's unresolvable step: the inner unit's rows then read <c>Y</c>, which nothing declares.</summary>
    private const string Refused =
        "refused UndeclaredIdentifier: Identifier 'Y' is used in conditional branch '{0}', but it is not declared in the branch pattern.";

    private static string RefusedIn(string branch) => string.Format(System.Globalization.CultureInfo.InvariantCulture, Refused, branch);

    public static TheoryData<InnerPosition, string, string> DeferredCases() => new()
    {
        { InnerPosition.PlaceholderOpens, "S", "value 12" },
        { InnerPosition.KeptBranchInPlaceholder, "S", "value 12" },
        { InnerPosition.PlaceholderOpens, "Nope", RefusedIn("G") },
        { InnerPosition.KeptBranchInPlaceholder, "Nope", RefusedIn("Q") },
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
        var normal = await RunSource(source);
        var host = new ModuleHost();
        var staged = await StageAndRun(source, position, share: false, host);
        Assert.Equal(1, host.Fetches);
        Assert.StartsWith(expected, staged.Text, StringComparison.Ordinal);
        AssertAgreesWithTheSource(staged, normal);
    }

    /// <summary>
    /// THE PROBE, now the regression of its finding (see the class summary): the shared tree elaborates eagerly, each unit
    /// materializes, and the program gives what the unshared tree and the source give — 12, or the inner unit's refusal of
    /// the unresolvable step. With the block held by a branch the inner unit keeps by reference, the inner unit reads the
    /// outer unit's completed entry for it (it receives that unit's views), and nothing of that is observable.
    /// </summary>
    [Theory]
    [MemberData(nameof(DeferredCases))]
    public async Task SharedOpenTargetBlock_BetweenAKeptBranchAndANestedPlaceholder_RunsLikeTheUnsharedTree(
        InnerPosition position, string innerStep, string expected)
    {
        var source = Source(position, innerStep);
        var host = new ModuleHost();
        var shared = await StageAndRun(source, position, share: true, host);
        Assert.Equal(await StageAndRun(source, position, share: false, new ModuleHost()), shared);
        Assert.StartsWith(expected, shared.Text, StringComparison.Ordinal);
        Assert.Equal(1, host.Fetches);
        AssertAgreesWithTheSource(shared, await RunSource(source));
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
        Assert.Equal("12", Assert.IsType<RunResult.Success>(await RunSource(source, loads: false)).ToDisplayString());
        var host = new ModuleHost();
        Assert.Equal(new StagedOutcome("value 12"), await StageAndRun(source, position, share: false, host));
        Assert.Equal(new StagedOutcome("value 12"), await StageAndRun(source, position, share: true, host));
        Assert.Equal(0, host.Fetches);
    }

    private static string KeptBranch(string family, string block, string step, string row)
        => "  " + family + "(0) = 0\n" +
           "  " + family + "(j) = { open " + block + "." + step + "\n" +
           "    " + row + " }\n";

    private static string PlaceholderOpening(string family, string holder, string block, string step, string row)
        => "  " + family + "(0) = 0\n" +
           "  " + family + "(m) = { open " + block + "." + step + "\n" +
           "    " + holder + " = " + Load + "\n" +
           "    " + row + " }\n";

    private static string PlaceholderKeeping(string family, string holder, string inner, string block, string step, string row)
        => "  " + family + "(0) = 0\n" +
           "  " + family + "(m) = { " + holder + " = " + Load + "\n" +
           "    " + inner + "(0) = 0\n" +
           "    " + inner + "(k) = { open " + block + "." + step + "\n" +
           "      " + row + " }\n" +
           "    " + inner + "(m) }\n";

    private static string Unit(string families, string output)
        => "F(0) = 0\nF(n) = { H = " + Load + "\n" + families + "  " + output + " }\n";

    /// <summary>
    /// Further shapes of one shared block, each with its expected outcome and the number of written blocks that become
    /// the first one:
    /// <list type="bullet">
    /// <item>two load-free branches of the outer unit: provisional reaches only eagerly, reaches with diagnostics only in
    /// the unit;</item>
    /// <item>two nested placeholders, holding the block in their own open lists or in a load-free branch each: provisional
    /// reaches eagerly and in the outer unit, and each inner unit its own;</item>
    /// <item>a block with an open of its own, shared by two load-free branches or by a load-free branch and a placeholder's
    /// own open list;</item>
    /// <item>an eager holder written before or after the deferred family: the loader's load-free walk copies the eager
    /// holder's block, so the eager operation sees separate objects and the
    /// unit elaborates the copy it keeps.</item>
    /// </list>
    /// </summary>
    public static TheoryData<string, string, int, string> SharedVariants() => new()
    {
        {
            "two kept branches",
            Unit(KeptBranch("K", Block, "S", "j + Y") + KeptBranch("L", Block, "S", "j * Y"), "K(5) + L(2)") + "F(1)\n",
            1, "value 14"
        },
        {
            "two kept branches, one step unresolvable",
            Unit(KeptBranch("K", Block, "S", "j + Y") + KeptBranch("L", Block, "Nope", "j * Y"), "K(5) + L(2)") + "F(1)\n",
            1, RefusedIn("L")
        },
        {
            "two placeholders opening the block",
            Unit(PlaceholderOpening("G", "H2", Block, "S", "m + Y") + PlaceholderOpening("P", "H3", Block, "S", "m * Y"), "G(1) + P(2)") + "F(1)\n",
            1, "value 10"
        },
        {
            "two placeholders keeping a branch that opens the block",
            Unit(PlaceholderKeeping("G", "H2", "Q", Block, "S", "k + Y") + PlaceholderKeeping("P", "H3", "R", Block, "S", "k * Y"), "G(1) + P(2)") + "F(1)\n",
            1, "value 10"
        },
        {
            "two placeholders keeping a branch, one step unresolvable",
            Unit(PlaceholderKeeping("G", "H2", "Q", Block, "S", "k + Y") + PlaceholderKeeping("P", "H3", "R", Block, "Nope", "k * Y"), "G(1) + P(2)") + "F(1)\n",
            1, RefusedIn("R")
        },
        {
            "a block with an open, two kept branches",
            Unit(KeptBranch("K", BlockWithOpen, "S", "j + Y") + KeptBranch("L", BlockWithOpen, "S", "j * Y"), "K(5) + L(2)") + "F(1)\n",
            1, "value 14"
        },
        {
            "a block with an open, a kept branch and a placeholder opening it",
            Unit(KeptBranch("K", BlockWithOpen, "S", "j + Y") + PlaceholderOpening("G", "H2", BlockWithOpen, "S", "m + Y"), "K(5) + G(1)") + "F(1)\n",
            1, "value 12"
        },
        {
            "an eager holder before the deferred family",
            "A = { open " + Block + ".S\n  Y }\n" + Unit(KeptBranch("K", Block, "S", "j + Y"), "K(5)") + "A + F(1)\n",
            1, "value 11"
        },
        {
            "an eager holder after the deferred family",
            Unit(KeptBranch("K", Block, "S", "j + Y"), "K(5)") + "A = { open " + Block + ".S\n  Y }\n" + "A + F(1)\n",
            1, "value 11"
        },
        {
            "the inner validator rejects a missing step on the inherited block",
            Unit(KeptBranch("K", BlockWithOpen, "S", "j + Y") + PlaceholderKeeping("G", "H2", "Q", BlockWithOpen, "Nope", "k"), "K(5) + G(1)") + "F(1)\n",
            1, "refused UnresolvedOpenTarget:"
        },
        {
            "the kept branch reports after an earlier placeholder",
            Unit(PlaceholderKeeping("G", "H2", "Q", Block, "S", "k + Y") + KeptBranch("K", Block, "Nope", "j"), "K(5) + G(1)") + "F(1)\n",
            1, "refused UnresolvedOpenTarget:"
        },
        {
            "a placeholder before the kept branch",
            Unit(PlaceholderKeeping("G", "H2", "Q", Block, "S", "k + Y") + KeptBranch("K", Block, "S", "j + Y"), "K(5) + G(1)") + "F(1)\n",
            1, "value 12"
        },
        {
            "a block with an open, kept again in the inner unit",
            Unit(KeptBranch("K", BlockWithOpen, "S", "j + Y") + PlaceholderKeeping("G", "H2", "Q", BlockWithOpen, "S", "k + Y"), "K(5) + G(1)") + "F(1)\n",
            1, "value 12"
        },
    };

    /// <summary>
    /// The further shapes (see <see cref="SharedVariants"/>) run like the unshared tree and the source, and download the
    /// unused module once.
    /// </summary>
    [Theory]
    [MemberData(nameof(SharedVariants))]
    public async Task SharedOpenTargetBlock_FurtherShapes_RunLikeTheUnsharedTree(string shape, string source, int shared, string expected)
    {
        Assert.NotEmpty(shape);
        var host = new ModuleHost();
        var outcome = await StageAndRun(source, SharedHeads(share: true, shared), host);
        Assert.Equal(await StageAndRun(source, SharedHeads(share: false, 0), new ModuleHost()), outcome);
        Assert.StartsWith(expected, outcome.Text, StringComparison.Ordinal);
        Assert.Equal(1, host.Fetches);
        AssertAgreesWithTheSource(outcome, await RunSource(source));
    }

    [Fact]
    public async Task Placeholder_ReachesTheSharedOpenBlockThroughACallArgument()
    {
        var source = Unit("  G(0) = 0\n" +
            "  G(m) = { H2 = " + Load + "\n" +
            "    if(true, { open " + Block + ".S\n      m + Y }, 0) }\n" +
            KeptBranch("K", Block, "S", "j + Y"), "K(5) + G(1)") + "F(1)\n";

        static Algorithm.User ShareThroughArgument(Algorithm.User raw) => WithSecondBranch(raw, "F", outer =>
        {
            var kept = OpenHead(Family(outer, "K").Branches[1].Body);
            return WithSecondBranch(outer, "G", body =>
            {
                var call = Assert.IsType<Expr.Call>(Assert.Single(body.Output));
                var argument = Assert.IsType<Expr.AlgorithmExpr>(call.Args[1]);
                var holder = Assert.IsType<Algorithm.User>(argument.Algorithm);
                var open = Assert.IsType<Expr.DotCall>(Assert.Single(holder.Opens));
                var shared = argument with { Algorithm = holder with { Opens = [open with { Target = kept }] } };
                return body with { Output = [call with { Args = [call.Args[0], shared, call.Args[2]] }] };
            });
        });

        var host = new ModuleHost();
        var shared = await StageAndRun(source, ShareThroughArgument, host);
        Assert.Equal(new StagedOutcome("value 12"), shared);
        Assert.Equal(1, host.Fetches);
        Assert.Equal(await StageAndRun(source, raw => raw, new ModuleHost()), shared);
        AssertAgreesWithTheSource(shared, await RunSource(source));
    }

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public async Task SharedBlock_ReportsItsOwnDiagnosticAtTheKeptOccurrence(bool placeholderFirst)
    {
        const string invalid = "{ public S = { public Y = 3 }\n    Broken(x) = ~x }";
        var kept = KeptBranch("K", invalid, "S", "j + Y");
        var placeholder = PlaceholderKeeping("G", "H2", "Q", invalid, "S", "k + Y");
        var source = Unit(placeholderFirst ? placeholder + kept : kept + placeholder, "K(5) + G(1)") + "F(1)\n";
        // Give both reaches K's actual source object, including the invalid marker's span.
        var shared = await StageAndRun(source, raw => RawTree(raw, InnerPosition.KeptBranchInPlaceholder, share: true), new ModuleHost());
        var unshared = await StageAndRun(source, raw => raw, new ModuleHost());
        Assert.StartsWith("refused InvalidGraceMarker:", shared.Text, StringComparison.Ordinal);
        Assert.Equal(unshared, shared);
        AssertAgreesWithTheSource(shared, await RunSource(source));
    }

    /// <summary>
    /// The publication guard still refuses a GENUINE double publication of an open-target block's one context: a second
    /// detected or resolved view in the operation that published the first, and any other view of an entry an earlier
    /// operation completed, in the unit that inherits it. Receiving the published view is what the passes do instead;
    /// <c>InheritedOpenBlock</c> finds the inherited entry from the block or from a view of it, and nothing in an
    /// operation that inherits nothing.
    /// </summary>
    [Fact]
    public void PublicationGuard_StillRefusesASecondViewOfAnOpenTargetBlock()
    {
        var root = SourceProvenance.ParseSyntaxValidRoot("A = { open { public S = 1 }.S\n  S }\nA\n");
        var holder = root.Properties.Single(property => property.Name == "A").Value;
        var block = OpenHead(holder).Algorithm;
        var operation = StaticStructureAdmission.Create(root).Operation;
        var prelude = operation.Queries.Keys.Root;
        var key = operation.ContextOf(prelude, block);
        var detected = block with { };
        var resolved = block with { };

        operation.Publish(key, StaticPublicationStage.Detected, detected);
        operation.Publish(key, StaticPublicationStage.Detected, detected);
        var second = Assert.Throws<InvalidOperationException>(() => operation.Publish(key, StaticPublicationStage.Detected, block with { }));
        Assert.Equal("A static context can publish each pass's body only once.", second.Message);
        operation.Publish(key, StaticPublicationStage.Resolved, resolved);
        Assert.Throws<InvalidOperationException>(() => operation.Publish(key, StaticPublicationStage.Resolved, block with { }));
        Assert.Null(operation.InheritedOpenBlock(block, StaticPublicationStage.Detected));
        Assert.Same(resolved, operation.Published(key, StaticPublicationStage.Resolved));

        var a = operation.ContextOf(operation.Root, holder);
        operation.Publish(a, StaticPublicationStage.Detected, holder);
        operation.Publish(a, StaticPublicationStage.Resolved, holder);
        operation.Publish(operation.Root, StaticPublicationStage.Detected, root);
        operation.Publish(operation.Root, StaticPublicationStage.Resolved, root);
        var unit = operation.Freeze().Materialize(operation.Root, SourceProvenance.ParseSyntaxValidRoot("0"), new Pattern.Bind("n"),
            new(1_000_000, 4, 200_000, 4_000_000));

        Assert.Same(detected, unit.InheritedOpenBlock(block, StaticPublicationStage.Detected));
        Assert.Same(resolved, unit.Published(key, StaticPublicationStage.Resolved));
        Assert.Same(key, unit.ContextOf(prelude, block));
        unit.Publish(key, StaticPublicationStage.Detected, detected);
        var changed = Assert.Throws<InvalidOperationException>(() => unit.Publish(key, StaticPublicationStage.Detected, block with { }));
        Assert.Equal("A completed external publication cannot change.", changed.Message);
        Assert.Throws<InvalidOperationException>(() => unit.Publish(key, StaticPublicationStage.Resolved, block with { }));
    }
}
