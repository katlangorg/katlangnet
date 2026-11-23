using KatLang.ParserFuzz;
using KatLang.Tests.StructuralFuzz;

namespace KatLang.Tests.SemanticTesting;

/// <summary>
/// SEM-2C: the named tick block (<see cref="SemanticTickShapes"/>, ids <c>sys/tick/&lt;group&gt;/&lt;shape&gt;</c>) —
/// <c>tick()</c>-observed evaluation order inside callbacks, loop rows and selectors, member reads through
/// transparent references and forwarding carriers, and two nested parameterized owners. The block adds new ids
/// only (<see cref="SemanticPathCoverageTests"/> and <c>SemanticReductionTests.FixedCorpus_RendersByteIdentically</c>
/// keep pinning every earlier case), its own cases are pinned here, every claim is admitted on runner evidence, and
/// every shape's control — the expectation of its NAMED REJECTED READING over the same program — is rejected.
/// </summary>
public class SemanticTickShapeTests
{
    /// <summary>The block in corpus order. Adding, removing or reordering a shape is a reviewed change of this list.</summary>
    private static readonly string[] ExpectedLocalIds =
    [
        "sys/tick/callback/map",
        "sys/tick/callback/filter",
        "sys/tick/callback/reduce",
        "sys/tick/callback/map-fault",
        "sys/tick/loop/repeat-rows",
        "sys/tick/loop/repeat-rows-crossed",
        "sys/tick/loop/while-flag-first",
        "sys/tick/loop/while-dead-transition",
        "sys/tick/loop/while-fault",
        "sys/tick/select/receiver-first",
        "sys/tick/select/spread-formation",
        "sys/tick/select/retained",
        "sys/tick/select/eager-result",
        "sys/tick/select/reject",
        "sys/tick/member/transparent",
        "sys/tick/member/carrier",
        "sys/tick/member/transparent-chain",
        "sys/tick/member/passed",
        "sys/tick/owners/inner-local",
        "sys/tick/owners/outer-local",
        "sys/tick/owners/inner-local-same-args",
        "sys/tick/owners/outer-local-same-args",
        "sys/tick/owners/chain",
    ];

    /// <summary>
    /// SHA-256 over <see cref="SemanticPathCoverageTests.CanonicalLine"/> of every tick case, in corpus order,
    /// recorded when the block was added. A change means an existing tick id now renders a different program or
    /// expectation, which needs a recipe-version bump instead.
    /// <para>Re-recorded in November 2026 for a LANGUAGE change, not a recipe change: issue #203 made
    /// <c>reduce</c> evaluate its accumulators on demand, so <c>sys/tick/callback/reduce</c> renders the same
    /// program with the expectation of the new semantics (its former expectation is now its rejected reading).
    /// No other tick case changed.</para>
    /// </summary>
    private const string TickBlockDigest = "sha256:395f9c549cb5d0600cc0629b20cab803ad3e39a50cb4629cc0c2e48229ff7038";

    /// <summary>Declaration-reorder members of the block: one per case whose root has two or more declarations.</summary>
    private const int ExpectedReorderMembers = 11;

    private enum PairKind
    {
        /// <summary>Each shape's rejected reading is its partner's intended expectation (the contrast IS the rule).</summary>
        Mirror,

        /// <summary>Both spellings observe the same thing under the rule, while the rejected reading tells them apart.</summary>
        SameObservation,

        /// <summary>Each owner gets a fresh activation on equal arguments at its own level.</summary>
        Contrast,
    }

    private static readonly (string A, string B, PairKind Kind)[] Pairs =
    [
        ("sys/tick/loop/repeat-rows", "sys/tick/loop/repeat-rows-crossed", PairKind.SameObservation),
        ("sys/tick/select/retained", "sys/tick/select/eager-result", PairKind.Mirror),
        ("sys/tick/member/transparent", "sys/tick/member/carrier", PairKind.Mirror),
        ("sys/tick/owners/inner-local", "sys/tick/owners/outer-local", PairKind.Mirror),
        ("sys/tick/owners/inner-local-same-args", "sys/tick/owners/outer-local-same-args", PairKind.Contrast),
    ];

    private static List<SemanticCase> TickCases
        => SemanticGrammarCorpusTests.Cases.Where(c => SemanticTickShapes.IsTickBlock(LocalId(c))).ToList();

    [Fact]
    public void Block_IsExactlyTheNamedShapes_PinnedByDigest_AndEachRebuildsFromItsIdAlone()
    {
        Assert.Equal(ExpectedLocalIds, SemanticTickShapes.Shapes.Select(s => s.LocalId));
        var cases = TickCases;
        Assert.Equal(ExpectedLocalIds, cases.Select(LocalId));
        var digest = SemanticPathCoverageTests.Digest(cases);
        Assert.True(digest == TickBlockDigest, $"tick block changed: digest {digest}, pinned {TickBlockDigest}");

        foreach (var semanticCase in cases)
        {
            Assert.Equal("systematic", semanticCase.Tier);
            Assert.Contains(SemanticTickShapes.Family, semanticCase.Families);
            Assert.True(SemanticCorpus.TryReconstruct(semanticCase.CaseId, SemanticRecipe.RecipeVersion, out var rebuilt, out var problem), problem);
            Assert.Equal(SemanticPathCoverageTests.CanonicalLine(semanticCase), SemanticPathCoverageTests.CanonicalLine(rebuilt));

            // Replay compatibility: the descriptor round-trips and rebuilds without drift.
            var text = SemanticDescriptor.Write(semanticCase);
            Assert.True(SemanticDescriptor.TryParse(text, out var parsed, out var parseProblem), $"{semanticCase.CaseId}: {parseProblem}");
            Assert.Null(SemanticReplay.Drift(parsed.Case, semanticCase));
        }
    }

    /// <summary>Every tick case passes, and every evidence-backed path it claims is admitted on the runner's evidence.</summary>
    [Fact]
    public void EveryTickCase_Passes_WithEveryClaimAdmittedOnEvidence()
    {
        var failures = new List<string>();
        foreach (var semanticCase in TickCases)
        {
            var result = SemanticGrammarCorpusTests.ResultOf(semanticCase);
            if (!result.Passed) failures.Add(SemanticGrammarCorpusTests.Report(semanticCase, result));
            if (!result.PathRejections.IsEmpty) failures.Add($"{semanticCase.CaseId}: rejected claims [{string.Join("; ", result.PathRejections)}]");
            var claimed = semanticCase.Paths & SemanticPath.EvidenceBacked;
            if ((result.PathsExercised & claimed) != claimed)
                failures.Add($"{semanticCase.CaseId}: claimed {claimed}, exercised {result.PathsExercised & SemanticPath.EvidenceBacked}");
        }

        Assert.True(failures.Count == 0, string.Join(Environment.NewLine, failures));

        // The loop rows run planned with their tick() rows as generic expressions, and the dead transition stays planned.
        Assert.All(new[] { "loop/repeat-rows", "loop/repeat-rows-crossed", "loop/while-flag-first", "loop/while-fault" },
            shape => Assert.True(Case(shape).Paths.HasFlag(SemanticPath.GenericInsideOptimizedLoop), shape));
        Assert.True(Case("loop/while-dead-transition").Paths.HasFlag(SemanticPath.OptimizedLoop));
    }

    /// <summary>
    /// The control of every shape: the SAME program built with the expectation of its named rejected reading
    /// (<see cref="SemanticCorpus.TickShapeBuilder"/> with <c>alternative</c>). The expectation must differ from
    /// the intended one, and the runner must reject it on the value, the outcome or the host events — so each
    /// anchor tells the intended rule from a plausible wrong one.
    /// </summary>
    [Fact]
    public void EveryShape_RejectsItsNamedAlternativeReading()
    {
        var failures = new List<string>();
        for (var index = 0; index < SemanticTickShapes.Shapes.Length; index++)
        {
            var shape = SemanticTickShapes.Shapes[index];
            Assert.False(string.IsNullOrWhiteSpace(shape.Rule), shape.LocalId);
            Assert.False(string.IsNullOrWhiteSpace(shape.RejectedReading), shape.LocalId);
            var intended = SemanticCorpus.TickShapeBuilder(index, alternative: false).Build();
            var rejected = SemanticCorpus.TickShapeBuilder(index, alternative: true).Build();
            Assert.Equal(intended.CaseId, rejected.CaseId);
            Assert.Equal(intended.Members.Select(m => m.Source), rejected.Members.Select(m => m.Source));
            Assert.Equal(intended.MinimumCacheHits, rejected.MinimumCacheHits);
            Assert.True(ExpectationText(intended.Expected) != ExpectationText(rejected.Expected),
                $"{shape.LocalId}: the rejected reading '{shape.RejectedReading}' constructs the intended expectation");

            var result = SemanticRunner.Run(rejected);
            if (result.Verdict != SemanticVerdict.Mismatch)
            {
                failures.Add($"{shape.LocalId}: the rejected reading '{shape.RejectedReading}' was not rejected ({result.Verdict})");
                continue;
            }

            // Every structure-projecting surface rejects it on the base member, not only one profile.
            foreach (var profile in new[] { SemanticProfiles.SyncGeneric, SemanticProfiles.SyncOptimized, SemanticProfiles.AsyncTwin })
            {
                if (!result.FindingRecords.Any(f => f.Member == SemanticMember.BaseRole && f.Profile == profile
                        && f.Facet is SemanticFindingFacet.Value or SemanticFindingFacet.Outcome or SemanticFindingFacet.HostEvents))
                    failures.Add($"{shape.LocalId}: {profile} did not reject the rejected reading on its value, outcome or host events");
            }
        }

        Assert.True(failures.Count == 0, string.Join(Environment.NewLine, failures));
    }

    /// <summary>
    /// The variant pairs expose their route and ownership: a mirror pair's rejected readings are each other's
    /// rules, a same-observation pair agrees under the rule and disagrees under the rejected reading, and a
    /// contrast pair's intended observations differ. The pairs are exactly the declared <c>PairedWith</c> links.
    /// </summary>
    [Fact]
    public void VariantPairs_ExposeTheirRouteAndOwnership()
    {
        var declared = SemanticTickShapes.Shapes.Where(s => s.PairedWith is not null)
            .Select(s => (s.LocalId, Partner: SemanticTickShapes.LocalPrefix + s.Group + "/" + s.PairedWith)).ToList();
        Assert.Equal(
            Pairs.SelectMany(p => new[] { (p.A, p.B), (p.B, p.A) }).Order(),
            declared.Order());

        foreach (var (a, b, kind) in Pairs)
        {
            var intendedA = Value(a, alternative: false);
            var intendedB = Value(b, alternative: false);
            var rejectedA = Value(a, alternative: true);
            var rejectedB = Value(b, alternative: true);
            switch (kind)
            {
                case PairKind.Mirror:
                    Assert.Equal(intendedB, rejectedA);
                    Assert.Equal(intendedA, rejectedB);
                    Assert.NotEqual(intendedA, intendedB);
                    break;
                case PairKind.SameObservation:
                    Assert.Equal(intendedA, intendedB);
                    Assert.NotEqual(rejectedA, rejectedB);
                    break;
                default:
                    Assert.NotEqual(intendedA, intendedB);
                    Assert.Equal(intendedB, rejectedA); // Sharing the two equal inner calls looks like outer ownership.
                    Assert.NotEqual(rejectedA, rejectedB); // Sharing equal outer calls persists across outer activations too.
                    break;
            }

            // The two shapes of a pair differ in one construct: same group, no partner, no context.
            var shapeA = SemanticTickShapes.Shapes.Single(s => s.LocalId == a);
            var shapeB = SemanticTickShapes.Shapes.Single(s => s.LocalId == b);
            Assert.Equal(shapeA.Group, shapeB.Group);
            Assert.True(shapeA is { Partner: null, Context: 0 } && shapeB is { Partner: null, Context: 0 }, $"{a} / {b}");
        }
    }

    /// <summary>
    /// The two observation channels stay distinct. Every valid tick case is a Lean-guarded identity-prelude case,
    /// whose RESULT carries the tick order to Lean; a successful shape emits no host event (its order is pinned by
    /// the value on both sides), while a fault shape's traced ticks are C#-only host events and Lean sees its error
    /// kind. Every successful shape ends its row with the evaluation-count control <c>tick()</c>.
    /// </summary>
    [Fact]
    public void LeanSeesTheTickOrder_AndHostEventsStayCSharpEvidence()
    {
        var included = SemanticGeneratedLeanArtifactTests.IncludedCases(SemanticCorpus.All()).Select(c => c.CaseId).ToHashSet(StringComparer.Ordinal);
        foreach (var (shape, index) in SemanticTickShapes.Shapes.Select((s, i) => (s, i)))
        {
            var semanticCase = SemanticCorpus.TickShapeBuilder(index, alternative: false).Build();
            Assert.Contains(semanticCase.CaseId, included);
            var fragment = SemanticTickShapes.Build(shape, new SemanticGrammar.Gen(SemanticChooser.Systematic(0)), alternative: false);
            if (fragment.Failing)
            {
                Assert.NotEmpty(fragment.Events);
                Assert.All(fragment.Events, e => Assert.StartsWith("trace:", e, StringComparison.Ordinal));
                Assert.Contains("failure", fragment.Features);
                Assert.True(shape.Partner is null, $"{shape.LocalId}: a fault shape takes no partner");
            }
            else
            {
                Assert.Empty(fragment.Events);
                Assert.True(fragment.Row is MExpr.ListLit { Items: [.., MExpr.Prim { Name: "tick", Args: [] }] },
                    $"{shape.LocalId}: the row does not end with its tick() count control");
            }
        }
    }

    /// <summary>Alpha-rename runs on every tick case and declaration-reorder exactly where the root has two or more declarations.</summary>
    [Fact]
    public void Transformations_RunWhereSupported()
    {
        var reorders = 0;
        foreach (var semanticCase in TickCases)
        {
            Assert.Contains(semanticCase.Members, m => m.Role == SemanticMember.AlphaRenameRole);
            var hasReorder = semanticCase.Members.Any(m => m.Role == SemanticMember.DeclarationReorderRole);
            var rootDeclarations = SourceProvenance.ParseSyntaxValidRoot(semanticCase.Source).Properties.Count;
            Assert.True(hasReorder == rootDeclarations >= 2, $"{semanticCase.CaseId}: reorder {hasReorder}, {rootDeclarations} root declarations");
            if (hasReorder) reorders++;
            var result = SemanticGrammarCorpusTests.ResultOf(semanticCase);
            Assert.Contains("relation:" + SemanticMember.AlphaRenameRole, result.RelationsChecked);
            Assert.Equal(hasReorder, result.RelationsChecked.Contains("relation:" + SemanticMember.DeclarationReorderRole));
        }

        Assert.Equal(ExpectedReorderMembers, reorders);
    }

    /// <summary>
    /// The symbol-addressed member read renders under its declaration's name, renames with it BY NAME (so a
    /// carrier's own member keeps sharing the target member's name), survives the rewriter, and a read of a
    /// symbol no scope declares is refused.
    /// </summary>
    [Fact]
    public void MemberRead_RendersRenamesAndValidatesWithItsDeclaration()
    {
        static StructuralProgram MemberProgram(string name)
        {
            var shape = SemanticTickShapes.Shapes.Single(s => s.Group == "member" && s.Name == name);
            var gen = new SemanticGrammar.Gen(SemanticChooser.Systematic(0));
            var fragment = SemanticTickShapes.Build(shape, gen, alternative: false);
            return gen.Finish(new MScope(fragment.Decls, [fragment.Row]));
        }

        var program = MemberProgram("carrier");
        program.ValidateNaming();
        var members = ModelRewriter.CollectExprs<MExpr.MemberRead>(program.Root);
        Assert.Equal(2, members.Count);
        var own = members[0].Target;
        var member = members[1].Target;
        Assert.NotEqual(own, member);

        var alpha = SemanticCorpus.AlphaRename(program);
        Assert.Equal(alpha.Names[member], alpha.Names[own]);

        var splitNames = new Dictionary<Sym, string>(program.Names) { [own] = "localMember" };
        var split = program with { Names = splitNames };
        split.ValidateNaming();
        Assert.Contains("v3 = {\n  localMember = tick()", split.Render(), StringComparison.Ordinal);
        Assert.Contains("[v3.localMember, v1.v2, tick()]", split.Render(), StringComparison.Ordinal);

        // Nav(t) = t.M can receive either library or carrier. Both declarations must stay addressable.
        var both = MemberProgram("passed");
        var originalRead = Assert.Single(ModelRewriter.CollectExprs<MExpr.MemberRead>(both.Root), r => r.OtherTargets.Length > 0);
        var rewritten = ModelRewriter.ReplaceExpr(both.Root, originalRead.Receiver, originalRead.Receiver);
        var sharedRead = Assert.Single(ModelRewriter.CollectExprs<MExpr.MemberRead>(rewritten), r => r.OtherTargets.Length > 0);
        var sharedNames = new Dictionary<Sym, string>(both.Names) { [Assert.Single(sharedRead.OtherTargets)] = "localMember" };
        var broken = both with { Root = rewritten, Names = sharedNames };
        Assert.Contains("different names", Assert.Throws<InvalidOperationException>(broken.ValidateNaming).Message, StringComparison.Ordinal);

        var stranger = new Sym(program.Names.Keys.Max(s => s.Id) + 1);
        var dangling = program with { Root = ModelRewriter.ReplaceExpr(program.Root, members[1], members[1] with { Target = stranger }) };
        var refused = Assert.Throws<InvalidOperationException>(dangling.ValidateNaming);
        Assert.Contains("which no scope declares", refused.Message, StringComparison.Ordinal);
    }

    private static SemanticCase Case(string shape) => TickCases.Single(c => LocalId(c) == SemanticTickShapes.LocalPrefix + shape);

    private static string? Value(string localId, bool alternative)
    {
        var index = Array.IndexOf(ExpectedLocalIds, localId);
        Assert.True(index >= 0, localId);
        return SemanticCorpus.TickShapeBuilder(index, alternative).Build().Expected.ValueIdentity;
    }

    private static string ExpectationText(SemanticExpectation e)
        => $"{e.Kind}|{e.ValueIdentity}|{e.EmittedCount}|{e.ErrorCategory}|{string.Join(",", e.Events)}";

    private static string LocalId(SemanticCase c) => c.CaseId[SemanticRecipe.CasePrefix.Length..];
}
